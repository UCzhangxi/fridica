//! Drains the durable outbox through a delivery adapter, a bounded batch per
//! pass; the outcome mapping (sent, retry, ambiguous, rejected) is the store's.
use crate::{
    core::{
        delivery::{Delivery, DeliveryOutcome},
        time::Clock,
    },
    github::client::{Api, Operation, Request},
    store::Shared,
};
use anyhow::{bail, Result};
use fridica_core::{
    delivery::ClaimedPost,
    egress::{self, DenyList},
    store::{ArrivedMessage, PostOutcome, Store as _},
};
use regex::Regex;
use std::{
    path::Path,
    sync::{Arc, LazyLock},
    time::Duration,
};

static VERDICT: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"^VERDICT (\S+)#([0-9]{1,9}) ([0-9a-f]{40}) (approve \(code review\)|approve|changes)$",
    )
    .unwrap()
});
static SUBJECT: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"([\w.-]+/[\w.-]+)(?:#|/pull/)([0-9]{1,9})").unwrap());

/// The PRs a job brief names (`<owner>/<repo>#<PR>` or a pull URL): the only
/// ones its verdict lines may sign.
pub(crate) fn subjects(brief: &str) -> Vec<String> {
    let names = SUBJECT.captures_iter(brief);
    names.map(|m| format!("{}#{}", &m[1], &m[2])).collect()
}
/// A text's verdict lines outside code fences, and its other lines.
pub(crate) fn verdicts(text: &str) -> (Vec<&str>, Vec<&str>) {
    let mut fenced = false;
    text.lines().partition(|line| {
        let line = line.trim_start();
        let fence = ["```", "~~~"].into_iter().find(|f| line.starts_with(f));
        fenced ^= fence.is_some_and(|f| line.matches(f).count() % 2 == 1);
        !fenced && line.starts_with("VERDICT ")
    })
}
/// The text with its verdict lines first, so a split keeps them in the post.
pub(crate) fn hoist(text: &str) -> String {
    match verdicts(text) {
        (lines, _) if lines.is_empty() => text.into(),
        (lines, rest) => [lines, rest].concat().join("\n"),
    }
}

pub struct Dispatcher<D: Delivery> {
    pub store: Shared,
    pub delivery: Arc<D>,
    pub clock: Arc<dyn Clock>,
    pub owner: String,
    pub observe_only: bool,
    pub timeout: Duration,
    /// Reads a PR's live head for verdict lines; None signs nothing.
    pub heads: Option<Arc<dyn Api>>,
}
impl<D: Delivery> Dispatcher<D> {
    /// Turns each `VERDICT <owner>/<repo>#<PR> <sha> <verdict>` line outside
    /// code fences (provision04) into one line on top: the SIGN-OFF line only
    /// if the PR is one the job's brief names (`review`) and its head, read
    /// now, is still `<sha>`; else why it was not signed.
    async fn sign(&self, text: &str, review: &[String]) -> String {
        let (lines, rest) = verdicts(text);
        let (mut top, mut first) = (vec![], None);
        let parsed: Vec<_> = lines
            .iter()
            .filter_map(|l| VERDICT.captures(l.trim()))
            .collect();
        for line in &lines {
            let Some(m) = VERDICT.captures(line.trim()) else {
                top.push(format!(
                    "Not signed: malformed verdict line: {}",
                    line.trim()
                ));
                continue;
            };
            let (repo, n, sha, verdict) = (&m[1], m[2].parse().unwrap_or(0), &m[3], &m[4]);
            let live = match &self.heads {
                _ if review.is_empty() => Err("no review subject".into()),
                _ if !review.contains(&format!("{repo}#{n}")) => {
                    Err(format!("the job reviews {}", review.join(", ")))
                }
                _ if parsed
                    .iter()
                    .any(|o| o[1] == m[1] && o[2] == m[2] && (&o[3], &o[4]) != (&m[3], &m[4])) =>
                {
                    Err("conflicting verdicts".into())
                }
                _ if *first.get_or_insert_with(|| repo.to_owned()) != repo => {
                    Err("one repository per message".into())
                }
                Some(api) => api
                    .get(Request {
                        repo: repo.into(),
                        operation: Operation::Pull { number: n },
                    })
                    .await
                    .map_err(|e| format!("head not read: {}", e.message()))
                    .and_then(|v| {
                        v["head"]["sha"]
                            .as_str()
                            .map(str::to_owned)
                            .ok_or("head not read".into())
                    }),
                None => Err("head not read: GitHub is off".into()),
            };
            let line = match live {
                Ok(live) if live == sha => format!("SIGN-OFF #{n} {sha} {verdict}"),
                Ok(live) => format!("#{n} not signed: its head moved from {sha} to {live}."),
                Err(why) => format!("#{n} not signed: {why}."),
            };
            if !top.contains(&line) {
                top.push(line);
            }
        }
        if top.is_empty() {
            return text.into();
        }
        top.extend(rest.into_iter().map(str::to_owned));
        top.join("\n")
    }
    /// Bound each pass so intake/control tasks cannot be starved by a busy queue.
    pub async fn drain(&self, limit: usize) -> Result<usize> {
        self.drain_checked(limit, None).await
    }
    /// Like `drain`, with the owner's egress deny list (re-read every pass, as
    /// it may be edited at any time). A post that breaks a rule is not sent:
    /// it fails with `egress_<rule>`, which names the rule, never the term.
    /// An unreadable list holds every post back rather than sending unchecked.
    ///
    /// A SIGN-OFF line written as such is not checked here (#109); a verdict
    /// line is signed against the live head, in the copy that is sent.
    pub async fn drain_checked(&self, limit: usize, deny: Option<&Path>) -> Result<usize> {
        if self.observe_only {
            return Ok(0);
        }
        let rules = match deny.map(crate::config::egress::deny_list).transpose() {
            Ok(rules) => rules.unwrap_or_default(),
            Err(_) => {
                let now = self.clock.now();
                self.store
                    .transact(move |u| {
                        u.note_unless_since("egress_deny_list_unavailable", "{}", now, now - 3600.)
                    })
                    .await?;
                return Ok(0);
            }
        };
        let mut sent = 0;
        let mut attempted = 0;
        while attempted < limit {
            let (now, batch) = (self.clock.now(), (limit - attempted).min(20));
            let batch = self
                .store
                .transact(move |u| u.ready_posts(now, batch))
                .await?;
            if batch.is_empty() {
                break;
            }
            let mut progressed = false;
            for id in batch {
                let now = self.clock.now();
                let Some(post) = self
                    .store
                    .transact(move |u| u.claim_post(now, Some(id)))
                    .await?
                else {
                    continue;
                };
                attempted += 1;
                let mut sending = post.clone();
                let meta = post.post.meta.as_ref().map(|m| m["review"].clone());
                let review: Vec<String> =
                    serde_json::from_value(meta.unwrap_or_default()).unwrap_or_default();
                sending.post.text = self.sign(&post.post.text, &review).await;
                let text = sending.post.text.clone();
                // Every broken rule is recorded, each as `egress_<rule>`, so
                // the owner sees all of them in one pass.
                let refused = check(&sending, &rules);
                let result = if !refused.is_empty() {
                    DeliveryOutcome::Rejected {
                        code: refused
                            .iter()
                            .map(|rule| format!("egress_{}", rule.replace(':', "_")))
                            .collect::<Vec<_>>()
                            .join("+"),
                    }
                } else {
                    tokio::time::timeout(self.timeout, self.delivery.send(sending))
                        .await
                        .unwrap_or(DeliveryOutcome::Ambiguous {
                            code: "delivery_timeout".into(),
                        })
                };
                let (owner, now) = (self.owner.clone(), self.clock.now());
                // A stale attempt's late result commits before it is reported.
                let outcome = self
                    .store
                    .transact(move |u| {
                        let p = &post.post;
                        // The thread history keeps what was sent: the sign-off
                        // or why it was not signed, not the verdict line.
                        if let DeliveryOutcome::Sent { reference } = &result {
                            if text != p.text && !reference.is_empty() {
                                u.keep_message(&ArrivedMessage {
                                    event_id: format!("self:{}:{reference}", p.channel),
                                    workspace: p.session_id.split(':').next().unwrap_or("").into(),
                                    channel: p.channel.clone(),
                                    ts: reference.clone(),
                                    root_ts: p.thread_ts.clone().unwrap_or(reference.clone()),
                                    thread_ts: p.thread_ts.clone(),
                                    sender: owner.clone(),
                                    text,
                                    files: "[]".into(),
                                    source: "self".into(),
                                    meta: p.meta.as_ref().map(ToString::to_string),
                                    received_at: now,
                                    attachments: "[]".into(),
                                    mentions_owner: false,
                                })?;
                            }
                        }
                        u.finish_delivery(&post, &result, &owner, now)
                    })
                    .await?;
                if outcome == PostOutcome::Stale {
                    bail!("stale delivery attempt or changed payload");
                }
                if outcome == PostOutcome::Sent {
                    sent += 1;
                    progressed = true;
                }
            }
            if !progressed {
                break;
            }
        }
        Ok(sent)
    }
}
/// The text a post would publish: its message, its file name and, for an
/// upload of text, its contents.
fn check(post: &ClaimedPost, rules: &DenyList) -> Vec<String> {
    let p = &post.post;
    let upload = p.blob.as_deref().and_then(|b| std::str::from_utf8(b).ok());
    let mut broken: Vec<String> = [Some(p.text.as_str()), Some(p.filename.as_str()), upload]
        .into_iter()
        .flatten()
        .flat_map(|text| egress::scan(text, rules))
        .collect();
    broken.sort();
    broken.dedup();
    broken
}
