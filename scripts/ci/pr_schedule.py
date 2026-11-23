#!/usr/bin/env python3
"""Schedule `PR check` runs with a concurrency cap and per-file serialization (#6787, Step 3).

    scripts/ci/pr_schedule.py [--dry-run]

Runs from .github/workflows/pr_schedule.yml using main's scripts and read/dispatch/status
permissions only (no contents:write or pull-requests:write). On each invocation:

  1. lists all open non-draft pull requests against `main`, their changed files, and their latest
     `"PR check"` commit status (plus whether a legacy `Verdict` check run already exists);
  2. lists active (`in_progress`, `queued`) and recently `completed` runs of `pr_check.yml`;
  3. syncs `"PR check"` commit statuses from completed `workflow_dispatch` runs unless Auto-merge
     has already marked the commit `"Queued for re-check (after <id>)"`;
  4. while active checks are below `MAX_CONCURRENT_CHECKS`, dispatches eligible waiting PRs
     (skipping drafts, active runs, recent dispatches within `DISPATCH_GRACE_SECONDS`, and any PR
     whose touched `RiemannMasullo/` files overlap a currently active/dispatched PR check).
"""
from datetime import datetime, timezone
import json
import os
import re
import subprocess
import sys
import urllib.parse
from pathlib import Path

import plain_proof

BRANCH = "main"
CHECK_WORKFLOW = "pr_check.yml"
CHECK_WORKFLOW_PATH = ".github/workflows/pr_check.yml"
STATUS_CONTEXT = "PR check"
LEGACY_CHECK_NAME = "Verdict"
DISPATCH_TITLE = re.compile(r"^PR check #(\d+) ([0-9a-f]{40})$")
RECHECK_RE = re.compile(r"^Queued for re-check \(after (\d+)\):")
DISPATCHED_RE = re.compile(r"^PR check dispatched \(after (\d+),")
DISPATCHED_PREFIX = "PR check dispatched"
DEFAULT_MAX_CONCURRENT = 28
DISPATCH_GRACE_SECONDS = 300
MAX_ATTEMPTS = 12
SHA = re.compile(r"[0-9a-f]{40}")
REPO = re.compile(r"[A-Za-z0-9._-]+/[A-Za-z0-9._-]+")

OPEN_PRS_QUERY = """
query($owner: String!, $name: String!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, baseRefName: "main", first: 100, after: $cursor,
                 orderBy: {field: UPDATED_AT, direction: ASC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        isDraft
        updatedAt
        headRefOid
        files(first: 50) {
          totalCount
          nodes { path }
        }
        commits(last: 1) {
          nodes {
            commit {
              statusCheckRollup {
                contexts(first: 50) {
                  nodes {
                    __typename
                    ... on StatusContext {
                      context
                      state
                      description
                      createdAt
                    }
                    ... on CheckRun {
                      name
                      status
                      conclusion
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}
"""


class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(f"{status}: {message}")
        self.status, self.message = status, message


class Api:
    """The GitHub REST and GraphQL API through `gh`, with no shell."""

    def __init__(self, repo, dry_run=False):
        if not REPO.fullmatch(repo):
            raise SystemExit("GH_REPO must be owner/name")
        self.repo, self.dry_run, self.calls = repo, dry_run, 0

    def call(self, path, method="GET", body=None):
        cmd = ["gh", "api", "--method", method, f"repos/{self.repo}/{path}".rstrip("/"),
               "-H", "X-GitHub-Api-Version: 2022-11-28"]
        if body is not None:
            cmd += ["--input", "-"]
        self.calls += 1
        done = subprocess.run(cmd, input=None if body is None else json.dumps(body).encode(),
                              capture_output=True)
        if done.returncode:
            stderr = done.stderr.decode("utf-8", "replace")
            code = re.search(r"\(HTTP (\d+)\)", stderr)
            try:
                message = str(json.loads(done.stdout).get("message", ""))
            except (ValueError, AttributeError):
                message = stderr
            raise ApiError(int(code.group(1)) if code else 0, message[:300])
        return json.loads(done.stdout) if done.stdout.strip() else None

    def graphql(self, query_text, **variables):
        cmd = ["gh", "api", "graphql", "-f", f"query={query_text}"]
        for key, value in variables.items():
            if value is not None:
                cmd += ["-f", f"{key}={value}"]
        self.calls += 1
        done = subprocess.run(cmd, capture_output=True)
        if done.returncode:
            stderr = done.stderr.decode("utf-8", "replace")
            raise ApiError(0, stderr[:300])
        data = json.loads(done.stdout)
        if data.get("errors"):
            raise ApiError(0, str(data["errors"])[:300])
        return data["data"]

    def change(self, what, path, method, body=None):
        if self.dry_run:
            print(f"  (dry run) would {what}")
            return {}
        return self.call(path, method, body)


def query(**params):
    return urllib.parse.urlencode(params)


def parse_dispatch_title(title):
    m = DISPATCH_TITLE.fullmatch(title or "")
    return (int(m.group(1)), m.group(2)) if m else None


def pending_after_id(description):
    for pattern in (RECHECK_RE, DISPATCHED_RE):
        m = pattern.match(description or "")
        if m:
            return int(m.group(1))
    return None


def parse_iso_time(text):
    if not text:
        return None
    try:
        return datetime.fromisoformat(text.replace("Z", "+00:00")).timestamp()
    except ValueError:
        return None


def library_files(paths):
    return {p for p in paths if plain_proof.library_file(p)}


def extract_rollup(node):
    """Return (latest 'PR check' StatusContext dict or None, has_legacy_verdict_check_run)."""
    commits = (node.get("commits") or {}).get("nodes") or []
    if not commits:
        return None, False
    rollup = (commits[0].get("commit") or {}).get("statusCheckRollup") or {}
    contexts = (rollup.get("contexts") or {}).get("nodes") or []
    pr_statuses = [c for c in contexts
                   if c.get("__typename") == "StatusContext" and c.get("context") == STATUS_CONTEXT]
    latest_status = None
    if pr_statuses:
        best = max(pr_statuses, key=lambda c: c.get("createdAt") or "")
        latest_status = dict(
            state=(best.get("state") or "").lower(),
            description=best.get("description") or "",
            created_at=best.get("createdAt") or "",
        )
    has_legacy = any(
        c.get("__typename") == "CheckRun" and c.get("name") == LEGACY_CHECK_NAME
        for c in contexts
    )
    return latest_status, has_legacy


def status_from_conclusion(conclusion):
    if conclusion == "success":
        return "success", "PR check passed"
    if conclusion == "failure":
        return "failure", "PR check failed (see run summary)"
    if conclusion == "cancelled":
        return "error", "PR check was cancelled"
    return "error", f"PR check ended in {conclusion or 'unknown'}"[:140]


class Scheduler:
    def __init__(self, api, max_concurrent=DEFAULT_MAX_CONCURRENT, now=None):
        self.api = api
        self.max_concurrent = max_concurrent
        self.now = time_now() if now is None else now
        self.actions = []       # (pr_number, sha, outcome)
        self.stats = {}

    def open_pull_requests(self):
        owner, name = self.api.repo.split("/", 1)
        prs = {}
        cursor = None
        for _ in range(20):
            data = self.api.graphql(OPEN_PRS_QUERY, owner=owner, name=name, cursor=cursor)
            conn = data["repository"]["pullRequests"]
            for node in conn["nodes"]:
                if node.get("isDraft"):
                    continue
                sha = node.get("headRefOid") or ""
                if not SHA.fullmatch(sha):
                    continue
                files_info = node.get("files") or {}
                paths = [f["path"] for f in (files_info.get("nodes") or [])]
                if files_info.get("totalCount", 0) > len(paths):
                    paths = self.pull_files(node["number"])
                status, has_legacy = extract_rollup(node)
                prs[node["number"]] = dict(
                    number=node["number"],
                    head_sha=sha,
                    updated_at=node.get("updatedAt") or "",
                    files=paths,
                    lib_files=library_files(paths),
                    status=status,
                    has_legacy=has_legacy,
                )
            page = conn["pageInfo"]
            if not page.get("hasNextPage") or not page.get("endCursor"):
                break
            cursor = page["endCursor"]
        return prs

    def pull_files(self, number):
        paths, page = [], 1
        while page <= 10:
            batch = self.api.call(f"pulls/{number}/files?" + query(per_page=100, page=page))
            paths.extend(entry["filename"] for entry in batch)
            if len(batch) < 100:
                break
            page += 1
        return paths

    def workflow_runs(self, repo_id, prs):
        by_head = {}
        for pr in prs.values():
            by_head.setdefault(pr["head_sha"], []).append(pr["number"])

        def fetch(status):
            runs = self.api.call(
                f"actions/workflows/{CHECK_WORKFLOW}/runs?" + query(status=status, per_page=100)
            )["workflow_runs"]
            return [r for r in runs
                    if r.get("path") == CHECK_WORKFLOW_PATH
                    and (r.get("repository") or {}).get("id") == repo_id]

        active_runs = fetch("in_progress") + fetch("queued")
        completed_runs = fetch("completed")

        def key_for(run):
            event = run.get("event")
            if event == "workflow_dispatch":
                if (run.get("head_branch") != BRANCH
                        or (run.get("head_repository") or {}).get("id") != repo_id):
                    return None
                return parse_dispatch_title(run.get("display_title"))
            if event == "pull_request":
                nums = by_head.get(run.get("head_sha") or "")
                if nums and len(nums) == 1:
                    return (nums[0], run["head_sha"])
            return None

        active_by_key = {}
        for r in active_runs:
            k = key_for(r)
            if k:
                active_by_key.setdefault(k, []).append(r)

        completed_by_key = {}
        for r in completed_runs:
            k = key_for(r)
            if k:
                completed_by_key.setdefault(k, []).append(r)

        return active_runs, active_by_key, completed_by_key

    def post_status(self, sha, state, description, target_url=None):
        body = dict(state=state, context=STATUS_CONTEXT, description=description[:140])
        if target_url:
            body["target_url"] = target_url
        try:
            self.api.change(f"set {STATUS_CONTEXT!r} status on {sha[:12]} to {state}: {description}",
                            f"statuses/{sha}", "POST", body)
        except ApiError as problem:
            print(f"  could not set commit status on {sha[:12]}: {problem}")

    def sync_statuses(self, prs, active_by_key, completed_by_key):
        synced = 0
        for number, pr in prs.items():
            sha = pr["head_sha"]
            key = (number, sha)
            if key in active_by_key:
                continue
            dispatched = [r for r in completed_by_key.get(key, []) if r.get("event") == "workflow_dispatch"]
            if not dispatched:
                continue
            latest = max(dispatched, key=lambda r: r["id"])
            status = pr["status"]
            if status is not None and status["state"] != "pending":
                continue
            if status is not None:
                after_id = pending_after_id(status["description"])
                if after_id is not None and latest["id"] <= after_id:
                    continue
            state, desc = status_from_conclusion(latest.get("conclusion"))
            self.post_status(sha, state, desc, latest.get("html_url"))
            pr["status"] = dict(state=state, description=desc, created_at="")
            synced += 1
        return synced

    def dispatch_waiting(self, prs, active_runs, active_by_key, completed_by_key):
        active_count = len(active_runs)
        locked_files = set()
        grace_keys = set()

        for (number, sha) in active_by_key:
            if number in prs and prs[number]["head_sha"] == sha:
                locked_files |= prs[number]["lib_files"]

        for number, pr in prs.items():
            key = (number, pr["head_sha"])
            if key in active_by_key:
                continue
            status = pr["status"]
            if status and status["state"] == "pending" and status["description"].startswith(DISPATCHED_PREFIX):
                ts = parse_iso_time(status["created_at"])
                if ts is not None and (self.now - ts) < DISPATCH_GRACE_SECONDS:
                    grace_keys.add(key)
                    active_count += 1
                    locked_files |= pr["lib_files"]

        candidates = []
        for number, pr in prs.items():
            sha = pr["head_sha"]
            key = (number, sha)
            if key in active_by_key or key in grace_keys:
                continue
            status = pr["status"]
            done = completed_by_key.get(key, [])
            is_recheck = False
            recheck_after_id = 0
            if status and status["state"] == "pending":
                m = RECHECK_RE.match(status["description"])
                if m:
                    after_id = int(m.group(1))
                    if any(r["id"] > after_id for r in done):
                        continue
                    attempts = sum(r.get("run_attempt", 1) for r in done)
                    if attempts >= MAX_ATTEMPTS:
                        continue
                    is_recheck = True
                    recheck_after_id = after_id
                elif status["description"].startswith(DISPATCHED_PREFIX):
                    after_id = pending_after_id(status["description"])
                    if after_id is not None and any(r["id"] > after_id for r in done):
                        continue
                    if after_id is None and done:
                        continue
                    attempts = sum(r.get("run_attempt", 1) for r in done)
                    if attempts >= MAX_ATTEMPTS:
                        continue
                    is_recheck = bool(after_id)
                    recheck_after_id = after_id or 0
                else:
                    continue
            elif status is not None:
                continue
            elif done or pr["has_legacy"]:
                continue
            candidates.append((is_recheck, recheck_after_id, pr))

        candidates.sort(key=lambda item: (
            not item[0],
            len(item[2]["lib_files"]) > 0,
            item[2]["updated_at"],
            item[2]["number"],
        ))

        dispatched = 0
        skipped_busy = 0
        skipped_cap = 0
        workflow_url = f"https://github.com/{self.api.repo}/actions/workflows/{CHECK_WORKFLOW}"

        for is_recheck, recheck_after_id, pr in candidates:
            number, sha, lib = pr["number"], pr["head_sha"], pr["lib_files"]
            if active_count >= self.max_concurrent:
                skipped_cap += 1
                self.actions.append((number, sha, "waiting: concurrency cap reached"))
                continue
            overlap = sorted(lib & locked_files)
            if overlap:
                skipped_busy += 1
                self.actions.append((number, sha, f"waiting: file busy ({overlap[0]})"))
                continue
            done = completed_by_key.get((number, sha), [])
            after_id = max([r["id"] for r in done], default=0)
            if is_recheck:
                after_id = max(after_id, recheck_after_id)
            self.api.change(
                f"dispatch {CHECK_WORKFLOW} for #{number} ({sha[:12]})",
                f"actions/workflows/{CHECK_WORKFLOW}/dispatches",
                "POST",
                dict(ref=BRANCH, inputs=dict(pr=str(number), head_sha=sha)),
            )
            self.post_status(sha, "pending", f"{DISPATCHED_PREFIX} (after {after_id}, for #{number})", workflow_url)
            locked_files |= lib
            active_count += 1
            dispatched += 1
            kind = "dispatched re-check" if is_recheck else "dispatched"
            self.actions.append((number, sha, kind))

        return dict(
            open_non_draft=len(prs),
            active_runs=len(active_runs),
            grace_pending=len(grace_keys),
            locked_files=len(locked_files),
            eligible=len(candidates),
            dispatched=dispatched,
            skipped_busy=skipped_busy,
            skipped_cap=skipped_cap,
        )

    def run(self):
        given = os.environ.get("GITHUB_REPOSITORY_ID", "")
        repo_id = int(given) if given.isdigit() else self.api.call("")["id"]
        prs = self.open_pull_requests()
        active_runs, active_by_key, completed_by_key = self.workflow_runs(repo_id, prs)
        synced = self.sync_statuses(prs, active_by_key, completed_by_key)
        stats = self.dispatch_waiting(prs, active_runs, active_by_key, completed_by_key)
        stats["synced_statuses"] = synced
        self.stats = stats
        return stats

    def summary(self):
        target = os.environ.get("GITHUB_STEP_SUMMARY")
        if not target or not self.stats:
            return
        s = self.stats
        lines = [
            f"Active `PR check` runs: {s['active_runs']} (+{s['grace_pending']} in grace) / "
            f"{self.max_concurrent} cap; {s['locked_files']} library files locked; "
            f"dispatched {s['dispatched']}, busy {s['skipped_busy']}, capped {s['skipped_cap']}, "
            f"synced {s['synced_statuses']}.",
            "",
        ]
        if self.actions:
            lines += ["| Pull request | Commit | Action |", "|---|---|---|"]
            for number, sha, action in self.actions[:100]:
                safe = re.sub(r"[^\x20-\x7e]", "?", action).replace("|", "/")
                lines.append(f"| #{number} | `{sha[:12]}` | {safe} |")
        with open(target, "a") as out:
            out.write("\n".join(lines) + "\n")


def time_now():
    import time
    return time.time()


def main(argv):
    dry_run = "--dry-run" in argv
    raw_cap = os.environ.get("MAX_CONCURRENT_CHECKS", "")
    max_concurrent = int(raw_cap) if raw_cap.isdigit() else DEFAULT_MAX_CONCURRENT
    api = Api(os.environ.get("GH_REPO", ""), dry_run=dry_run)
    scheduler = Scheduler(api, max_concurrent=max_concurrent)
    stats = scheduler.run()
    scheduler.summary()
    print(
        f"open={stats['open_non_draft']} active={stats['active_runs']} "
        f"locked_files={stats['locked_files']} eligible={stats['eligible']} "
        f"dispatched={stats['dispatched']} busy={stats['skipped_busy']} "
        f"capped={stats['skipped_cap']} synced={stats['synced_statuses']} "
        f"({api.calls} API calls)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
