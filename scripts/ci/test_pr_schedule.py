#!/usr/bin/env python3
"""Tests for pr_schedule.py and the PR check / PR schedule / Stop workflow wiring."""
from pathlib import Path
import os
import re
import unittest
from unittest import mock

import pr_schedule

REPO_ID = 1
ROOT = Path(__file__).resolve().parent.parent.parent
SEC1 = "RiemannMasullo/AppA_AlgebraicNT/Sec1.lean"
SEC2 = "RiemannMasullo/AppB_AnalyticNT/Sec2.lean"
SEC3 = "RiemannMasullo/Ch05_ThetaZSpaces/Sec3b.lean"


class FakeApi:
    repo = "owner/name"
    dry_run = False

    def __init__(self):
        self.calls = 0
        self.changes = []
        self.pr_nodes = []
        self.runs = []
        self.pull_files_map = {}

    def add_pr(self, number, files, draft=False, updated_at="2026-01-01T00:00:00Z",
               status=None, legacy_check=False, head=None, total_files=None):
        head = head or format(number, "040x")
        contexts = []
        if status is not None:
            contexts.append(dict(
                __typename="StatusContext",
                context=pr_schedule.STATUS_CONTEXT,
                state=status["state"].upper(),
                description=status["description"],
                createdAt=status.get("created_at", "2026-01-01T00:00:00Z"),
            ))
        if legacy_check:
            contexts.append(dict(
                __typename="CheckRun",
                name=pr_schedule.LEGACY_CHECK_NAME,
                status="COMPLETED",
                conclusion="SUCCESS",
            ))
        self.pr_nodes.append(dict(
            number=number,
            isDraft=draft,
            updatedAt=updated_at,
            headRefOid=head,
            files=dict(
                totalCount=total_files if total_files is not None else len(files),
                nodes=[dict(path=p) for p in files],
            ),
            commits=dict(nodes=[dict(commit=dict(statusCheckRollup=dict(contexts=dict(nodes=contexts))))]),
        ))
        return head

    def add_run(self, run_id, pr, sha, status="in_progress", conclusion=None,
                event="workflow_dispatch", branch="main", repo_id=REPO_ID):
        self.runs.append(dict(
            id=run_id,
            path=pr_schedule.CHECK_WORKFLOW_PATH,
            event=event,
            status=status,
            conclusion=conclusion,
            head_sha=sha if event == "pull_request" else "b" * 40,
            head_branch=branch,
            repository=dict(id=repo_id),
            head_repository=dict(id=repo_id if event == "workflow_dispatch" else 50 + pr),
            display_title=f"PR check #{pr} {sha}" if event == "workflow_dispatch" else "Legacy PR",
            run_attempt=1,
            html_url=f"https://github.com/owner/name/actions/runs/{run_id}",
        ))

    def call(self, path, method="GET", body=None):
        self.calls += 1
        if method != "GET":
            raise AssertionError(f"write via call: {method} {path}")
        if path == "":
            return dict(id=REPO_ID)
        if path.startswith(f"actions/workflows/{pr_schedule.CHECK_WORKFLOW}/runs?"):
            m = re.search(r"status=([a-z_]+)", path)
            want = m.group(1)
            return dict(workflow_runs=[r for r in self.runs if r["status"] == want])
        if m := re.fullmatch(r"pulls/(\d+)/files\?.*", path):
            return [dict(filename=p) for p in self.pull_files_map[int(m.group(1))]]
        raise AssertionError(f"unexpected REST path: {path}")

    def graphql(self, _query_text, **variables):
        self.calls += 1
        assert variables["owner"] == "owner" and variables["name"] == "name"
        return dict(repository=dict(pullRequests=dict(
            pageInfo=dict(hasNextPage=False, endCursor=None),
            nodes=list(self.pr_nodes),
        )))

    def change(self, _what, path, method, body=None):
        self.changes.append((method, path, body))
        return {}

    def dispatches(self):
        return [(int(c[2]["inputs"]["pr"]), c[2]["inputs"]["head_sha"])
                for c in self.changes
                if c[0] == "POST" and c[1] == f"actions/workflows/{pr_schedule.CHECK_WORKFLOW}/dispatches"]

    def statuses(self):
        return [(c[1].split("/")[1], c[2])
                for c in self.changes if c[0] == "POST" and c[1].startswith("statuses/")]


class ScheduleTest(unittest.TestCase):
    NOW = 1767225600.0  # 2026-01-01T00:00:00Z

    def setUp(self):
        self.api = FakeApi()
        environment = mock.patch.dict(os.environ, clear=True)
        environment.start()
        self.addCleanup(environment.stop)

    def run_scheduler(self, max_concurrent=28, now=None):
        sched = pr_schedule.Scheduler(self.api, max_concurrent=max_concurrent,
                                      now=self.NOW if now is None else now)
        stats = sched.run()
        return stats, sched

    def test_concurrency_cap_stops_dispatching(self):
        h1 = self.api.add_pr(1, [SEC1])
        self.api.add_run(101, 1, h1, status="in_progress")
        self.api.add_pr(2, [SEC2], updated_at="2026-01-01T00:01:00Z")
        self.api.add_pr(3, [SEC3], updated_at="2026-01-01T00:02:00Z")

        stats, _ = self.run_scheduler(max_concurrent=2)
        self.assertEqual(stats["dispatched"], 1)
        self.assertEqual(stats["skipped_cap"], 1)
        self.assertEqual([n for n, _ in self.api.dispatches()], [2])

    def test_per_file_serialization_blocks_overlapping_pr_only(self):
        h1 = self.api.add_pr(1, [SEC1])
        self.api.add_run(101, 1, h1, status="in_progress")
        self.api.add_pr(2, [SEC1], updated_at="2026-01-01T00:01:00Z")
        self.api.add_pr(3, [SEC2], updated_at="2026-01-01T00:02:00Z")
        self.api.add_pr(4, [SEC2], updated_at="2026-01-01T00:03:00Z")
        self.api.add_pr(5, ["README.md"], updated_at="2026-01-01T00:04:00Z")

        stats, _ = self.run_scheduler(max_concurrent=10)
        # Non-library PR #5 and disjoint #3 dispatch; #2 (overlaps #1) and #4 (overlaps newly dispatched #3) wait.
        self.assertEqual(stats["dispatched"], 2)
        self.assertEqual(stats["skipped_busy"], 2)
        self.assertEqual([n for n, _ in self.api.dispatches()], [5, 3])

    def test_draft_and_legacy_checked_prs_are_skipped(self):
        self.api.add_pr(1, [SEC1], draft=True)
        self.api.add_pr(2, [SEC2], legacy_check=True)
        self.api.add_pr(3, [SEC3])

        stats, _ = self.run_scheduler(max_concurrent=10)
        self.assertEqual(stats["open_non_draft"], 2)
        self.assertEqual([n for n, _ in self.api.dispatches()], [3])

    def test_dispatch_grace_prevents_double_dispatch_and_locks_files(self):
        self.api.add_pr(1, [SEC1], status=dict(
            state="pending",
            description="PR check dispatched (after 0, for #1)",
            created_at="2025-12-31T23:58:00Z",  # 120s ago < 300s grace
        ))
        self.api.add_pr(2, [SEC1], updated_at="2026-01-01T00:01:00Z")

        stats, _ = self.run_scheduler(max_concurrent=10)
        self.assertEqual(stats["grace_pending"], 1)
        self.assertEqual(stats["dispatched"], 0)
        self.assertEqual(stats["skipped_busy"], 1)

        # Once grace period passes with no workflow run appearing, #1 is re-dispatched.
        stats2, _ = self.run_scheduler(max_concurrent=10, now=self.NOW + 400)
        self.assertEqual(stats2["dispatched"], 1)
        self.assertEqual([n for n, _ in self.api.dispatches()], [1])

    def test_status_sync_and_recheck_precedence(self):
        h1 = self.api.add_pr(1, [SEC1], status=dict(
            state="pending",
            description="PR check dispatched (after 0, for #1)",
            created_at="2025-12-31T23:40:00Z",
        ))
        self.api.add_run(201, 1, h1, status="completed", conclusion="success")

        h2 = self.api.add_pr(2, [SEC2], status=dict(
            state="pending",
            description="PR check dispatched (after 0, for #2)",
            created_at="2025-12-31T23:40:00Z",
        ))
        self.api.add_run(202, 2, h2, status="completed", conclusion="failure")

        h3 = self.api.add_pr(3, [SEC3], status=dict(
            state="pending",
            description="Queued for re-check (after 203): main moved",
        ))
        self.api.add_run(203, 3, h3, status="completed", conclusion="success")

        stats, _ = self.run_scheduler(max_concurrent=10)
        self.assertEqual(stats["synced_statuses"], 2)
        statuses = dict(self.api.statuses())
        self.assertEqual(statuses[h1]["state"], "success")
        self.assertEqual(statuses[h2]["state"], "failure")
        # #3 must NOT be synced to success from old run 203; it must be re-dispatched instead.
        self.assertEqual(statuses[h3]["state"], "pending")
        self.assertIn("PR check dispatched (after 203,", statuses[h3]["description"])
        self.assertEqual(self.api.dispatches(), [(3, h3)])

    def test_dispatched_recheck_is_not_clobbered_by_previous_completed_run(self):
        h3 = self.api.add_pr(3, [SEC3], status=dict(
            state="pending",
            description="PR check dispatched (after 203, for #3)",
            created_at="2025-12-31T23:59:50Z",  # 10s ago < 300s grace
        ))
        self.api.add_run(203, 3, h3, status="completed", conclusion="success")

        stats, _ = self.run_scheduler(max_concurrent=10)
        self.assertEqual(stats["synced_statuses"], 0)
        self.assertEqual(stats["dispatched"], 0)
        self.assertEqual(self.api.statuses(), [])

        # Past the grace window with no new run appearing, #3 is re-dispatched rather than synced.
        stats2, _ = self.run_scheduler(max_concurrent=10, now=self.NOW + 400)
        self.assertEqual(stats2["synced_statuses"], 0)
        self.assertEqual(stats2["dispatched"], 1)
        self.assertEqual(self.api.dispatches(), [(3, h3)])

    def test_recheck_respects_max_attempts(self):
        h1 = self.api.add_pr(1, [SEC1], status=dict(
            state="pending",
            description="Queued for re-check (after 500): main moved",
        ))
        for i in range(pr_schedule.MAX_ATTEMPTS):
            self.api.add_run(400 + i, 1, h1, status="completed", conclusion="success")
        stats, _ = self.run_scheduler(max_concurrent=10)
        self.assertEqual(stats["dispatched"], 0)


class WorkflowWiring(unittest.TestCase):
    pr_check = (ROOT / ".github/workflows/pr_check.yml").read_text()
    pr_schedule_wf = (ROOT / ".github/workflows/pr_schedule.yml").read_text()
    stop_pr_check = (ROOT / ".github/workflows/stop_pr_check.yml").read_text()

    def test_concurrency_group_matches_stop_workflow(self):
        self.assertIn("group: pr-check-${{ inputs.pr }}-${{ inputs.head_sha }}", self.pr_check)
        self.assertIn(
            "group: pr-check-${{ github.event.pull_request.number }}-${{ github.event.pull_request.head.sha }}",
            self.stop_pr_check,
        )
        self.assertIn("run-name: PR check #${{ inputs.pr }} ${{ inputs.head_sha }}", self.pr_check)

    def test_scheduler_is_least_privilege_and_runs_main_code(self):
        self.assertIn("ref: main", self.pr_schedule_wf)
        self.assertNotIn("contents: write", self.pr_schedule_wf)
        self.assertNotIn("pull-requests: write", self.pr_schedule_wf)
        self.assertIn("actions: write", self.pr_schedule_wf)
        self.assertIn("statuses: write", self.pr_schedule_wf)
        self.assertNotIn("github.event.pull_request.", self.pr_schedule_wf)


if __name__ == "__main__":
    unittest.main()
