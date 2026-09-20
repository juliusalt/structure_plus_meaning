"""finalize.py: a task's check, then (after its verdict) its commit and push, in a temporary git repository with a bare
origin; the task's stage follows (v2.checked, v2.committed)."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import PLANNER_STATE  # noqa: E402


class FinalizeTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.remote = self.w.repository()
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.session("implement-3", "implementer", "k3", task="3", state="done", live=False)
        self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3"}})
        self.w.task("3")
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.w.write("THEORY_MAP.md", "an unrelated change of another task\n")
        self.w.write(".build/tasks/3/commit.md", "Add the readiness theory\n\nValidation: the check passes.\n")

    def tearDown(self):
        self.w.close()

    def spec(self, check):
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": check, "files": ["theories/Ready.thy"], "message": ".build/tasks/3/commit.md"}))

    def outcome(self):
        return json.loads((self.w.project / ".build/tasks/3/finalized.json").read_text())

    def stage(self):
        return self.w.st()["tasks"]["3"]["stage"]

    def heard(self):
        forks = [c["args"][-1] for c in self.w.calls("--bg") if "-n" in c["args"]]
        return " ".join(e["text"] for e in self.w.st()["events"]) + " ".join(forks)

    def test_a_passing_check_sends_the_task_to_its_review_and_commits_nothing(self):
        self.spec("grep -q Ready theories/Ready.thy && echo checked")
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 0, err)
        self.assertTrue(self.outcome()["ok"])
        self.assertIn("checked", (self.w.project / ".build/tasks/3/finalize.log").read_text())
        self.assertEqual(self.stage(), "reviewing")
        self.assertEqual(self.w.git("log", "--format=%s"), "start\n")
        (review,) = [c["args"] for c in self.w.calls("--bg") if "review-3" in c["args"]]
        self.assertIn("You are review-3, a reviewer", review[-1])

    def py(self, code):
        """Run v2 code in this world; its printed output."""
        r = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n{code}"],
                           env=self.w.env, capture_output=True, text=True, cwd=self.w.project)
        self.assertEqual(r.stderr, "")
        return r.stdout

    def test_a_check_runs_in_the_working_tree_as_it_is_and_marks_its_processes(self):
        self.w.write("theories/Base.thy", "a producing session's draft stays where it is\n")
        self.spec("cat \"$ORCH_PROJECT/.build/tasks/3/finalizer.pid\" > .build/seen; grep -q Ready theories/Ready.thy")
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 0, err)
        pids = (self.w.project / ".build/seen").read_text().split()
        self.assertEqual(len(pids), 2)  # the finalizer and its check's process group, for the watchdog
        self.assertFalse((self.w.project / ".build/tasks/3/finalizer.pid").exists())  # gone with the finalizer
        self.assertEqual((self.w.project / "theories/Base.thy").read_text(), "a producing session's draft stays where it is\n")

    def test_a_commit_waits_for_another_git_process_holding_the_index(self):
        self.spec("true")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        lock = self.w.project / ".git/index.lock"
        lock.write_text("")
        release = subprocess.Popen(["sh", "-c", f"sleep 3; rm -f {lock}"])
        code, _, err = self.w.run("finalize.py", "commit", "3")
        release.wait()
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add the readiness theory\n")

    def test_a_task_that_leaves_leaves_its_work_in_the_tree(self):
        # the harness took a task's changes out so the next check saw one task's work alone, and moved the parts of
        # one change separately in doing it; it takes nothing out now (2026-09-20)
        base = "a\nb\nc\nd\ne\n"
        self.w.write("theories/Shared.thy", base)
        self.w.git("add", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "shared")
        self.w.write("theories/Shared.thy", "A\nb\nc\nd\ne\n")
        self.w.write("theories/New.thy", "new\n")
        out = self.py('v2.own("3", ["theories/Shared.thy", "theories/New.thy"]); print(v2.leave("3", "parked"))')
        self.assertIn("stay in the working tree", out)
        self.assertEqual((self.w.project / "theories/Shared.thy").read_text(), "A\nb\nc\nd\ne\n")  # its edit stands
        self.assertTrue((self.w.project / "theories/New.thy").exists())  # and its new file with it
        self.assertFalse((self.w.project / ".build/tasks/3/shelf/manifest.json").exists())
        # and while it stands there, the tree is that task's: another session drafts instead of writing
        self.w.set_st(tasks={"3": {"stage": "parked"}})
        self.assertEqual(self.py('print(v2.tree_holder(v2.peek(), {"task": "9"}))').strip(), "3")
        self.assertIsNone(eval(self.py('print(repr(v2.tree_holder(v2.peek(), {"task": "3"})))').strip()))

    def test_a_check_that_never_ran_costs_the_task_no_round(self):
        # a quick fix reused an output directory the tool refuses; two one-second failures sent to the planner a task
        # whose check had passed (2026-09-20)
        self.spec("python3 -c \"raise SystemExit(__import__('sys').stderr.write("
                  "'Traceback (most recent call last)\\nAssertionError: Use a fresh output directory.\\n') and 1)\"")
        for i in (1, 2):
            self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3"}})
            self.assertEqual(self.w.run("finalize.py", "check", "3")[0], 1)
            self.assertEqual(self.stage(), "fixing")  # back to its own session, not to the planner
            self.assertEqual(self.w.st()["tasks"]["3"].get("checks_failed"), None)  # and no round spent
            self.assertIn("did not run at all", self.w.st()["tasks"]["3"]["fix_text"])
            self.assertIn("did not run", (self.w.state / "v2.log").read_text())
        self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3",
                                   "spec_errors": 2}})
        self.w.run("finalize.py", "check", "3")
        self.assertEqual(self.stage(), "planner")  # a command that stays unrunnable is the planner's

    def test_a_failing_check_gets_one_quick_fix_then_goes_to_the_planner(self):
        self.spec("echo '*** Failed to finish proof'; exit 1")
        self.assertEqual(self.w.run("finalize.py", "check", "3")[0], 1)
        self.assertEqual(self.stage(), "fixing")
        (fix,) = [c["args"] for c in self.w.calls("--bg") if c["args"][:3] == ["--bg", "--resume", "k3"]]
        self.assertIn("*** Failed to finish proof", fix[3])
        self.w.set_st(tasks=dict(self.w.st()["tasks"], **{"3": dict(self.w.st()["tasks"]["3"], stage="checking")}))
        self.w.run("finalize.py", "check", "3")
        self.assertEqual(self.stage(), "planner")
        self.assertIn("failed its check again after a quick fix", self.heard())

    def test_an_accepted_task_is_committed_with_its_named_files_and_pushed(self):
        self.spec("true")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "summary": "Readiness is in."}})
        code, _, err = self.w.run("finalize.py", "commit", "3")
        self.assertEqual(code, 0, err)
        o = self.outcome()
        self.assertTrue(o["pushed"])
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add the readiness theory\n")
        # the task's files, and the planner's state as it stands (HANDOFF.md), as every task commit before v2
        self.assertEqual(self.w.git("show", "--name-only", "--format=", "HEAD"), "HANDOFF.md\ntheories/Ready.thy\n")
        self.assertIn("THEORY_MAP.md", self.w.git("status", "--porcelain"))  # not taken by this commit
        self.assertEqual(self.w.git("rev-parse", "--short", "main", cwd=self.remote).strip(), o["commit"])
        self.assertEqual(self.stage(), "done")
        self.assertEqual(self.w.read_task("3")["status"], "completed")
        self.assertIn(f"Task 3 is committed as {o['commit']}. Readiness is in.", self.heard())
        self.assertTrue(self.w.st()["sessions"]["implement-3"]["released"])

    def test_a_failed_commit_goes_to_the_planner(self):
        self.spec("true")
        self.w.write("theories/Ready.thy", "")
        self.w.git("add", "theories/Ready.thy")
        self.w.git("commit", "-q", "-m", "already")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 1)
        self.assertEqual(self.stage(), "planner")
        self.assertIn("its commit failed", self.heard())

    def test_a_commit_carrying_a_placeholder_is_refused_and_goes_to_the_planner(self):
        self.spec("true")
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin\n(* CHECK_NUMBERS *)\nend\n")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 1)
        self.assertEqual(self.w.git("log", "--format=%s"), "start\n")  # nothing committed
        self.assertEqual(self.w.git("diff", "--cached", "--name-only"), "")  # and nothing left staged
        self.assertIn("CHECK_NUMBERS", self.outcome()["commit_error"])
        self.assertEqual(self.stage(), "planner")

    def test_a_name_in_braces_is_the_change_s_own_words_and_not_a_draft_s_stand_in(self):
        # {ISABELLE_RUN_LIMIT} in a tool's own f-string was refused as an unfilled placeholder (2026-09-20)
        self.spec("true")
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin\n"
                     "(* prints f'at most {ISABELLE_RUN_LIMIT} runs', and quotes the harness's {WHAT} *)\nend\n")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 0)
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add the readiness theory\n")
        self.assertIn("taken as its own words", (self.w.state / "v2.log").read_text())

    def test_a_commit_does_not_carry_another_unfinished_task_s_file(self):
        self.spec("true")
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Ready.thy", "THEORY_MAP.md"],
             "message": ".build/tasks/3/commit.md"}))
        self.w.task("4")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"},
                             "4": {"stage": "running"}})
        (self.w.state / "tree-owners.json").write_text(json.dumps({"THEORY_MAP.md": "4"}))
        # it waits for an append in flight to land, and refuses only when it does not
        self.assertEqual(self.w.run("finalize.py", "commit", "3", env={"ORCH_COMMIT_WAIT": "0"})[0], 1)
        self.assertEqual(self.w.git("log", "--format=%s"), "start\n")
        self.assertIn("THEORY_MAP.md (task 4)", self.outcome()["commit_error"])
        self.assertEqual(self.stage(), "planner")

    def test_an_entry_is_closed_by_the_commit_that_carries_it_and_never_by_blame(self):
        entry = "## This batch\n\nits content\n\nRecorded 2026-09-20, commit `\u2026`.\n"
        self.w.write("DECISIONS.md", entry)
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["DECISIONS.md"], "message": ".build/tasks/3/commit.md"}))
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 0)
        mine = self.w.git("rev-parse", "--short", "HEAD").strip()
        # its own hash does not exist while it is being made: the commit records what it left open
        self.assertIn("commit `\u2026`.", (self.w.project / "DECISIONS.md").read_text())
        self.assertEqual(json.loads((self.w.state / "entry-commit.json").read_text()),
                         {"heading": "## This batch", "commit": mine})
        # the line is byte-identical to one an earlier commit introduced, so blame would name that commit;
        # the next commit touching the file closes it with the one that carries the entry (2026-09-20)
        self.w.write("DECISIONS.md", entry + "\n## A later batch\n\nmore\n")
        self.w.task("4")
        self.w.write(".build/tasks/4/commit.md", "A later batch\n")
        self.w.write(".build/tasks/4/finalize.json", json.dumps(
            {"check": "true", "files": ["DECISIONS.md"], "message": ".build/tasks/4/commit.md"}))
        self.w.session("implement-4", "implementer", "k4", task="4", state="done", live=False)
        self.w.set_st(tasks={"4": {"stage": "committing", "role": "implementer", "session": "implement-4"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "4")[0], 0)
        text = (self.w.project / "DECISIONS.md").read_text()
        self.assertIn(f"Recorded 2026-09-20, commit `{mine}`.", text)
        self.assertNotIn("commit `\u2026`.", text)
        self.assertFalse((self.w.state / "entry-commit.json").exists())

    def test_a_check_that_advances_the_base_holds_the_machine_while_it_runs(self):
        self.spec("test -e .claude/state-probe || cat $ORCH_STATE_DIR/isabelle-exclusive > seen; tools/x --advance-base; true")
        self.w.run("finalize.py", "check", "3")
        claim = json.loads((self.w.project / "seen").read_text())
        self.assertEqual(claim["task"], "3")
        self.assertIn("advances the base heap", claim["why"])
        self.assertTrue(str(claim["pid"]).isdigit())  # what holds it, so a claim cannot outlive its check
        self.assertFalse((self.w.state / "isabelle-exclusive").exists())

    def test_a_check_waits_while_another_advances_the_base(self):
        (self.w.state / "isabelle-exclusive").write_text(f"9 {os.getpid()}")  # a holder whose process is alive
        self.spec("true")
        started = time.time()
        self.w.run("finalize.py", "check", "3", env={"ORCH_ISABELLE_WAIT": "1", "ORCH_ISABELLE_POLL": "0.2"})
        self.assertGreaterEqual(time.time() - started, 1)  # it waited its limit, then ran

    def test_a_marker_left_by_a_check_that_is_gone_holds_nothing(self):
        # a check killed before its own cleanup left one behind, and the next waited an hour behind it (2026-09-20)
        for left in ("9 2147483646", "9"):  # a process that is not there, and the form before the process was named
            (self.w.state / "isabelle-exclusive").write_text(left)
            self.spec("true")
            started = time.time()
            self.w.run("finalize.py", "check", "3", env={"ORCH_ISABELLE_WAIT": "30", "ORCH_ISABELLE_POLL": "0.2"})
            self.assertLess(time.time() - started, 10)  # it ran at once
            self.assertTrue(self.outcome()["ok"])
            self.assertFalse((self.w.state / "isabelle-exclusive").exists())  # and the stale marker is gone

    def test_a_check_that_outlives_its_limit_fails_and_leaves_nothing_running(self):
        self.spec("sleep 5; true")
        started = time.time()
        code, _, _ = self.w.run("finalize.py", "check", "3", env={"ORCH_FINAL_MAX": "1"})
        self.assertEqual(code, 1)
        self.assertLess(time.time() - started, 4)
        self.assertEqual(subprocess.run(["pgrep", "-f", "^sleep 5$"], capture_output=True).stdout, b"")
        self.assertIn("did not finish within 1 s", (self.w.project / ".build/tasks/3/finalize.log").read_text())


if __name__ == "__main__":
    unittest.main()
