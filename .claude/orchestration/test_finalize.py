"""finalize.py: a task's check, then (after its verdict) its commit and push, in a temporary git repository with a bare
origin; the task's stage follows (v2.checked, v2.committed)."""
import json
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

    def test_a_task_that_leaves_has_its_changes_set_aside_and_merged_back_when_taken_up(self):
        base = "a\nb\nc\nd\ne\n"
        self.w.write("theories/Shared.thy", base)
        self.w.git("add", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "shared")
        self.w.write("theories/Shared.thy", "A\nb\nc\nd\ne\n")
        self.w.write("theories/New.thy", "new\n")
        out = self.py('v2.own("3", ["theories/Shared.thy", "theories/New.thy"]); print(v2.leave("3", "parked"))')
        self.assertIn("set aside under .build/tasks/3/shelf/", out)
        self.assertEqual((self.w.project / "theories/Shared.thy").read_text(), base)
        self.assertFalse((self.w.project / "theories/New.thy").exists())
        self.assertTrue((self.w.project / "theories/Ready.thy").exists())  # not the task's: stays
        self.w.write("theories/Shared.thy", "a\nb\nc\nd\nE\n")  # meanwhile another task's change lands
        self.w.git("add", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "landed")
        out = self.py('print(v2.take_up("3"))')
        self.assertIn("are back in the working tree (2 paths)", out)
        self.assertEqual((self.w.project / "theories/Shared.thy").read_text(), "A\nb\nc\nd\nE\n")
        self.assertEqual((self.w.project / "theories/New.thy").read_text(), "new\n")

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

    def test_a_check_that_advances_the_base_holds_the_machine_while_it_runs(self):
        self.spec("test -e .claude/state-probe || cat $ORCH_STATE_DIR/isabelle-exclusive > seen; tools/x --advance-base; true")
        self.w.run("finalize.py", "check", "3")
        self.assertEqual((self.w.project / "seen").read_text(), "3")
        self.assertFalse((self.w.state / "isabelle-exclusive").exists())

    def test_a_check_waits_while_another_advances_the_base(self):
        (self.w.state / "isabelle-exclusive").write_text("9")
        self.spec("true")
        started = time.time()
        self.w.run("finalize.py", "check", "3", env={"ORCH_ISABELLE_WAIT": "1", "ORCH_ISABELLE_POLL": "0.2"})
        self.assertGreaterEqual(time.time() - started, 1)  # it waited its limit, then ran

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
