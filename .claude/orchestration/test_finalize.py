"""finalize.py: a task's check, then (after its verdict) its commit and push, in a temporary git repository with a bare
origin; the task's stage follows (v2.checked, v2.committed)."""
import json
import re
import os
from pathlib import Path
import subprocess
import sys
import threading
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import PLANNER_STATE  # noqa: E402


FAKE_CHECK = "import json\nprint(json.dumps({'refusals': []}))\ndef source_checks():\n    return {'refusals': []}\n"
MAP_HEAD = "| Theory | Direct imports | Content |\n|---|---|---|\n"


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

    def test_a_recorded_check_that_would_take_the_base_into_the_task_s_tree_is_not_run(self):
        # jobs recorded before the rule still name their own directory; none of them runs, and the round is not spent
        self.spec("python3 -B tools/incremental_check.py check --advance-base --output .build/tasks/3/final-check")
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 1, err)
        self.assertFalse(self.outcome()["ok"])
        self.assertEqual(self.outcome()["seconds"], 0)
        self.assertIn(".build/tasks/3/final-check", (self.w.project / ".build/tasks/3/finalize.log").read_text())
        self.assertNotIn("final-check", os.listdir(self.w.project / ".build/tasks/3"))

    def py(self, code):
        """Run v2 code in this world; its printed output."""
        r = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n{code}"],
                           env=self.w.env, capture_output=True, text=True, cwd=self.w.project)
        self.assertEqual(r.stderr, "")
        return r.stdout

    def test_a_failed_check_is_told_by_its_errors_and_not_by_its_last_lines(self):
        # task 143's second failure went to the planner as 28 lines of recipes accepted and a 1.5K summary, its error
        # list after them (2026-09-22 11:47)
        log = self.w.project / ".build/tasks/3/finalize.log"
        log.parent.mkdir(parents=True, exist_ok=True)
        tail = lambda: subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                       f"import finalize; print(finalize.log_tail({str(log)!r}))"],
                                      env=self.w.env, capture_output=True, text=True).stdout
        log.write_text("".join(f'{{"recipe": "r{i}", "status": "accepted"}}\n' for i in range(40)) + '{"summary": "'
                       + "x" * 1500 + '"}\n[this check reported 1 error, listed here with where each stands.]\n'
                       "- r7 failed (exit 1) [r7.log]\n")
        said = tail()
        self.assertIn("- r7 failed (exit 1) [r7.log]", said)
        self.assertNotIn('"recipe": "r39"', said)
        self.assertIn("(the whole log: .build/tasks/3/finalize.log)", said)
        names = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import "
                                "finalize; print(finalize.listed([f'validation/r{i}.json' for i in range(166)]))"],
                               env=self.w.env, capture_output=True, text=True).stdout      # task 94's 166 receipts
        self.assertIn("validation/r11.json and 154 more", names)
        self.assertNotIn("r12.json", names)
        log.write_text("".join(f"line {i} " + "y" * 500 + "\n" for i in range(40)))   # no list: its last lines, cut
        said = tail()
        self.assertIn("line 39", said)
        self.assertNotIn("line 20 ", said)
        self.assertLess(len(said), 6000)

    def test_a_check_the_proof_base_refuses_is_nobody_s_failure_and_runs_again(self):
        # from 14:06 to 14:08 on 2026-09-22 every check failed in a second with "Accepted heap/database changed", the
        # base led to by a link its tools could not read, and six tasks were sent to fix commands that were right
        refused = self.w.root / "refused"
        refused.write_text("")
        self.spec(f"sh -c 'if [ -e {refused} ]; then echo \"AssertionError: Accepted heap/database changed.\"; exit 1; fi; echo checked'")
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 1, err)
        self.assertEqual(self.stage(), "checking")                          # no quick fix, no round counted
        self.assertFalse(self.w.st()["tasks"]["3"].get("checks_failed"))
        self.assertIn("refused task 3's check before it began", (self.w.state / "v2.log").read_text())
        self.w.run("watchdog.py", env={"ORCH_BASE_RETRY": "3600"})
        self.assertEqual(self.stage(), "checking")                          # the base has not changed: it waits
        refused.unlink()
        self.w.run("watchdog.py", env={"ORCH_BASE_RETRY": "0"})             # ORCH_SYNC: run again at once
        self.assertEqual(self.stage(), "reviewing")

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
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
        lock = self.w.project / ".git/index.lock"
        lock.write_text("")
        release = subprocess.Popen(["sh", "-c", f"sleep 3; rm -f {lock}"])
        code, _, err = self.w.run("finalize.py", "commit", "3")
        release.wait()
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add the readiness theory\n")

    def test_a_check_run_again_writes_to_a_fresh_output(self):
        # the check tool refuses an output directory that exists, to keep its evidence, so a check run again — after
        # a quick fix, or for a task taken back to be checked before its review — never ran as written (2026-09-21:
        # tasks 22 and 50 named .build/check-task22 and .build/check-50, both there)
        (self.w.project / ".build/out").mkdir(parents=True)
        self.spec('python3 -c "import os, sys; os.mkdir(sys.argv[2])" --output .build/out')
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 0, err)
        self.assertTrue((self.w.project / ".build/out-2").is_dir())
        self.assertIn("holds an earlier run's evidence", (self.w.state / "v2.log").read_text())

    def test_nothing_is_committed_before_its_review_accepts_it(self):
        # the owner, 2026-09-21: review before commit, never after. Task 52 was to commit four tasks' work in one
        # commit with their reviews to follow, and the finalizer took whatever a task named
        self.spec("true")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 1)  # its own review never accepted it
        self.assertIn("committed after its review has accepted it", self.outcome()["commit_error"])
        self.w.write("tools/theirs.py", "print('task 5')\n")
        self.py('v2.own("5", ["tools/theirs.py"])')
        self.w.task("5", subject="another task", status="completed")
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Ready.thy", "tools/theirs.py"], "message": ".build/tasks/3/commit.md"}))
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "verdict": "accept"}, "5": {"stage": "done"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 1)  # nor another's, completed or not
        self.assertIn("tools/theirs.py (task 5)", self.outcome()["commit_error"])
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "start\n")
        self.assertEqual(self.w.read_task("5")["status"], "in_progress")  # and task 5 was taken back: see below
        self.w.task("5", subject="another task", status="completed")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "verdict": "accept"}, "5": {"stage": "done", "review_tasks": ["6"]},
                             "6": {"verdict": "accept"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 0)  # once both are reviewed, it lands

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

    def test_a_check_is_not_run_at_all_while_the_working_tree_refuses_every_check(self):
        # a change is a set of parts, and a part taken out refuses every task's check and not only its own. Running
        # it anyway spends the check and costs the task a round for something it did not do (2026-09-20).
        self.spec("true")
        self.w.write("ROOT", 'session Development = HOL +\n  theories\n    Ready\n    Missing\n')
        self.assertEqual(self.w.run("finalize.py", "check", "3")[0], 1)
        self.assertEqual(self.stage(), "fixing")
        self.assertEqual(self.outcome()["seconds"], 0)                    # it never ran
        self.assertIn("not run, the working tree is inconsistent", (self.w.state / "v2.log").read_text())
        tail = (self.w.project / ".build/tasks/3/finalize.log").read_text()
        self.assertIn("The working tree refuses every check as it stands, whatever this task did", tail)
        self.assertIn("Missing", tail)
        self.assertIn("whatever this task did", self.w.st()["tasks"]["3"]["fix_text"])

    def test_a_failing_check_gets_one_quick_fix_then_goes_to_the_planner(self):
        self.spec("echo '*** Failed to finish proof'; exit 1")
        self.assertEqual(self.w.run("finalize.py", "check", "3")[0], 1)
        self.assertEqual(self.stage(), "fixing")
        (fix,) = [c["args"] for c in self.w.calls("--bg") if c["args"][:3] == ["--bg", "--resume", "k3"]]
        self.assertIn("- Failed to finish proof", fix[3])        # the check's own list of its errors (log_tail)
        self.assertIn("(the whole log: .build/tasks/3/finalize.log)", fix[3])
        self.w.set_st(tasks=dict(self.w.st()["tasks"], **{"3": dict(self.w.st()["tasks"]["3"], stage="checking")}))
        self.w.run("finalize.py", "check", "3")
        self.assertEqual(self.stage(), "planner")
        self.assertIn("failed its check again after a quick fix", self.heard())

    def test_an_accepted_task_is_committed_with_its_named_files_and_pushed(self):
        self.spec("true")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "summary": "Readiness is in.", "verdict": "accept"}})
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

    def test_a_tracked_file_gitignore_matches_is_committed_deleted(self):
        # task 48 was to remove the tracked tools/__pycache__/build.cpython-314.pyc, which .gitignore matches, and the
        # finalizer refused the path as "ignored" (2026-09-21): ignore rules reach only untracked files
        self.w.write("tools/__pycache__/build.cpython-314.pyc", "compiled\n")
        self.w.git("add", "-f", "tools/__pycache__/build.cpython-314.pyc")
        self.w.git("commit", "-q", "-m", "a compiled object, tracked")
        self.w.write(".gitignore", "__pycache__/\n*.pyc\n")
        (self.w.project / "tools/__pycache__/build.cpython-314.pyc").unlink()
        files = ["tools/__pycache__/build.cpython-314.pyc", ".gitignore"]
        said = self.w.v2("finalize", "3", "--check", "true", "--files", *files, "--message", ".build/tasks/3/commit.md",
                         env=self.w.as_session("k3"))
        self.assertNotIn("not ignored", said)                                        # the path is the repository's
        self.w.write(".build/tasks/3/finalize.json", json.dumps({"check": "true", "files": files,
                                                                 "message": ".build/tasks/3/commit.md"}))
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "summary": "Removed.", "verdict": "accept"}})
        code, _, err = self.w.run("finalize.py", "commit", "3")
        self.assertEqual(code, 0, err)
        shown = self.w.git("show", "--name-status", "--format=", "HEAD")
        self.assertIn("D\ttools/__pycache__/build.cpython-314.pyc", shown)
        self.assertIn("A\t.gitignore", shown)

    def test_a_failed_commit_goes_to_the_planner(self):
        self.spec("true")
        self.w.write("theories/Ready.thy", "")
        self.w.git("add", "theories/Ready.thy")
        self.w.git("commit", "-q", "-m", "already")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 1)
        self.assertEqual(self.stage(), "planner")
        self.assertIn("its commit failed", self.heard())

    def test_a_commit_carrying_a_placeholder_is_refused_and_goes_to_the_planner(self):
        self.spec("true")
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin\n(* CHECK_NUMBERS *)\nend\n")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
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
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
        self.assertEqual(self.w.run("finalize.py", "commit", "3")[0], 0)
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add the readiness theory\n")
        self.assertIn("taken as its own words", (self.w.state / "v2.log").read_text())

    def test_a_commit_does_not_carry_another_unfinished_task_s_file(self):
        self.spec("true")
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Ready.thy", "THEORY_MAP.md"],
             "message": ".build/tasks/3/commit.md"}))
        self.w.task("4")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"},
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
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
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
        self.w.set_st(tasks={"4": {"stage": "committing", "role": "implementer", "session": "implement-4",
                                   "verdict": "accept"}})
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
        mine = f"5.{os.getpid()}"  # its own: tests run side by side, and another's `sleep 5` is no leak of this one
        self.spec(f"sleep {mine}; true")
        started = time.time()
        code, _, _ = self.w.run("finalize.py", "check", "3", env={"ORCH_FINAL_MAX": "1"})
        self.assertEqual(code, 1)
        self.assertLess(time.time() - started, 4)
        self.assertEqual(subprocess.run(["pgrep", "-f", f"^sleep {mine}$"], capture_output=True).stdout, b"")
        self.assertIn("did not finish within 1 s", (self.w.project / ".build/tasks/3/finalize.log").read_text())


    def documents(self):
        """A task whose change is documents only: a decision, and a row of THEORY_MAP.md for a theory that is there."""
        self.w.write("tools/check.py", FAKE_CHECK)
        self.w.write("THEORY_MAP.md", MAP_HEAD + "| Ready | Main | ready |\n")
        self.w.write("DECISIONS.md", "# Decisions\n\nReady is kept.\n")
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "documents", "files": ["DECISIONS.md", "THEORY_MAP.md"], "message": ".build/tasks/3/commit.md"}))

    def test_a_commit_of_documents_is_checked_by_the_finalizer_itself_with_no_machine(self):
        # design-171 changed DECISIONS.md alone, spent two requests inventing a check to hand over, and would have
        # waited for a heavy run and run five minutes of Isabelle that no document can change (2026-09-22)
        self.documents()
        full = dict(ORCH_ISABELLE_RUNS="2", ORCH_ISABELLE_WAIT="600", ORCH_ISABELLE_POLL="0.2")  # the machine full
        started = time.time()
        code, _, err = self.w.run("finalize.py", "check", "3", env=full)
        self.assertEqual(code, 0, err)
        self.assertLess(time.time() - started, 30)  # it waited for no heavy run
        self.assertTrue(self.outcome()["ok"])
        self.assertEqual(self.stage(), "reviewing")
        self.assertIn("check of task 3: passed (its documents; no machine)", (self.w.state / "v2.log").read_text())
        self.assertIn("the documents check passed", (self.w.project / ".build/tasks/3/finalize.log").read_text())
        # a row for a theory that is not there, and a conflict left in a document, are this commit's to repair
        self.w.write("THEORY_MAP.md", MAP_HEAD + "| Ready | Main | ready |\n| Gone | Main | removed |\n")
        self.w.write("DECISIONS.md", "# Decisions\n<<<<<<< ours\nReady is kept.\n=======\nReady goes.\n>>>>>>> theirs\n")
        self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3"}})
        code, _, err = self.w.run("finalize.py", "check", "3", env=full)
        self.assertEqual(code, 1, err)
        log = (self.w.project / ".build/tasks/3/finalize.log").read_text()
        self.assertIn("2 errors", log)
        self.assertIn("THEORY_MAP.md has a row for Gone, which no theory is", log)
        self.assertIn("DECISIONS.md holds a conflict marker", log)
        self.assertFalse(self.outcome()["ok"])

    def test_a_row_head_already_lacks_a_theory_for_is_not_the_documents_commit_s(self):
        self.w.write("THEORY_MAP.md", MAP_HEAD + "| Ghost | Main | never there |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a row for a theory that is not there")
        self.documents()
        self.w.write("THEORY_MAP.md", MAP_HEAD + "| Ghost | Main | never there |\n| Ready | Main | ready |\n")
        code, _, err = self.w.run("finalize.py", "check", "3")
        self.assertEqual(code, 0, err)


class LandingTests(unittest.TestCase):
    """Main never moves into a state worse than it was, and never by work checked against a main that has moved on:
    HEAD went inconsistent on 2026-09-20 through a commit that took ROOT whole, and a task in its own tree was
    checked on its branch, never together with what landed beside it."""

    tearDown, outcome, stage, heard = (FinalizeTests.tearDown, FinalizeTests.outcome, FinalizeTests.stage,
                                       FinalizeTests.heard)

    def setUp(self):
        FinalizeTests.setUp(self)
        (self.w.project / "theories/Ready.thy").unlink()  # the fixture's installed file: here it is written per test
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n")
        self.w.write("theories/Base.thy", "theory Base imports Main begin end\n")
        self.w.write(".gitattributes", "ROOT merge=union\n")  # as the repository merges its index files
        self.w.git("add", "ROOT", "theories/Base.thy", ".gitattributes")
        self.w.git("commit", "-q", "-m", "the base theory")
        self.w.git("push", "-q", "origin", "main")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})

    def commit(self, files, env=None):
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": files, "message": ".build/tasks/3/commit.md"}))
        return self.w.run("finalize.py", "commit", "3", env=env)

    def test_a_commit_that_would_leave_head_inconsistent_is_refused(self):
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Ready\n")
        self.w.write("theories/Ready.thy", "theory Ready imports Base begin end\n")
        head = self.w.git("rev-parse", "HEAD")
        self.assertEqual(self.commit(["ROOT"])[0], 1)  # the declaration without the theory it declares
        self.assertEqual(self.w.git("rev-parse", "HEAD"), head)
        self.assertIn("would leave HEAD inconsistent", self.outcome()["commit_error"])
        self.assertIn("ROOT declares Ready, which is not in theories/", self.heard())
        self.assertEqual(self.w.git("diff", "--cached", "--name-only"), "")  # and nothing is left staged
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"])[0], 0)  # with it, it lands
        self.assertEqual(self.stage(), "done")

    def test_a_commit_is_not_refused_for_trouble_head_already_has(self):
        # what HEAD already holds is not this commit's to repair: it may not add to it, and nothing more
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Ghost\n")
        self.w.git("commit", "-q", "--no-verify", "-am", "declare a theory that is not there")
        self.w.write("theories/Ready.thy", "theory Ready imports Base begin end\n")
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Ghost\n    Ready\n")
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"])[0], 0)

    def train_checks(self):
        """The checks landing trains ran (train.py writes each output under .build/tasks/trains/)."""
        trains = self.w.project / ".build/tasks/trains"
        return sorted(p.name for p in trains.glob("*-train*") if p.is_dir()) if trains.exists() else []

    def tree(self):
        self.env = dict(ORCH_TREES="1")
        path = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               "print(v2.worktree('3'))"], env=dict(self.w.env, **self.env), capture_output=True,
                              text=True).stdout.strip()
        tree = Path(path)
        (tree / "theories/Ready.thy").write_text("theory Ready imports Base begin end\n")
        (tree / "ROOT").write_text("session S = HOL +\n  theories\n    Base\n    Ready\n")
        return tree

    def land_beside(self):
        """Another task lands while task 3 is reviewed: its theory and its ROOT line, in main."""
        self.w.write("theories/Other.thy", "theory Other imports Base begin end\n")
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Other\n")
        self.w.git("add", "ROOT", "theories/Other.thy")
        self.w.git("commit", "-q", "-m", "another task's work")

    def test_a_task_in_its_tree_is_checked_with_what_landed_before_it_lands(self):
        tree = self.tree()
        self.land_beside()
        both = "sh -c 'test -f theories/Other.thy && test -f theories/Ready.thy && mkdir -p {output}'"
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_LANDING_CHECK=both))
        self.assertEqual(code, 0, err)
        self.assertEqual(len(self.train_checks()), 1)  # checked where both stood: its train, with main
        self.assertEqual(self.stage(), "done")
        root = (self.w.project / "ROOT").read_text()
        self.assertIn("    Other\n", root)
        self.assertIn("    Ready\n", root)
        self.assertTrue(self.outcome()["landing_check"])
        self.assertFalse(tree.exists())  # landed: its tree is taken away
        # with the planner's state, as a commit made in the one tree takes it: with every task in a tree of its own,
        # nothing committed HANDOFF.md at all (2026-09-22)
        self.assertEqual(self.w.git("status", "--porcelain", "--", "HANDOFF.md"), "")
        self.assertIn("HANDOFF.md", self.w.git("show", "--stat", "--format=", "HEAD"))

    def test_receipts_a_task_did_not_commit_are_put_back_before_it_lands(self):
        # task 94's tree held receipts of its own retain while main's retention wrote the same files (2026-09-22); git
        # merges nothing over a file changed in the tree
        self.w.write("validation/incremental-check.json", '{"retained": 0}\n')
        self.w.git("add", "validation/incremental-check.json")
        self.w.git("commit", "-q", "-m", "a retention")
        tree = self.tree()
        (tree / "validation/incremental-check.json").write_text('{"retained": "by the task"}\n')
        (tree / "validation/reconstruction").mkdir(parents=True, exist_ok=True)
        (tree / "validation/reconstruction/new-verified.json").write_text("{}\n")
        self.w.write("validation/incremental-check.json", '{"retained": 1}\n')
        self.w.git("add", "validation/incremental-check.json")
        self.w.git("commit", "-q", "-m", "the next retention")
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"],
                                   env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        self.assertEqual((self.w.project / "validation/incremental-check.json").read_text(), '{"retained": 1}\n')
        self.assertFalse((self.w.project / "validation/reconstruction/new-verified.json").exists())
        # its train merges its branch, never its tree: what the tree holds uncommitted meets nothing of main's

    def test_a_landing_lets_main_go_while_its_check_with_what_landed_waits_for_the_machine(self):
        # one landing held main from 11:24 to 12:23 on 2026-09-22 waiting for a heavy run, and tasks 147 and 132 were
        # refused after sixty minutes each behind it, their work whole
        self.tree()
        self.land_beside()                                                   # its check will be made with what landed
        env = dict(self.w.env, **self.env, ORCH_ISABELLE_RUNS="2", ORCH_ISABELLE_WAIT="6", ORCH_ISABELLE_POLL="0.2",
                   ORCH_LANDING_CHECK="mkdir -p {output}")                   # the machine full the whole while
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["ROOT", "theories/Ready.thy"], "message": ".build/tasks/3/commit.md"}))
        landing = subprocess.Popen([sys.executable, str(fakes.HERE / "finalize.py"), "commit", "3"], env=env,
                                   cwd=self.w.project, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        time.sleep(2)
        free = subprocess.run([sys.executable, "-c", f"import sys, time; sys.path.insert(0, {str(fakes.HERE)!r}); "
                               "import v2\nwith v2.landing(time.time() + 1) as held: print(held)"],
                              env=self.w.env, capture_output=True, text=True).stdout.strip()
        self.assertEqual(free, "True")                                       # main is not held while it waits
        self.assertEqual(landing.wait(timeout=60), 0, landing.stderr.read())  # and past its budget it lands, as before
        self.assertIn("lets main go while its check with what landed waits for the machine",
                      (self.w.state / "v2.log").read_text())
        self.assertEqual(self.stage(), "done")

    def test_a_commit_that_waited_out_other_landings_stays_queued_and_the_next_lander_lands_it(self):
        # task 147's commit was refused after sixty minutes of other landings and went to the planner, which queued it
        # again to its implementer, with nothing to do (2026-09-22 12:24): now it stays queued, and whoever lands next
        # lands it — the watchdog starts a lander when entries wait and nobody lands them
        self.tree()
        hold = subprocess.Popen([sys.executable, "-c", f"import sys, time; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                 "import v2\nwith v2.landing(time.time() + 1): time.sleep(4)"], env=self.w.env)
        time.sleep(1)
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))
        hold.wait(timeout=30)
        self.assertEqual(code, 0, err)
        entry = json.loads((self.w.state / "landing-queue.json").read_text())["3"]
        self.assertFalse(entry.get("decided"))                               # queued, undecided
        self.assertEqual(self.stage(), "committing")
        self.assertIn("task 3 stays queued past its finalizer's budget", (self.w.state / "v2.log").read_text())
        self.assertNotIn("lands_again", self.w.st()["tasks"]["3"])
        tasks = self.w.st()["tasks"]
        tasks["3"]["finishing_since"] = time.time() - 7200                   # its finalizer ended long ago
        self.w.set_st(tasks=tasks)
        self.w.run("watchdog.py", env=self.env)                              # ORCH_SYNC: the lander runs at once
        self.assertIn("nobody lands it: a lander starts", (self.w.state / "v2.log").read_text())
        self.assertEqual(self.stage(), "done")
        self.assertIn("    Ready\n", (self.w.project / "ROOT").read_text())
        self.assertFalse([c for c in self.w.calls("--bg") if "implement-3" in " ".join(c["args"])])  # no session of it

    def test_work_that_does_not_stand_with_what_landed_goes_back_to_be_fixed(self):
        tree = self.tree()
        self.land_beside()
        head = self.w.git("rev-parse", "HEAD")
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_LANDING_CHECK="false"))
        self.assertEqual(code, 1, err)
        self.assertEqual(self.w.git("rev-parse", "HEAD"), head)  # main did not move
        self.assertEqual(self.stage(), "fixing")  # a failed check: the task's quick fix
        self.assertIn("does not stand with what landed", self.w.st()["tasks"]["3"]["fix_text"])
        self.assertTrue((tree / "theories/Other.thy").exists())  # the tree holds both, where the fix is checked

    def test_nothing_is_checked_again_when_nothing_landed_meanwhile(self):
        self.tree()
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_LANDING_CHECK="false"))
        self.assertEqual(code, 0, err)  # its check saw exactly what lands
        self.assertEqual(self.stage(), "done")
        self.assertNotIn("landing_check", self.outcome())

    def four_stands_in_the_one_tree(self, before="    Base\n"):
        """Task 4, working in the one tree, has its ROOT line and its theory there, uncommitted."""
        self.w.task("4")
        self.w.set_st(tasks={**self.w.st()["tasks"], "4": {"stage": "running", "role": "implementer"}})
        self.w.write("ROOT", "session S = HOL +\n  theories\n" + before + "    Four\n")
        self.w.write("theories/Four.thy", "theory Four imports Base begin end\n")
        (self.w.state / "tree-owners.json").write_text(json.dumps({"ROOT": "4", "theories/Four.thy": "4"}))

    def test_a_landing_waits_for_what_stands_uncommitted_in_the_one_tree(self):
        # the merge into the one tree would overwrite task 4's working ROOT, and git refuses it. Task 24 was sent to
        # the planner for task 54's THEORY_MAP.md at 23:02:10 — "work no review has accepted", which a commit made
        # in its own tree never carries — and 54 committed it 56 seconds later (2026-09-21)
        self.tree()
        self.land_beside()                  # main has moved: a landing check is owed, and one is enough
        self.four_stands_in_the_one_tree(before="    Base\n    Other\n")
        env = dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}")
        four = threading.Timer(1.5, lambda: (self.w.git("add", "ROOT", "theories/Four.thy"),
                                             self.w.git("commit", "-q", "-m", "task 4")))
        four.start()
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=env)
        four.join()
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        root = (self.w.project / "ROOT").read_text()
        self.assertIn("    Four\n", root)
        self.assertIn("    Ready\n", root)
        self.assertIn("waits for what stands uncommitted in the one tree: ROOT (task 4)",
                      (self.w.state / "v2.log").read_text())
        # waited for before its commit, not found after its landing check: that check would be run a second time
        self.assertEqual(len(self.train_checks()), 1)

    def test_a_landing_that_waited_its_budget_out_is_refused_as_what_it_is(self):
        tree = self.tree()
        self.four_stands_in_the_one_tree()
        head, branch = self.w.git("rev-parse", "HEAD"), self.w.git("rev-parse", "HEAD", cwd=tree)
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))
        self.assertEqual(code, 1, err)
        error = self.outcome()["commit_error"]
        self.assertIn("over what stands there uncommitted: ROOT (task 4)", error)
        self.assertNotIn("no review has accepted", error)
        self.assertEqual(self.w.git("rev-parse", "HEAD"), head)                 # main did not move
        self.assertEqual(self.w.git("rev-parse", "HEAD", cwd=tree), branch)     # and nothing was committed
        self.assertIn("    Four\n", (self.w.project / "ROOT").read_text())    # task 4's work stands untouched

    def test_a_commit_standing_on_its_branch_lands_when_its_commit_is_made_again(self):
        # a landing that did not happen (merge_refused) leaves the commit on the branch; made again, a commit of
        # nothing would fail, so it lands as it stands
        tree = self.tree()
        self.w.git("add", "ROOT", "theories/Ready.thy", cwd=tree)
        self.w.git("commit", "-q", "-m", "Add the readiness theory", cwd=tree)
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=self.env)
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        self.assertIn("    Ready\n", (self.w.project / "ROOT").read_text())
        self.assertIn("Add the readiness theory", self.w.git("log", "--format=%s"))

    def test_a_row_one_side_changed_beside_the_other_s_new_row_stands_once(self):
        # union keeps both versions of a row one side changed next to a row the other added: task 24's branch added
        # its row under Development_Loci's while main changed that row, and the merge held it twice (2026-09-21)
        self.w.write(".gitattributes", "ROOT merge=union\nTHEORY_MAP.md merge=union\n")
        self.w.write("THEORY_MAP.md", "| Theory | Imports |\n| Base | Main |\n| Tail | Base |\n")
        self.w.git("add", ".gitattributes", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()
        (tree / "THEORY_MAP.md").write_text("| Theory | Imports |\n| Base | Main |\n| Ready | Base |\n| Tail | Base |\n")
        self.w.write("THEORY_MAP.md", "| Theory | Imports |\n| Base | Main, Extra |\n| Tail | Base |\n")
        self.w.git("commit", "-q", "-am", "another task changes the Base row")
        code, _, err = self.commit(["ROOT", "theories/Ready.thy", "THEORY_MAP.md"],
                                   env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertEqual(code, 0, err)
        self.assertEqual((self.w.project / "THEORY_MAP.md").read_text(),
                         "| Theory | Imports |\n| Base | Main, Extra |\n| Ready | Base |\n| Tail | Base |\n")

    def test_a_row_both_sides_changed_is_refused_as_what_the_gate_found(self):
        # a real conflict stays one, and is said as the gate said it: task 24's was cut to git's last 300 characters
        # and called lines "written in the same place by another task" (2026-09-21)
        for hook in ("pre-commit", "pre-merge-commit"):
            os.symlink(fakes.HERE / "commit_gate.py", self.w.project / ".git/hooks" / hook)
        self.w.write(".gitattributes", "ROOT merge=union\nTHEORY_MAP.md merge=union\n")
        self.w.write("THEORY_MAP.md", "| Theory | Imports |\n| Base | Main |\n")
        self.w.git("add", ".gitattributes", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()
        (tree / "THEORY_MAP.md").write_text("| Theory | Imports |\n| Base | Main, Ours |\n| Ready | Base |\n")
        self.w.write("THEORY_MAP.md", "| Theory | Imports |\n| Base | Main, Theirs |\n")
        self.w.git("commit", "-q", "-am", "another task changes the Base row otherwise")
        head = self.w.git("rev-parse", "HEAD")
        code, _, err = self.commit(["ROOT", "theories/Ready.thy", "THEORY_MAP.md"],
                                   env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertEqual(code, 1, err)
        self.assertEqual(self.w.git("rev-parse", "HEAD"), head)
        said = self.heard()
        self.assertIn("THEORY_MAP.md holds the row of Base 2 times", said)
        self.assertIn("queue it (`v2.py queue 3`)", said)
        self.assertNotIn("written in the same place", said)
        self.assertNotIn("--no-verify", said)  # the gate's finding, not git's and the gate's words around it

    def test_what_comes_to_stand_during_a_landing_is_waited_for_with_main_let_go(self):
        # task 80's landing check took five minutes, task 66 wrote DECISIONS.md in the one tree meanwhile, and the merge
        # was refused to the planner (2026-09-22 00:00:55): it waits, lets main go, and lands again from its branch
        tree = self.tree()
        self.land_beside()                                                    # main moved: its landing check runs
        mark = Path(self.w.root) / "wrote"
        check = (f"sh -c 'mkdir -p {{output}} && if [ ! -e {mark} ]; then touch {mark}; printf \"    Four\\n\" >> "
                 f"{self.w.project}/ROOT; echo \"theory Four imports Base begin end\" > {self.w.project}/theories/Four.thy; fi'")

        def four_commits():                                                   # task 4 commits what it wrote
            for _ in range(300):
                if mark.exists():
                    time.sleep(1)
                    self.w.git("add", "ROOT", "theories/Four.thy")
                    self.w.git("commit", "-q", "-m", "task 4")
                    return
                time.sleep(0.05)
        four = threading.Thread(target=four_commits)
        four.start()
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_LANDING_CHECK=check))
        four.join()
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        root = (self.w.project / "ROOT").read_text()
        for name in ("Ready", "Four", "Other"):
            self.assertIn(f"    {name}\n", root)
        self.assertIn("the landing of task 3 waits for what stands uncommitted in the one tree: ROOT",
                      (self.w.state / "v2.log").read_text())

    def test_a_commit_that_waited_its_budget_out_on_the_one_tree_is_made_again_when_queued(self):
        # its review accepted it; a new session would find nothing to do and its check and review judge it again
        tree = self.tree()
        self.four_stands_in_the_one_tree()
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))[0], 1)
        self.assertIn("It lands again by itself once they are committed", self.outcome()["commit_error"])
        self.assertEqual(self.stage(), "planner")
        self.w.git("add", "ROOT", "theories/Four.thy")
        self.w.git("commit", "-q", "-m", "task 4")                       # what stood is committed
        said = self.w.v2("queue", "3", env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertIn("3: its commit is made again, with no session", said)
        self.assertEqual(self.stage(), "done")                           # ORCH_SYNC: the commit ran at once
        self.assertFalse([c for c in self.w.calls("--bg") if "implement-3" in " ".join(c["args"])])  # no session of it
        self.assertIn("    Ready\n", (self.w.project / "ROOT").read_text())

    def test_a_landing_waits_for_another_git_process_holding_its_tree_s_index(self):
        # the landing's commit in task 95's tree met a `git status` there, "Unable to create index.lock: File exists",
        # and was taken for the commit gate's refusal: the task went back and a new designer found its work whole
        # (2026-09-22 03:49)
        tree = self.tree()
        self.land_beside()                                            # a merge into its branch is made, and committed
        lock = self.w.project / ".git/worktrees" / tree.name / "index.lock"
        lock.parent.mkdir(parents=True, exist_ok=True)
        lock.write_text("")
        release = subprocess.Popen(["sh", "-c", f"sleep 3; rm -f {lock}"])
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        release.wait()
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        self.assertIn("    Ready\n", (self.w.project / "ROOT").read_text())

    def test_a_task_brings_main_into_its_branch_while_it_works(self):
        # implement-94 could not check against task 36, which was in main and not in its branch, and was told to copy
        # main's text into its tree by hand, since no session merges (q50, 2026-09-22)
        tree = self.tree()                          # its Ready.thy made and its ROOT changed, nothing committed
        self.land_beside()                          # main: another task's theory and its ROOT line
        ask = lambda: self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        said = ask()                                # main changed ROOT, which the session has changed and not committed
        self.assertIn("is in your branch now; your changes to ROOT, which main changed too, are carried onto it", said)
        self.assertTrue((tree / "theories/Other.thy").exists())                    # what landed is there
        self.assertTrue((tree / "theories/Ready.thy").exists())                    # and its own work as it was
        self.assertIn("    Ready\n", (tree / "ROOT").read_text())                   # its line, with main's
        self.assertIn("    Other\n", (tree / "ROOT").read_text())
        self.assertNotIn("Ready", self.w.git("show", "HEAD:ROOT", cwd=tree))           # and still its own to hand over
        self.assertIn("Bring main into task 3", self.w.git("log", "-1", "--format=%s", cwd=tree))
        self.assertIn("nothing to bring", ask())
        self.assertIn("refused", self.w.v2("bring-main"))                         # no task's session: nothing

    def test_main_brought_in_under_uncommitted_rows_leaves_no_row_twice_at_the_landing(self):
        # implement-176 was refused bring-main for its uncommitted THEORY_MAP.md and copied main's rows in by hand; its
        # branch held them without main in its history, main changed one of them again, and its landing found that row
        # twice (2026-09-22 16:21)
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()
        (tree / "THEORY_MAP.md").write_text((tree / "THEORY_MAP.md").read_text() + "| Ready | readiness |\n")
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, stated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row")
        said = self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        self.assertIn("your changes to THEORY_MAP.md, which main changed too, are carried onto it", said)
        self.assertEqual((tree / "THEORY_MAP.md").read_text(), "| Theory | Offers |\n|---|---|\n| Base | the base |\n"
                         "| Other | other, stated |\n| Ready | readiness |\n")
        self.assertIn("other, stated", self.w.git("show", "HEAD:THEORY_MAP.md", cwd=tree))  # main is in its history
        self.assertTrue((self.w.project / ".build/tasks/3/bring-main/THEORY_MAP.md").exists())  # its own, as it was
        # main restates the row again: the landing merges from the merge, and the row is there once
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, restated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row again")
        said = self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        self.assertEqual((tree / "THEORY_MAP.md").read_text().count("| Other |"), 1, said)
        self.assertIn("| Other | other, restated |", (tree / "THEORY_MAP.md").read_text())

    def test_bring_main_leaves_the_session_s_uncommitted_index_rows_as_they_are(self):
        # implement-139's uncommitted ROOT line and THEORY_MAP row were dropped by bring-main, which agreed the rows of
        # files main had not changed and staged the rest of its edits into the merge commit (2026-09-22 10:05)
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()                                  # its Ready.thy made and its ROOT changed, uncommitted
        (tree / "THEORY_MAP.md").write_text("| Theory | Offers |\n|---|---|\n| Base | the base |\n| Ready | readiness |\n")
        self.w.write("theories/Other.thy", "theory Other imports Base begin end\n")
        self.w.git("add", "theories/Other.thy")
        self.w.git("commit", "-q", "--no-verify", "-m", "main changes neither index file")
        said = self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        self.assertIn("is in your branch now", said)
        self.assertIn("    Ready\n", (tree / "ROOT").read_text())                    # its uncommitted edits stand
        self.assertIn("| Ready | readiness |", (tree / "THEORY_MAP.md").read_text())
        self.assertNotIn("Ready", self.w.git("show", "HEAD:ROOT", cwd=tree))           # and are not committed
        self.assertNotIn("Ready", self.w.git("show", "HEAD:THEORY_MAP.md", cwd=tree))

    def test_a_row_a_branch_copied_from_main_is_main_s_when_main_changes_it_again(self):
        # task 176's session copied main's rows into its map by hand and its branch was committed so, without main in
        # its history; main changed a copied row again, and the merge of the two held it twice — at its landing
        # (2026-09-22 16:21), and in bring-main's merge commit, which the gate refused (q62, 16:50)
        self.w.write(".gitattributes", "ROOT merge=union\nTHEORY_MAP.md merge=union\n")  # as the repository's
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other |\n")
        self.w.git("add", ".gitattributes", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, stated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row")
        (tree / "THEORY_MAP.md").write_text(self.w.git("show", "main:THEORY_MAP.md") + "| Ready | readiness |\n")
        self.w.git("add", "-A", cwd=tree)
        self.w.git("commit", "-q", "--no-verify", "-m", "the task's work, main's rows copied in", cwd=tree)
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, restated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row again")
        said = self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        self.assertIn("is in your branch now", said)
        self.assertEqual(self.w.git("show", "HEAD:THEORY_MAP.md", cwd=tree), "| Theory | Offers |\n|---|---|\n"
                         "| Base | the base |\n| Other | other, restated |\n| Ready | readiness |\n")

    def test_a_row_the_session_copied_from_main_and_did_not_commit_is_main_s_too(self):
        self.w.write(".gitattributes", "ROOT merge=union\nTHEORY_MAP.md merge=union\n")  # as the repository's
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other |\n")
        self.w.git("add", ".gitattributes", "THEORY_MAP.md")
        self.w.git("commit", "-q", "-m", "the map")
        tree = self.tree()
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, stated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row")
        (tree / "THEORY_MAP.md").write_text(self.w.git("show", "main:THEORY_MAP.md") + "| Ready | readiness |\n")
        self.w.write("THEORY_MAP.md", "| Theory | Offers |\n|---|---|\n| Base | the base |\n| Other | other, restated |\n")
        self.w.git("add", "THEORY_MAP.md")
        self.w.git("commit", "-q", "--no-verify", "-m", "a task restates Other's row again")
        said = self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        self.assertNotIn("holds main's and your version", said)
        self.assertEqual((tree / "THEORY_MAP.md").read_text(), "| Theory | Offers |\n|---|---|\n"
                         "| Base | the base |\n| Other | other, restated |\n| Ready | readiness |\n")

    def test_lines_both_sides_changed_are_written_by_the_session_and_brought_in(self):
        # task 128's landing did not merge (2026-09-22 11:32): its session could see no conflict, running no merge, and
        # writing main's version with its lines in it was refused by bring-main as uncommitted (implement-94.2)
        shared = "theory Shared\n  imports Base\nbegin\nlemma s: True by simp\nend\n"
        self.w.write("theories/Shared.thy", shared)
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Shared\n")
        self.w.git("add", "ROOT", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "a shared theory")
        tree = self.tree()
        (tree / "ROOT").write_text("session S = HOL +\n  theories\n    Base\n    Shared\n    Ready\n")
        (tree / "theories/Shared.thy").write_text(shared.replace("lemma s: True", 'lemma s: "True"'))
        self.w.git("add", "-A", cwd=tree)
        self.w.git("commit", "-q", "--no-verify", "-m", "the task's work", cwd=tree)
        mine = "session S = HOL +\n  theories\n    Base\n    Shared\n    Ready\n    Mine\n"
        (tree / "ROOT").write_text(mine)                                          # and a line not committed
        self.w.write("theories/Shared.thy", shared.replace("by simp", "by auto"))
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Shared\n    Theirs\n")
        self.w.git("add", "theories/Shared.thy", "ROOT")
        self.w.git("commit", "-q", "-m", "another task changes the same line")
        ask = lambda: self.w.v2("bring-main", env=dict(self.env, **self.w.as_session("k3")))
        said = ask()
        self.assertIn("refused: main and your branch changed the same lines of theories/Shared.thy", said)
        self.assertEqual((tree / "ROOT").read_text(), mine)                      # set aside, and back as it was
        draft = self.w.project / ".build/tasks/3/merge/theories/Shared.thy"
        self.assertIn("<<<<<<< HEAD", draft.read_text())                            # both sides, marked
        self.assertIn('lemma s: "True" by simp', draft.read_text())
        self.assertIn("lemma s: True by auto", draft.read_text())
        self.assertIn("refused", ask())                                           # still marked: nothing taken
        draft.write_text(shared.replace("lemma s: True by simp", 'lemma s: "True" by auto'))
        said = ask()
        self.assertIn("is in your branch now, with your theories/Shared.thy", said)
        self.assertIn('lemma s: "True" by auto', (tree / "theories/Shared.thy").read_text())
        self.assertEqual([l.strip() for l in (tree / "ROOT").read_text().splitlines()[2:]],
                         ["Base", "Shared", "Ready", "Theirs", "Mine"])           # its uncommitted line carried over
        self.assertIn("Bring main into task 3", self.w.git("log", "-1", "--format=%s", cwd=tree))
        self.assertFalse((self.w.project / ".build/tasks/3/merge").exists())
        self.assertIn("nothing to bring", ask())

    def test_imports_both_sides_added_on_one_line_merge_as_a_list(self):
        # task 124's branch and main each added an import at the end of one theory's import list; the landing was
        # refused and a session spent putting its import on a line of its own (2026-09-22 08:45)
        shared = "theory Shared\n  imports Base\nbegin\nlemma s: True by simp\nend\n"
        self.w.write("theories/Shared.thy", shared)
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Shared\n")
        self.w.git("add", "ROOT", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "a shared theory")
        tree = self.tree()
        (tree / "ROOT").write_text("session S = HOL +\n  theories\n    Base\n    Shared\n    Ready\n")
        (tree / "theories/Shared.thy").write_text(shared.replace("imports Base", "imports Base Ready"))
        self.w.write("theories/Other.thy", "theory Other imports Base begin end\n")
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Other\n    Shared\n")
        self.w.write("theories/Shared.thy", shared.replace("imports Base", "imports Base Other"))
        self.w.git("add", "ROOT", "theories/Shared.thy", "theories/Other.thy")
        self.w.git("commit", "-q", "-m", "another task adds an import on the same line")
        code, _, err = self.commit(["ROOT", "theories/Ready.thy", "theories/Shared.thy"],
                                   env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        landed = (self.w.project / "theories/Shared.thy").read_text()
        # both names, each once; main's layout first, since a landing train merges the task onto main
        self.assertEqual(re.findall(r"\b(Base|Ready|Other)\b", landed.split("begin")[0]), ["Base", "Other", "Ready"])
        self.assertIn("lemma s: True by simp", landed)

    def test_a_theory_both_sides_changed_beyond_its_imports_still_conflicts(self):
        shared = "theory Shared\n  imports Base\nbegin\nlemma s: True by simp\nend\n"
        self.w.write("theories/Shared.thy", shared)
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Shared\n")
        self.w.git("add", "ROOT", "theories/Shared.thy")
        self.w.git("commit", "-q", "-m", "a shared theory")
        tree = self.tree()
        (tree / "ROOT").write_text("session S = HOL +\n  theories\n    Base\n    Shared\n    Ready\n")
        (tree / "theories/Shared.thy").write_text(shared.replace("by simp", "by auto"))
        self.w.write("theories/Shared.thy", shared.replace("by simp", "by blast"))
        self.w.git("commit", "-q", "-am", "another task changes the same proof")
        code, _, _ = self.commit(["ROOT", "theories/Ready.thy", "theories/Shared.thy"],
                                 env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}"))
        self.assertEqual(code, 1)
        self.assertIn("merge conflict: theories/Shared.thy", self.outcome()["commit_error"])
        # kept for its session, both sides marked, when the task is queued again (task 128, 2026-09-22)
        marked = (self.w.project / ".build/tasks/3/merge/theories/Shared.thy").read_text()
        self.assertIn("<<<<<<<", marked)
        self.assertIn("by auto", marked)
        self.assertIn("by blast", marked)
        self.assertIn(".build/tasks/3/merge/", self.heard())

    def test_a_commit_kept_out_by_the_one_tree_lands_by_itself_once_what_stood_is_committed(self):
        # the planner was told to queue it then, and had to watch the one tree for the moment: task 32 waited 60
        # minutes on task 62's ROOT and THEORY_MAP.md (2026-09-22 02:57)
        self.tree()
        self.four_stands_in_the_one_tree()
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))[0], 1)
        self.assertTrue(self.w.st()["tasks"]["3"].get("lands_again"))
        env = dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}")
        self.w.run("watchdog.py", env=env)
        self.assertEqual(self.stage(), "planner")                          # task 4's ROOT still stands
        self.w.git("add", "ROOT", "theories/Four.thy")
        self.w.git("commit", "-q", "-m", "task 4")
        self.w.run("watchdog.py", env=env)
        self.assertEqual(self.stage(), "done")                             # ORCH_SYNC: the commit ran at once
        self.assertIn("    Ready\n", (self.w.project / "ROOT").read_text())
        heard = self.heard() + json.dumps(self.w.mail("plan-1"))  # a live planner is told by mail
        self.assertIn("Task 3 lands again by itself", heard)
        self.assertNotIn("lands_again", self.w.st()["tasks"]["3"])
        self.assertFalse([c for c in self.w.calls("--bg") if "implement-3" in " ".join(c["args"])])  # no session of it

    def test_a_review_awaiting_its_task_s_commit_keeps_its_verdict_when_the_planner_names_it(self):
        # accepted, a review is done here and completed in the list only when its task commits; the planner names
        # every task in its order, and the review read as reopened lost its verdict — task 32, queued to land again,
        # was started afresh and checked and reviewed a second time (2026-09-22 02:58)
        self.w.task("5", subject="Review of task 3", description="Kind: review\nReviews: 3\n")
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3",
                                   "kind": "build", "review_tasks": ["5"]},
                             "5": {"stage": "done", "kind": "review", "reviews": "3", "verdict": "accept"}})
        self.tree()
        self.four_stands_in_the_one_tree()
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))[0], 1)
        self.w.git("add", "ROOT", "theories/Four.thy")
        self.w.git("commit", "-q", "-m", "task 4")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        _, said, _ = self.w.run("v2.py", "queue", "5", "3", env=dict(self.env, ORCH_LANDING_CHECK="mkdir -p {output}",
                                                                   **self.w.as_session("p1")))
        self.assertIn("3: its commit is made again, with no session", said)
        self.assertEqual(self.stage(), "done")
        self.assertFalse([c for c in self.w.calls("--bg") if "implement-3" in " ".join(c["args"])])  # no session of it

    def test_a_dropped_commit_kept_out_by_the_one_tree_does_not_land_by_itself(self):
        # the planner's to re-plan once it drops it
        self.tree()
        self.four_stands_in_the_one_tree()
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, ORCH_ISABELLE_WAIT="1"))[0], 1)
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.w.run("v2.py", "drop", "3", env=dict(self.env, **self.w.as_session("p1")))
        self.assertNotIn("lands_again", self.w.st()["tasks"]["3"])
        self.w.git("add", "ROOT", "theories/Four.thy")
        self.w.git("commit", "-q", "-m", "task 4")
        self.w.run("watchdog.py", env=self.env)
        self.assertEqual(self.stage(), "planner")

    def test_main_moves_by_one_landing_at_a_time(self):
        # a landing's re-check must still be true when it lands: nothing else moves main in between
        import fcntl
        self.w.write("theories/Ready.thy", "theory Ready imports Base begin end\n")
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Ready\n")
        with open(self.w.state / "landing.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            code, _, _ = self.commit(["ROOT", "theories/Ready.thy"], env={"ORCH_ISABELLE_WAIT": "1"})
        self.assertEqual(code, 1)
        self.assertIn("other landings held main", self.outcome()["commit_error"])
        self.assertEqual(self.w.st()["tasks"]["3"].get("lands_again_why"), "main")  # the watchdog lands it again by itself
        self.w.set_st(tasks={"3": {"stage": "committing", "role": "implementer", "session": "implement-3", "verdict": "accept"}})
        self.assertEqual(self.commit(["ROOT", "theories/Ready.thy"])[0], 0)  # and once it is free, it lands

    def test_main_does_not_move_under_a_check_of_the_one_tree(self):
        # a landing merges into main's working files, which a check of a task in the one tree is reading
        import fcntl
        self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3"}})
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Base.thy"], "message": ".build/tasks/3/commit.md"}))
        with open(self.w.state / "landing.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)  # a landing in progress
            code, _, _ = self.w.run("finalize.py", "check", "3", env={"ORCH_ISABELLE_WAIT": "1"})
        self.assertEqual(code, 1)
        self.assertIn("landings held main", (self.w.project / ".build/tasks/3/finalize.log").read_text())
        with open(self.w.state / "landing.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_SH)  # another check of the one tree: they run beside each other
            self.w.set_st(tasks={"3": {"stage": "checking", "role": "implementer", "session": "implement-3"}})
            self.assertEqual(self.w.run("finalize.py", "check", "3", env={"ORCH_ISABELLE_WAIT": "1"})[0], 0)

    def test_a_manual_commit_is_held_to_the_same_rule(self):
        # the owner's commits and a Codex session's go past the finalizer: the hook holds them to the same function
        for hook in ("pre-commit", "pre-merge-commit"):
            os.symlink(fakes.HERE / "commit_gate.py", self.w.project / ".git/hooks" / hook)
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Ready\n")
        self.w.git("add", "ROOT")
        refused = subprocess.run(["git", "-C", str(self.w.project), "commit", "-q", "-m", "declare Ready"],
                                 env=self.w.env, capture_output=True, text=True)
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("ROOT declares Ready, which is not in theories/", refused.stderr)
        self.w.write("theories/Ready.thy", "theory Ready imports Base begin end\n")
        self.w.git("add", "theories/Ready.thy")
        subprocess.run(["git", "-C", str(self.w.project), "commit", "-q", "-m", "declare Ready with its theory"],
                       env=self.w.env, check=True)  # passes, and raises if it did not


    def test_a_landing_of_documents_is_checked_with_what_landed_by_the_documents_check(self):
        self.w.write("tools/check.py", FAKE_CHECK)
        self.w.git("add", "tools/check.py")
        self.w.git("commit", "-q", "-m", "the source checks")
        tree = self.tree()
        self.w.git("checkout", "--", "ROOT", cwd=tree)  # a decision alone: no theory, no ROOT line
        (tree / "theories/Ready.thy").unlink()
        (tree / "DECISIONS.md").write_text("# Decisions\n\nOther comes first.\n")
        self.land_beside()
        self.w.write(".build/tasks/3/finalize.json", json.dumps(
            {"check": "documents", "files": ["DECISIONS.md"], "message": ".build/tasks/3/commit.md"}))
        code, _, err = self.w.run("finalize.py", "commit", "3", env=dict(
            self.env, ORCH_LANDING_CHECK="false", ORCH_ISABELLE_RUNS="2", ORCH_ISABELLE_WAIT="600"))
        self.assertEqual(code, 0, err)  # no heavy run waited for, and the repository's check never ran
        self.assertEqual(self.stage(), "done")
        logs = list((self.w.project / ".build/tasks/trains").glob("*-train3.log"))
        self.assertEqual(len(logs), 1)
        self.assertIn("the documents check passed", logs[0].read_text())
        self.assertIn("the train of tasks 3: its documents check passed", (self.w.state / "v2.log").read_text())
        self.assertEqual((self.w.project / "DECISIONS.md").read_text(), "# Decisions\n\nOther comes first.\n")

    FAKE_CHECKER = """import json, os, subprocess, sys, time
args = sys.argv[1:]
out = os.path.realpath(args[args.index('--output') + 1])  # as activate_context: resolved
if args[0] == 'retain':
    os.makedirs('validation', exist_ok=True)
    json.dump({'retained': os.path.basename(out)}, open('validation/incremental-check.json', 'w'))
    sys.exit(0)
pointer = os.environ['ORCH_ACTIVE_CONTEXT']
try:
    parent = json.load(open(pointer))['directory']
except (OSError, ValueError):
    parent = None
os.makedirs(os.path.join(out, 'proof'))
os.makedirs(os.path.join(out, 'recipes'))
json.dump({'parent': parent}, open(os.path.join(out, 'proof', 'accepted-context.json'), 'w'))
json.dump({'status': 'accepted', 'phases': {'proof': 1.0}, 'rebuilt_theories': ['Ready']},
          open(os.path.join(out, 'incremental.json'), 'w'))
if os.environ.get('FAKE_MOVE_MAIN'):  # another landing, meanwhile
    project = os.environ['ORCH_PROJECT']
    open(os.path.join(project, 'moved.txt'), 'a').write('moved\\n')
    subprocess.run(['git', '-C', project, 'add', 'moved.txt'])
    subprocess.run(['git', '-C', project, 'commit', '-q', '--no-verify', '-m', 'main moved'])
if '--advance-base' in args:
    json.dump({'directory': os.path.join(out, 'proof')}, open(pointer, 'w'))
"""

    def fake_checker(self):
        """The repository's incremental check, faked: its advance of the base and its retention of receipts. And a base
        it stands on, whose check's bulk is still there."""
        self.w.write("tools/incremental_check.py", self.FAKE_CHECKER)
        self.w.write("validation/incremental-check.json", '{"retained": "before"}')
        self.w.git("add", "tools/incremental_check.py", "validation/incremental-check.json")
        self.w.git("commit", "-q", "-m", "the incremental check")
        old = self.w.project / ".build/bases/old"
        (old / "proof").mkdir(parents=True)
        (old / "recipes").mkdir()
        (old / "proof/accepted-context.json").write_text('{"parent": null}')
        self.before = json.dumps({"directory": str(old / "proof")})
        (self.w.state / "active-context.json").write_text(self.before)
        return old

    def test_a_landing_check_advances_the_base_and_its_receipts_are_committed_by_the_harness(self):
        # a check rebuilt every theory changed since a base the planner advanced by hand, and after one landing ~155
        # theories and 35 recipes in ~330 s whatever the task changed (notes/plan-landing-train.md 1a)
        old = self.fake_checker()
        self.tree()
        self.land_beside()
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=self.env)
        self.assertEqual(code, 0, err)
        self.assertEqual(self.stage(), "done")
        active = json.loads((self.w.state / "active-context.json").read_text())["directory"]
        self.assertRegex(active, r"\.build/bases/\d{8}-\d{6}-train3/proof$")  # the base is what landed
        self.assertTrue(self.w.git("log", "-1", "--format=%s").startswith(
            "Retain the recipe receipts of the check task 3 landed with"))
        self.assertIn("-train3", (self.w.project / "validation/incremental-check.json").read_text())
        self.assertEqual(self.w.git("status", "--porcelain", "--", "validation"), "")
        (entry,) = [json.loads(line) for line in (self.w.state / "lineage.jsonl").read_text().splitlines()]
        self.assertEqual((entry["task"], entry["depth"], entry["ok"], entry["rebuilt"]), ("3", 1, True, 1))
        self.assertFalse((old / "recipes").exists())  # a level of the lineage keeps its proof, not its check's bulk
        self.assertTrue((old / "proof").exists())
        self.assertTrue((Path(active).parent / "recipes").exists())  # the base in use stays whole

    def test_a_base_advanced_for_a_landing_that_did_not_happen_is_put_back(self):
        self.fake_checker()
        self.tree()
        self.land_beside()
        code, _, err = self.commit(["ROOT", "theories/Ready.thy"], env=dict(self.env, FAKE_MOVE_MAIN="1"))
        self.assertEqual(code, 1, err)  # main moved under each of its checks: it does not land
        self.assertEqual((self.w.state / "active-context.json").read_text(), self.before)
        self.assertIn("the base is back where it was", (self.w.state / "v2.log").read_text())
        self.assertNotIn("Retain the recipe receipts", self.w.git("log", "--format=%s"))


FAKE_REPORTING_CHECK = """import json, os, sys, time
out = sys.argv[-1]  # `--output DIR`, as the repository's check is written, or DIR alone
started = time.time()
time.sleep(float(os.environ.get('SLOW', 0)))
os.makedirs(out, exist_ok=True)
here = lambda name: os.path.exists(os.path.join('theories', name + '.thy'))
time.sleep(sum(float(x.split(':')[1]) for x in os.environ.get('SLOW_WITH', '').split(',') if x and here(x.split(':')[0])))
fails = [x for x in os.environ.get('FAIL_WITH', '').split(',') if x]  # a theory that fails the check, told by name
pairs = [x.split('+') for x in os.environ.get('FAIL_TOGETHER', '').split(',') if x]  # two that fail only together
open(os.environ['CHECKS'], 'a').write(f"{out} {started} {time.time()}\\n")
if os.environ.get('MOVE_MAIN') and not os.path.exists(os.environ['MOVE_MAIN']):  # the owner commits meanwhile
    open(os.environ['MOVE_MAIN'], 'w').write('moved')
    project = os.environ['ORCH_PROJECT']
    open(os.path.join(project, 'OWNER.md'), 'w').write('the owner\\n')
    os.system(f"git -C {project} add OWNER.md && git -C {project} commit -q --no-verify -m 'the owner'")
bad = [t for t in fails if here(t)]
together = [a + '+' + b for a, b in pairs if here(a) and here(b)]
if bad:
    json.dump({'status': 'failed', 'failed_recipes': ['r'], 'error': 'AssertionError: Failed recipes: r'},
              open(os.path.join(out, 'incremental.json'), 'w'))
    json.dump({'r': {'files': {'theories/' + t + '.thy': 'x' for t in bad}}}, open(os.path.join(out, 'manifests.json'), 'w'))
    print('recipe r failed')
    sys.exit(1)
if together:
    print('failed together: ' + ', '.join(together))
    sys.exit(1)
proof = [t for t in os.environ.get('FAIL_PROOF', '').split(',') if t and here(t)]  # its proofs fail, as the real check
if proof:  # says it: Isabelle's messages in the proof's build.log, one JSON line naming that log in its own output
    os.makedirs(os.path.join(out, 'proof'))
    log = os.path.join(out, 'proof', 'build.log')
    with open(log, 'w') as f:
        for t in proof:
            for n in (3, 7, 11):
                where = f'(line {n} of "{os.path.abspath(os.path.join("theories", t + ".thy"))}")'
                f.write(f'*** Failed to finish proof {where}:\\n*** goal (1 subgoal):\\n***  1. False\\n'
                        f'*** At command "by" {where}\\n')
    report = {'status': 'failed', 'error': 'AssertionError: Incremental proof failed; see ' + os.path.abspath(log)}
    json.dump(report, open(os.path.join(out, 'incremental.json'), 'w'))
    print(json.dumps(report))
    sys.exit(1)
json.dump({'status': 'accepted', 'phases': {}}, open(os.path.join(out, 'incremental.json'), 'w'))
"""


class TrainTests(unittest.TestCase):
    """Every accepted task waiting to land lands in one train, checked once with main; a failure is resolved by
    attribution and bisection on both heavy slots, never task by task (train.py, notes/plan-landing-train.md)."""

    tearDown, heard = FinalizeTests.tearDown, FinalizeTests.heard
    train_checks, land_beside = LandingTests.train_checks, LandingTests.land_beside

    def setUp(self):
        LandingTests.setUp(self)
        self.w.write("tools/fake_check.py", FAKE_REPORTING_CHECK)
        self.w.git("add", "tools/fake_check.py")
        self.w.git("commit", "-q", "-m", "the check")
        self.checks = self.w.root / "checks.txt"
        self.env = dict(ORCH_TREES="1", CHECKS=str(self.checks),
                        ORCH_LANDING_CHECK="python3 -B tools/fake_check.py --output {output}")
        self.w.set_st(tasks={})

    def accepted(self, tid, documents=False):
        """Task `tid`, accepted in its own tree: a theory T<tid> and its ROOT line (or a document alone)."""
        self.w.task(tid)
        self.w.session(f"implement-{tid}", "implementer", f"k{tid}", task=tid, state="done", live=False)
        tasks = self.w.st()["tasks"]
        tasks[tid] = {"stage": "committing", "role": "implementer", "session": f"implement-{tid}", "verdict": "accept",
                      "summary": f"T{tid} is in."}
        self.w.set_st(tasks=tasks)
        path = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               f"print(v2.worktree({tid!r}))"], env=dict(self.w.env, **self.env), capture_output=True,
                              text=True).stdout.strip()
        tree = Path(path)
        if documents:
            (tree / f"NOTE{tid}.md").write_text(f"# Note {tid}\n")
            files = [f"NOTE{tid}.md"]
        else:
            (tree / f"theories/T{tid}.thy").write_text(f"theory T{tid} imports Base begin end\n")
            root = (tree / "ROOT").read_text()
            (tree / "ROOT").write_text(root + f"    T{tid}\n")
            files = ["ROOT", f"theories/T{tid}.thy"]
        self.w.write(f".build/tasks/{tid}/commit.md", f"Add T{tid}\n\nValidation: the check passes.\n")
        self.w.write(f".build/tasks/{tid}/finalize.json", json.dumps(
            {"check": "documents" if documents else "true", "files": files, "message": f".build/tasks/{tid}/commit.md"}))
        return tree

    def queued(self, *tids, env=None):
        """Their finalizers commit them on their branches and leave them queued (main is held by another landing)."""
        import fcntl
        with open(self.w.state / "landing.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            for tid in tids:
                code, _, err = self.w.run("finalize.py", "commit", tid, env=dict(self.env, ORCH_ISABELLE_WAIT="1",
                                                                                   **(env or {})))
                self.assertEqual(code, 0, err)
        queue = json.loads((self.w.state / "landing-queue.json").read_text())
        self.assertEqual(sorted(t for t, e in queue.items() if not e.get("decided")), sorted(tids))

    def land(self, env=None):
        code, _, err = self.w.run("finalize.py", "land-queue", env=dict(self.env, **(env or {})), timeout=120)
        self.assertEqual(code, 0, err)

    def ran(self):
        return [line.split()[0] for line in self.checks.read_text().splitlines()] if self.checks.exists() else []

    def side_by_side(self):
        """Whether two of the checks ran at once."""
        spans = [tuple(map(float, line.split()[1:])) for line in self.checks.read_text().splitlines()]
        return any(a[0] < b[1] and b[0] < a[1] for i, a in enumerate(spans) for b in spans[i + 1:])

    def stage(self, tid):
        return self.w.st()["tasks"][tid]["stage"]

    def test_accepted_tasks_waiting_land_together_after_one_check(self):
        for tid in ("3", "4", "5"):
            self.accepted(tid)
        self.land_beside()                                                 # main moved: the combination is checked
        self.queued("3", "4", "5")
        self.land()
        self.assertEqual(len(self.ran()), 1)                               # one check of the three with main
        self.assertEqual([self.stage(t) for t in ("3", "4", "5")], ["done"] * 3)
        root = (self.w.project / "ROOT").read_text()
        for name in ("Other", "T3", "T4", "T5"):
            self.assertIn(f"    {name}\n", root)
        log = self.w.git("log", "--format=%s")
        for tid in ("3", "4", "5"):
            self.assertIn(f"Take up the work of task {tid}", log)
        self.assertIn("Tasks 3, 4 and 5 landed together as", self.heard())
        self.assertIn("Validation: the harness's check of tasks 3, 4 and 5 together with main, exactly as it lands, "
                      "passed", self.w.git("log", "-1", "--format=%B"))
        self.assertIn("T4 is in.", self.heard())
        for tid in ("3", "4", "5"):
            self.assertFalse((self.w.project / ".build/trees" / tid).exists())  # each tree taken away

    def test_a_train_of_the_content_its_batch_checked_lands_on_the_batch_s_kept_build(self):
        # C10: the batches' proofs took a median 186 s and the trains' 216 s on 09-22's afternoon, nearly all of it the
        # same members' theories; a batch keeps its heap, and a train of exactly that content adopts it
        pointer = self.w.root / "active-context.json"
        base = self.w.project / ".build/bases/base-a/proof"
        base.mkdir(parents=True)
        pointer.write_text(json.dumps({"directory": str(base)}))
        out = ".build/bases/20260923-batch8-9"
        (self.w.project / out / "proof").mkdir(parents=True)
        (self.w.project / out / "incremental.json").write_text(json.dumps(
            {"status": "accepted", "base": str(base), "kept_context": str(self.w.project / out / "proof")}))
        self.w.write("HANDOFF.md", "the planner's state\n")
        self.w.git("add", "HANDOFF.md")
        self.w.git("commit", "-q", "-m", "the planner's state")
        code = f"""
import sys, json; sys.path.insert(0, {str(fakes.HERE)!r})
import v2, train, finalize as fz
v2.LANDING_CHECK = "python3 -B tools/no_such_tool/incremental_check.py check --output {{output}}"
fz.ADVANCE = True
train.record_build("HEAD", {out!r})
first = train.content_key("HEAD")
v2.git_out("commit", "-q", "--allow-empty", "-m", "nothing", quiet=True)
open({str(self.w.project / 'HANDOFF.md')!r}, "a").write("more of the planner's state\\n")
import subprocess
subprocess.run(["git", "-C", {str(self.w.project)!r}, "commit", "-q", "-am", "the planner's state again"])
same = train.content_key("HEAD") == first                        # the planner's state aside: the same content
plan = train.Plan(["8", "9"])
plan.head, plan.tree = v2.git_out("rev-parse", "HEAD").strip(), v2.PROJECT
train.check(plan, plan.head, {{"8": {{"head": plan.head}}, "9": {{"head": plan.head}}}})
print(json.dumps({{"same": same, "reused": plan.reused, "ok": plan.ok, "out": plan.out, "log": plan.log}}))
train.settle_pointer(plan.out, None)                              # the landing adopts the kept build as the base
open({str(pointer)!r}, "w").write(json.dumps({{"directory": "/another/base"}}))
print(json.dumps({{"moved": train.kept_build(plan.head)}}))      # on another base: none
open({str(pointer)!r}, "w").write(json.dumps({{"directory": {str(base)!r}}}))
open({str(self.w.project / 'theories/Base.thy')!r}, "a").write("(* changed *)\\n")
subprocess.run(["git", "-C", {str(self.w.project)!r}, "commit", "-q", "-am", "a theory changed"])
print(json.dumps({{"other": train.kept_build("HEAD"), "keeps": train.keeps_heap()}}))
"""
        said = subprocess.run([sys.executable, "-c", code], env=dict(self.w.env, **self.env, ORCH_ACTIVE_CONTEXT=str(pointer)),
                              capture_output=True, text=True, cwd=self.w.project)
        first, moved, second = [json.loads(line) for line in said.stdout.strip().splitlines()[-3:]]
        self.assertIsNone(moved["moved"])
        self.assertEqual((first["same"], first["reused"], first["ok"], first["out"]), (True, True, True, out), said.stderr)
        self.assertIsNone(second["other"])                                  # other content: checked as always
        self.assertTrue(second["keeps"])                                    # a batch of the repository's check keeps it
        log = (self.w.state / "v2.log").read_text()
        self.assertIn("lands on the build its check batch made", log)
        # adopted by the repository's checker (a stand-in's absence says which context it was to be)
        self.assertIn(f"could not be set to the check that landed ({self.w.project / out / 'proof'})", log)

    def test_a_member_whose_lines_conflict_leaves_the_train_and_the_others_land(self):
        self.w.write("NOTES.md", "one line\n")
        self.w.git("add", "NOTES.md")
        self.w.git("commit", "-q", "-m", "a shared file")
        for tid in ("3", "4", "5"):
            tree = self.accepted(tid)
            if tid != "3":
                (tree / "NOTES.md").write_text(f"one line, as task {tid} has it\n")
                spec = json.loads((self.w.project / f".build/tasks/{tid}/finalize.json").read_text())
                spec["files"].append("NOTES.md")
                self.w.write(f".build/tasks/{tid}/finalize.json", json.dumps(spec))
        self.queued("3", "4", "5")
        self.land()
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["done", "done"])
        self.assertNotEqual(self.stage("5"), "done")
        self.assertIn("NOTES.md", (self.w.project / ".build/tasks/5/finalized.json").read_text())
        self.assertTrue((self.w.project / ".build/tasks/5/merge/NOTES.md").exists())  # kept marked for its session
        self.assertEqual((self.w.project / "NOTES.md").read_text(), "one line, as task 4 has it\n")

    def test_a_failure_its_report_names_costs_one_check_more_and_the_others_land(self):
        for tid in ("3", "4", "5"):
            self.accepted(tid)
        self.land_beside()
        self.queued("3", "4", "5")
        self.land(env=dict(FAIL_WITH="T4"))
        self.assertEqual(len(self.ran()), 2, self.ran())                   # the whole, then what its report cleared
        self.assertEqual([self.stage(t) for t in ("3", "5")], ["done", "done"])
        self.assertEqual(self.stage("4"), "fixing")                        # its quick fix, in the tree that holds main
        self.assertIn("does not stand with what landed", self.w.st()["tasks"]["4"]["fix_text"])
        self.assertTrue((self.w.project / ".build/trees/4/theories/T5.thy").exists())
        self.assertIn("recipe r failed", (self.w.project / ".build/tasks/4/landing.log").read_text())
        self.assertIn("its report clears 3 and 5, checked again without task 4, which it finds",
                      (self.w.state / "v2.log").read_text())

    def test_a_failure_nothing_names_is_found_by_halves_never_member_by_member(self):
        for tid in ("3", "4", "5", "6"):
            self.accepted(tid)
        self.land_beside()
        self.queued("3", "4", "5", "6")
        self.land(env=dict(FAIL_TOGETHER="T6+Other", SLOW="1"))            # the report says nothing of who
        self.assertEqual([self.stage(t) for t in ("3", "4", "5")], ["done"] * 3)
        self.assertEqual(self.stage("6"), "fixing")
        self.assertLessEqual(len(self.ran()), 5, self.ran())               # the whole, then two halves a round
        self.assertIn("they are checked in halves", (self.w.state / "v2.log").read_text())
        self.assertTrue(self.side_by_side())                               # the halves on both heavy slots at once

    def test_two_that_each_stand_alone_but_not_together_land_the_first_and_fix_the_second(self):
        for tid in ("3", "4"):
            self.accepted(tid)
        self.land_beside()
        self.queued("3", "4")
        self.land(env=dict(FAIL_TOGETHER="T3+T4"))
        self.assertEqual(self.stage("3"), "done")
        self.assertEqual(self.stage("4"), "fixing")                        # it does not stand with what landed
        self.assertEqual(len(self.ran()), 4, self.ran())                   # whole, both halves, the second on the first

    def test_a_train_of_documents_takes_no_heavy_slot(self):
        for tid in ("3", "4"):
            self.accepted(tid, documents=True)
        self.w.write("tools/check.py", FAKE_CHECK)
        self.w.git("add", "tools/check.py")
        self.w.git("commit", "-q", "-m", "the source checks")
        self.queued("3", "4")
        self.land(env=dict(ORCH_ISABELLE_RUNS="2", ORCH_ISABELLE_WAIT="600"))  # the machine full the whole while
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["done", "done"])
        self.assertEqual(self.ran(), [])                                   # the repository's check never ran
        self.assertIn("its documents check passed", (self.w.state / "v2.log").read_text())

    def test_a_landing_whose_report_was_never_made_is_reported_by_the_watchdog(self):
        # task 151 landed at 15:30:23 on 2026-09-22 while its lander went on to the next train holding its report; its
        # finalizer had ended, and the watchdog sent a task that had landed to the planner
        self.accepted("3")
        tasks = self.w.st()["tasks"]
        tasks["3"]["finishing_since"] = time.time() - 7200
        self.w.set_st(tasks=tasks)
        (self.w.state / "landing-queue.json").write_text(json.dumps({"3": {
            "head": "x", "documents": False, "queued": time.time() - 900, "decided": time.time() - 600, "code": 0,
            "what": "landed", "ref": "abc1234"}}))
        self.w.run("watchdog.py", env=self.env)
        self.assertEqual(self.stage("3"), "done")
        self.assertIn("task 3 landed as abc1234; its report was never made", (self.w.state / "v2.log").read_text())
        self.assertNotIn("ended without reporting", self.heard())

    def test_a_train_that_waited_for_the_one_tree_is_not_checked_again(self):
        # what stood uncommitted over its files went away without a commit: main is where it was, and so is the check
        for tid in ("3", "4"):
            self.accepted(tid)
        self.queued("3", "4")
        mark = self.w.root / "started"
        check = (f"sh -c 'python3 -B tools/fake_check.py {{output}} && if [ ! -e {mark} ]; then touch {mark}; "
                 f"echo draft > {self.w.project}/theories/T3.thy; fi'")

        def withdrawn():                                                  # the one tree's draft goes away again
            for _ in range(300):
                if mark.exists():
                    time.sleep(1)
                    (self.w.project / "theories/T3.thy").unlink()
                    return
                time.sleep(0.05)
        away = threading.Thread(target=withdrawn)
        away.start()
        self.land(env=dict(ORCH_LANDING_CHECK=check))
        away.join()
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["done", "done"])
        self.assertEqual(len(self.ran()), 1, self.ran())                   # checked once, whatever the wait
        self.assertIn("waits for what stands uncommitted in the one tree", (self.w.state / "v2.log").read_text())

    def test_a_train_the_proof_base_refuses_stays_queued_and_nobody_is_found(self):
        for tid in ("3", "4"):
            self.accepted(tid)
        self.land_beside()
        self.queued("3", "4")
        refused = self.w.root / "refused"
        refused.write_text("")
        check = (f"sh -c 'if [ -e {refused} ]; then echo \"AssertionError: Accepted heap/database changed.\"; exit 1; "
                 "fi; python3 -B tools/fake_check.py {output}'")
        self.land(env=dict(ORCH_LANDING_CHECK=check, ORCH_ISABELLE_WAIT="2", ORCH_BASE_RETRY="1"))
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["committing", "committing"])  # nobody sent to a fix
        queue = json.loads((self.w.state / "landing-queue.json").read_text())
        self.assertFalse(any(queue[t].get("decided") for t in ("3", "4")))
        self.assertIn("refused a combined check before it began", (self.w.state / "v2.log").read_text())
        refused.unlink()
        self.land(env=dict(ORCH_LANDING_CHECK=check))
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["done", "done"])

    def test_main_moved_by_the_owner_during_the_check_is_brought_in_and_checked(self):
        for tid in ("3", "4"):
            self.accepted(tid)
        self.queued("3", "4")
        self.land(env=dict(MOVE_MAIN=str(self.w.root / "moved")))
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["done", "done"])
        self.assertEqual(len(self.ran()), 2, self.ran())                   # checked again on what the owner committed
        self.assertIn("the owner", self.w.git("log", "--format=%s"))
        self.assertTrue((self.w.project / "OWNER.md").exists())
        self.assertNotIn("ATTENTION", (self.w.state / "v2.log").read_text())  # seen as moved, not met at the merge


class BatchTests(unittest.TestCase):
    """The repository's check of every task waiting for one, run once for all (train.Batch, notes/plan-landing-train.md
    1b): sessions ask for it (v2.py check) and are parked, finalizers' hand-overs join it, a failure goes to its own."""

    tearDown, heard = FinalizeTests.tearDown, FinalizeTests.heard

    def setUp(self):
        TrainTests.setUp(self)
        self.env.update(ORCH_BATCHES="1")

    ran, stage, side_by_side = TrainTests.ran, TrainTests.stage, TrainTests.side_by_side

    def working(self, tid):
        """Task `tid` under way in its own tree: a theory T<tid> and its ROOT line, uncommitted."""
        self.w.task(tid)
        self.w.session(f"implement-{tid}", "implementer", f"k{tid}", task=tid, state="working")
        tasks = self.w.st()["tasks"]
        tasks[tid] = {"stage": "running", "role": "implementer", "session": f"implement-{tid}"}
        self.w.set_st(tasks=tasks)
        path = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               f"print(v2.worktree({tid!r}))"], env=dict(self.w.env, **self.env), capture_output=True,
                              text=True).stdout.strip()
        tree = Path(path)
        (tree / f"theories/T{tid}.thy").write_text(f"theory T{tid} imports Base begin end\n")
        (tree / "ROOT").write_text((tree / "ROOT").read_text() + f"    T{tid}\n")
        self.w.write(f".build/tasks/{tid}/commit.md", f"Add T{tid}\n\nValidation: the check passes.\n")
        return tree

    def asked(self, *tids):
        """Their sessions ask for the check while a batch is running, and wait for the next."""
        import fcntl
        with open(self.w.state / "batcher.pid.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            for tid in tids:
                said = self.w.v2("check", env=dict(self.env, ORCH_ISABELLE_WAIT="1", **self.w.as_session(f"k{tid}")))
                self.assertIn("queued", said)
        for tid in tids:
            self.assertEqual(self.stage(tid), "parked")

    def batch(self, env=None):
        code, _, err = self.w.run("finalize.py", "check-batch", env=dict(self.env, **(env or {})), timeout=120)
        self.assertEqual(code, 0, err)

    def resumed(self, tid):
        return " ".join(c["args"][-1] for c in self.w.calls("--resume") if f"implement-{tid}" in json.dumps(c)) + \
            " ".join(c["args"][-1] for c in self.w.calls("-p") if f"k{tid}" in json.dumps(c))

    def handed_over(self, tid, **env):
        """Its session hands over, as _finishing.md has it: the repository's check, its files, its result."""
        as_ = dict(self.env, **env, **self.w.as_session(f"k{tid}"))
        said = self.w.v2("finalize", tid, "--check", f"python3 -B tools/incremental_check.py check --output "
                         f".build/tasks/{tid}/check", "--files", "ROOT", f"theories/T{tid}.thy", "--message",
                         f".build/tasks/{tid}/commit.md", env=as_)
        self.assertIn("prepared", said)
        self.w.write(f".build/tasks/{tid}/result.md", fakes.RESULT.format(status="done"))
        self.assertIn("recorded", self.w.v2("result", tid, env=as_))

    def test_the_checks_tasks_ask_for_are_run_once_for_all(self):
        for tid in ("3", "4"):
            self.working(tid)
        self.asked("3", "4")
        self.batch()
        self.assertEqual(len(self.ran()), 1)                               # one check of both with main
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["running", "running"])  # resumed with the result
        resumes = " ".join(" ".join(c["args"]) for c in self.w.calls())
        self.assertIn("passed", resumes)
        queue = json.loads((self.w.state / "check-queue.json").read_text())
        self.assertEqual({t: queue[t]["what"] for t in ("3", "4")}, {"3": "passed", "4": "passed"})
        self.assertIn("with main and the work of task 4 passed", queue["3"]["text"])

    def test_a_failure_goes_to_its_own_task_and_the_others_pass(self):
        for tid in ("3", "4", "5"):
            self.working(tid)
        self.asked("3", "4", "5")
        self.batch(env=dict(FAIL_WITH="T4"))
        self.assertEqual(len(self.ran()), 2, self.ran())                   # the whole, then what its report cleared
        queue = json.loads((self.w.state / "check-queue.json").read_text())
        self.assertEqual({t: queue[t]["what"] for t in ("3", "4", "5")}, {"3": "passed", "4": "failed", "5": "passed"})
        self.assertIn("recipe r failed", queue["4"]["text"])
        # found by the report, it is told at once, not after the check of what the report cleared
        self.assertLess(queue["4"]["decided"], min(queue["3"]["decided"], queue["5"]["decided"]))

    def test_a_half_found_alone_is_told_when_its_own_check_ends(self):
        # task 223's half failed at 18:48:44 and was told nothing until task 227's half beside it ended, twenty minutes
        # on (2026-09-22)
        for tid in ("3", "4"):
            self.working(tid)
        self.asked("3", "4")
        self.batch(env=dict(FAIL_TOGETHER="T4+T4", SLOW_WITH="T3:4,T4:1"))  # the whole fails naming nobody: halves
        queue = json.loads((self.w.state / "check-queue.json").read_text())
        self.assertEqual({t: queue[t]["what"] for t in ("3", "4")}, {"3": "passed", "4": "failed"})
        spans = [line.split() for line in self.checks.read_text().splitlines()]
        self.assertTrue(self.side_by_side())                               # the halves, each on a heavy slot
        three = next(float(end) for out, _, end in spans if out.endswith("-batch3"))
        self.assertLess(queue["4"]["decided"], three)                      # told before the half beside it ended

    def test_a_failure_s_text_lists_every_error_its_check_reported(self):
        # the repository's check logs one JSON line naming the proof's build.log; task 153 was told that line, cut at
        # 300 characters, and not one of its errors (2026-09-22 15:46)
        for tid in ("3", "4", "5"):
            self.working(tid)
        self.asked("3", "4", "5")
        self.batch(env=dict(FAIL_PROOF="T4"))
        queue = json.loads((self.w.state / "check-queue.json").read_text())
        self.assertEqual({t: queue[t]["what"] for t in ("3", "4", "5")}, {"3": "passed", "4": "failed", "5": "passed"})
        self.assertIn("[this check reported 4 errors", queue["4"]["text"])
        for n in (3, 7, 11):
            self.assertIn(f"- T4.thy:{n}: Failed to finish proof", queue["4"]["text"])

    def test_a_tree_its_session_had_checked_is_handed_over_and_not_checked_again(self):
        self.working("3")
        self.asked("3")
        self.batch()
        self.assertEqual(len(self.ran()), 1)
        tasks = self.w.st()["tasks"]
        tasks["3"] = {"stage": "running", "role": "implementer", "session": "implement-3"}
        self.w.set_st(tasks=tasks)
        self.handed_over("3")
        self.assertEqual(self.stage("3"), "reviewing")                     # passed: the tree its check passed on
        self.assertEqual(len(self.ran()), 1)                               # and not run again
        self.assertIn("not run again", (self.w.project / ".build/tasks/3/finalize.log").read_text())

    def test_hand_overs_waiting_are_checked_together_and_go_to_their_reviews(self):
        import fcntl
        for tid in ("3", "4"):
            tree = self.working(tid)
        tree3 = tree.parent / "3"
        probe = self.w.project / ".build/tasks/3/probe"                # its session's probe of T3 as its tree holds it
        (probe / "theories").mkdir(parents=True)
        (probe / "theories/T3.thy").write_text((tree3 / "theories/T3.thy").read_text())
        (probe / "probe.ML").write_text(f'val _ = Thy_Info.use_thy_legacy "{probe}/theories/T3";\n')
        (probe / "probe.log").write_text("### theory \"Draft.T3\"\nPROBE THEORIES LOADED\n")
        with open(self.w.state / "batcher.pid.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            for tid in ("3", "4"):
                self.handed_over(tid, ORCH_ISABELLE_WAIT="1")
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["checking", "checking"])
        self.w.run("watchdog.py", env=self.env)                           # nobody checks them: a batcher starts
        self.assertIn("nobody checks it: a batcher starts", (self.w.state / "v2.log").read_text())
        self.assertEqual(len(self.ran()), 1)
        self.assertEqual([self.stage(t) for t in ("3", "4")], ["reviewing", "reviewing"])
        self.assertIn("check of task 3: passed (with task 4)", (self.w.state / "v2.log").read_text())
        # accepted, it is committed with what the harness's check found, beside its session's words (task 181's review
        # asked a session for an outcome it could not know when it wrote its message, 2026-09-22 15:25)
        tasks = self.w.st()["tasks"]
        tasks["3"].update(stage="committing", verdict="accept")
        self.w.set_st(tasks=tasks)
        code, _, err = self.w.run("finalize.py", "commit", "3", env=self.env)
        self.assertEqual(code, 0, err)
        message = self.w.git("log", "--format=%B", "-n", "1", "--grep", "Add T3", "--all")
        self.assertIn("Validation: the check passes.", message)                   # the session's words, kept
        self.assertIn("Checked by the harness: the repository's check of this work with main and the work of task 4 "
                      "passed", message)
        # and what its session verified by probing, as the harness keeps the runs, rather than narrated
        self.assertIn("Probed in its session, as the harness keeps the runs: T3, as the tree holds it, to the "
                      "completion marker with no error (1 run).", message)


if __name__ == "__main__":
    unittest.main()



class AdmissionTests(unittest.TestCase):
    """Three finalizers started in one second on 2026-09-21: each counted the Isabelle processes, found none started
    yet, and three checks ran against a limit of two. One decides at a time, and a run it is let start counts as
    running until its finalizer ends."""

    def setUp(self):
        from unittest.mock import patch
        import tempfile
        import finalize
        import v2
        self.temp = tempfile.TemporaryDirectory()
        state = Path(self.temp.name)
        self.finalize = finalize
        self.patches = [patch.object(v2, "STATE", str(state)), patch.object(v2, "ADMITTED", str(state / "admitted")),
                        patch.object(v2, "MACHINE_WAIT", str(state / "machine-wait")),
                        patch.object(v2, "MACHINE_TURN", str(state / "machine-turn")),
                        patch.object(v2, "ISABELLE_MAX", 2), patch.object(finalize, "POLL", 0.05),
                        patch.dict(os.environ, {"ORCH_ISABELLE_RUNS": "1",  # one run already going
                                                "ORCH_MEM_AVAILABLE_GB": "1000"})]  # and memory enough
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.temp.cleanup()

    def waited(self, tid):
        start = time.time()
        self.finalize.wait_for_isabelle(tid, False, end=start + 0.5)
        return time.time() - start

    def test_a_run_let_start_counts_until_its_finalizer_ends(self):
        self.assertLess(self.waited("22"), 0.2)     # one running, one free: 22 starts at once
        self.assertGreaterEqual(self.waited("46"), 0.5)  # 22's run counts though its Isabelle is not up: 46 waits
        self.finalize.admitted_no_more("22")
        self.finalize.admitted_no_more("46")
        self.assertLess(self.waited("50"), 0.2)     # both ended: 50 starts at once

    def test_the_machine_goes_in_the_planner_s_order_finalizers_included(self):
        # the owner, 2026-09-22: a finalizer took a freed heavy slot within a poll while a task parked for the machine
        # waited for a dispatch to resume it — task 94 waited two hours behind landings
        import v2
        state = Path(v2.STATE)
        write = lambda tasks, sessions={}: (state / "v2.json").write_text(json.dumps(
            {"queue": ["1", "22"], "tasks": tasks, "sessions": sessions}))
        with patch.dict(os.environ, {"ORCH_ISABELLE_RUNS": "0"}):
            write({})
            v2.machine_waiting("1")                             # task 1's finalizer, ahead in the queue, waits
            self.assertGreaterEqual(self.waited("22"), 0.5)  # 22 waits behind it
            v2.machine_waiting("1", waiting=False)
            self.assertLess(self.waited("22"), 0.2)          # 1 waits no more: 22 goes
            self.finalize.admitted_no_more("22")
            parked = {"1": {"stage": "parked", "parked": {"for": "machine", "run": "heavy", "since": time.time()}}}
            write(parked)                                    # task 1 parked for the machine, a slot free to resume it
            self.assertGreaterEqual(self.waited("22"), 0.5)
            busy = {f"w{i}": {"role": "implementer", "state": "working"} for i in range(v2.WORKERS_MAX)}
            write(parked, busy)                              # no slot could resume it: it holds nothing up
            self.assertLess(self.waited("22"), 0.2)
            self.finalize.admitted_no_more("22")
            v2.machine_turn("1")                             # resumed for the machine: its turn is held
            self.assertGreaterEqual(self.waited("22"), 0.5)
            self.finalize.admitted_no_more("22")
            v2.admit_session("implement-1", "1")             # until its check is let start (a run now, one of two)
            self.assertLess(self.waited("22"), 0.2)

    def test_a_check_waits_for_memory(self):
        with patch.dict(os.environ, {"ORCH_ISABELLE_RUNS": "0", "ORCH_MEM_AVAILABLE_GB": "1"}):
            self.assertGreaterEqual(self.waited("22"), 0.5)                       # no heavy run, but memory short

    def test_probes_do_not_hold_a_check_and_hold_one_that_advances_the_base(self):
        # a probe is not a heavy run (v2.PROBE_MAX): a check waits only for a heavy slot; a check that advances the base
        # replaces the heap under every probe, and waits for no run at all
        with patch.dict(os.environ, {"ORCH_ISABELLE_RUNS": "0", "ORCH_PROBE_RUNS": "8"}):
            self.assertLess(self.waited("22"), 0.2)
            self.finalize.admitted_no_more("22")
            start = time.time()
            self.finalize.wait_for_isabelle("46", True, end=start + 0.5)
            self.assertGreaterEqual(time.time() - start, 0.5)
