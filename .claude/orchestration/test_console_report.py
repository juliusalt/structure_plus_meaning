#!/usr/bin/env python3
"""The run's data aggregator (console_report.py): the console's figures and everything the run produced, as text to
monitor a live run by — each extraction checked over a world whose records say what the answer must be."""
import json
import os
import subprocess
import sys
import time
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402


def stamp(epoch):
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(epoch))


class ReportTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.base()
        self.w.kb()
        self.t0 = int(time.time()) - 3600
        self.w.env["TMPDIR"] = str(self.w.root)
        self.w.set_st(active=True)

    def tearDown(self):
        self.w.close()

    def log(self, *lines):
        """v2.log's lines, each (seconds after t0, text)."""
        with open(self.w.state / "v2.log", "a") as f:
            for at, text in lines:
                f.write(f"{stamp(self.t0 + at)} {text}\n")

    def run_report(self, *args):
        done = subprocess.run([sys.executable, "-B", str(HERE / "console_report.py"), *args], capture_output=True,
                              text=True, timeout=120, env=self.w.env, cwd=self.w.project)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout

    def stopped_call(self, name, sid, text, started):
        """A session whose one call the guard stopped with `text`."""
        self.w.session(name, "implementer" if name.startswith("implement") else "fixer", sid, state="done", live=False,
                       started=started, task=name.split("-")[1])
        self.w.transcript(sid, [
            fakes.assistant("m1", fakes.iso(started + 5), [{"type": "tool_use", "id": "a", "name": "Bash",
                                                             "input": {"command": "sleep 60"}}]),
            {"type": "user", "timestamp": fakes.iso(started + 6), "message": {"content": [
                {"type": "tool_result", "tool_use_id": "a", "content": text, "is_error": True}]}}])

    def test_a_check_is_counted_once_and_a_task_fails_by_its_own_verdict(self):
        # each check was said twice — the batch's line, and the line telling the session its verdict — and counted twice
        self.log((10, "the work of task 5 is checked together with main (python3 -B tools/incremental_check.py check)"),
                 (100, "the check of task 5: failed in 90 s"), (100, "the check task 5's session asked for: failed"),
                 (100, "check of task 5: failed"),
                 (200, "the work of tasks 5 and 6 is checked together with main (python3 -B tools/incremental_check.py check)"),
                 (300, "the check of tasks 5 and 6: failed in 100 s"),
                 (300, "the batch of tasks 5 and 6 failed its check: its report clears 6, checked again without task 5"),
                 (300, "check of task 5: failed"), (300, "check of task 6: passed (with task 5)"))
        checks = self.run_report("checks", "--since", "all")
        self.assertIn("runs in the window: 2 (batch failed 2)", checks)
        self.assertIn("verdicts per task: failed 2, passed 1", checks)
        self.assertIn("the batch of tasks 5 and 6 failed its check: its report clears 6", checks)
        self.assertIn("task 5's check failed 2× in the window", self.run_report("findings", "checks", "--since", "all"))

    def test_lost_sessions_say_what_is_known_of_them(self):
        self.w.session("fix-8", "fixer", "", state="lost", live=False, task="8", started=self.t0)
        self.log((5, "start of fix-8 not confirmed"))
        self.w.session("fix-9", "fixer", "gone9", state="lost", live=False, task="9", started=self.t0)
        self.w.session("fix-10", "fixer", "s10", state="lost", live=False, task="10", started=self.t0,
                       lost_why="outgrew its quick fix's budget")
        self.w.transcript("s10", [fakes.assistant("m1", fakes.iso(self.t0 + 5), [{"type": "text", "text": "Working."}],
                                                  usage={"cache_read_input_tokens": 500000, "output_tokens": 900})])
        # a session given up says why, in its record, from the moment it is (watchdog.lost)
        self.w.session("fix-11", "fixer", "s11", task="11", started=self.t0)
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(HERE)!r}); import watchdog; "
                        "watchdog.lost('fix-11', 'outgrew its window')"], env=self.w.env, capture_output=True, timeout=60)
        self.assertEqual(self.w.st()["sessions"]["fix-11"]["lost_why"], "outgrew its window")
        found = self.run_report("findings", "--since", "all")
        self.assertIn("never started: their start was not confirmed: fix-8", found)
        self.assertIn("lost, their transcripts gone: fix-9", found)
        self.assertIn("fix-10 (fixer, task 10) lost after 1 requests", found)
        self.assertIn("outgrew its quick fix's budget", found)
        self.assertNotIn("after 0 requests", found)                      # unknown is not none

    def test_a_parked_session_stands_and_is_not_ended(self):
        self.w.session("implement-12", "implementer", "s12", state="parked", live=False, task="12", started=self.t0)
        self.w.session("implement-13", "implementer", "s13", state="done", live=False, task="13", started=self.t0,
                       released=True)
        out = self.run_report("report", "--only", "sessions", "--since", "all", "--quick")
        standing, ended = out.split("  standing:")[1].split("ended in the window")
        self.assertIn("implement-12", standing)
        self.assertNotIn("implement-12", ended)
        self.assertIn("implement-13", ended)

    def test_the_tasks_time_is_told_by_stage_and_by_what_it_waited_for(self):
        self.w.task("7")
        self.log((0, "started implement-7 (implementer, from high)"), (600, "result of task 7: done"),
                 (610, "task 7's check waits for the next batch"),
                 (900, "the work of task 7 is checked together with main (python3 -B tools/incremental_check.py check)"),
                 (1200, "the check of task 7: passed in 300 s"), (1260, "started review-7 (reviewer, from xhigh)"),
                 (1500, "task 7 is committed on its branch and waits to land with the next train"),
                 (1800, "the train of tasks 7 is checked together with main (python3 -B tools/incremental_check.py check)"),
                 (2100, "the train of tasks 7 landed as abcdef12"))
        self.w.task("7", status="completed")
        out = self.run_report("waits", "--since", "all")
        self.assertIn("landed 1", out)
        for stage, spent in (("working", "10m"), ("check queue", "4m"), ("checking", "5m"), ("review", "4m"),
                             ("landing queue", "5m"), ("landing check", "5m")):
            self.assertRegex(out, rf"{stage}\s+{spent}")
        self.assertRegex(out, r"result, awaiting its check\s+10s\s+\d+%\s+waiting")

    def test_a_guard_stop_across_sessions_is_one_finding_opened_by_its_id(self):
        for i, name in enumerate(("implement-20", "fix-21", "implement-22")):
            self.stopped_call(name, f"s2{i}", "Waiting is refused (sleep, wait loops, tail -f): a background job's "
                              "completion notifies you.", self.t0 + 60 * i)
        found = self.run_report("findings", "delivery", "--since", "all")
        self.assertIn("3 call(s) stopped by the guard in 3 session(s) (implementer 2, fixer 1): Waiting is refused", found)
        gid = found.split("console_report.py delivery ")[1].split()[0]
        whole = self.run_report("delivery", gid, "--since", "all")
        for name, role in (("implement-20", "implementer"), ("fix-21", "fixer"), ("implement-22", "implementer")):
            self.assertIn(f"{name}#1 ({role}; `session {name} --from 1 --to 1 --full`)", whole)

    def test_a_pass_says_only_what_changed_since_the_last(self):
        self.w.task("30")
        self.w.set_st(tasks={"30": {"stage": "ready", "kind": "build"}}, queue=["30"])
        self.log((100, "the planner edited the graph: 1 operation(s)"))
        first = self.run_report("changes", "--since", "all")
        self.assertIn("conditions:", first)
        self.assertIn("the planner edited the graph", first)
        self.assertTrue((self.w.root / "console-report.last.json").exists())
        again = self.run_report("changes")
        self.assertIn("conditions: 0 new", again)                         # nothing said twice
        self.assertNotIn("the planner edited the graph", again)
        self.assertIn("tasks: 0 moved", again)
        st = self.w.st()
        st["tasks"]["30"] = {"stage": "parked", "kind": "build", "parked": {"since": time.time() - 4 * 3600, "for": "probe"}}
        (self.w.state / "v2.json").write_text(json.dumps(st))
        time.sleep(1.1)                                                   # a line after the last pass
        self.log((int(time.time()) - self.t0, "task 30's probe waits for room on the machine: it runs as soon as there "
                                              "is, and its session is parked"))
        moved = self.run_report("changes")
        self.assertIn("NEW", moved)
        self.assertIn("#30 parked for probe", moved)                     # overdue past its hold
        self.assertIn("#30: ready → parked", moved)
        self.assertIn("task 30's probe waits for room", moved)
        # a look at the whole moves no marker: the next pass still starts where the last pass ended
        mark = json.loads((self.w.root / "console-report.last.json").read_text())["at"]
        self.run_report("report", "--since", "all", "--quick", "--only", "run")
        self.assertEqual(json.loads((self.w.root / "console-report.last.json").read_text())["at"], mark)

    def test_every_product_of_the_run_can_be_opened(self):
        self.w.task("40", subject="The product")
        (self.w.project / ".build" / "tasks" / "40").mkdir(parents=True)
        (self.w.project / ".build" / "tasks" / "40" / "review.md").write_text("Verdict: accept\n\nA finding.\n")
        self.w.session("implement-40", "implementer", "s40", state="done", live=False, task="40", started=self.t0)
        self.w.transcript("s40", [
            fakes.assistant("m1", fakes.iso(self.t0 + 5), [{"type": "tool_use", "id": "a", "name": "Bash",
                                                             "input": {"command": "v2.py result 40"}}]),
            {"type": "user", "timestamp": fakes.iso(self.t0 + 6), "message": {"content": [
                {"type": "tool_result", "tool_use_id": "a", "content": "refused: the result has no `Acceptance` part"}]}}])
        session = self.run_report("session", "implement-40", "--full")
        self.assertIn("REFUSED Bash: v2.py result 40", session)
        self.assertIn("refused: the result has no `Acceptance` part", session)
        task = self.run_report("task", "40")
        self.assertIn("== TASK #40", task)
        self.assertIn("review.md", task)
        self.assertIn("implement-40", task)
        self.assertIn("A finding.", self.run_report("task", "40", "--file", "review.md"))
        (self.w.project / "outside.txt").write_text("not the task's")
        self.assertIn("no file", self.run_report("task", "40", "--file", "../../../outside.txt"))
        self.assertIn('"name": "implement-40"', self.run_report("record", "session", "implement-40"))
        self.assertIn("no file", self.run_report("file", "/etc/passwd"))
        self.log((10, "the train of tasks 40 landed as 12345678"))
        self.assertIn("landed as 12345678", self.run_report("log", "--grep", "landed", "--since", "all"))
        inventory = self.run_report("inventory", "--since", "all")
        for part in ("sessions", "task folders", "#40: review.md", "logs"):
            self.assertIn(part, inventory)

    def test_the_costs_are_said_in_a_window_with_no_requests(self):
        # the line with the requests and the cache's share vanished whole in a window with no input tokens
        out = self.run_report("report", "--only", "costs", "--since", "1m", "--quick")
        self.assertIn("sessions 0 · requests 0 · a request —", out)

    def test_errors_are_grouped_and_a_traceback_said_by_its_exception(self):
        with open(self.w.state / "warm.log", "a") as f:
            f.write(f"{stamp(self.t0 + 5)} warm high: Traceback (most recent call last):\n"
                    '  File "x.py", line 1, in <module>\nKeyError: \'sessionId\'\n')
        self.log((5, "ATTENTION mail to fix-3 reached nobody (lost): an answer"),
                 (6, "ATTENTION mail to fix-4 reached nobody (lost): an answer"))
        out = self.run_report("errors", "--since", "all")
        self.assertIn("warm high: Traceback (most recent call last): … KeyError: 'sessionId'", out)
        self.assertIn("v2.log ×2: ATTENTION mail to fix-N reached nobody", out)


if __name__ == "__main__":
    unittest.main()
