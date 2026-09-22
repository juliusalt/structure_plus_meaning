"""The context gauge, mail and turn control by role (ctx_gauge.py), run as the hooks run in a throwaway world."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ctx_gauge  # noqa: E402
import fakes  # noqa: E402
from fakes import assistant  # noqa: E402


class GaugeTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.kb()
        self.w.session("plan-1", "planner", "p1", origin="kb-1", settings="planner-settings.json")
        self.w.session("implement-4", "implementer", "w4", task="4")
        self.w.session("review-3", "reviewer", "r3", task="3", origin="xhigh")
        self.w.session("kb-2", "kb", "k2")

    def tearDown(self):
        self.w.close()

    def at(self, sid, tokens):
        """The session's transcript, its latest request carrying `tokens`."""
        return self.w.transcript(sid, [assistant("m1", fakes.iso(time.time()), usage={
            "input_tokens": 2, "cache_read_input_tokens": tokens - 1002, "cache_creation_input_tokens": 1000,
            "output_tokens": 0})])

    def gauge(self, sid, tokens=100_000, tool="Bash"):
        hook = {"session_id": sid, "tool_name": tool, "tool_input": {"command": "true"}, "tool_response": {"stdout": ""},
                "transcript_path": self.at(sid, tokens), "hook_event_name": "PostToolUse", "cwd": str(self.w.project)}
        code, out, err = self.w.hook("ctx_gauge.py", "gauge", hook)
        self.assertEqual((code, err), (0, ""))
        return out["hookSpecificOutput"]["additionalContext"] if out else ""

    def stop(self, sid, records=()):
        """The Stop hook's reason, or None; `records` are added to the session's transcript after its latest request."""
        path = self.at(sid, 100_000)
        with open(path, "a") as f:
            f.write("".join(json.dumps(r) + "\n" for r in records))
        code, out, err = self.w.hook("ctx_gauge.py", "stop", {"session_id": sid, "hook_event_name": "Stop",
                                                             "transcript_path": path})
        self.assertEqual((code, err), (0, ""))
        return out["reason"] if out else None

    def set_session(self, name, **fields):
        st = self.w.st()
        st["sessions"][name].update(fields)
        (self.w.state / "v2.json").write_text(json.dumps(st))

    def post(self, name, text):
        (self.w.state / "mail").mkdir(exist_ok=True)
        with open(self.w.state / "mail" / f"{name}.jsonl", "a") as f:
            f.write(json.dumps({"from": "the planner", "text": text, "at": "t"}) + "\n")

    def test_a_producing_session_whose_work_was_taken_on_may_end_its_turn(self):
        # `v2.py result` answers "End your turn now" and this hook blocked it, while ask, escalate and park each
        # refuse a session the harness treats as closed: fix-49.2 sat in that loop on 2026-09-20, recording its
        # result twice, because the record saying it was done had gone into a worktree's parallel state. The task's
        # stage is the second witness, so the way out does not rest on one piece of bookkeeping.
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        said = self.stop("w4")
        # what it is told is what may_end applies to it: a park, and not a question of its own
        self.assertIn("Your turn ends with your result recorded, or once you have parked", said)
        self.assertIn("v2.py park run", said)
        self.assertNotIn("or while you wait on a question of your own", said)
        for stage in ("checking", "reviewing", "committing", "done", "planner"):
            self.w.set_st(tasks={"4": {"stage": stage, "session": "implement-4"}})
            self.assertIsNone(self.stop("w4"), f"still blocked at stage {stage}")
        # a supporting session is told the rule that holds for it: its turn does end while its question is open
        said = self.stop("r3")
        self.assertIn("or while you wait on a question of your own", said)
        self.assertIn("v2.py verdict 3 accept|reject", said)

    def test_a_reviewer_whose_run_the_machine_refused_may_end_its_turn_while_it_is_full(self):
        (self.w.state / "work-r3.json").write_text(json.dumps({"run_refused": "heavy"}))
        self.w.env["ORCH_ISABELLE_RUNS"] = str(ctx_gauge.v2.ISABELLE_MAX)
        self.assertIsNone(self.stop("r3"))                     # the watchdog wakes it when a run may start
        self.w.env["ORCH_ISABELLE_RUNS"] = "0"
        self.assertIn("v2.py verdict 3 accept|reject", self.stop("r3"))  # a run may start: it goes on

    def test_a_turn_that_cannot_end_at_all_is_named_once_it_says_a_loop(self):
        # fix-49.2 turned for as long as the owner let it on 2026-09-20: its Stop hook blocked it and every way out
        # was refused. The hard mark is the backstop, a whole window of requests away, and a session that calls no
        # tool between its turns never reaches it. Nothing said anything while it went round.
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        for _ in range(ctx_gauge.BLOCK_LOOP - 1):
            self.assertIsNotNone(self.stop("w4"))
        log = self.w.state / "v2.log"
        self.assertNotIn("turns in a row", log.read_text() if log.exists() else "")  # not for an ordinary block
        self.assertIsNotNone(self.stop("w4"))
        self.assertIn(f"implement-4 (implementer on task 4) has been told to continue {ctx_gauge.BLOCK_LOOP} turns "
                      "in a row: its turn cannot end", (self.w.state / "v2.log").read_text())
        # a turn that does end clears the count: the next block starts again from one
        self.w.set_st(tasks={"4": {"stage": "done", "session": "implement-4"}})
        self.assertIsNone(self.stop("w4"))
        self.assertFalse((self.w.state / "flags" / "w4.blocks").exists())

    def test_the_notice_comes_once_near_the_end_by_role_and_the_hard_mark_after(self):
        self.assertNotIn("near the end", self.gauge("p1", ctx_gauge.SOFT - 5000))
        text = self.gauge("p1", ctx_gauge.SOFT + 1000)
        self.assertIn("write HANDOFF.md as the planner's state, the events you have not handled under `## Now`", text)
        self.assertIn("v2.py planned --notes", text)
        self.assertNotIn("near the end", self.gauge("p1", ctx_gauge.SOFT + 2000))  # once
        self.assertIn(".build/tasks/4/result.md", self.gauge("w4", ctx_gauge.SOFT + 1000))
        self.assertIn("v2.py verdict 3 accept|reject", self.gauge("r3", ctx_gauge.SOFT + 1000))
        self.assertFalse((self.w.state / "flags/w4.hard").exists())
        self.gauge("w4", ctx_gauge.HARD + 1000)
        self.assertTrue((self.w.state / "flags/w4.hard").exists())

    def test_what_reaches_the_model_is_counted_and_not_what_the_transcript_keeps_beside_it(self):
        # plan-40 was told "Context is at 948K tokens" at 652K (2026-09-22 09:48): its call ended before its request was
        # recorded, and the task list's reminder after the one before counted whole — 744K characters, of which the
        # model is given one line a task
        usage = {"input_tokens": 2, "cache_read_input_tokens": 623_609, "cache_creation_input_tokens": 1000,
                 "output_tokens": 20_000}
        tasks = [{"id": str(i), "subject": f"Task {i}", "description": "x" * 5000, "status": "pending"} for i in range(137)]
        hook_said = {"type": "hook_success", "hookEvent": "PreToolUse", "hookName": "PreToolUse:Bash",
                     "stdout": json.dumps({"updatedInput": {"command": "y" * 60_000}})}
        path = self.w.transcript("p1", [assistant("m1", fakes.iso(time.time()), usage=usage),
                                        {"type": "attachment", "attachment": {"type": "task_reminder", "content": tasks}},
                                        {"type": "attachment", "attachment": hook_said}])
        self.assertLess(ctx_gauge.next_request_tokens(path, "Bash", {"stdout": ""}), 660_000)
        hook = {"session_id": "p1", "tool_name": "Bash", "tool_input": {"command": "true"}, "tool_response": {"stdout": ""},
                "transcript_path": path, "hook_event_name": "PostToolUse", "cwd": str(self.w.project)}
        code, out, err = self.w.hook("ctx_gauge.py", "gauge", hook)
        self.assertNotIn("near the end of your window", json.dumps(out or {}))
        # what does reach it is counted: a hook's additional context, a tool's result
        said = {"type": "hook_additional_context", "content": ["z" * 700_000]}
        path = self.w.transcript("p1", [assistant("m1", fakes.iso(time.time()), usage=usage),
                                        {"type": "attachment", "attachment": said}])
        self.assertGreater(ctx_gauge.next_request_tokens(path, "Bash", {"stdout": ""}), 900_000)

    def test_mail_is_delivered_at_the_next_tool_call(self):
        self.post("implement-4", "Keep the statement of ready_holds.")
        text = self.gauge("w4")
        self.assertIn("Message from the planner", text)
        self.assertIn("Keep the statement of ready_holds.", text)
        self.assertEqual(self.w.mail("implement-4"), [])
        self.assertNotIn("Message from", self.gauge("w4"))  # once; what remains is the countdown

    def hook_out(self, sid, **extra):
        hook = {"session_id": sid, "tool_name": "Bash", "tool_input": {"command": "true"},
                "tool_response": {"stdout": ""}, "transcript_path": self.at(sid, 100_000),
                "hook_event_name": "PostToolUse", "cwd": str(self.w.project), **extra}
        code, out, err = self.w.hook("ctx_gauge.py", "gauge", hook)
        self.assertEqual((code, err), (0, ""))
        return out

    def end_mark(self, sid, age=0):
        (self.w.state / "flags").mkdir(exist_ok=True)
        (self.w.state / "flags" / f"{sid}.ended").write_text(str(time.time() - age))

    def test_a_call_that_ended_the_turn_ends_it_before_the_request_that_would_say_so(self):
        # 172 requests in nine hours of 2026-09-22 only said the turn was over — "Parked while the check runs." —
        # each reading the whole context again (the owner: the cost balloons)
        self.assertNotIn("continue", self.hook_out("w4") or {})  # a call that ended nothing
        self.end_mark("w4")
        (self.w.state / "flags" / "w4.blocks").write_text("3")
        out = self.hook_out("w4")
        self.assertEqual(out, {"continue": False, "stopReason": ctx_gauge.ENDED_REASON})
        self.assertFalse((self.w.state / "flags" / "w4.ended").exists())  # taken: it ends that one turn
        self.assertFalse((self.w.state / "flags" / "w4.blocks").exists())  # the Stop hook, which clears it, does not run
        self.assertNotIn("continue", self.hook_out("w4") or {})

    def test_mail_that_came_meanwhile_goes_on_to_the_session_instead(self):
        self.end_mark("r3")
        self.post("review-3", "Judge the fix as well.")
        out = self.hook_out("r3")
        self.assertNotIn("continue", out)
        self.assertIn("Judge the fix as well.", out["hookSpecificOutput"]["additionalContext"])
        self.assertFalse((self.w.state / "flags" / "r3.ended").exists())

    def test_mail_to_a_session_that_parked_waits_in_its_box_for_its_resume(self):
        # implement-40 parked in the call its message of the harness came with, and said "Parked for the machine;
        # ending turn." to it (2026-09-22 10:24)
        self.set_session("implement-4", state="parked")
        self.end_mark("w4")
        self.post("implement-4", "queued: 2 Isabelle run(s) are going.")
        self.assertEqual(self.hook_out("w4"), {"continue": False, "stopReason": ctx_gauge.ENDED_REASON})
        self.assertEqual(len(self.w.mail("implement-4")), 1)  # kept for its first call once resumed

    def test_a_parked_session_woken_by_its_run_makes_no_request_and_is_told_at_its_resume(self):
        # implement-40 and implement-90, parked for their runs, were woken by each run's end and answered "Waiting to
        # be resumed." — a request for nothing, the harness resuming them afterwards (2026-09-22)
        note = ("<task-notification>\n<task-id>bq1</task-id>\n<output-file>/x/bq1.output</output-file>\n"
                "<status>completed</status>\n<summary>Background command finished</summary>\n</task-notification>")
        self.w.transcript("w4", [{"type": "user", "message": {"content": [{"type": "tool_result",
            "content": "Command running in background with ID: bq1. Output is being written to: /x/bq1.output"}]}}])
        jobs = lambda: subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                       "import v2; print(v2.running_jobs('implement-4'))"], env=self.w.env,
                                      capture_output=True, text=True).stdout.strip()
        self.assertEqual(jobs(), "['bq1']")
        prompt = lambda sid: self.w.hook("ctx_gauge.py", "owner", {"session_id": sid, "prompt": note,
                                                                   "hook_event_name": "UserPromptSubmit"})[1]
        self.assertIsNone(prompt("w4"))                                    # working: the notification wakes it
        self.set_session("implement-4", state="parked")
        self.assertIs(prompt("w4")["continue"], False)                     # parked: no request
        self.assertEqual(jobs(), "[]")                                     # and its run has ended, as the harness reads
        self.assertIn("<task-id>bq1</task-id>", (self.w.state / "notified" / "w4.txt").read_text())

    def test_a_mark_whose_hook_never_ran_ends_nothing(self):
        self.end_mark("w4", age=ctx_gauge.ENDED_FRESH + 60)
        self.assertNotIn("continue", self.hook_out("w4") or {})
        self.assertFalse((self.w.state / "flags" / "w4.ended").exists())

    def test_a_session_without_a_role_is_left_alone(self):
        self.assertEqual(self.gauge("other", ctx_gauge.HARD + 1000), "")
        self.assertIsNone(self.stop("other"))
        self.assertFalse((self.w.state / "flags").exists())

    def test_a_working_session_keeps_its_own_cache_warm_and_not_its_origins(self):
        # its requests read its own entry, not the shorter ones under it: plan-42's kept kb-10 looking warm, and
        # design-171's the xhigh layer, while their entries expired unpinged (2026-09-22: 527K, and 235K twice)
        old = time.time() - 3000
        for name in ("plan-1", "kb-1"):
            self.w.hit(name, age=3000)
        (self.w.state / "max-base.hit").write_text("")
        os.utime(self.w.state / "max-base.hit", (old, old))
        self.gauge("p1")
        self.assertGreater((self.w.state / "hits/plan-1").stat().st_mtime, old + 100)
        for path in ("hits/kb-1", "max-base.hit"):
            self.assertLess((self.w.state / path).stat().st_mtime, old + 100, path)

    def test_the_planner_s_turn_ends_when_it_has_handled_what_it_was_given(self):
        # it lives across its events: its turn ends with the last of them, it is sealed warm, and the next wakes it
        self.assertIsNone(self.stop("p1"))
        self.post("plan-1", "Task 4 is committed.")
        self.assertIn("Task 4 is committed.", self.stop("p1"))  # mail first: what is unread continues the turn
        self.assertIsNone(self.stop("p1"))

    def test_a_session_ends_its_turn_only_when_its_piece_of_work_has_ended_or_it_waits(self):
        self.assertIn("v2.py result 4", self.stop("w4"))
        self.assertIn("v2.py verdict 3", self.stop("r3"))
        self.w.set_st(asks={"q1": {"from": "implement-4", "state": "open", "text": "q", "asked": time.time()},
                            "q2": {"from": "review-3", "state": "open", "text": "q", "asked": time.time()}})
        self.assertIsNotNone(self.stop("w4"))  # a producing session does not wait holding the slot: it parks
        self.assertIsNone(self.stop("r3"))  # another may wait on its question
        running = [{"type": "user", "message": {"content": [{"type": "tool_result",
                    "content": "Command running in background with ID: bj7. Output is being written to: x"}]}}]
        self.assertIn("v2.py result 4", self.stop("w4", running))  # nor on its own run: it parks for it
        self.set_session("implement-4", state="parked")
        self.assertIsNone(self.stop("w4", running))  # parked, for its run, a fix, the tree or an answer
        self.w.set_st(asks={})
        self.assertIsNotNone(self.stop("r3"))
        self.assertIsNone(self.stop("r3", running))  # another session may wait for its own job
        for name, sid in (("implement-4", "w4"), ("review-3", "r3")):
            self.set_session(name, state="done")
            self.assertIsNone(self.stop(sid))
        self.assertIsNone(self.stop("k2"))  # the knowledge base, always
        self.set_session("plan-1", state="working", owner=True)
        self.assertIsNone(self.stop("p1"))  # a planner the owner speaks to waits for the owner

    def test_mail_waiting_continues_the_turn(self):
        self.set_session("plan-1", state="done")
        self.post("plan-1", "Which order?")
        self.assertIn("Which order?", self.stop("p1"))
        self.assertIsNone(self.stop("p1"))

    def test_near_the_end_the_stop_reason_is_the_notice(self):
        self.gauge("w4", ctx_gauge.SOFT + 1000)
        self.assertTrue(self.stop("w4").startswith("Now write your result, partial"))

    def test_compaction_is_refused_and_marks_the_end(self):
        code, _, err = self.w.hook("ctx_gauge.py", "tripwire", {"session_id": "w4", "transcript_path": self.at("w4", 900_000)})
        self.assertEqual(code, 2)
        self.assertIn("Compaction is not allowed", err)
        self.assertTrue((self.w.state / "flags/w4.hard").exists())


if __name__ == "__main__":
    unittest.main()
