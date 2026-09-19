"""The context gauge, mail and turn control by role (ctx_gauge.py), run as the hooks run in a throwaway world."""
import json
import os
from pathlib import Path
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

    def test_mail_is_delivered_at_the_next_tool_call(self):
        self.post("implement-4", "Keep the statement of ready_holds.")
        text = self.gauge("w4")
        self.assertIn("Message from the planner", text)
        self.assertIn("Keep the statement of ready_holds.", text)
        self.assertEqual(self.w.mail("implement-4"), [])
        self.assertNotIn("Message from", self.gauge("w4"))  # once; what remains is the countdown

    def test_a_session_without_a_role_is_left_alone(self):
        self.assertEqual(self.gauge("other", ctx_gauge.HARD + 1000), "")
        self.assertIsNone(self.stop("other"))
        self.assertFalse((self.w.state / "flags").exists())

    def test_a_working_session_keeps_its_own_and_its_origins_caches_warm(self):
        old = time.time() - 3000
        for name in ("plan-1", "kb-1"):
            self.w.hit(name, age=3000)
        (self.w.state / "max-base.hit").write_text("")
        os.utime(self.w.state / "max-base.hit", (old, old))
        self.gauge("p1")
        for path in ("hits/plan-1", "hits/kb-1", "max-base.hit"):
            self.assertGreater((self.w.state / path).stat().st_mtime, old + 100, path)

    def test_a_session_ends_its_turn_only_when_its_piece_of_work_has_ended_or_it_waits(self):
        self.assertIn("v2.py planned", self.stop("p1"))
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
        for name, sid in (("plan-1", "p1"), ("implement-4", "w4"), ("review-3", "r3")):
            self.set_session(name, state="done")
            self.assertIsNone(self.stop(sid))
        self.assertIsNone(self.stop("k2"))  # the knowledge base, always
        self.set_session("plan-1", state="working", owner=True)
        self.assertIsNone(self.stop("p1"))  # an episode the owner speaks to waits for the owner

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
