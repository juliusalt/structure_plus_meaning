"""The watchdog's flows (watchdog.py), one run at a time in a throwaway world with a fake `claude` (fakes.py)."""
import datetime
import json
import os
from pathlib import Path
import sys
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import BRIEF, PLANNER_STATE, assistant  # noqa: E402
import v2  # noqa: E402


def hour_text(epoch):
    h = datetime.datetime.fromtimestamp(epoch).hour
    return f"{h % 12 or 12}{'am' if h < 12 else 'pm'}"


class WatchdogTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)

    def tearDown(self):
        self.w.close()

    def run_watchdog(self, **env):
        code, out, err = self.w.run("watchdog.py", env={k: str(v) for k, v in env.items()})
        self.assertEqual((code, err), (0, ""))
        log = (self.w.state / "v2.log").read_text() if (self.w.state / "v2.log").exists() else ""
        self.assertNotIn("watchdog error", log)
        return log

    def said(self, sid, text="ok", ago=0.0, model="claude-opus-5"):
        self.w.transcript(sid, [assistant("m1", fakes.iso(time.time() - ago), [{"type": "text", "text": text}], model=model)])

    def resumed(self, sid):
        return [c["args"] for c in self.w.calls("--bg") if c["args"][:3] == ["--bg", "--resume", sid]]

    def forked(self, prefix=""):
        return [c["args"][c["args"].index("-n") + 1] for c in self.w.calls("--bg") if "-n" in c["args"]
                and c["args"][c["args"].index("-n") + 1].startswith(prefix)]

    def s(self, name):
        return self.w.st()["sessions"][name]

    def update(self, name, **fields):
        st = self.w.st()
        st["sessions"][name].update(fields)
        (self.w.state / "v2.json").write_text(json.dumps(st))

    def heard(self):
        return " ".join(e["text"] for e in self.w.st()["events"]) + " ".join(
            c["args"][-1] for c in self.w.calls("--bg") if "-n" in c["args"])

    # ------------------------------------------------------------ nothing to do

    def test_an_inactive_or_stopped_orchestration_is_left_alone(self):
        self.w.set_st(active=False, events=[{"at": "2026-09-19T10:00:00", "from": "x", "text": "y"}])
        self.run_watchdog()
        self.assertEqual(self.w.calls(), [])
        self.w.set_st(active=True)
        (self.w.state / "stopped").write_text("x")
        self.run_watchdog()
        self.assertEqual(self.w.calls(), [])

    # ------------------------------------------------------------ live sessions

    def test_a_lost_producing_session_gives_its_task_to_the_planner(self):
        self.w.session("implement-4", "implementer", "w4", task="4", live=False)
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        self.run_watchdog()
        self.run_watchdog()
        self.assertEqual(self.s("implement-4")["state"], "working")
        self.run_watchdog()
        self.assertEqual((self.s("implement-4")["state"], self.w.st()["tasks"]["4"]["stage"]), ("lost", "planner"))
        self.assertIn("implement-4 (implementer) on task 4 is gone", self.heard())

    def test_a_lost_review_and_a_lost_consultation_start_again(self):
        self.w.task("4")
        self.w.session("implement-4", "implementer", "w4", task="4", state="done", live=False)
        self.w.session("review-4", "reviewer", "r4", task="4", live=False)
        self.w.session("ask-q1", "consultant", "a1", origin="kb-1", qid="q1", live=False)
        self.w.set_st(tasks={"4": {"stage": "reviewing", "role": "implementer", "session": "implement-4",
                                   "reviewing": "review-4", "reviewed_by": "review-4"}},
                      asks={"q1": {"from": "implement-4", "to": "kb", "text": "Why?", "asked": time.time(), "state": "open",
                                   "target": "kb", "session": "ask-q1"}})
        for _ in range(3):
            self.run_watchdog()
        self.assertIn("review-4.2", self.forked("review-"))
        self.assertIn("ask-q1.2", self.forked("ask-"))

    def test_an_idle_session_with_mail_is_resumed_with_it(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        (self.w.state / "mail").mkdir()
        (self.w.state / "mail/implement-4.jsonl").write_text(json.dumps({"from": "ask-q1", "text": "The answer.", "at": "t"}) + "\n")
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertTrue(resume[3].startswith("[harness] Message from ask-q1"))
        self.assertEqual(self.w.mail("implement-4"), [])

    def test_an_idle_session_whose_work_has_ended_or_that_waits_is_sealed(self):
        self.w.session("review-3", "reviewer", "r3", task="3", status="idle", state="done")
        self.w.session("brief-4", "task-designer", "w4", task="4", status="idle", settings="planner-settings.json")
        self.w.set_st(asks={"q1": {"from": "brief-4", "state": "open", "text": "q", "asked": time.time(), "target": "kb"}})
        self.said("w4")
        self.run_watchdog()
        stopped = [c["args"][1] for c in self.w.calls("stop")]
        self.assertIn("id-r3", stopped)
        self.assertIn("id-w4", stopped)
        self.assertTrue(self.s("brief-4")["sealed"])
        self.assertEqual(self.s("brief-4")["state"], "waiting")  # held warm for its answer

    def test_a_session_waiting_on_its_answer_is_held_warm_and_given_back_when_it_went_cold(self):
        self.w.session("implement-4", "implementer", "w4", task="4", state="parked", live=False)
        self.w.set_st(asks={"q1": {"from": "implement-4", "state": "open", "text": "q", "asked": time.time(),
                                   "target": "planner"}},
                      tasks={"4": {"stage": "parked", "session": "implement-4",
                                   "parked": {"for": "answer", "since": time.time(), "questions": ["q1"]}}})
        self.w.hit("implement-4", age=v2.PING_AGE + 60)
        self.run_watchdog(ORCH_PING_WAIT=0)
        self.assertTrue(self.w.wait_for(self.w.state / "ping-implement-4", 5))  # pinged before its cache expires
        self.w.hit("implement-4", age=v2.WARM_MAX + 60)
        self.run_watchdog()
        self.assertEqual(self.s("implement-4")["state"], "lost")
        self.assertEqual(self.w.st()["tasks"]["4"]["stage"], "planner")  # the producing slot is free again

    def test_mail_that_cannot_be_delivered_is_kept(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle", warm=False)
        self.w.hit("implement-4", age=v2.WARM_MAX + 60)
        self.said("w4")
        (self.w.state / "mail").mkdir(exist_ok=True)
        (self.w.state / "mail" / "implement-4.jsonl").write_text(json.dumps({"from": "kb", "text": "the answer", "at": "t"}) + "\n")
        self.run_watchdog()
        self.assertIn("the answer", json.dumps(self.w.mail("implement-4")))
        self.assertEqual(self.s("implement-4")["state"], "lost")

    def test_a_session_with_running_jobs_is_neither_sealed_nor_resumed(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.w.set_st(asks={"q1": {"from": "implement-4", "state": "open", "text": "q", "asked": time.time()}})
        self.w.transcript("w4", [assistant("m1", fakes.iso(time.time() - 600), [{"type": "text", "text": "ok"}]),
                                 {"type": "user", "message": {"content": [{"type": "tool_result", "content":
                                  "Command running in background with ID: bx7. Output is being written to: /t/bx7.output"}]}}])
        (self.w.state / "mail").mkdir()
        (self.w.state / "mail/implement-4.jsonl").write_text(json.dumps({"from": "q", "text": "x", "at": "t"}) + "\n")
        self.run_watchdog()
        self.assertEqual(self.w.calls("stop"), [])
        self.assertEqual(self.resumed("w4"), [])
        self.w.transcript("w4", [{"type": "user", "message": {"content": [{"type": "tool_result", "content":
                                  "Command running in background with ID: bx7."}]}},
                                 {"type": "user", "message": {"content": "<task-notification><task-id>bx7</task-id>"
                                                                          "<status>completed</status></task-notification>"}},
                                 assistant("m2", fakes.iso(time.time()), [{"type": "text", "text": "ok"}])])
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 1)  # its mail, now that nothing of its own runs

    def test_an_episode_the_owner_left_is_asked_to_end(self):
        self.w.session("plan-2", "planner", "p2", status="idle", owner=True, settings="planner-settings.json")
        self.said("p2", ago=60)
        self.run_watchdog()
        self.assertEqual(self.resumed("p2"), [])  # it waits for the owner
        self.said("p2", ago=2000)
        self.run_watchdog()
        self.assertIn("The owner has been silent for half an hour", self.resumed("p2")[0][3])

    def test_a_usage_limit_stop_is_resumed_once_the_limit_has_reset(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.said("w4", f"You've hit your limit · resets {hour_text(time.time() + 7200)}", ago=60, model="<synthetic>")
        self.run_watchdog()
        self.assertEqual(self.resumed("w4"), [])
        said = time.time() - 3 * 3600
        self.said("w4", f"You've hit your limit · resets {hour_text(said + 3600)}", ago=3 * 3600, model="<synthetic>")
        self.w.hit("implement-4")
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("usage limit, which has now reset", resume[3])

    def test_a_session_at_the_end_of_its_window_is_lost(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        (self.w.state / "flags").mkdir()
        (self.w.state / "flags/w4.hard").write_text("x")
        self.said("w4")
        self.run_watchdog()
        self.assertEqual(self.s("implement-4")["state"], "lost")
        self.assertIn("reached the end of its window", self.heard())

    def test_a_stalled_session_is_resumed_once_within_the_backoff(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.said("w4", ago=600)
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("Your turn ended before your piece of work did", resume[3])
        self.w.set_status("implement-4", "idle")
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 1)

    # ------------------------------------------------------------ held sessions

    def test_the_knowledge_base_is_pinged_before_its_cache_expires(self):
        self.w.hit("kb-1", age=v2.PING_AGE + 60)
        self.run_watchdog()
        self.assertTrue((self.w.state / "ping-kb-1").exists())
        for _ in range(100):
            if self.forked("warm-kb-1"):
                break
            time.sleep(0.05)
        (ping,) = [c["args"] for c in self.w.calls("--bg") if "warm-kb-1" in c["args"]]
        self.assertEqual(ping[ping.index("--resume") + 1], "kbsid")
        self.assertIn("Keep-warm ping", ping[-1])
        self.run_watchdog()
        self.assertEqual(len(self.forked("warm-kb-1")), 1)  # one ping at a time

    def test_what_nothing_refers_to_is_released_and_what_may_come_back_is_held(self):
        self.w.session("implement-4", "implementer", "w4", task="4", state="done", live=False)
        self.w.session("review-5", "reviewer", "r5", task="5", state="done", live=False)
        self.w.session("brief-6", "task-designer", "b6", task="6", state="done", live=False, ended=time.time())
        self.w.set_st(tasks={"4": {"stage": "reviewing", "session": "implement-4"},
                             "5": {"stage": "done", "reviewed_by": "review-5"},
                             "6": {"stage": "ready", "briefed_by": "brief-6"}})
        self.run_watchdog()
        self.assertTrue(self.s("review-5").get("released"))
        self.assertFalse(self.s("implement-4").get("released"))
        self.assertFalse(self.s("brief-6").get("released"))
        self.update("brief-6", ended=time.time() - v2.HOLD_MAX - 60)
        self.run_watchdog()
        self.assertTrue(self.s("brief-6").get("released"))

    def test_a_parked_session_records_a_partial_result_after_its_hold(self):
        self.w.session("implement-4", "implementer", "w4", task="4", state="parked", live=False)
        self.w.set_st(tasks={"4": {"stage": "parked", "session": "implement-4",
                                   "parked": {"since": time.time() - v2.HOLD_PARK - 60, "why": "slow", "after": "9"}}})
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("has not landed within 3 hours. Record a partial result now", resume[3])

    # ------------------------------------------------------------ finishing

    def test_a_quick_fix_past_its_budget_and_a_silent_finalizer_go_to_the_planner(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle",
                       fix={"since": time.time() - v2.FIX_MINUTES * 60 - 600})
        self.w.set_st(tasks={"4": {"stage": "fixing", "session": "implement-4", "fixing": "implement-4"},
                             "5": {"stage": "checking", "finishing_since": time.time() - 7200}})
        self.said("w4")
        self.run_watchdog()
        st = self.w.st()
        self.assertEqual((st["tasks"]["4"]["stage"], st["tasks"]["5"]["stage"]), ("planner", "planner"))
        self.assertIn("outgrew its quick fix's budget", self.heard())
        self.assertIn("The finalizer of task 5 ended without reporting", self.heard())  # no finalizer runs for it

    def test_a_finalizer_that_still_runs_is_given_its_whole_wait_and_check(self):
        (self.w.project / ".build/tasks/5").mkdir(parents=True)
        (self.w.project / ".build/tasks/5/finalizer.pid").write_text(str(os.getpid()))  # alive
        self.w.set_st(tasks={"5": {"stage": "checking", "finishing_since": time.time() - 7200}})
        self.run_watchdog()
        self.assertEqual(self.w.st()["tasks"]["5"]["stage"], "checking")  # waiting for Isabelle and checking: < 2h10
        self.w.set_st(tasks={"5": {"stage": "checking", "finishing_since": time.time() - 8200}})
        self.run_watchdog()
        self.assertEqual(self.w.st()["tasks"]["5"]["stage"], "planner")
        self.assertIn("has not reported within", self.heard())

    def test_the_dispatch_runs_after_the_care(self):
        self.w.task("1", BRIEF)
        self.w.set_st(queue=["1"])
        self.run_watchdog()
        self.assertEqual(self.forked("implement-"), ["implement-1"])


if __name__ == "__main__":
    unittest.main()
