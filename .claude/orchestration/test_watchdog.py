"""The watchdog's flows (watchdog.py), one run at a time in a throwaway world with a fake `claude` (fakes.py)."""
import datetime
import json
import os
from pathlib import Path
import sys
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402
from fakes import BRIEF, PLANNER_STATE, assistant  # noqa: E402
import v2  # noqa: E402
import watchdog  # noqa: E402


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

    def test_the_planner_between_its_events_is_sealed_held_and_never_released(self):
        # it lives across its events: a turn that ends means it has handled them, and the next event wakes it
        self.w.session("plan-1", "planner", "p1", status="idle", settings="planner-settings.json", origin="kb-1",
                       events=[{"at": "2026-09-20T10:00:00", "from": "x", "text": "handled"}])
        self.w.session("implement-9", "implementer", "w9", task="9")  # something works: this is no standstill
        self.said("p1")
        self.run_watchdog()
        self.assertEqual(self.s("plan-1")["state"], "idle")
        self.assertTrue(self.s("plan-1")["sealed"])
        self.assertEqual(self.s("plan-1")["events"], [])  # by ending its turn it says it has handled them
        self.assertIn("id-p1", [c["args"][1] for c in self.w.calls("stop")])
        self.w.set_rows([r for r in self.w.rows() if r["name"] != "plan-1"])
        self.w.hit("plan-1", age=v2.PING_AGE + 60)
        self.run_watchdog(ORCH_PING_WAIT=0)
        self.assertFalse(self.s("plan-1").get("released"))  # never released while it lives
        self.assertTrue((self.w.state / "ping-plan-1").exists())  # pinged before its cache expires

    def test_a_standstill_is_named_to_the_planner_because_only_it_can_move_the_graph(self):
        # the orchestration stood still three times on 2026-09-20 (six and a half hours), and only health.py said so
        self.w.session("plan-1", "planner", "p1", state="idle", live=False, settings="planner-settings.json")
        self.w.task("4", subject="The blocked one")
        self.w.set_st(queue=["4"], tasks={"4": {"stage": "parked", "kind": "build", "session": "implement-4",
                                                "parked": {"for": "fix", "after": "9", "since": time.time() - 7200}}})
        self.run_watchdog()
        told = " ".join(c["args"][-1] for c in self.w.calls("--bg") if "--resume" in c["args"])
        self.assertIn("Nothing is working and nothing in the queue can start", told)
        self.assertIn("task 4 has been parked 120 min for task 9", told)
        self.assertTrue((self.w.state / "standstill").exists())
        # said once, not at every run of the watchdog
        before = len(self.w.calls("--bg"))
        self.run_watchdog()
        self.assertEqual(len(self.w.calls("--bg")), before)

    def test_a_planner_that_goes_cold_between_its_events_is_lost_and_gives_them_back(self):
        self.w.session("plan-1", "planner", "p1", state="idle", live=False, settings="planner-settings.json",
                       events=[{"at": "2026-09-20T10:00:00", "from": "x", "text": "not handled"}])
        self.w.hit("plan-1", age=v2.WARM_MAX + 60)
        self.run_watchdog()
        self.assertTrue(self.s("plan-1").get("released"))
        # what it was given and had not handled goes back, and the dispatch that follows starts the next planner on it
        started = [c["args"][-1] for c in self.w.calls("--bg")
                   if "-n" in c["args"] and c["args"][c["args"].index("-n") + 1].startswith("plan-")]
        self.assertEqual(len(started), 1)
        self.assertIn("not handled", started[0])

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
        (self.w.state / "mail" / "implement-4.jsonl").write_text(
            json.dumps({"from": "kb", "text": "the answer", "at": "t"}) + "\n"
            + json.dumps({"from": "plan-1", "text": "and the order", "at": "t"}) + "\n")
        self.run_watchdog()
        kept = self.w.mail("implement-4")
        self.assertEqual([(m["from"], m["text"]) for m in kept],  # each with its own sender, not merged into one
                         [("kb", "the answer"), ("plan-1", "and the order")])
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

    def layer(self, who="xhigh"):
        (self.w.state / f"{who}-layer.json").write_text(json.dumps(
            {"sessionId": f"{who}-layer-sid", "model": "claude-opus-5[1m]", "effort": who, "context": 525_000,
             "sealed": "2026-09-20T10:00:00"}))

    def run_layers(self, share):
        """watchdog.layers() in this world, with the refresh itself intercepted: it would otherwise run base.sh
        against the real repository, re-measure the real frontier and load a real layer."""
        with patch.object(watchdog, "STATE", str(self.w.state)), patch.object(v2, "STATE", str(self.w.state)), \
                patch.object(watchdog, "stale_share", lambda who: share), \
                patch.object(watchdog.subprocess, "Popen") as popen:
            watchdog.layers()
            return [c.args[0] for c in popen.call_args_list]

    def test_a_layer_is_refreshed_when_what_it_holds_has_moved_and_not_before(self):
        # the rule of notes/bases-design.md section 8: 20% of the layer's tokens changed, about every 2.5 to 3 hours
        self.layer()
        self.assertEqual(self.run_layers(0.05), [])  # little has moved: the layer stands
        (self.w.state / "xhigh-layer.looked").unlink()
        (launched,) = self.run_layers(0.31)
        self.assertEqual(launched[1:], [str(Path(watchdog.HERE) / "base.sh"), "xhigh", "layer"])
        self.assertIn("31% of what it holds has changed", (self.w.state / "v2.log").read_text())

    def test_a_layer_is_refreshed_at_the_start_of_a_run_whatever_has_changed(self):
        self.layer()
        (self.w.state / "xhigh-layer.refresh").write_text("1")
        self.assertEqual(len(self.run_layers(0.0)), 1)
        self.assertFalse((self.w.state / "xhigh-layer.refresh").exists())  # asked once, not at every run
        self.assertIn("at the start of the run", (self.w.state / "v2.log").read_text())

    def test_a_base_with_no_layer_is_left_alone(self):
        self.assertEqual(self.run_layers(0.9), [])

    def test_only_one_refresh_of_a_layer_runs_at_a_time(self):
        # a refresh can take longer than the watchdog's own ping window, so the lock is base.sh's own and lasts as
        # long as the build does; two at once would fork the stable base twice and race over the same records
        self.layer()
        (self.w.state / "xhigh-layer.building").write_text("12345")
        self.assertEqual(self.run_layers(0.9), [])
        (self.w.state / "xhigh-layer.building").unlink()
        self.assertEqual(len(self.run_layers(0.9)), 1)

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
