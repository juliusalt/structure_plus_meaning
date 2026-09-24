"""The watchdog's flows (watchdog.py), one run at a time in a throwaway world with a fake `claude` (fakes.py)."""
import datetime
import json

v2_retries = lambda: int(os.environ.get("ORCH_API_RETRIES", 3))  # watchdog.API_RETRIES, as the test world has it
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
        """What the planner has been told: the events not yet with it, those a planner was started on, and those
        delivered to one that lives. Mail was missing here, so a notice that arrived after a planner had started
        read as never said (2026-09-21)."""
        return (" ".join(e["text"] for e in self.w.st()["events"])
                + " ".join(c["args"][-1] for c in self.w.calls("--bg") if "-n" in c["args"])
                + " ".join(m["text"] for n in self.w.st()["sessions"] if n.startswith("plan-")
                           for m in self.w.mail(n)))

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

    def test_a_session_the_supervisor_no_longer_runs_is_lost_though_it_is_still_listed(self):
        # the listing gives `status` (busy or idle) while the supervisor holds the session; a row with only the
        # coarser `state` is one whose process it no longer runs, and it stays listed. It counted as seen, so the
        # gone count never reached its limit and the session held its slot for ever (2026-09-21).
        self.w.session("implement-4", "implementer", "w4", task="4")
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        self.w.set_rows([dict(r, status=None, state="blocked") for r in self.w.rows()])
        for _ in range(watchdog.GONE_CHECKS - 1):
            self.run_watchdog()
            self.assertEqual(self.s("implement-4")["state"], "working")
        self.run_watchdog()
        self.assertEqual((self.s("implement-4")["state"], self.w.st()["tasks"]["4"]["stage"]), ("lost", "planner"))
        self.assertIn("is listed as blocked and no turn of it runs", (self.w.state / "v2.log").read_text())

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

    def test_mail_left_in_a_sealed_planners_box_is_not_left_there(self):
        # plan() posts to the planner and wakes it; when that resume fails the mail goes back into its box
        # (keep_mail) and nothing opens it again: plan() returns at once while no new event has come, and care() is
        # reached only for LIVE sessions, which the planner between its events (`idle`, sealed) is not. The wait was
        # unbounded — a message to the planner waited for the next message, and if none came, for ever.
        self.w.session("plan-1", "planner", "p1", state="idle", live=False, settings="planner-settings.json",
                       origin="kb-1", events=[{"at": "2026-09-20T20:14:59", "from": "the harness", "text": "trees"}])
        self.w.session("implement-9", "implementer", "w9", task="9")  # something works: no standstill to carry it
        (self.w.state / "mail").mkdir(exist_ok=True)
        (self.w.state / "mail" / "plan-1.jsonl").write_text(json.dumps(
            {"from": "the harness", "text": "the worktrees", "at": "2026-09-20T20:15:08"}) + "\n")
        self.run_watchdog()
        told = " ".join(str(c["args"][-1]) for c in self.w.calls("--bg") if "--resume" in c["args"])
        self.assertIn("the worktrees", told)
        self.assertFalse(v2.has_mail("plan-1"))

    def test_a_sealed_planner_gone_cold_with_mail_gives_its_events_back(self):
        self.w.session("plan-1", "planner", "p1", state="idle", live=False, settings="planner-settings.json",
                       origin="kb-1", events=[{"at": "2026-09-20T20:14:59", "from": "x", "text": "not handled"}])
        (self.w.state / "mail").mkdir(exist_ok=True)
        (self.w.state / "mail" / "plan-1.jsonl").write_text(json.dumps(
            {"from": "x", "text": "not handled", "at": "2026-09-20T20:15:08"}) + "\n")
        self.w.hit("plan-1", age=v2.WARM_MAX + 60)
        self.run_watchdog()
        self.assertEqual(self.s("plan-1")["state"], "lost")
        started = [c["args"][-1] for c in self.w.calls("--bg")
                   if "-n" in c["args"] and c["args"][c["args"].index("-n") + 1].startswith("plan-")]
        self.assertTrue(started and "not handled" in started[0], started)

    def test_a_completed_or_dropped_task_is_not_named_as_the_planners_to_re_plan(self):
        # on 2026-09-20 the standstill told the planner that tasks 5, 9, 18 and 21 had come back and had not been
        # re-planned. 5, 9 and 18 were committed and completed; 21 had been dropped and was not in the list at all.
        # All four statements were false, and they were the only thing about tasks it was told that day: the stage is
        # the harness's own bookkeeping, which nothing clears, and the graph is what says what is still to be done.
        self.w.session("plan-1", "planner", "p1", state="idle", live=False, settings="planner-settings.json")
        self.w.task("4", subject="Finished elsewhere", status="completed")
        self.w.task("6", subject="Really back with the planner")
        self.w.set_st(queue=[], tasks={"4": {"stage": "planner"}, "5": {"stage": "planner"},
                                       "6": {"stage": "planner"}})
        self.run_watchdog()
        told = " ".join(str(c["args"][-1]) for c in self.w.calls("--bg") if "--resume" in c["args"])
        self.assertIn("task 6 is yours", told)
        self.assertNotIn("task 4 is yours", told)  # completed in the graph
        self.assertNotIn("task 5 is yours", told)  # dropped: not in the task list at all

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
        # the ping runs in the background and marks the session hit when it ends: waited for, or its hit could land
        # after the age set below and the session read as warm (it failed so under the suite's load, 2026-09-23)
        end = time.time() + 20
        while time.time() < end and "ping implement-4:" not in (self.w.state / "v2.log").read_text():
            time.sleep(0.1)
        self.w.hit("implement-4", age=v2.WARM_MAX + 60)
        self.run_watchdog()
        self.assertEqual(self.s("implement-4")["state"], "lost")
        self.assertEqual(self.w.st()["tasks"]["4"]["stage"], "planner")  # the producing slot is free again

    def test_mail_that_cannot_be_delivered_is_kept_and_named_when_the_session_goes(self):
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle", warm=False)
        self.w.hit("implement-4", age=v2.WARM_MAX + 60)
        self.said("w4")
        (self.w.state / "mail").mkdir(exist_ok=True)
        (self.w.state / "mail" / "implement-4.jsonl").write_text(json.dumps({"from": "kb", "text": "the answer", "at": "t"}) + "\n")
        (self.w.state / "mail" / "implement-4.jsonl").write_text(
            json.dumps({"from": "kb", "text": "the answer", "at": "t"}) + "\n"
            + json.dumps({"from": "plan-1", "text": "and the order", "at": "t"}) + "\n")
        self.run_watchdog()
        # the resume failed, so the mail went back in the box (each with its own sender, not merged into one) — and
        # the session was lost and released in the same pass, so it is named rather than left where no one opens it
        self.assertEqual(self.w.mail("implement-4"), [])
        # said once, by the one place that empties the box: the loss said it too, and said the box was kept
        self.assertEqual((self.w.state / "v2.log").read_text().count("never read"), 1)
        said = self.heard()
        self.assertIn("2 message(s) to implement-4 (implementer on task 4) were never read: from kb, plan-1", said)
        self.assertIn("2 message(s) to implement-4 from kb, plan-1 were never read: it is released",
                      (self.w.state / "v2.log").read_text())
        self.assertIn("Message from kb", said)
        self.assertIn("the answer", said)
        self.assertIn("Message from plan-1", said)
        self.assertIn("and the order", said)
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
        # mail for it waits with it: resuming to hand mail over spends the resume on a turn that hits the limit
        # again, while unread() has already emptied the box — it would be read by nobody (2026-09-21)
        (self.w.state / "mail").mkdir(exist_ok=True)
        (self.w.state / "mail" / "implement-4.jsonl").write_text(
            json.dumps({"from": "plan-1", "text": "the order changed", "at": "t"}) + "\n")
        self.run_watchdog()
        self.assertEqual(self.resumed("w4"), [])
        self.assertEqual([m["text"] for m in self.w.mail("implement-4")], ["the order changed"])
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
        # and the rule it is given is the one that holds for a producing session
        self.assertIn("once you have parked (`v2.py park run|tree|fix|answer`)", resume[3])
        self.assertNotIn("while you wait on a question of your own", resume[3])
        self.w.set_status("implement-4", "idle")
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 1)
        # a supporting session is given the rule that holds for it
        self.w.session("review-4", "reviewer", "r4", task="4", status="idle")
        self.said("r4", ago=600)
        self.run_watchdog()
        (resume,) = self.resumed("r4")
        self.assertIn("or while you wait on a question of your own", resume[3])

    # ------------------------------------------------------------ held sessions

    def layer(self, who="xhigh"):
        (self.w.state / f"{who}-layer.json").write_text(json.dumps(
            {"sessionId": f"{who}-layer-sid", "model": "claude-opus-5[1m]", "effort": who, "context": 525_000,
             "sealed": "2026-09-20T10:00:00", "flags": fakes.LEAN}))

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

    def test_a_layer_can_be_asked_for_by_hand_whatever_has_changed(self):
        self.layer()
        (self.w.state / "xhigh-layer.refresh").write_text("1")
        self.assertEqual(len(self.run_layers(0.0)), 1)
        self.assertFalse((self.w.state / "xhigh-layer.refresh").exists())  # asked once, not at every run
        self.assertIn("asked for by hand", (self.w.state / "v2.log").read_text())

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
        (ping,) = [c["args"] for c in self.w.calls("--bg") if any(a.startswith("warm-kb-1-") for a in c["args"])]
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
        self.assertTrue(self.s("brief-6").get("released"))  # an author is not held to be asked (2026-09-22)

    def test_the_machine_s_isabelle_processes_are_written_with_the_run_each_counts_in(self):
        # a session's sandbox cannot see the machine's processes, and the count was of processes where the limit is of
        # runs (2026-09-21): the watchdog, which sees them, writes what one run is
        procs = {1: (0, "systemd", "/sbin/init"), 10: (1, "python3", "python3 tools/incremental_check.py check"),
                 11: (10, "poly", "poly -q"), 12: (10, "poly", "poly -q")}
        with patch.object(watchdog.v2, "machine_processes", lambda: procs), \
                patch.object(watchdog, "STATE", str(self.w.state)):
            watchdog.isabelle_snapshot()
        snap = json.loads((self.w.state / "isabelle-processes.json").read_text())
        self.assertEqual((snap["runs"], snap["heavy"], snap["probes"]), (1, 1, 0))
        self.assertEqual([p["run"] for p in snap["processes"]], [10, 10])
        self.assertEqual({p["kind"] for p in snap["processes"]}, {"heavy"})
        self.assertIn("rss_mb", snap["processes"][0])
        self.assertIn("incremental_check.py", snap["processes"][0]["run_command"])
        self.assertEqual(snap["processes"][0]["ancestors"][1]["pid"], 10)
        with patch.object(watchdog.v2, "machine_processes", lambda: {1: (0, "systemd", "/sbin/init")}), \
                patch.object(watchdog, "STATE", str(self.w.state)):
            watchdog.isabelle_snapshot()                                        # no run: written all the same
        self.assertEqual(json.loads((self.w.state / "isabelle-processes.json").read_text())["runs"], 0)

    def test_a_rejecting_reviewer_is_held_while_the_fix_waits_within_the_hold(self):
        # review-23 was released when its task's fix parked for the tree, review-47 when its task went back to the
        # planner (2026-09-21): each re-review then needs a new reviewer that reads everything again
        self.w.session("review-5", "reviewer", "r5", task="5", reviews="4", state="done", live=False, ended=time.time())
        self.w.set_st(tasks={"5": {"stage": "ready", "reviewed_by": "review-5", "verdict": "reject"},
                             "4": {"stage": "parked", "session": "fix-4"}})
        self.run_watchdog()
        self.assertFalse(self.s("review-5").get("released"))                      # its fix parked
        self.w.set_st(tasks=dict(self.w.st()["tasks"], **{"4": {"stage": "planner"}}))
        self.run_watchdog()
        self.assertFalse(self.s("review-5").get("released"))                      # the task with the planner
        self.update("review-5", ended=time.time() - v2.HOLD_MAX - 60)
        self.run_watchdog()
        self.assertTrue(self.s("review-5").get("released"))                       # within the hold's bound

    def test_an_author_is_not_held_to_be_asked(self):
        # held while tasks it briefed or designed were open, pinged for questions none ever came: 26 pings and 16.4M
        # tokens read in one run, design-66 an hour after it had landed (the owner, 2026-09-22)
        self.w.session("brief-6", "task-designer", "b6", task="6", state="done", live=False, ended=time.time())
        self.w.session("design-7", "designer", "d7", task="7", state="done", live=False, ended=time.time())
        self.w.task("8", subject="built on the design", blockedBy=["7"])
        self.w.set_st(tasks={"6": {"stage": "done"}, "7": {"stage": "done"},
                             "8": {"stage": "running", "briefed_by": "brief-6"}})
        self.run_watchdog()
        self.assertTrue(self.s("brief-6").get("released"))
        self.assertTrue(self.s("design-7").get("released"))

    def test_a_task_designer_is_held_while_its_proposal_waits_on_the_planner(self):
        # brief 13's designer was released three seconds after its result, before the planner had read its proposal,
        # and the planner's correction found no session (2026-09-21)
        self.w.session("brief-6", "task-designer", "b6", task="6", state="done", live=False, ended=time.time())
        self.w.set_st(tasks={"6": {"stage": "proposed", "session": "brief-6", "proposal": ".build/tasks/6/p.json"}})
        self.run_watchdog()
        self.assertFalse(self.s("brief-6").get("released"))
        self.update("brief-6", ended=time.time() - v2.HOLD_MAX - 60)               # within the hold's bound
        self.run_watchdog()
        self.assertTrue(self.s("brief-6").get("released"))

    def test_a_parked_session_records_a_partial_result_after_its_hold(self):
        self.w.session("implement-4", "implementer", "w4", task="4", state="parked", live=False)
        self.w.set_st(tasks={"4": {"stage": "parked", "session": "implement-4",
                                   "parked": {"since": time.time() - v2.HOLD_PARK - 60, "why": "slow", "after": "9"}}})
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("has not landed within 3 hours. Record a partial result now", resume[3])

    def test_a_reviewer_waiting_on_the_machine_is_woken_when_a_run_may_start(self):
        self.w.session("review-4", "reviewer", "r4", task="4", status="idle")
        self.said("r4", ago=600)
        (self.w.state / "work-r4.json").write_text(json.dumps({"run_refused": "heavy"}))
        self.run_watchdog(ORCH_ISABELLE_RUNS=v2.ISABELLE_MAX)
        self.assertEqual(self.resumed("r4"), [])               # not woken to be refused again
        self.run_watchdog(ORCH_ISABELLE_RUNS=0)
        (resume,) = self.resumed("r4")
        self.assertIn("A run may start on the machine now: run your check and continue.", resume[3])

    def test_a_turn_the_api_broke_off_is_redone_within_a_minute_a_few_times_in_a_row(self):
        # investigate-82's reply was cut by "API Error: Server error mid-response" and it waited for the stall's rule,
        # ten minutes of a loop's backoff, told only that its turn had ended (2026-09-22)
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        error = "API Error: Server error mid-response. The response above may be incomplete."
        self.said("w4", error, ago=20, model="<synthetic>")
        self.run_watchdog()
        self.assertEqual(self.resumed("w4"), [])                        # a moment first
        self.said("w4", error, ago=90, model="<synthetic>")
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("The API failed mid-response", resume[3])
        self.assertIn("Redo that step", resume[3])
        # blocked, as such a session is listed, it is not gone: it is resumed the same way
        blocked = lambda: self.w.set_rows([dict(r, status="blocked", state="blocked") if r["name"] == "implement-4"
                                           else r for r in self.w.rows()])
        self.w.set_rows([dict(r, status="blocked", state="blocked") if r["name"] == "implement-4" else r
                         for r in self.w.rows()])
        os.utime(self.w.state / "implement-4.woken", (time.time() - 120, time.time() - 120))
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 1)                    # one failure, one resume, however long
        for n in range(2, v2_retries() + 1):
            blocked()                                                   # its resumed turn broken off again
            self.said("w4", error, ago=90 - n, model="<synthetic>")
            (self.w.state / "implement-4.woken").write_text("x")
            os.utime(self.w.state / "implement-4.woken", (time.time() - 120, time.time() - 120))
            self.run_watchdog()
            self.assertEqual(len(self.resumed("w4")), n)
        self.assertNotIn("implement-4 is listed as blocked", (self.w.state / "v2.log").read_text())
        blocked()
        self.said("w4", error, ago=80, model="<synthetic>")
        (self.w.state / "implement-4.woken").write_text("x")
        os.utime(self.w.state / "implement-4.woken", (time.time() - 120, time.time() - 120))
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), v2_retries())       # enough in a row: a stall like any other
        self.said("w4", "a reply of its own", ago=30)                    # and one of its own starts the count again
        self.w.set_rows([dict(r, status="idle") if r["name"] == "implement-4" else r for r in self.w.rows()])
        self.run_watchdog()
        self.assertFalse((self.w.state / "api-errors-implement-4").exists())

    def test_a_slow_part_of_a_pass_is_named(self):
        # a pass of 04:19:30–04:27:07 on 2026-09-22 held every resume and start for seven minutes, and nothing said
        # which part
        self.run_watchdog(ORCH_SLOW_PART=-1)
        log = (self.w.state / "v2.log").read_text()
        self.assertIn("the watchdog's layers took", log)
        self.assertIn("the dispatch's produce took", log)
        self.run_watchdog()
        self.assertEqual((self.w.state / "v2.log").read_text().count("the watchdog's layers took"), 1)

    def test_a_failure_after_a_reply_of_its_own_is_not_counted_in_a_row(self):
        # plan-35, working again after one failure, was counted "2 of 3 in a row" at its next: the count was reset
        # only when a pass found it idle (2026-09-22 04:08)
        self.w.session("implement-4", "implementer", "w4", task="4", status="idle")
        self.w.set_st(tasks={"4": {"stage": "running", "session": "implement-4"}})
        error = "API Error: 529 Overloaded."
        self.said("w4", error, ago=200, model="<synthetic>")
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 1)
        self.w.transcript("w4", [assistant("m1", fakes.iso(time.time() - 200), [{"type": "text", "text": error}],
                                           model="<synthetic>"),
                                 assistant("m2", fakes.iso(time.time() - 150), [{"type": "text", "text": "working"}]),
                                 assistant("m3", fakes.iso(time.time() - 90), [{"type": "text", "text": error}],
                                           model="<synthetic>")])
        self.w.set_rows([dict(r, status="blocked", state="blocked") if r["name"] == "implement-4" else r
                         for r in self.w.rows()])                       # its resumed turn ended on the failure
        (self.w.state / "implement-4.woken").write_text("x")
        os.utime(self.w.state / "implement-4.woken", (time.time() - 120, time.time() - 120))
        self.run_watchdog()
        self.assertEqual(len(self.resumed("w4")), 2)
        log = (self.w.state / "v2.log").read_text()
        self.assertEqual(log.count("implement-4: the API failed mid-response; resumed to redo its step (1 of"), 2)
        self.assertNotIn("(2 of", log)
        self.assertEqual((self.w.state / "api-errors-implement-4").read_text().split()[0], "1")

    def test_a_task_parked_for_the_machine_is_held_for_its_turn_as_for_the_tree(self):
        # a slot on the machine always comes, only later when landings and measurements are many: task 94 waited two
        # hours for one on 2026-09-22 with an hour of its three left
        self.assertEqual(v2.hold_of({"parked": {"for": "machine"}}), v2.HOLD_TREE)
        self.assertEqual(v2.hold_of({"parked": {"for": "tree"}}), v2.HOLD_TREE)
        for kind in ("fix", "answer", "run"):
            self.assertEqual(v2.hold_of({"parked": {"for": kind}}), v2.HOLD_PARK, kind)

    def test_a_task_parked_for_the_one_tree_is_held_for_its_turn(self):
        # landings go one at a time and a turn always comes: tasks 66 and 68 had waited 1.5-1.7 hours on 2026-09-21,
        # and the owner chose 6 hours for such a wait, where a fix or an answer that may never come keeps 3
        self.w.session("implement-4", "implementer", "w4", task="4", state="parked", live=False)
        self.w.write(".build/tasks/7/finalize.json", json.dumps({"check": "true", "files": ["ROOT"], "message": "m"}))
        checking = {"stage": "checking"}  # task 7's check holds the tree meanwhile
        self.w.set_st(tasks={"7": checking, "4": {"stage": "parked", "session": "implement-4", "parked": {
            "since": time.time() - 4 * 3600, "for": "tree", "holder": "7"}}})
        self.run_watchdog()
        self.assertEqual(self.resumed("w4"), [])
        self.w.set_st(tasks={"7": checking, "4": {"stage": "parked", "session": "implement-4", "parked": {
            "since": time.time() - v2.HOLD_TREE - 60, "for": "tree", "holder": "7"}}})
        self.run_watchdog()
        (resume,) = self.resumed("w4")
        self.assertIn("The working tree has not come free for you within 6 hours. Record a partial result now", resume[3])

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

    def test_an_accepted_task_left_in_review_with_no_review_due_has_its_commit_made(self):
        # tasks 128 and 147 (2026-09-22): accepted, their landings interrupted by the reboot, queued again and checked
        # again, and put in review with no review due — where nothing moved them for eight hours
        (self.w.project / ".build/tasks/5").mkdir(parents=True)
        final = self.w.project / ".build/tasks/5/finalize.json"
        final.write_text(json.dumps({"check": "true", "files": ["theories/A.thy"], "message": ".build/tasks/5/m.md"}))
        accepted = {"stage": "done", "kind": "review", "reviews": "5", "verdict": "accept", "round": 0}
        log = self.w.state / "v2.log"
        made = "task 5 was accepted and stood in review with no review due: its commit is made"

        def run(task=None, review=None, held=False):
            log.write_text("")
            self.w.set_st(tasks={"5": dict({"stage": "reviewing", "kind": "build", "review_tasks": ["6"]}, **(task or {})),
                                 "6": dict(accepted, **(review or {}))})
            marker = self.w.state / v2.GRAPH_HELD
            marker.write_text("x") if held else (marker.unlink() if marker.exists() else None)
            self.run_watchdog()
            return self.w.st()["tasks"]["5"].get("stage"), made in log.read_text()

        self.assertEqual(run(review={"verdict": None}), ("reviewing", False))  # its review is still to be given
        self.assertEqual(run(task={"reviewing": "review-6"}), ("reviewing", False))  # a review of it runs: it judges
        self.assertEqual(run(held=True), ("reviewing", False))                # the graph held: the planner's order first
        final.unlink()
        self.assertEqual(run(), ("reviewing", False))                         # no final job: nothing of it to commit
        final.write_text(json.dumps({"check": "true", "files": ["theories/A.thy"], "message": ".build/tasks/5/m.md"}))
        stage, said = run()
        self.assertTrue(said)                                                 # accepted and handed over: committed,
        self.assertNotEqual(stage, "reviewing")                               # whatever its commit then finds

    def test_the_dispatch_runs_after_the_care(self):
        self.w.task("1", BRIEF)
        self.w.set_st(queue=["1"])
        self.run_watchdog()
        self.assertEqual(self.forked("implement-"), ["implement-1"])


class HeldIndexTests(unittest.TestCase):
    """The generated indexes the bases hold follow main (watchdog.held_indexes): made only by a build of a base, what the
    parts hold of them never changed between builds, and the delta, the stale lines, what is pending and the parts'
    accounts were all blind to them (found by the simulation of the run of 09-21/22, 2026-09-23)."""

    def git(self, *args):
        import subprocess
        return subprocess.run(["git", "-C", self.repo, *args], capture_output=True, text=True, check=True).stdout

    def setUp(self):
        import tempfile
        self.temp = tempfile.TemporaryDirectory()
        self.repo = self.temp.name
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.email", "t@example.org")
        self.git("config", "user.name", "t")
        self.commit("DECISIONS.md", "## One\n")

    def tearDown(self):
        self.temp.cleanup()

    def commit(self, name, text):
        Path(self.repo, name).write_text(text)
        self.git("add", name)
        self.git("commit", "-q", "-m", name)

    def test_the_held_indexes_are_made_again_once_for_each_commit_of_main(self):
        import select_base_load
        made = []
        with patch.object(v2, "PROJECT", self.repo), patch.object(watchdog, "STATE", self.repo), \
                patch.object(select_base_load, "refresh_indexes", lambda who=None: made.append(who)):
            watchdog.held_indexes()
            watchdog.held_indexes()
            self.assertEqual(made, [None])                                # every base's, once for this commit
            self.commit("DECISIONS.md", "## One\n\n## Two\n")          # a decision lands
            watchdog.held_indexes()
            self.assertEqual(made, [None, None])

    def test_the_indexes_are_made_before_the_layers_and_the_deltas_read_them(self):
        order = []
        names = ("planner_mail", "finishing", "holds", "held_indexes", "layers", "deltas", "isabelle_snapshot")
        patches = [patch.object(watchdog, n, (lambda n: lambda: order.append(n))(n)) for n in names]
        patches += [patch.object(v2, n, lambda: None) for n in ("lands_when_free", "archive")]
        patches.append(patch.object(v2, "peek", lambda: {"sessions": {}}))
        for p in patches:
            p.start()
        try:
            watchdog.watch()
        finally:
            for p in reversed(patches):
                p.stop()
        self.assertLess(order.index("held_indexes"), order.index("layers"))
        self.assertLess(order.index("layers"), order.index("deltas"))


if __name__ == "__main__":
    unittest.main()
