"""v2.py: the forms, the state and the mail, the task lock, and the flows between the knowledge base, planning
episodes, the producing and supporting sessions, consultations and the finalizer, run in a throwaway world with a fake
`claude` (fakes.py)."""
import json
import subprocess
import os
from pathlib import Path
import sys
import threading
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
from fakes import BRIEF, BRIEF_TASK, PLANNER_STATE, RESULT, REVIEW_TASK  # noqa: E402
import v2  # noqa: E402

NODE = "Serves: the reach of a state\nDeliverable: a theory of reach\nDecided: reach is a closure\n"
VERDICT = "Verdict: {v}\n## Summary\nThe readiness theory is in place.\n## Findings\n{f}\n## Follow-ups\nMeasure the reach.\n"


class FormTests(unittest.TestCase):
    def test_a_brief_in_form_passes_and_its_fields_are_read_whole(self):
        self.assertEqual(v2.brief_problems(BRIEF), [])
        self.assertEqual(v2.brief_kind(BRIEF), "build")
        self.assertEqual(v2.deliverables(BRIEF), ["theories/Ready.thy"])
        self.assertEqual(v2.inputs(BRIEF), ["theories/Base.thy", "Base.base_def", "DECISIONS.md"])

    def test_fields_may_run_over_lines_and_end_at_the_next_field(self):
        brief = BRIEF.replace("Deliverable: `theories/Ready.thy`, the readiness theory",
                              "Deliverable:\n- `theories/Ready.thy`: the theory\n- `DECISIONS.md`: the decision")
        brief = brief.replace("Inputs: `theories/Base.thy:1-40`, `Base.base_def`, and the decision in `DECISIONS.md`",
                              "Inputs:\n- `theories/Base.thy:1-40`\n- **Decided:** not a field here")
        self.assertEqual(v2.brief_problems(brief), [])
        self.assertEqual(v2.deliverables(brief), ["theories/Ready.thy", "DECISIONS.md"])
        self.assertEqual(v2.inputs(brief), ["theories/Base.thy"])
        self.assertNotIn("the proof", v2.section(brief, "Plan"))

    def test_a_brief_out_of_form_is_told_what_is_missing(self):
        problems = v2.brief_problems("Kind: refactor\nServes: x\nDeliverable: a theory\nPlan:\n1. one step\n")
        self.assertIn("the brief has no `Acceptance:` line", problems)
        self.assertTrue(any(p.startswith("Kind must be one of") for p in problems))
        self.assertTrue(any("at least two numbered steps" in p for p in problems))
        self.assertIn("the Deliverable names no file in backticks", problems)
        with patch.object(v2, "PROJECT", str(HERE.parent.parent)):
            problems = v2.brief_problems(BRIEF.replace("`theories/Ready.thy`", "`theories/`"))
        self.assertTrue(any("names the directory `theories/`" in p for p in problems), problems)

    def test_every_kind_is_briefed_in_the_same_form_sized_to_one_window(self):
        self.assertEqual(v2.brief_problems(BRIEF_TASK), [])
        self.assertEqual(v2.brief_problems(REVIEW_TASK.format(task="4")), [])
        self.assertEqual(v2.reviewed(REVIEW_TASK.format(task="4")), "4")
        self.assertIn("a review task names the task it reviews on its `Reviews:` line",
                      v2.brief_problems(REVIEW_TASK.replace("Reviews: `{task}`\n", "")))
        self.assertIn("the brief has no `Size:` line", v2.brief_problems(BRIEF.replace("Size: about 120K tokens of work\n", "")))
        self.assertIn("the Size is an estimate in tokens of work (for example `Size: about 150K`)",
                      v2.brief_problems(BRIEF.replace("about 120K tokens of work", "a third of a window")))
        self.assertIn(f"the Size (900K) is beyond what a build session has room for ({v2.room_of('build') // 1000}K): "
                      "split the task", v2.brief_problems(BRIEF.replace("about 120K", "about 900K")))
        design = BRIEF.replace("Kind: build", "Kind: design")
        self.assertEqual(v2.brief_problems(design.replace("about 120K", "about 250K")), [])  # no separate cap
        self.assertIn(f"the Size (900K) is beyond what a design session has room for ({v2.room_of('design') // 1000}K): "
                      "split the task", v2.brief_problems(design.replace("about 120K", "about 900K")))

    def test_results_verdicts_and_the_planners_state(self):
        self.assertEqual(v2.result_problems(RESULT.format(status="partial")), [])
        self.assertIn("the `Status:` line must say done, partial or blocked", v2.result_problems("Status: finished\n"))
        self.assertEqual(v2.verdict_problems(VERDICT.format(v="accept", f=""), "accept"), [])
        self.assertEqual(v2.verdict_problems("## Summary\nfine\n", "reject"),
                         ["a rejection lists its blocking findings under `## Findings`"])
        self.assertEqual(v2.part(VERDICT.format(v="reject", f="- the lemma is unused"), "Findings"), "- the lemma is unused")
        self.assertEqual(v2.planner_state_problems(PLANNER_STATE), [])
        self.assertIn("HANDOFF.md has no `## Open` section", v2.planner_state_problems("## Graph\n## Now\n"))

    def test_what_each_role_produces_and_reads(self):
        with patch.object(v2, "BUILD", "/nonexistent"):
            self.assertEqual(v2.deliverables_of({"role": "reviewer", "task": "4"})["deliverables"], [".build/tasks/4/review.md"])
            self.assertTrue(v2.deliverables_of({"role": "task-designer", "task": "4"})["task_tools"])
            self.assertEqual(v2.deliverables_of({"role": "planner", "name": "plan-2"})["drafts"], ".build/plans/plan-2/")
            self.assertEqual(v2.deliverables_of({"role": "implementer", "task": "4"})["drafts"], ".build/tasks/4/")
        for role, statements in (("planner", True), ("task-designer", True), ("kb", True), ("implementer", False),
                                 ("reviewer", False), ("designer", False)):  # the designer forks the middle base
            self.assertEqual(v2.statements_only({"role": role}), statements, role)

    def test_iso_compares_with_the_transcripts_timestamps(self):
        t = 1_789_000_000.25
        self.assertEqual(v2.iso(t), fakes.iso(t))
        self.assertLess(v2.iso(t), fakes.iso(t + 0.001))

    def test_every_role_has_a_protocol_with_nothing_left_unfilled(self):
        values = dict(NAME="x-1", ID="7", KIND="build", SUBJECT="S", BRIEF="B", STALE="st", WHAT="w", SESSION="s",
                      BEFORE="", NODE="n", WHY="y", GRAPH="g", LIST="l", QID="q1", ASKER="a", TARGET="kb-1",
                      QUESTION="q", NOTE="", EVENTS="e", QUEUE="7", STATUS="s", OWNER="", HANDOFF="h", ORIGIN_NOTE="",
                      TASK="6", REVIEW="r", FIRST="")
        import re
        for role in v2.ROLES:
            text = v2.render(role, **values)
            self.assertTrue(text.startswith("You are x-1, "), role)
            self.assertEqual(re.findall(r"\{[A-Z_]+\}|\{\{[\w-]+\}\}", text), [], role)


class InProcessTests(unittest.TestCase):
    def setUp(self):
        self.world = fakes.World()
        self.patches = [patch.object(v2, "STATE", str(self.world.state)),
                        patch.object(v2, "TASKS", str(self.world.home / ".claude/tasks"))]
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in self.patches:
            p.stop()
        self.world.close()

    def test_mail_is_taken_in_order_once(self):
        self.assertEqual(v2.take_mail("plan-1"), "")
        v2.post("plan-1", "implement-3", "first")
        v2.post("plan-1", "the finalizer", "second")
        self.assertTrue(v2.has_mail("plan-1"))
        mail = v2.take_mail("plan-1")
        self.assertLess(mail.index("Message from implement-3"), mail.index("Message from the finalizer"))
        self.assertFalse(v2.has_mail("plan-1"))

    def test_roles_are_found_by_session(self):
        self.world.session("plan-1", "planner", "p")
        self.world.session("implement-2", "implementer", "w", task="2")
        self.assertEqual(v2.role_of("p")[0], "planner")
        self.assertEqual(v2.role_of("w")[1]["task"], "2")
        self.assertEqual(v2.role_of("x"), (None, None))
        self.assertEqual(v2.role_of(""), (None, None))

    def test_task_updates_take_claude_codes_lock_and_break_a_stale_one(self):
        self.world.task("5")
        lock = self.world.tasks / "5.json.lock"
        lock.mkdir()
        threading.Timer(0.3, lock.rmdir).start()
        started = time.time()
        v2.update_task("5", status="in_progress", owner="implement-5")
        self.assertGreaterEqual(time.time() - started, 0.25)
        self.assertEqual(self.world.read_task("5")["owner"], "implement-5")
        lock.mkdir()
        os.utime(lock, (time.time() - 60, time.time() - 60))
        v2.update_task("5", status="completed")
        self.assertEqual(self.world.read_task("5")["status"], "completed")
        self.assertFalse(lock.exists())

    def test_setting_changes_aside_never_stops_the_orchestration(self):
        def broken(*_):
            raise OSError("disk full")
        real = v2._leave
        v2._leave = broken
        try:
            self.assertIn("could not be set aside (OSError('disk full'))", v2.leave("4", "lost"))
        finally:
            v2._leave = real

    def test_warmth_follows_the_last_hit_down_the_origins(self):
        self.world.session("kb-1", "kb", "k", origin="max", warm=False)
        self.world.session("ask-q1", "consultant", "a", origin="kb-1", warm=False)
        self.assertFalse(v2.warm("kb-1"))
        v2.hit_chain("ask-q1")
        self.assertTrue(v2.warm("kb-1") and v2.warm("ask-q1"))
        self.assertTrue((self.world.state / "max-base.hit").exists())
        self.world.hit("kb-1", age=v2.WARM_MAX + 5)
        self.assertFalse(v2.warm("kb-1"))


class Flow(unittest.TestCase):
    """A world with a sealed base, a sealed and warm knowledge base, and HANDOFF.md in the planner's form."""

    def setUp(self):
        self.w = fakes.World()
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)

    def tearDown(self):
        self.w.close()

    def forks(self, name_prefix=""):
        return [c["args"] for c in self.w.calls("--bg") if "--fork-session" in c["args"] and "-n" in c["args"]
                and c["args"][c["args"].index("-n") + 1].startswith(name_prefix)]

    def resumes(self, sid=None):
        return [c["args"] for c in self.w.calls("--bg") if "--fork-session" not in c["args"]
                and (sid is None or c["args"][2] == sid)]

    def s(self, name):
        return self.w.st()["sessions"][name]

    def heard(self):
        """What the planner has been told: the events waiting for an episode, and those given to episodes."""
        return " ".join(e["text"] for e in self.w.st()["events"]) + " " + " ".join(a[-1] for a in self.forks("plan-"))

    def t(self, tid):
        return self.w.st()["tasks"].get(tid, {})

    def as_(self, name, *args):
        return self.w.v2(*args, env=self.w.as_session(self.s(name)["sid"]))


class StartTests(Flow):
    def setUp(self):
        self.w = fakes.World()

    def test_the_first_start_builds_the_knowledge_base_then_a_planning_episode_takes_up_the_handoff(self):
        self.assertIn("not started", self.w.v2("start"))  # no base yet
        self.w.base()
        self.w.write("HANDOFF.md", "# Handoff\n\n## Work order\nT3\n")
        self.assertEqual(self.w.v2("start"), "active; knowledge base kb-1")
        (fork,) = self.forks("kb-")
        self.assertEqual(fork[fork.index("--resume") + 1], "base-sid")
        self.assertTrue(fork[fork.index("--settings") + 1].endswith("planner-settings.json"))
        self.assertIn("You are kb-1, the knowledge base", fork[-1])
        self.assertTrue((self.w.state / "owner-directions-new.md").exists())
        self.w.v2("dispatch")
        self.assertEqual(self.forks("plan-"), [])  # the knowledge base is still loading
        self.w.reply(self.s("kb-1")["sid"], "INTEGRATED")
        self.w.v2("dispatch")
        st = self.w.st()
        self.assertEqual((st["kb"], self.s("kb-1")["kb_state"]), ("kb-1", "sealed"))
        (plan,) = self.forks("plan-")
        self.assertEqual(plan[plan.index("--resume") + 1], self.s("kb-1")["sid"])
        self.assertIn("You are plan-1, a planning episode", plan[-1])
        self.assertIn("## The first episode: a new task graph", plan[-1])
        self.assertIn("they do not bind it", plan[-1])  # the history and the handoff inform the graph
        self.assertIn("uncommitted changes that no task owns yet: none", plan[-1])
        self.assertNotIn("{UNOWNED}", plan[-1])
        self.assertEqual(st["events"], [])
        self.w.task("1")  # once a graph exists, later episodes are ordinary
        self.w.set_st(events=[{"at": "2026-09-19T00:00:00", "from": "x", "text": "e"}], plan_ended=1.0)
        self.assertEqual(v2_first(self.w), "")


def v2_first(world):
    """The first episode's part, as v2 renders it in that world."""
    code = f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; print(v2.first_episode(), end='')"
    return subprocess.run([sys.executable, "-c", code], env=world.env, capture_output=True, text=True).stdout


class PlanningTests(Flow):
    def test_an_episode_queues_ends_with_notes_and_the_knowledge_base_integrates_them(self):
        self.w.task("1")
        self.w.task("2", description=BRIEF_TASK, subject="Reach")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json", origin="kb-1")
        self.assertEqual(self.as_("plan-1", "queue", "1", "2"), "queued")
        # the queue dispatches: task 1, a build, to the producing slot; task 2, a brief task, to a task designer
        (impl,) = self.forks("implement-")
        self.assertEqual(impl[impl.index("--resume") + 1], "base-sid")  # the high base falls back to the max one
        self.assertIn("Deliverable: `theories/Ready.thy`", impl[-1])
        (brief,) = self.forks("brief-")
        self.assertIn("Reach", brief[-1])
        self.assertEqual((self.t("1")["stage"], self.t("2")["stage"]), ("running", "running"))
        self.assertEqual(self.w.read_task("1")["status"], "in_progress")
        self.assertIn("refused: v2.py planned --notes FILE", self.as_("plan-1", "planned"))
        self.w.write("HANDOFF.md", "# nothing\n")
        self.w.write(".build/plans/plan-1/notes.md", "Decided: readiness is a path.")
        self.assertIn("not in the form of the planner's state", self.as_("plan-1", "planned", "--notes", ".build/plans/plan-1/notes.md"))
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.assertEqual(self.as_("plan-1", "planned", "--notes", ".build/plans/plan-1/notes.md"), "planned. End your turn now.")
        self.assertEqual(self.s("plan-1")["state"], "done")
        (integration,) = self.resumes("kbsid")
        self.assertTrue(integration[3].startswith("[harness] Integrate these notes"))
        self.assertIn("readiness is a path", integration[3])
        self.assertEqual(self.s("kb-1")["kb_state"], "integrating")
        self.assertIn("readiness is a path", (self.w.state / "kb-1-notes.md").read_text())
        self.w.reply("kbsid", "INTEGRATED")
        self.w.v2("dispatch")
        self.assertEqual((self.s("kb-1")["kb_state"], self.s("kb-1")["state"]), ("sealed", "done"))
        # grown past the room its forks need: a new knowledge base loads HANDOFF.md (not the notes) and takes over
        self.assertEqual(v2.KB_MAX, v2.SOFT - v2.ROOM["planner"])
        st = self.w.st()
        st["sessions"]["kb-1"]["context"] = v2.KB_MAX + 1
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        (new,) = self.forks("kb-")
        self.assertIn("Read now, together, what the library does not hold: HANDOFF.md", new[-1])
        self.assertNotIn("notes.md", new[-1])
        self.w.reply(self.s("kb-2")["sid"], "INTEGRATED")
        self.w.v2("dispatch")
        self.assertEqual(self.w.st()["kb"], "kb-2")
        self.assertTrue(self.s("kb-1")["released"])

    def test_a_fresh_knowledge_base_near_its_limit_asks_for_condensing_and_a_base_rebuild(self):
        self.w.set_st(kb_building="kb-2")
        self.w.session("kb-2", "kb", "k2", kb_state="building", settings="planner-settings.json", started=time.time() - 5)
        self.w.transcript("k2", [fakes.assistant("m1", fakes.iso(time.time()), [{"type": "text", "text": "INTEGRATED"}],
                                                 usage={"input_tokens": 0, "cache_read_input_tokens": v2.KB_MAX - 10_000,
                                                        "cache_creation_input_tokens": 0, "output_tokens": 5})])
        self.w.v2("dispatch")
        self.assertIn("condense HANDOFF.md", self.heard())
        self.assertIn("a base rebuild is due (the owner's)", (self.w.state / "v2.log").read_text())

    def test_events_start_an_episode_and_a_lost_one_gives_them_back(self):
        self.w.set_st(events=[{"at": time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(time.time() - 60)),
                               "from": "review-3", "text": "Task 3 accepted."}])
        self.w.v2("dispatch")
        (plan,) = self.forks("plan-")
        self.assertIn("from review-3: Task 3 accepted.", plan[-1])
        self.assertEqual(self.w.st()["events"], [])
        self.w.set_rows([r for r in self.w.rows() if r["name"] != "plan-1"])
        for _ in range(3):
            self.w.run("watchdog.py")
        again = self.forks("plan-")[1]  # the next episode is given them again
        self.assertIn("Task 3 accepted.", again[-1])
        self.assertIn("The planning episode plan-1 is gone before it ended", again[-1])

    def test_a_designer_forks_the_middle_base_and_gathers_the_handoff(self):
        self.w.base("xhigh", sid="xhigh-sid")
        self.w.task("4", description=BRIEF.replace("Kind: build", "Kind: design"))
        self.w.set_st(queue=["4"])
        self.w.v2("dispatch")
        (design,) = self.forks("design-")
        self.assertEqual(design[design.index("--resume") + 1], "xhigh-sid")
        self.assertTrue(design[design.index("--settings") + 1].endswith("worker-settings.json"))
        self.assertIn("Open your first gather with HANDOFF.md", design[-1])

class TaskTests(Flow):
    def setUp(self):
        super().setUp()
        self.remote = self.w.repository()
        self.w.task("1")
        self.w.write("theories/Base.thy", "theory Base imports Main begin\ndefinition base where \"base = True\"\nend\n")
        self.w.set_st(queue=["1"])
        self.w.v2("dispatch")
        self.impl = "implement-1"

    def finish(self, check="true"):
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.w.write(".build/tasks/1/commit.md", "Add readiness\n\nValidation: checked.\n")
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="done"))
        self.assertIn("prepared", self.as_(self.impl, "finalize", "1", "--check", check, "--files", "theories/Ready.thy",
                                           "--message", ".build/tasks/1/commit.md"))
        return self.as_(self.impl, "result", "1")

    def verdict(self, name, v, findings=""):
        self.w.write(".build/tasks/1/review.md", VERDICT.format(v=v, f=findings))
        return self.as_(name, "verdict", "1", v, "--file", ".build/tasks/1/review.md")

    def test_one_finalization_at_a_time_and_a_withdrawn_task_is_announced(self):
        self.w.write(".build/tasks/9/finalize.json", json.dumps({"check": "true", "files": ["theories/X.thy"], "message": "m"}))
        st = self.w.st()
        st["tasks"]["9"] = {"stage": "reviewing"}
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.write("theories/Ready.thy", "x")
        self.w.write(".build/tasks/1/commit.md", "m")
        out = self.as_(self.impl, "finalize", "1", "--check", "true", "--files", "theories/Ready.thy", "--message",
                       ".build/tasks/1/commit.md")
        self.assertIn("refused: task 9 holds the working tree", out)
        self.w.write("theories/X.thy", "task 9's theory\n")
        code = (f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n"
                "v2.own('9', ['theories/X.thy'])\nwith v2.state() as st: v2.to_planner(st, '9', 'the finalizer', 'failed twice')")
        subprocess.run([sys.executable, "-c", code], env=self.w.env, check=True)
        self.assertFalse((self.w.project / "theories/X.thy").exists())  # set aside: no longer in the working tree
        self.w.v2("dispatch")
        self.assertIn("Task 9 went back to the planner", json.dumps(self.w.mail(self.impl)))
        self.assertIn("prepared", self.as_(self.impl, "finalize", "1", "--check", "true", "--files", "theories/Ready.thy",
                                           "--message", ".build/tasks/1/commit.md"))

    def test_the_gather_prints_every_source_at_once_and_the_next_opens_after_production(self):
        out = self.as_(self.impl, "step", "1", "1", "theories/Base.thy:2-2", "Base.base")
        self.assertIn("== theories/Base.thy:2-2\n     2\tdefinition base", out)
        self.assertIn("== Base.base\n== theories/Base.thy:2", out)
        self.assertIn("step 1 has not produced yet", self.as_(self.impl, "step", "1", "2", "theories/Base.thy"))
        meter = self.w.state / f"work-{self.s(self.impl)['sid']}.json"
        m = json.loads(meter.read_text())
        self.assertEqual(m["reads"][str(self.w.project / "theories/Base.thy")]["ranges"], [[2, 2]])
        m["productions"] = 1
        meter.write_text(json.dumps(m))
        self.assertIn("Step 2 of task 1", self.as_(self.impl, "step", "1", "2", "theories/Base.thy"))
        self.assertIn("you work on task 1, not 9", self.as_(self.impl, "step", "9", "1", "x"))

    def test_a_result_is_refused_while_the_sessions_own_jobs_run(self):
        self.w.transcript(self.s(self.impl)["sid"], [{"type": "user", "message": {"content": [{"type": "tool_result",
                          "content": "Command running in background with ID: bq1. Output is being written to: x"}]}}])
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="partial"))
        self.assertIn("your background jobs bq1 are still running", self.as_(self.impl, "result", "1"))
        self.assertIn("your runs bq1 are going on: park for them", self.as_(self.impl, "park", "fix"))
        self.assertTrue(self.as_(self.impl, "escalate", "--efficiency", "slow").startswith("reported"))  # it continues
        out = self.as_(self.impl, "park", "run")
        self.assertIn("parked: end your turn now; another worker produces meanwhile", out)
        self.assertEqual(self.t("1")["parked"]["for"], "run")
        self.assertEqual(self.w.v2("status").split("producing: ")[1].split("\n")[0], "-")  # the slot is free

    def test_parked_for_its_run_the_slot_goes_to_another_worker_and_the_task_comes_back_after(self):
        sid = self.s(self.impl)["sid"]
        job = lambda done: self.w.transcript(sid, [{"type": "user", "message": {"content": [{"type": "tool_result",
            "content": "Command running in background with ID: bq1. Output is being written to: x"}]}}] + ([{
            "type": "user", "message": {"content": "<task-notification><task-id>bq1</task-id><status>completed</status>"}}]
            if done else []))
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.own('1', ['theories/Ready.thy'])"], env=self.w.env, check=True)
        job(done=False)
        self.assertIn("parked", self.as_(self.impl, "park", "run"))
        self.w.task("2", subject="The next task")
        self.w.set_st(queue=["1", "2"])
        self.w.set_rows([r for r in self.w.rows() if r["name"] != self.impl])
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("implement-2")), 1)  # the slot went to another worker
        self.assertTrue((self.w.project / "theories/Ready.thy").exists())  # the run still reads the task's changes
        refusal = self.w.run("work_meter.py", "guard", stdin=json.dumps({
            "session_id": self.s("implement-2")["sid"], "tool_name": "Edit", "tool_input": {"file_path": str(
                self.w.project / "ROOT")}, "cwd": str(self.w.project), "hook_event_name": "PreToolUse"}))[1]
        self.assertIn("Task 1 holds the working tree (parked for its run, which reads its changes)", refusal)
        job(done=True)
        self.w.v2("dispatch")
        self.assertFalse((self.w.project / "theories/Ready.thy").exists())  # the run has ended: set aside, tree free
        self.assertEqual(self.t("1")["stage"], "parked")  # the slot is implement-2's
        st = self.w.st()
        st["sessions"]["implement-2"]["state"] = "done"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")
        self.assertIn("The run you parked for has ended", self.resumes(sid)[-1][3])
        self.assertTrue((self.w.project / "theories/Ready.thy").exists())  # its changes are back

    def test_a_session_still_working_is_told_when_the_fix_it_reported_lands(self):
        self.as_(self.impl, "escalate", "--efficiency", "the closure is quadratic")
        self.w.task("3", subject="Linear closure")
        self.w.session("plan-2", "planner", "p2", settings="planner-settings.json", origin="kb-1")
        self.as_("plan-2", "after", "1", "3")
        self.w.v2("dispatch")
        self.assertEqual(self.w.mail(self.impl), [])
        self.w.task("3", subject="Linear closure", status="completed")
        self.w.v2("dispatch")
        self.assertIn("Task 3, the fix of the performance problem you reported, has landed", json.dumps(self.w.mail(self.impl)))
        self.w.v2("dispatch")
        self.assertEqual(len(self.w.mail(self.impl)), 1)  # told once

    def test_a_statements_reader_gathers_statements(self):
        self.w.session("brief-5", "task-designer", "b5", task="5", settings="planner-settings.json")
        self.w.write("theories/Proof.thy", 'theory Proof imports Main begin\nlemma l: "True"\n  by simp\nend\n')
        out = self.w.v2("step", "5", "1", "theories/Proof.thy", "tools/x.py", "diff", env=self.w.as_session("b5"))
        self.assertIn("proof", out)
        self.assertNotIn("by simp", out)
        self.assertIn("(refused: the statements of your task are your reading", out)

    def test_a_task_is_checked_reviewed_fixed_once_reviewed_again_and_committed(self):
        self.assertIn("recorded", self.finish())
        self.assertEqual(self.t("1")["stage"], "reviewing")
        (review,) = self.forks("review-")
        self.assertIn("produced by implement-1", review[-1])
        self.assertIn("refused: the verdict is not in form", self.as_("review-1", "verdict", "1", "reject", "--file", "nope"))
        self.assertIn("rejected task 1", self.verdict("review-1", "reject", "- `ready_def` duplicates `base_def`"))
        # one quick fix: the implementer resumed with every finding
        self.assertEqual(self.t("1")["stage"], "fixing")
        fix = self.resumes(self.s(self.impl)["sid"])[-1]
        self.assertIn("duplicates `base_def`", fix[3])
        self.assertIn(f"at most {v2.FIX_MINUTES} minutes", fix[3])
        self.assertTrue(self.s(self.impl).get("fix"))
        self.assertIn("recorded", self.finish())
        # the re-review: the same reviewer, resumed
        self.assertEqual(self.t("1")["stage"], "reviewing")
        self.assertIn("Judge those findings and whatever the fix itself broke", self.resumes(self.s("review-1")["sid"])[-1][3])
        self.assertIn("accepted task 1", self.verdict("review-1", "accept"))
        t = self.t("1")
        self.assertEqual(t["stage"], "done")
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add readiness\n")
        self.assertEqual(self.w.git("rev-parse", "--short", "main", cwd=self.remote).strip(),
                         json.loads((self.w.project / ".build/tasks/1/finalized.json").read_text())["commit"])
        self.assertEqual(self.w.read_task("1")["status"], "completed")
        ev = self.heard()
        self.assertIn("is committed as", ev)
        self.assertIn("The readiness theory is in place. Follow-ups proposed: Measure the reach.", ev)
        self.assertTrue(self.s(self.impl)["released"] and self.s("review-1")["released"])

    def test_a_second_rejection_and_a_second_failed_check_go_to_the_planner(self):
        self.finish()
        self.verdict("review-1", "reject", "- a")
        self.finish()
        self.verdict("review-1", "reject", "- a again")
        self.assertEqual(self.t("1")["stage"], "planner")
        self.assertIn("rejected again after its fix round", self.heard())

    def test_a_failed_check_gets_one_quick_fix(self):
        self.finish(check="echo '*** Failed to finish proof'; exit 1")
        self.assertEqual(self.t("1")["stage"], "fixing")
        self.assertIn("Failed to finish proof", self.resumes(self.s(self.impl)["sid"])[-1][3])
        self.finish(check="exit 1")
        self.assertEqual(self.t("1")["stage"], "planner")
        self.assertIn("failed its check again", self.heard())

    def test_a_cold_session_is_not_resumed_for_its_fix_but_a_fixer_starts(self):
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="done"))
        self.w.write("theories/Ready.thy", "x")
        self.w.write(".build/tasks/1/commit.md", "m")
        self.as_(self.impl, "finalize", "1", "--check", "exit 1", "--files", "theories/Ready.thy", "--message",
                 ".build/tasks/1/commit.md")
        self.w.hit(self.impl, age=v2.WARM_MAX + 60)  # its cache has expired
        with open(self.w.state / "hits" / self.impl) as _:
            pass
        env = dict(self.w.as_session(self.s(self.impl)["sid"]))
        self.w.run("v2.py", "result", "1", env=env)
        (fixer,) = self.forks("fix-")
        self.assertIn("You are fix-1, a fixer", fixer[-1])
        self.assertEqual(self.resumes(self.s(self.impl)["sid"]), [])

    def test_a_performance_problem_is_reported_and_the_work_goes_on_until_waiting_for_the_fix_is_sooner(self):
        out = self.as_(self.impl, "escalate", "--efficiency", "the reach takes 640 s against 5")
        self.assertTrue(out.startswith("reported: continue with whatever does not depend on the fix"))
        self.assertEqual((self.t("1")["stage"], self.s(self.impl)["state"]), ("running", "working"))  # not parked
        self.assertIn("the reach takes 640 s", self.heard())
        self.w.task("3", subject="Faster reach")
        self.w.session("plan-2", "planner", "p2", settings="planner-settings.json", origin="kb-1")
        self.assertIn("task 1 is told when 3 has landed", self.as_("plan-2", "after", "1", "3"))
        out = self.as_(self.impl, "park", "fix", "nothing else is left, and the fix is sooner than the run")
        self.assertTrue(out.startswith("parked: end your turn now; another worker produces meanwhile"))
        self.assertEqual((self.t("1")["stage"], self.s(self.impl)["state"]), ("parked", "parked"))
        self.assertEqual(self.t("1")["parked"]["after"], "3")  # the fix the planner named
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "parked")
        self.w.task("3", subject="Faster reach", status="completed")
        self.w.set_rows([r for r in self.w.rows() if r["name"] != "implement-3"])
        st = self.w.st()
        for n, s in st["sessions"].items():
            if n.startswith("implement-") and n != self.impl:
                s["state"] = "done"
        st["tasks"]["9"] = {"stage": "reviewing"}  # another task's finalization holds the working tree
        self.w.write(".build/tasks/9/finalize.json", json.dumps({"check": "true", "files": ["theories/X.thy"], "message": "m"}))
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")  # its wait is over: the slot is its before any new task
        resumed = self.resumes(self.s(self.impl)["sid"])[-1][3]
        self.assertIn("has landed (task 3)", resumed)
        self.assertIn("Task 9 holds the working tree now: draft under .build/tasks/1/ meanwhile", resumed)
        st = self.w.st()
        st["tasks"]["9"]["stage"] = "done"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertIn("it is yours", json.dumps(self.w.mail(self.impl)))  # told when the tree is free


class ConsultationTests(Flow):
    def setUp(self):
        super().setUp()
        self.w.task("0", description=BRIEF.replace("Kind: build", "Kind: design"), status="completed")
        self.w.task("1", blockedBy=["0"])
        self.w.session("design-0", "designer", "d0", task="0", state="done", live=False,
                       settings="planner-settings.json", origin="kb-1")
        self.w.session("implement-1", "implementer", "i1", task="1")
        self.w.set_st(tasks={"1": {"stage": "running", "session": "implement-1"}})

    def test_a_question_to_the_knowledge_base_is_answered_by_a_fork_of_it(self):
        out = self.w.v2("ask", "--to", "kb", "Is readiness a path?", env=self.w.as_session("i1"))
        self.assertTrue(out.startswith("asked as q1 (the knowledge base)"))
        (ask,) = self.forks("ask-")
        self.assertEqual(ask[ask.index("--resume") + 1], "kbsid")
        self.assertTrue(ask[ask.index("--settings") + 1].endswith("planner-settings.json"))
        self.assertIn("Is readiness a path?", ask[-1])
        self.assertEqual(self.w.st()["asks"]["q1"]["state"], "open")
        sid = self.s("ask-q1")["sid"]
        self.assertEqual(self.w.v2("reply", "q1", "Yes: DECISIONS.md, readiness.", env=self.w.as_session(sid)),
                         "answered; end your turn")
        self.assertEqual(self.s("ask-q1")["state"], "done")
        self.assertIn("Yes: DECISIONS.md, readiness.", self.w.mail("implement-1")[0]["text"])  # busy: its hooks deliver

    def test_a_question_to_a_warm_author_forks_the_author_and_a_cold_one_the_knowledge_base(self):
        self.w.v2("ask", "--to", "designer", "Why a path?", env=self.w.as_session("i1"))
        ask = self.forks("ask-")[0]
        self.assertEqual(ask[ask.index("--resume") + 1], "d0")
        self.w.v2("reply", "q1", "Because.", "--decision", env=self.w.as_session(self.s("ask-q1")["sid"]))
        self.assertIn("decides something not decided before", self.heard())
        self.assertIn("Because.", self.resumes("kbsid")[-1][3])  # integrated into the knowledge base at once
        self.w.hit("design-0", age=v2.WARM_MAX + 60)
        self.w.v2("ask", "--to", "designer", "Why a closure?", env=self.w.as_session("i1"))
        self.assertEqual(len(self.forks("ask-")), 1)  # the knowledge base is integrating: no fork of it meanwhile
        self.w.reply("kbsid", "INTEGRATED")
        self.w.v2("dispatch")
        ask = self.forks("ask-")[1]
        self.assertEqual(ask[ask.index("--resume") + 1], "kbsid")
        self.assertIn("whose cache has expired", ask[-1])

    def test_several_questions_are_answered_at_once_and_one_that_must_wait_holds_up_no_other(self):
        for q in ("Is readiness a path?", "Is reach a closure?", "Why keys?"):
            self.w.v2("ask", "--to", "kb", q, env=self.w.as_session("i1"))
        self.assertEqual(len(self.forks("ask-")), 3)  # three consultations of the knowledge base run side by side
        st = self.w.st()
        st["sessions"]["kb-1"]["kb_state"] = "integrating"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("ask", "--to", "kb", "And the verdict?", env=self.w.as_session("i1"))
        self.w.v2("ask", "--to", "designer", "Why a path?", env=self.w.as_session("i1"))
        asks = self.forks("ask-")
        self.assertEqual(len(asks), 4)  # the designer's question does not wait behind the knowledge base's
        self.assertEqual(asks[-1][asks[-1].index("--resume") + 1], "d0")
        self.assertEqual(self.w.st()["asks"]["q4"]["state"], "queued")

    def test_the_planner_tells_a_working_session_and_a_consultation_asks_nothing(self):
        self.w.session("plan-3", "planner", "p3", settings="planner-settings.json", origin="kb-1")
        self.assertIn("refused: no session works on task 9", self.as_("plan-3", "tell", "9", "x"))
        self.assertEqual(self.as_("plan-3", "tell", "1", "The review changes the statement: keep the old one."),
                         "told implement-1")
        self.assertIn("The review changes the statement", json.dumps(self.w.mail("implement-1")))
        self.assertIn("refused: telling a working session is the planner's", self.as_("implement-1", "tell", "1", "x"))
        self.w.v2("ask", "--to", "kb", "Why?", env=self.w.as_session("i1"))
        ask = self.s("ask-q1")
        self.assertIn("refused: questions are asked by the sessions working on a task",
                      self.w.v2("ask", "--to", "kb", "And this?", env=self.w.as_session(ask["sid"])))
        self.assertIn("refused: questions are asked", self.w.v2("ask", "--to", "kb", "Mine?"))  # the owner: talk.sh

    def test_a_question_to_the_planner_waits_for_the_next_episode(self):
        self.w.v2("ask", "--to", "planner", "Split the task?", env=self.w.as_session("i1"))
        self.assertIn("Question q1", self.heard())
        self.w.set_status("implement-1", "idle")
        self.w.session("plan-3", "planner", "p3", settings="planner-settings.json", origin="kb-1")
        self.assertEqual(self.w.v2("reply", "q1", "No.", env=self.w.as_session("p3")), "answered")
        self.assertIn("Answer to your question q1", self.resumes("i1")[-1][3])


class SupportTests(Flow):
    def setUp(self):
        super().setUp()
        self.w.task("1")
        self.w.task("2", description=BRIEF_TASK)
        self.w.session("implement-1", "implementer", "i1", task="1", state="done", live=False)
        self.w.session("implement-9", "implementer", "i9", task="9")  # producing

    def test_one_supporting_session_at_a_time_the_brief_first_when_nothing_is_ready(self):
        self.w.set_st(queue=["2"], tasks={"1": {"stage": "reviewing", "kind": "build", "session": "implement-1"}})
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("brief-")), 1)
        self.assertEqual(self.forks("review-"), [])
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("brief-")), 1)  # one at a time

    def test_the_review_first_when_something_is_ready(self):
        self.w.task("3")
        self.w.set_st(queue=["2", "3"], tasks={"1": {"stage": "reviewing", "kind": "build", "session": "implement-1"}})
        self.w.v2("dispatch")
        self.assertEqual((len(self.forks("review-")), len(self.forks("brief-"))), (1, 0))

    def test_an_unformed_task_is_not_taken_up_and_the_planner_is_told(self):
        self.w.task("4", description=NODE)
        self.w.set_st(queue=["4"], sessions={k: v for k, v in self.w.st()["sessions"].items() if k != "implement-9"})
        self.w.v2("dispatch")
        self.assertEqual(self.forks("implement-4") + self.forks("brief-4"), [])
        self.assertIn("Task 4 is queued but its brief is not in form", self.heard())

    def test_a_brief_task_records_its_tasks_every_build_with_a_review_task(self):
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        (fork,) = self.forks("brief-")
        self.assertIn("## Your brief task", fork[-1])
        self.assertIn("reach is a closure", fork[-1])
        sid = self.s("brief-2")["sid"]
        self.w.task("5", description=BRIEF)
        refused = self.w.v2("briefed", "2", "5", env=self.w.as_session(sid))
        self.assertIn("task 5 is a build task without a review task", refused)
        self.w.task("6", description=REVIEW_TASK.format(task="5"))
        self.assertEqual(self.w.v2("briefed", "2", "5", "6", env=self.w.as_session(sid)), "briefed. End your turn now.")
        st = self.w.st()
        self.assertEqual(st["queue"], ["2", "5", "6", "7"])
        self.assertEqual((st["tasks"]["5"]["review_tasks"], st["tasks"]["6"]["reviews"]), (["6"], "5"))
        self.assertEqual((st["tasks"]["2"]["stage"], self.w.read_task("2")["status"]), ("done", "completed"))
        self.assertEqual(st["tasks"]["5"]["briefed_by"], "brief-2")


class ReviewTaskTests(Flow):
    """A build with two review tasks: committed only when both accept; one rejection sends every finding to its fix."""

    def setUp(self):
        super().setUp()
        self.w.repository()
        self.w.task("5")
        self.w.task("6", description=REVIEW_TASK.format(task="5"))
        self.w.task("7", description=REVIEW_TASK.format(task="5"))
        self.w.session("implement-5", "implementer", "i5", task="5", state="done", live=False)
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.w.write(".build/tasks/5/commit.md", "Add readiness\n")
        self.w.write(".build/tasks/5/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Ready.thy"], "message": ".build/tasks/5/commit.md"}))
        self.w.set_st(queue=["5", "6", "7"], tasks={
            "5": {"stage": "reviewing", "kind": "build", "session": "implement-5", "review_tasks": ["6", "7"]},
            "6": {"stage": "ready", "kind": "review", "reviews": "5"}, "7": {"stage": "ready", "kind": "review", "reviews": "5"}})

    def verdict(self, rid, v, findings=""):
        self.w.write(f".build/tasks/{rid}/review.md", VERDICT.format(v=v, f=findings))
        return self.as_(f"review-{rid}", "verdict", rid, v, "--file", f".build/tasks/{rid}/review.md")

    def test_both_reviews_accept_and_the_task_is_committed(self):
        self.w.v2("dispatch")
        (first,) = self.forks("review-")
        self.assertIn("review task 6 of task 5", first[-1])
        self.assertIn("check the definition against the decided closure", first[-1])
        self.assertIn("v2.py step 5 1 result diff log", first[-1])
        self.assertIn("its other reviews are pending", self.verdict("6", "accept"))
        self.assertEqual(self.t("5")["stage"], "reviewing")
        self.assertEqual(len(self.forks("review-")), 2)  # the second review starts when the slot is free
        self.assertIn("accepted task 5", self.verdict("7", "accept"))
        self.assertEqual(self.t("5")["stage"], "done")
        self.assertEqual([self.w.read_task(x)["status"] for x in ("5", "6", "7")], ["completed"] * 3)
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add readiness\n")

    def test_a_rejection_gathers_every_finding_and_only_the_rejecting_review_judges_again(self):
        self.w.v2("dispatch")
        self.verdict("6", "reject", "- `ready_def` duplicates `base_def`")
        self.assertEqual(self.t("5")["stage"], "reviewing")  # the other review first
        self.verdict("7", "accept")
        self.assertEqual(self.t("5")["stage"], "fixing")
        fix = [c["args"] for c in self.w.calls("--bg") if c["args"][:3] == ["--bg", "--resume", "i5"]][-1]
        self.assertIn("From 6", fix[3])
        self.assertIn("duplicates `base_def`", fix[3])
        self.w.write(".build/tasks/5/result.md", RESULT.format(status="done"))
        self.as_("implement-5", "result", "5")
        self.assertEqual(self.t("5")["stage"], "reviewing")
        again = [c["args"] for c in self.w.calls("--bg") if c["args"][:3] == ["--bg", "--resume", self.s("review-6")["sid"]]]
        self.assertIn("The findings you listed on task 5 are fixed", again[-1][3])
        self.assertEqual(len(self.forks("review-")), 2)  # review 7 accepted: it does not judge again
        self.verdict("6", "accept")
        self.assertEqual(self.t("5")["stage"], "done")


class GrowthTests(Flow):
    def test_the_graph_shows_open_tasks_and_counts_the_completed(self):
        self.w.task("1", status="completed")
        self.w.task("2")
        text = self.w.v2("graph")
        self.assertIn("- 2 [pending]", text)
        self.assertNotIn("- 1 [", text)
        self.assertIn("and 1 completed task", text)
        self.assertIn("- 1 [completed]", self.w.v2("graph", "--all"))

    def test_tasks_briefed_while_an_episode_ran_keep_their_place_in_its_order(self):
        self.w.session("plan-1", "planner", "p1", started=time.time() - 60, settings="planner-settings.json")
        self.w.task("5", BRIEF_TASK)
        self.w.task("6")
        self.w.task("7")
        self.w.set_st(queue=["5", "6"], tasks={"6": {"stage": "ready", "kind": "build", "queued_at": time.time(),
                                                      "brief_task": "5"},
                                                "7": {"stage": "ready", "queued_at": time.time() - 3600}})
        out = self.as_("plan-1", "queue", "7", "5")
        self.assertIn("kept, briefed since this episode began: 6", out)
        self.assertEqual(self.w.st()["queue"], ["7", "5", "6"])
        self.assertIn("refused", self.w.v2("queue", "7", env=self.w.as_session("kbsid")))

    def test_the_knowledge_base_is_rebuilt_before_it_outgrows_its_forks_room_and_when_its_base_is_rebuilt(self):
        st = self.w.st()
        st["sessions"]["kb-1"].update(context=v2.KB_MAX - v2.KB_MARGIN + 1000, built_context=500_000,
                                      base_sid="base-sid")
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.w.st()["kb"], "kb-1")  # it still serves while its successor loads
        self.assertTrue(self.w.st()["kb_building"].startswith("kb-2"))
        self.w.close()
        self.setUp()
        st = self.w.st()
        st["sessions"]["kb-1"].update(context=500_000, built_context=500_000, base_sid="an-older-base")
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertTrue(self.w.st()["kb_building"].startswith("kb-2"))

    def test_no_episode_starts_before_the_last_episodes_notes_are_integrated(self):
        self.w.set_st(events=[{"at": "2026-09-19T00:00:00", "from": "x", "text": "an event"}], notes=["a note"],
                      kb_building="kb-2")
        self.w.session("kb-2", "kb", "kb2sid", kb_state="building", settings="planner-settings.json")
        self.w.v2("dispatch")
        self.assertEqual(self.forks("plan-"), [])

    def test_what_nothing_refers_to_is_archived(self):
        old = time.time() - v2.ARCHIVE_AFTER - 60
        self.w.session("review-1", "reviewer", "r1", state="done", live=False, released=True, ended=old, task="1")
        self.w.session("implement-2", "implementer", "i2", state="done", live=False, released=True, ended=old, task="2")
        self.w.set_st(tasks={"1": {"stage": "done"}, "2": {"stage": "reviewing", "session": "implement-2"}},
                      asks={"q1": {"from": "x", "state": "answered", "answered": old, "asked": old, "text": "q"}})
        sys.path.insert(0, str(fakes.HERE))
        self.assertEqual(self.w.run("v2.py", "status")[0], 0)
        code = ("import sys; sys.path.insert(0, %r); import v2; print(v2.archive())" % str(fakes.HERE))
        out = subprocess.run([sys.executable, "-c", code], env=self.w.env, capture_output=True, text=True).stdout
        self.assertEqual(out.strip(), "2")
        st = self.w.st()
        self.assertNotIn("review-1", st["sessions"])
        self.assertIn("implement-2", st["sessions"])  # its task is still open
        self.assertEqual(st["asks"], {})
        self.assertEqual(len((self.w.state / "v2-archive.jsonl").read_text().splitlines()), 2)


class HarnessTests(Flow):
    def test_stop_seals_every_session_and_start_tells_the_next_episode_what_was_interrupted(self):
        self.w.task("1")
        self.w.set_st(queue=["1"])
        self.w.v2("dispatch")
        self.assertEqual(self.w.v2("stop"), "stopped implement-1")
        st = self.w.st()
        self.assertFalse(st["active"])
        self.assertEqual((self.s("implement-1")["state"], st["tasks"]["1"]["stage"]), ("lost", "planner"))
        self.assertEqual(self.w.rows(), [])
        self.w.v2("start")
        self.assertIn("while implement-1 (implementer) worked on task 1", self.heard())

    def test_what_the_owner_types_to_a_session_is_recorded_and_reaches_the_planner(self):
        self.w.session("implement-4", "implementer", "i4", task="4")
        self.w.session("plan-2", "planner", "p2", settings="planner-settings.json")
        ledger = self.w.root / "owner-ledger.md"
        ledger.write_text("# Owner ledger\n\n## Owner directions\n\n## Open questions to the owner\n\nQ1\n")

        def typed(sid, text):
            self.w.hook("ctx_gauge.py", "owner", {"session_id": sid, "hook_event_name": "UserPromptSubmit", "prompt": text})
        typed("i4", "Use the path store here, not a list.")
        typed("i4", "[harness] Continue task 4.")  # the harness's own words
        typed("i4", "You are implement-4, an implementer forked from the loaded library")  # a launch prompt
        typed("p2", "Put the verdict before request construction.")
        text = ledger.read_text()
        self.assertIn("(to implement-4 (implementer, task 4); recorded by the harness):\n\n"
                      "> Use the path store here, not a list.", text)
        self.assertIn("(to plan-2 (planner); recorded by the harness):\n\n> Put the verdict before", text)
        self.assertNotIn("Continue task 4", text)
        self.assertNotIn("You are implement-4", text)
        self.assertLess(text.index("path store"), text.index("## Open questions"))
        events = [e["text"] for e in self.w.st()["events"]]
        self.assertEqual(len(events), 1)  # a planning episode acts on what it is told itself
        self.assertIn("The owner said to implement-4 (implementer, task 4): Use the path store", events[0])

    def test_status_and_who(self):
        self.w.task("1")
        self.w.set_st(queue=["1"])
        self.w.v2("dispatch")
        lines = self.w.v2("status").splitlines()
        self.assertEqual(lines[:4], ["orchestration: active", "knowledge base: kb-1 (sealed)", "planner: -",
                                     "producing: implement-1 on 1 (working)"])
        self.assertIn("queue: 1:running", lines)
        self.assertEqual((self.w.v2("who", "producer"), self.w.v2("who", "planner")), ("implement-1", ""))


if __name__ == "__main__":
    unittest.main()
