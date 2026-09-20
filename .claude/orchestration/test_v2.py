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

    def test_reading_what_a_task_leaves_never_stops_the_orchestration(self):
        def broken(*_):
            raise OSError("disk full")
        real = v2._leave
        v2._leave = broken
        try:
            self.assertIn("could not be read (OSError('disk full'))", v2.leave("4", "lost"))
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


# The values each role's first message is rendered with (v2.render's own defaults, and the call for that role).
PASSED = {
    "kb": {"NAME", "STALE"},
    "planner": {"NAME", "ID", "EVENTS", "HANDOFF", "GRAPH", "QUEUE", "STATUS", "LIST", "OWNER", "FIRST", "STALE"},
    "designer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT"},
    "implementer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT"},
    "investigator": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT"},
    "fixer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT"},
    "task-designer": {"NAME", "ID", "SUBJECT", "BRIEF", "WHY", "GRAPH", "LIST", "STALE"},
    "reviewer": {"NAME", "ID", "TASK", "SUBJECT", "REVIEW", "BRIEF", "SESSION", "STALE", "BEFORE"},
    "consultant": {"NAME", "ID", "QID", "ASKER", "TARGET", "QUESTION", "NOTE", "STALE"},
}
PASSED = {role: names | {"ROUNDS", "READ", "CIRCLING", "FIX_MINUTES", "FIX_ROUNDS", "HOLD_HOURS", "ROOM_DESIGN",
                         "ROOM_TASK", "BRIEF_BACKLOG"} for role, names in PASSED.items()}  # render's own defaults


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

    def test_a_planned_fix_is_told_that_nothing_failed_and_gets_no_bare_placeholder(self):
        # until 2026-09-20 every planned fix read the literal {WHAT} where what it repairs belongs
        self.w.task("1", description=BRIEF.replace("Kind: build", "Kind: fix"), subject="Fix the replay's default")
        self.w.set_st(queue=["1"], tasks={"1": {"stage": "ready", "kind": "fix", "queued_at": time.time()}})
        self.w.v2("dispatch")
        (fixer,) = self.forks("fix-")
        self.assertIn("Nothing failed: this task is a fix the planner planned", fixer[-1])
        self.assertNotIn("{WHAT}", fixer[-1])
        self.assertNotRegex(fixer[-1], r"\{[A-Z][A-Z_]{2,}\}")

    def test_no_role_s_first_message_carries_a_placeholder_of_its_own_protocol(self):
        # a protocol's shared parts name {STALE} and the fixer's names {WHAT}: a render that does not pass them sent
        # the literal to the session (2026-09-20: every planned fix, and every planning episode)
        import re as _re
        for role in v2.ROLES:
            text = open(Path(v2.PROTOCOLS) / f"{role}.md").read()
            for _ in range(2):
                text = _re.sub(r"\{\{([\w-]+)\}\}",
                               lambda m: open(Path(v2.PROTOCOLS) / f"_{m.group(1)}.md").read(), text)
            for name in _re.findall(r"\{([A-Z][A-Z_]{2,})\}", text):
                self.assertIn(name, PASSED[role], f"the {role} protocol names {{{name}}} and nothing passes it")

    def test_a_fix_blocked_behind_the_task_waiting_for_it_is_freed_and_the_planner_told(self):
        # task 5 waited for task 12 while what remained of it was queued behind task 5's own review (2026-09-20)
        self.w.task("1", subject="The waiting task")
        self.w.task("2", subject="Its review", blockedBy=["1"])
        self.w.task("3", subject="The fix it waits for", blockedBy=["2"])
        self.w.set_st(tasks={"1": {"stage": "parked", "efficiency_fix": "3",
                                   "parked": {"since": time.time(), "for": "fix", "after": "3"}}})
        self.w.v2("dispatch")
        self.assertEqual(self.w.read_task("3")["blockedBy"], [])
        self.assertIn("waits for its fix, task 3, which was blocked by 2", self.heard())

    def test_the_planner_cannot_name_a_fix_that_waits_on_the_task_it_fixes(self):
        self.w.task("1", subject="The waiting task")
        self.w.task("2", subject="The fix", blockedBy=["1"])
        self.w.set_st(tasks={"1": {"stage": "running"}, "2": {"stage": "ready"}})
        self.w.session("plan-1", "planner", "p1", state="working")
        self.assertIn("could never land", self.as_("plan-1", "after", "1", "2"))
        self.w.task("3", subject="A fix of its own", blockedBy=[])
        self.assertIn("task 1 is told when 3 has landed", self.as_("plan-1", "after", "1", "3"))

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
        self.assertIn("refused: task 9's finalization is in flight and one runs at a time", out)
        self.w.write("theories/X.thy", "task 9's theory\n")
        code = (f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n"
                "v2.own('9', ['theories/X.thy'])\nwith v2.state() as st: v2.to_planner(st, '9', 'the finalizer', 'failed twice')")
        subprocess.run([sys.executable, "-c", code], env=self.w.env, check=True)
        self.assertTrue((self.w.project / "theories/X.thy").exists())  # a task that leaves leaves its work whole
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

    def test_a_timing_run_takes_the_machine_and_falls_with_the_run(self):
        # a neighbour distorts a measurement as surely as it exceeds the memory; the harness gave that hold only to a
        # check advancing the base heap (the owner, 2026-09-20)
        said = self.as_(self.impl, "measuring", "the machinery's evaluation against its bound")
        self.assertIn("the machine is yours", said)
        claim = json.loads((self.w.state / "isabelle-exclusive").read_text())
        self.assertEqual((claim["task"], claim["session"]), ("1", self.impl))
        self.assertIn("machinery's evaluation", claim["why"])
        # it stands while the run does: a claim with neither run nor grace left falls, and the machine is free again
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "1", "why": "a measurement", "session": self.impl, "at": 0}))
        self.w.session("fix-9", "fixer", "f9", task="9", state="working")
        self.w.task("9", subject="Another task")
        self.assertIn("the machine is yours", self.w.v2("measuring", "theirs", env=self.w.as_session("f9")))
        self.assertEqual(json.loads((self.w.state / "isabelle-exclusive").read_text())["task"], "9")

    def test_the_machine_is_claimed_by_one_task_at_a_time(self):
        self.as_(self.impl, "measuring", "mine")
        self.w.session("fix-9", "fixer", "f9", task="9", state="working")
        self.w.task("9", subject="Another task")
        said = self.w.v2("measuring", "theirs", env=self.w.as_session("f9"))
        self.assertIn("task 1 holds the machine", said)
        self.assertIn("mine", said)

    def test_two_tasks_hold_their_own_trees_and_git_merges_their_lines(self):
        # what a worktree per task buys, and what it does not. A ROOT line, a DECISIONS entry and a THEORY_MAP row
        # are lines: git merges them where they stand apart, and says so where they stand together — against the old
        # harness, which moved whole files and deleted the lines of tasks that were still working (2026-09-20)
        run = lambda code: subprocess.run(
            [sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n{code}"],
            env=self.w.env, capture_output=True, text=True).stdout
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Later\n")
        self.w.git("add", "ROOT")
        self.w.git("commit", "-q", "-m", "the session")

        def install(tid, name, after):
            path = run(f'print(v2.worktree({tid!r}))').strip()
            root = Path(path, "ROOT")
            root.write_text(root.read_text().replace(f"    {after}\n", f"    {after}\n    {name}\n"))
            Path(path, "theories").mkdir(exist_ok=True)
            Path(path, "theories", name + ".thy").write_text(f"theory {name} imports Main begin end\n")
            self.w.git("add", "-A", cwd=path)
            self.w.git("commit", "-q", "-m", f"task {tid}", cwd=path)
            return path

        # all three branch from one commit, as concurrent tasks do
        install("1", "Mine", "Base")
        install("2", "Theirs", "Later")  # a line of its own, in its own place
        install("3", "Same", "Base")     # and one written where task 1 wrote
        self.assertIsNone(eval(run('print(repr(v2.merged("1")))').strip()))
        self.assertIsNone(eval(run('print(repr(v2.merged("2")))').strip()))
        root = (self.w.project / "ROOT").read_text()
        self.assertIn("    Mine\n", root)
        self.assertIn("    Theirs\n", root)  # both lines, in one file, the harness moving nothing
        self.assertTrue((self.w.project / "theories/Mine.thy").exists())
        self.assertTrue((self.w.project / "theories/Theirs.thy").exists())

        # two lines written at the same place do not merge by themselves: git names the file and nothing is lost
        self.assertEqual(eval(run('print(repr(v2.merged("3")))').strip()), ["ROOT"])
        self.assertIn("    Mine\n", (self.w.project / "ROOT").read_text())  # the merge is undone, not resolved
        self.assertNotIn("<<<<<<<", (self.w.project / "ROOT").read_text())
        self.assertIn("Same", self.w.git("show", "task/3:ROOT"))  # and the task's own line stands on its branch
        # with the union driver they do merge, and both lines stand
        self.w.write(".gitattributes", "ROOT merge=union\n")
        self.w.git("add", ".gitattributes")
        self.w.git("commit", "-q", "-m", "the index files merge by union")
        self.assertIsNone(eval(run('print(repr(v2.merged("3")))').strip()))
        root = (self.w.project / "ROOT").read_text()
        self.assertIn("    Mine\n", root)
        self.assertIn("    Same\n", root)
        for tid in ("1", "2", "3"):
            run(f'v2.worktree_gone({tid!r})')
        self.assertFalse(Path(self.w.project, ".build/trees/1").exists())

    def test_what_a_union_merge_can_get_wrong_is_reported(self):
        # union keeps both sides' lines, so it keeps one a side deleted and keeps two copies of one added twice.
        # Neither is trusted: the tree invariant reads ROOT, DECISIONS.md and THEORY_MAP.md and says so.
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Retired\n    Twice\n    Twice\n")
        self.w.write("theories/Base.thy", "theory Base imports Main begin end\n")
        self.w.write("theories/Twice.thy", "theory Twice imports Main begin end\n")
        self.w.write("DECISIONS.md", "## One decision\n\nx\n\n## One decision\n\ny\n")
        self.w.write("THEORY_MAP.md", "| Theory | Direct imports | Content |\n| Base | Main | a |\n| Base | Main | a |\n")
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(chr(10).join(v2.tree_trouble()))"], env=self.w.env, capture_output=True,
                             text=True).stdout
        self.assertIn("ROOT declares Retired, which is not in theories/", out)  # a line union brought back
        self.assertIn("ROOT declares Twice 2 times", out)
        self.assertIn('DECISIONS.md holds the entry "One decision" 2 times', out)
        self.assertIn("THEORY_MAP.md holds the row of Base 2 times", out)

    def test_a_task_that_stops_leaves_its_change_whole(self):
        # a change here is a set of parts — a theory, the ROOT line that declares it, the import that reaches it —
        # and the harness used to move the parts separately: a theory went while its declaration stayed, a
        # declaration went while its theory stayed, an import stayed while its theory went. Each left a tree every
        # task's check refuses (2026-09-20). Nothing is taken out now.
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Mine\n")
        self.w.write("theories/Mine.thy", "theory Mine imports Main begin end\n")
        self.w.write("theories/Boundary.thy", "theory Boundary imports Main Mine begin end\n")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.own('1', ['theories/Mine.thy', 'theories/Boundary.thy', 'ROOT'])"],
                       env=self.w.env, check=True)
        said = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               "print(v2.leave('1', 'parked'))"], env=self.w.env, capture_output=True, text=True).stdout
        self.assertIn("stay in the working tree", said)
        self.assertTrue((self.w.project / "theories/Mine.thy").exists())
        self.assertIn("Mine", (self.w.project / "ROOT").read_text())
        self.assertIn("Mine", (self.w.project / "theories/Boundary.thy").read_text())
        self.assertFalse((self.w.project / ".build/tasks/1/shelf/manifest.json").exists())  # and no shelf is made

    def test_the_tree_says_when_it_refuses_every_check(self):
        # the invariant the checks read, so a violation is named where it happens and not found by a builder later
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Declared\n    Absent\n")
        self.w.write("theories/Declared.thy", "theory Declared imports Main begin end\n")
        self.w.write("theories/Undeclared.thy", "theory Undeclared imports Main Nowhere begin end\n")
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(chr(10).join(v2.tree_trouble()))"], env=self.w.env, capture_output=True,
                             text=True).stdout
        self.assertIn("theories/Undeclared.thy is in the tree and no ROOT line declares it", out)
        self.assertIn("ROOT declares Absent, which is not in theories/", out)
        self.assertIn("imports Nowhere, which is neither in the tree nor in the history", out)

    def test_a_job_the_session_stopped_no_longer_counts_as_running(self):
        # TaskStop ends a job without a completion notice; counted as running, it held a session's mail and its
        # resume for ever (2026-09-20)
        sid = self.s(self.impl)["sid"]
        self.w.transcript(sid, [{"type": "user", "message": {"content": [{"type": "tool_result",
            "content": "Command running in background with ID: bq1. Output is being written to: x"}]}}])
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="partial"))
        self.assertIn("your background jobs bq1 are still running", self.as_(self.impl, "result", "1"))
        self.w.transcript(sid, [{"type": "user", "message": {"content": [{"type": "tool_result",
            "content": "Command running in background with ID: bq1. Output is being written to: x"}]}},
            {"type": "user", "message": {"content": [{"type": "tool_result",
             "content": '{"message":"Successfully stopped task: bq1 (python3 -B tools/replay.py)"}'}]}}])
        self.assertIn("recorded", self.as_(self.impl, "result", "1"))

    def test_a_job_whose_output_has_stood_still_for_hours_counts_as_ended(self):
        sid = self.s(self.impl)["sid"]
        out = self.w.project / ".build" / "job.output"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("")
        self.w.transcript(sid, [{"type": "user", "message": {"content": [{"type": "tool_result",
            "content": f"Command running in background with ID: bq1. Output is being written to: {out}"}]}}])
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="partial"))
        self.assertIn("your background jobs bq1 are still running", self.as_(self.impl, "result", "1"))
        os.utime(out, (time.time() - 10_000, time.time() - 10_000))
        self.assertIn("recorded", self.as_(self.impl, "result", "1"))

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
        self.assertTrue((self.w.project / "theories/Ready.thy").exists())  # the run has ended; its work stays
        self.assertEqual(self.t("1")["stage"], "parked")  # the slot is implement-2's
        st = self.w.st()
        st["sessions"]["implement-2"]["state"] = "done"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")
        self.assertIn("The run you parked for has ended", self.resumes(sid)[-1][3])
        self.assertTrue((self.w.project / "theories/Ready.thy").exists())  # its changes are back

    def test_a_check_parks_whoever_else_holds_changes_and_a_review_does_not(self):
        self.w.write("theories/Other.thy", "another task's theory\n")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.own('1', ['theories/Other.thy'])"], env=self.w.env, check=True)
        self.w.write(".build/tasks/9/finalize.json", json.dumps({"check": "true", "files": ["DECISIONS.md"], "message": "m"}))
        st = self.w.st()
        st["tasks"]["9"] = {"stage": "reviewing"}
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")  # a review holds its own files only: work goes on
        st = self.w.st()
        st["tasks"]["9"]["stage"] = "checking"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "parked")  # the check sees the tree: no one else writes meanwhile
        self.assertTrue((self.w.project / "theories/Other.thy").exists())  # and its work stays there, whole
        self.assertIn("check is running and sees the working tree", json.dumps(self.w.mail(self.impl)))
        st = self.w.st()
        st["tasks"]["9"]["stage"] = "reviewing"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")  # back once the check has ended, its files untouched by 9
        self.assertTrue((self.w.project / "theories/Other.thy").exists())

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
        st["tasks"]["9"] = {"stage": "checking"}  # another task's check holds the working tree
        self.w.write(".build/tasks/9/finalize.json", json.dumps({"check": "true", "files": ["theories/X.thy"], "message": "m"}))
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.v2("dispatch")
        self.assertEqual(self.t("1")["stage"], "running")  # its wait is over: the slot is its before any new task
        resumed = self.resumes(self.s(self.impl)["sid"])[-1][3]
        self.assertIn("has landed (task 3)", resumed)
        self.assertIn("Task 9 holds the working tree now: draft under .build/tasks/1/ meanwhile", resumed)  # its check
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

    def test_an_answer_to_a_parked_session_is_not_called_lost(self):
        # parked is alive: the session reads its mail when it is resumed, and four answers were declared lost to
        # sessions that were only waiting for the working tree (2026-09-20)
        self.w.session("implement-3", "implementer", "i3", task="3", state="working")
        self.w.task("3", subject="A build")
        self.as_("implement-3", "ask", "--to", "planner", "Which of the two?")
        self.w.set_st(sessions={k: (v | {"state": "parked"} if k == "implement-3" else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.session("plan-3", "planner", "p3", state="working")
        self.w.v2("reply", "q1", "The first one.", env=self.w.as_session("p3"))
        self.assertIs(self.w.st()["asks"]["q1"]["delivered"], True)
        log = self.w.state / "v2.log"
        self.assertNotIn("reached nobody", log.read_text() if log.exists() else "")
        self.assertIn("The first one.", json.dumps(self.w.mail("implement-3")))  # it waits in its mail

    def test_an_answer_to_a_session_that_has_ended_is_written_where_the_work_reads_it(self):
        # a designer or task designer asks without blocking and finishes in the same turn; four of twelve answers sat
        # unread in the mailboxes of sessions that had ended (2026-09-20)
        self.w.session("design-3", "designer", "d3", task="3", state="working")
        self.w.task("3", subject="A design")
        self.assertIn("asked", self.w.v2("ask", "--to", "planner", "Which of the two?",
                                         env=self.w.as_session("d3")))
        self.w.set_st(sessions={k: (v | {"state": "done", "ended": time.time()} if k == "design-3" else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.session("plan-3", "planner", "p3", state="working")
        self.w.v2("reply", "q1", "The first one, and here is why.", env=self.w.as_session("p3"))
        written = self.w.project / ".build/tasks/3/answers/q1.md"
        self.assertTrue(written.exists())
        self.assertIn("The first one, and here is why.", written.read_text())
        self.assertIs(self.w.st()["asks"]["q1"]["delivered"], False)
        self.assertIn("The answer to q1 reached nobody", self.heard())
        self.assertIn("answers that reached nobody: q1", self.w.v2("status"))
        # and it stops being loose when the planner has put what it decides where the work reads it
        self.assertIn("no longer loose", self.w.v2("carried", "q1", "into task 3's Planner's line",
                                                   env=self.w.as_session("p3")))
        self.assertNotIn("reached nobody", self.w.v2("status"))

    def test_one_session_works_at_a_time_when_the_owner_sets_that_rate(self):
        # 48 sessions in a day, each on a base of about half a million tokens: the rate is the owner's to set
        # (2026-09-20), and every slot answers to it
        self.w.set_st(queue=["2"], tasks={"1": {"stage": "reviewing", "kind": "build", "session": "implement-1"}})
        self.w.v2("dispatch", env=dict(self.w.env, ORCH_WORKERS="1"))
        self.assertEqual(self.forks("brief-") + self.forks("review-"), [])  # implement-9 is producing
        self.assertIn("working: 1 of at most 1", self.w.v2("status", env=dict(self.w.env, ORCH_WORKERS="1")))
        # with the producing session parked, the supporting work goes on in its gap
        self.w.set_st(sessions={k: (v | {"state": "parked"} if k == "implement-9" else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.v2("dispatch", env=dict(self.w.env, ORCH_WORKERS="1"))
        self.assertEqual(len(self.forks("review-") + self.forks("brief-")), 1)  # one, and only one

    def test_no_brief_is_detailed_while_the_builders_have_a_full_queue(self):
        # one brief task turned into 26 tasks while a single producing slot finished one build in a day; the graph's
        # multiplier is capped at what the builders can consume (the owner, 2026-09-20)
        for i in range(v2.BRIEF_BACKLOG):
            self.w.task(f"5{i}", description=BRIEF, subject=f"A build {i}")
        self.w.set_st(queue=["2"], tasks={"1": {"stage": "reviewing", "kind": "build", "session": "implement-1"}})
        self.w.v2("dispatch")
        self.assertEqual(self.forks("brief-"), [])  # nothing is detailed
        log = (self.w.state / "v2.log").read_text()
        self.assertIn("no brief is detailed while", log)
        self.assertIn(f"(at most {v2.BRIEF_BACKLOG}): 2 wait for the builders", log)
        self.assertIn(f"open build and fix tasks of at most {v2.BRIEF_BACKLOG}", self.w.v2("status"))
        self.assertIn("no brief is detailed until the builders have taken some", self.w.v2("status"))
        # as the builders take them, briefing resumes (with the review it did instead out of the way)
        for i in range(2):
            self.w.task(f"5{i}", description=BRIEF, subject=f"A build {i}", status="completed")
        self.w.set_st(tasks={"1": {"stage": "done"}},
                      sessions={k: v for k, v in self.w.st()["sessions"].items() if not k.startswith("review-")})
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("brief-")), 1)

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
