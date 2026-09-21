"""v2.py: the forms, the state and the mail, the task lock, and the flows between the knowledge base, planning
episodes, the producing and supporting sessions, consultations and the finalizer, run in a throwaway world with a fake
`claude` (fakes.py)."""
import json
import subprocess
import tempfile
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
            # it proposes and no longer edits the graph: the task tools are refused to it, so its production is
            # its proposal and its drafts under brief/ (2026-09-20)
            self.assertFalse(v2.deliverables_of({"role": "task-designer", "task": "4"})["task_tools"])
            self.assertEqual(v2.deliverables_of({"role": "task-designer", "task": "4"}),
                             {"deliverables": [".build/tasks/4/brief/proposal.json"],
                              "drafts": ".build/tasks/4/brief/", "task_tools": False})
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
                      TASK="6", REVIEW="r", FIRST="", TREE="t")
        import re
        with tempfile.TemporaryDirectory() as temp, patch.object(v2, "STATE", temp):
            # in its own state: render logs what it could not fill, and this test wrote that into the live log
            for role in v2.ROLES:
                text = v2.render(role, **values)
                self.assertTrue(text.startswith("You are x-1, "), role)
                self.assertEqual(re.findall(r"\{[A-Z_]+\}|\{\{[\w-]+\}\}", text), [], role)
            log = Path(temp) / "v2.log"
            self.assertEqual(log.read_text() if log.exists() else "", "")  # nothing was left out


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

    def test_the_tree_s_owner_is_read_with_one_git_call_not_one_per_path(self):
        # changed_paths() sat inside the comprehension's condition, so tree_writer ran a git subprocess per owned
        # path — ten of them a call — and the write guard reaches it on every Write and Edit a session makes
        # (2026-09-21: 21.4 ms a call, 2.3 after)
        calls = []
        real = v2.changed_paths
        with patch.object(v2, "changed_paths", lambda *a, **k: calls.append(1) or ["a.thy", "b.thy", "c.thy"]):
            with v2.owners() as o:
                o.update({"a.thy": "1", "b.thy": "2", "c.thy": "3"})
            v2.tree_writer({"tasks": {}})
            self.assertEqual(len(calls), 1)
            calls.clear()
            v2._owned_by("1")
            self.assertEqual(len(calls), 1)

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
        """What the planner has been told: the events not yet with it, those a new planner was started on, and those
        delivered to the one that lives (its mailbox, and the resume that carried them)."""
        mail = " ".join(m["text"] for n in self.w.st()["sessions"] if n.startswith("plan-") for m in self.w.mail(n))
        resumed = " ".join(c["args"][-1] for c in self.w.calls("--bg") if "--resume" in c["args"] and "-n" not in c["args"])
        return (" ".join(e["text"] for e in self.w.st()["events"]) + " "
                + " ".join(a[-1] for a in self.forks("plan-")) + " " + mail + " " + resumed)

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
        # not the shared graph's settings: the knowledge base may not edit the graph, and whatever were injected
        # into it would be carried by every session forked from it
        self.assertTrue(fork[fork.index("--settings") + 1].endswith("worker-settings.json"))
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
        self.assertIn("You are plan-1, the planner", plan[-1])
        self.assertIn("## The first planner: a new task graph", plan[-1])
        self.assertIn("they do not bind it", plan[-1])  # the history and the handoff inform the graph
        self.assertIn("uncommitted changes that no task owns yet: none", plan[-1])
        self.assertNotIn("{UNOWNED}", plan[-1])
        self.assertEqual(st["events"], [])
        self.w.task("1")  # once a graph exists, later episodes are ordinary
        self.w.set_st(events=[{"at": "2026-09-19T00:00:00", "from": "x", "text": "e"}], plan_ended=1.0)
        self.assertEqual(v2_first(self.w), "")


    def test_a_copy_of_the_harness_in_a_worktree_acts_on_the_one_state(self):
        # a worktree is a checkout of the repository, so it carries its own .claude/orchestration, and state/ is
        # gitignored: v2.py run from there made a second, empty v2.json and acted on it. fix-49.2 recorded its
        # finalize, its result and its whole account into that parallel state; the real harness saw none of it,
        # declared the session gone and handed its task back to the planner (2026-09-20).
        self.w.repository()
        wt = self.w.project / ".build/trees/9"
        self.w.git("worktree", "add", "-q", "-B", "task/9", str(wt), "HEAD")
        here = wt / ".claude/orchestration"
        here.mkdir(parents=True, exist_ok=True)
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              f"print(v2._one_tree({str(here)!r}))"],
                             env=self.w.env, capture_output=True, text=True).stdout.strip()
        self.assertEqual(out, str(self.w.project))   # the one tree, not the worktree it sits in
        self.assertTrue((wt / ".git").is_file())     # which is how it is told apart, without a git call

    def test_a_session_is_not_told_it_has_a_tree_that_trees_being_off_denies_it(self):
        # tree_text keyed off the directory alone, exactly as worktree_of did: with trees off and a tree left on
        # disk it would say "you are started in it" while worktree_of starts the session in the one tree
        (self.w.project / ".build/trees/9").mkdir(parents=True, exist_ok=True)
        said = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               "print(v2.tree_text('9'))"],
                              env=dict(self.w.env, ORCH_TREES="0"), capture_output=True, text=True).stdout
        self.assertIn("You work in the repository's one working tree", said)
        on = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                             "print(v2.tree_text('9'))"],
                            env=dict(self.w.env, ORCH_TREES="1"), capture_output=True, text=True).stdout
        self.assertIn("Your working tree is your task's own", on)

    def test_a_tree_left_behind_does_not_capture_its_task_while_trees_are_off(self):
        # worktree_of read the directory alone, so a tree left by an earlier run captured its task for ever after
        # ORCH_TREES was turned off: fix-49.2's cwd was .build/trees/49, the tree the planner had declared
        # discarded, while tree_text told it in the same message that it worked in the one tree. finalize.py runs
        # the check and makes the commit there too, and tree_trouble read it — which is where the two notices saying
        # "the working tree is inconsistent" came from (2026-09-20).
        (self.w.project / ".build/trees/9").mkdir(parents=True, exist_ok=True)
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.worktree_of('9')); print(v2.tree_of({'task': '9'}))"],
                             env=dict(self.w.env, ORCH_TREES="0"), capture_output=True, text=True).stdout.split("\n")
        self.assertEqual(out[0], str(self.w.project))   # the one tree, whatever is left on disk
        self.assertEqual(out[1], str(self.w.project))
        on = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                             "print(v2.worktree_of('9'))"],
                            env=dict(self.w.env, ORCH_TREES="1"), capture_output=True, text=True).stdout.strip()
        self.assertTrue(on.endswith(".build/trees/9"))  # and with trees on it is the task's own

    def test_a_fresh_start_drops_the_events_it_supersedes(self):
        # an unhandled event is carried for ever, and two classes go false while they wait. plan-31 was given two
        # fresh charges, for two different runs, and two notices saying the working tree was inconsistent — of a
        # tree that was consistent, written three hours and two runs earlier (2026-09-20).
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n")
        self.w.write("theories/Base.thy", "theory Base imports Main begin end\n")
        self.w.set_st(active=False, events=[
            {"at": "2026-09-20T21:08:54", "from": "the owner", "text": "an older charge", "kind": "fresh-charge"},
            {"at": "2026-09-20T20:24:21", "from": "the harness", "text": "the tree is inconsistent",
             "kind": "tree-trouble", "tree": None},
            {"at": "2026-09-20T20:25:57", "from": "the harness", "text": "implement-9 was interrupted"}])
        self.w.v2("start", "--fresh")
        texts = [e["text"] for e in self.w.st()["events"]]
        self.assertNotIn("an older charge", texts)            # superseded: a charge is about the run that issued it
        self.assertNotIn("the tree is inconsistent", texts)   # the tree is consistent now, so it is no longer true
        self.assertIn("implement-9 was interrupted", texts)   # untouched: what it has not handled it still needs
        self.assertEqual(len([t for t in texts if "This run begins on a knowledge base built fresh" in t]), 1)

    def test_a_fresh_start_runs_nothing_of_the_old_graph_until_the_planner_queues(self):
        # the run of 2026-09-20 began --fresh, charged its planner to take stock, and dispatched the old queue in the
        # same breath: task 7 was started, checked, reviewed and committed within ten minutes, before the planner had
        # said what of the inherited graph still stood (the owner).
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.task("1")
        self.w.set_st(active=False, queue=["1"], tasks={"1": {"stage": "ready", "kind": "build"}})
        self.w.v2("start", "--fresh")
        self.assertTrue((self.w.state / "graph-held").exists())
        self.w.reply(self.s("kb-2")["sid"], "INTEGRATED")
        self.w.v2("dispatch")
        (plan,) = self.forks("plan-")
        self.assertIn("THE GRAPH IS HELD", plan[-1])         # it is told, and told how to lift it
        self.assertIn("Take stock first", plan[-1])
        self.assertEqual(self.forks("implement-"), [])       # and nothing of the old graph has started
        self.assertEqual(self.t("1")["stage"], "ready")
        # the planner's own order is what releases it
        self.as_("plan-1", "queue", "1")
        self.assertFalse((self.w.state / "graph-held").exists())
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("implement-")), 1)

    def test_a_held_graph_is_named_again_while_it_stands_and_stops_when_it_is_lifted(self):
        # the hold ends on the planner's word alone, so it must not depend on a standstill: that is suppressed while
        # anything works, while the planner deliberates and while it has events waiting, and a planner that dropped
        # what the graph no longer needs and then forgot the order would have had nothing tell it (the owner)
        self.w.base()
        self.w.kb()
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.task("1")
        self.w.set_st(active=False, queue=["1"], tasks={"1": {"stage": "ready", "kind": "build"}})
        self.w.v2("start", "--fresh")
        self.assertIn("the graph is **held**", self.heard())  # the charge carries the first telling
        self.assertNotIn("The graph is held, and nothing of it runs", self.heard())  # and the reminder does not
        # not at every dispatch either
        before = len(self.w.st()["events"]) + len(self.w.calls("--bg"))
        self.w.v2("dispatch")
        self.assertEqual(len(self.w.st()["events"]) + len(self.w.calls("--bg")), before)
        # but it is named once the hold has stood that long
        told = self.w.state / "graph-held.told"
        old_at = time.time() - v2.GRAPH_HELD_EVERY - 60
        told.write_text(str(old_at))
        os.utime(told, (old_at, old_at))
        self.w.v2("dispatch")
        self.assertIn("The graph is held, and nothing of it runs", self.heard())
        self.assertIn("not one of them will start", self.heard())
        self.assertIn("Dropping alone does not lift it", self.heard())
        # and it stops the moment the hold is lifted
        (self.w.state / "graph-held").unlink()
        self.w.v2("dispatch")
        self.assertFalse(told.exists())

    def test_a_fresh_start_leaves_the_knowledge_base_behind_and_charges_the_first_planner(self):
        # the graph a run inherits was drawn under a harness that has changed, and some of it exists only because of
        # faults since fixed: the planner takes stock before it queues anything (the owner, 2026-09-20)
        self.w.base()
        self.w.kb()
        self.w.session("plan-9", "planner", "p9", state="idle", live=False, settings="planner-settings.json",
                       origin="kb-1")
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.task("1")
        self.w.set_st(notes=["what the last knowledge base had not taken up"])
        # it begins a run, it never rejoins one: under a run in progress it would take the context of whatever is
        # deliberating with the knowledge base and the planner it leaves behind
        refused = self.w.v2("start", "--fresh")
        self.assertIn("refused", refused)
        self.assertIn("stop.sh first", refused)
        self.assertIsNone(self.s("kb-1").get("released"))
        self.w.set_st(active=False)
        self.assertIn("active; knowledge base", self.w.v2("start", "--fresh"))
        self.assertTrue(self.s("kb-1").get("released"))     # the one that stood is left behind
        self.assertTrue(self.s("plan-9").get("released"))   # and so is the planner that would not fork the new one
        st = self.w.st()
        self.assertEqual(st["notes"], [])                   # they were for the base being left behind
        (kb,) = self.forks("kb-")                           # a new one is built at once
        self.assertIn("Read now, together, what the library does not hold: HANDOFF.md", kb[-1])
        self.assertNotIn("notes.md", kb[-1])
        self.assertEqual(self.forks("plan-"), [])           # nothing plans until it holds the knowledge
        self.w.reply(self.s("kb-2")["sid"], "INTEGRATED")
        self.w.v2("dispatch")
        (plan,) = self.forks("plan-")
        self.assertEqual(plan[plan.index("--resume") + 1], self.s("kb-2")["sid"])
        for said in ("take stock", "What has been produced", "What the graph no longer needs",
                     "What the structure should now be", "Only then queue"):
            self.assertIn(said, plan[-1])


def v2_first(world):
    """The first episode's part, as v2 renders it in that world."""
    code = f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; print(v2.first_episode(), end='')"
    return subprocess.run([sys.executable, "-c", code], env=world.env, capture_output=True, text=True).stdout


# The values each role's first message is rendered with (v2.render's own defaults, and the call for that role).
PASSED = {
    "kb": {"NAME", "STALE"},
    "planner": {"NAME", "ID", "EVENTS", "HANDOFF", "GRAPH", "QUEUE", "STATUS", "LIST", "OWNER", "FIRST", "STALE"},
    "designer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT", "TREE"},
    "implementer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT", "TREE"},
    "investigator": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT", "TREE"},
    "fixer": {"NAME", "ID", "KIND", "SUBJECT", "BRIEF", "STALE", "WHAT", "TREE"},
    "task-designer": {"NAME", "ID", "SUBJECT", "BRIEF", "WHY", "GRAPH", "LIST", "STALE"},
    "reviewer": {"NAME", "ID", "TASK", "SUBJECT", "REVIEW", "BRIEF", "SESSION", "STALE", "BEFORE"},
    "consultant": {"NAME", "ID", "QID", "ASKER", "TARGET", "QUESTION", "NOTE", "STALE"},
}
PASSED = {role: names | {"ROUNDS", "READ", "CIRCLING", "FIX_MINUTES", "FIX_ROUNDS", "HOLD_HOURS", "ROOM_DESIGN",
                         "ROOM_TASK", "BRIEF_BACKLOG", "GRAPH_DEPTH", "DEPTH", "WIDTH", "SLOTS", "CONSULT_HOURS",
                         "ISABELLE_MAX"}
          for role, names in PASSED.items()}  # render's own defaults


class PlanningTests(Flow):
    def event(self, text, sender="the harness"):
        st = self.w.st()
        self.w.set_st(events=st["events"] + [{"at": time.strftime("%Y-%m-%dT%H:%M:%S"), "from": sender, "text": text}])

    def test_the_status_the_messages_and_the_rule_read_the_same_figures(self):
        # the status showed the build-and-fix depth while start_brief records and cmd_propose compares the whole
        # graph's, so the planner read 10 where the rule applied 11; and the task designer was told a width of 2
        # against the status's 1, because its message did not skip what no slot can take (2026-09-21)
        self.w.task("1", description=BRIEF, metadata={"kind": "build"})
        self.w.task("2", description=REVIEW_TASK.format(task="1"), metadata={"kind": "review"}, blockedBy=["1"])
        self.w.task("3", description=BRIEF, metadata={"kind": "build"}, blockedBy=["2"])
        self.w.task("4", description=BRIEF, metadata={"kind": "build"})   # given back: no slot can take it
        self.w.set_st(queue=["1", "2", "3"], tasks={"4": {"stage": "planner", "kind": "build"}})
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "w, d = v2.graph_figures(); print(w, d); "
                              "print(v2.render('task-designer', NAME='b', ID='9', SUBJECT='s', BRIEF='b', WHY='-', "
                              "GRAPH='g', LIST=v2.LIST, STALE='-'))"],
                             env=self.w.env, capture_output=True, text=True).stdout
        width, depth = out.splitlines()[0].split()
        self.assertEqual((width, depth), ("1", "3"))          # 4 is skipped; the chain 3 -> 2 -> 1 is the whole one
        self.assertIn(f"The chain is **{depth}** tasks deep", out)
        self.assertIn(f"{width} build and fix tasks can start", out)
        said = self.w.v2("status")
        self.assertIn(f"{width} build and fix tasks can start", said)
        self.assertIn(f"the chain is {depth} deep", said)

    def test_the_graphs_shape_is_what_can_run_and_how_long_the_chain_is(self):
        # a count of open tasks says neither: on 2026-09-20 the graph held 17 open build and fix tasks, which
        # detained every brief, while only 5 of them could start at all and the chain was 19 deep
        self.w.task("1", subject="free", metadata={"kind": "build"})
        self.w.task("2", subject="free too", metadata={"kind": "build"})
        self.w.task("3", subject="reviews 1", metadata={"kind": "review"}, blockedBy=["1"])
        self.w.task("4", subject="after the review", metadata={"kind": "build"}, blockedBy=["3"])
        self.w.task("5", subject="done", status="completed", metadata={"kind": "build"})
        self.w.task("6", subject="after a finished one", metadata={"kind": "build"}, blockedBy=["5"])
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.graph_shape()); print(v2.graph_shape(('build','fix'))); "
                              "print(v2.graph_shape(skip=['1']))"],
                             env=self.w.env, capture_output=True, text=True).stdout.split("\n")
        self.assertEqual(out[0], "(3, 3, 5)")   # 1, 2 and 6 can run; 4 waits two deep; 5 is done and counts for none
        # the chain is walked over every task and counted over the kinds asked for: filtering the walk by kind would
        # cut it at task 3, the review, and call a chain of 3 a chain of 1
        self.assertEqual(out[1], "(3, 3, 4)")
        # `skip` leaves a task out of the WIDTH and still walks it for the depth: a task that came back to the
        # planner has every blocker done and counted as concurrency though no slot can take it, and two of those
        # would have held the width at the slots for ever and detained every brief (2026-09-20)
        self.assertEqual(out[2], "(2, 3, 5)")

    def test_a_git_failure_is_recorded_rather_than_read_as_nothing(self):
        # git_out turns a failure into None, and changed_paths turns None into "no paths", which reads as a clean
        # tree: from there tree_writer finds no owner and leave() tells a task nothing about the work it leaves
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.git_out('no-such-command')); print(v2.git_out('no-such-command', quiet=True))"],
                             env=self.w.env, capture_output=True, text=True).stdout.split()
        self.assertEqual(out, ["None", "None"])
        said = (self.w.state / "v2.log").read_text()
        self.assertEqual(said.count("git no-such-command failed"), 1)   # said once: the quiet one is an answer

    def test_startable_agrees_with_what_the_dispatch_would_actually_start(self):
        # a report that names a task produce() would refuse is a message that lies: the stage is the harness's
        # bookkeeping and the list is the graph, and between the planner completing a task and the next dispatch
        # healing its stage, startable would have named it
        self.w.task("4", description=BRIEF, subject="Finished", status="completed")
        self.w.task("5", description=BRIEF, subject="Really ready")
        self.w.set_st(queue=["4", "5"], tasks={"4": {"stage": "ready", "kind": "build"},
                                               "5": {"stage": "ready", "kind": "build"}})
        # and a review whose subject finished without being reviewed: pending_reviews will never offer it, so
        # naming it said the graph was wider than anything would take
        self.w.task("6", description=BRIEF, subject="An orphaned review")
        # 7 is completed in the list with its stage still `ready`, which is the window between the planner
        # completing it and the next dispatch healing the stage; 4's stage is `done` as reconcile leaves it
        self.w.task("7", description=BRIEF, subject="Completed, stage not yet healed", status="completed")
        self.w.set_st(queue=["4", "5", "6", "7"], tasks={"4": {"stage": "done", "kind": "build"},
                                                         "5": {"stage": "ready", "kind": "build"},
                                                         "6": {"stage": "ready", "kind": "review", "reviews": "4"},
                                                         "7": {"stage": "ready", "kind": "build"}})
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(' '.join(v2.startable()))"],
                             env=self.w.env, capture_output=True, text=True).stdout.strip()
        self.assertEqual(out, "5")

    def test_a_transcript_that_cannot_be_read_does_not_read_as_no_jobs_in_silence(self):
        # [] is "no job of its own runs", and the harness seals or resumes a session on that, which kills whatever
        # it started. A session that never started has no transcript and no jobs, which is not the same thing.
        self.w.session("implement-4", "implementer", "w4", task="4")
        (self.w.transcripts / "w4.jsonl").mkdir()          # there, and no read of it can succeed
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                              "import v2; print(v2.running_jobs('implement-4'))"],
                             env=self.w.env, capture_output=True, text=True)
        self.assertEqual((out.returncode, out.stdout.strip()), (0, "[]"), out.stderr)
        self.assertIn("the transcript of implement-4 could not be read", (self.w.state / "v2.log").read_text())
        before = (self.w.state / "v2.log").read_text().count("could not be read")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                        "import v2; v2.running_jobs('implement-4')"], env=self.w.env, capture_output=True, text=True)
        self.assertEqual((self.w.state / "v2.log").read_text().count("could not be read"), before)  # not every call
        self.w.session("implement-5", "implementer", "w5", task="5")   # started, nothing written yet
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                              "import v2; print(v2.running_jobs('implement-5'))"],
                             env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.stdout.strip(), "[]", out.stderr)   # no transcript yet: no job, and nothing is said
        self.assertEqual((self.w.state / "v2.log").read_text().count("could not be read"), before)

    def test_a_hold_whose_file_cannot_be_read_still_holds(self):
        # a hold is a switch that must fail closed: the file being there is what holds, and reading it is only how
        # the reason is told. Both read any failure as "no such file" and so as "nothing is held" (2026-09-21).
        for name, reason in ((v2.NO_LAUNCH, "held_back"), (v2.GRAPH_HELD, "graph_held")):
            (self.w.state / name).mkdir()          # there, and no read of it can succeed
            out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                  f"import v2; print(v2.{reason}())"], env=self.w.env, capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            self.assertIn(f"state/{name} is set", out.stdout)
            self.assertIn("could not be read", out.stdout)
            (self.w.state / name).rmdir()
            out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                  f"import v2; print(repr(v2.{reason}()))"], env=self.w.env, capture_output=True, text=True)
            self.assertEqual(out.stdout.strip(), "''")   # and no file is no hold, as before

    def test_a_state_or_an_ownership_map_that_cannot_be_read_is_never_written_over(self):
        # every caller writes back what it read, so reading an unreadable file as an empty one writes that emptiness
        # over the truth: the sessions, the tasks and the queue, or which task owns each change in the working tree
        for name, what in (("v2.json", "the orchestration's state"), ("tree-owners.json", "the working tree's")):
            (self.w.state / name).write_text("{ this is not json")
            out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                  "import v2, contextlib\n"
                                  "with contextlib.suppress(SystemExit):\n"
                                  "    v2.peek()\n"
                                  "    list(v2.owners(write=True).__enter__() for _ in [0])"],
                                 env=self.w.env, capture_output=True, text=True)
            self.assertNotEqual(out.returncode, 0, out.stdout)
            self.assertIn("is there and cannot be read", out.stderr)
            self.assertIn(what, out.stderr)
            self.assertEqual((self.w.state / name).read_text(), "{ this is not json")  # untouched
            (self.w.state / name).unlink()
        # the watchdog says so rather than standing still in silence, and the dispatch writes nothing
        (self.w.state / "v2.json").write_text("{ this is not json")
        self.w.run("watchdog.py")
        self.assertIn("cannot be read", (self.w.state / "v2.log").read_text())
        self.assertEqual((self.w.state / "v2.json").read_text(), "{ this is not json")

    def test_a_task_that_cannot_be_read_is_not_read_as_one_that_is_not_there(self):
        # None means "the planner took it out" everywhere: startable skips it, with_the_planner leaves it alone and
        # reconcile_stages names it to the planner as a conflict. A file that is there and unreadable must not turn
        # into that statement in silence.
        self.w.task("4")
        os.rename(self.w.tasks / "4.json", self.w.tasks / "4.json.away")
        (self.w.tasks / "4.json").mkdir()            # there, and no read of it can succeed
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.read_task('4'))"], env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.stdout.strip(), "None", out.stderr)
        self.assertIn("task 4 is in the list and could not be read", (self.w.state / "v2.log").read_text())
        (self.w.tasks / "4.json").rmdir()
        os.rename(self.w.tasks / "4.json.away", self.w.tasks / "4.json")
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print((v2.read_task('4') or {}).get('id'), v2.read_task('77'))"],
                             env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.stdout.strip(), "4 None", out.stderr)   # and one that is not there is still None

    def test_a_task_that_cannot_be_read_is_not_said_to_be_out_of_the_list(self):
        # every statement of the form "task N is not in the list" is about the planner having taken it out, and
        # None from read_task means an unreadable file as well: the notices would have said it of an I/O fault,
        # and a proposal would have been refused for it (2026-09-21)
        self.w.task("4", description=BRIEF, subject="Running, and its file unreadable")
        self.w.session("implement-4", "implementer", "w4", task="4")
        self.w.set_st(queue=["4"], tasks={"4": {"stage": "running", "kind": "build", "session": "implement-4"}})
        os.rename(self.w.tasks / "4.json", self.w.tasks / "4.json.away")
        (self.w.tasks / "4.json").mkdir()
        self.w.v2("dispatch")
        said = self.heard() + (self.w.state / "v2.log").read_text()
        self.assertIn("could not be read", said)                       # said for what it is
        self.assertNotIn("not in the task list at all", said)          # and not as the planner having taken it out
        (self.w.tasks / "4.json").rmdir()
        os.rename(self.w.tasks / "4.json.away", self.w.tasks / "4.json")

    def test_an_id_named_twice_in_the_order_is_one_place_in_the_queue(self):
        self.w.task("4")
        self.w.task("5")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.as_("plan-1", "queue", "4", "5", "4")
        self.assertEqual(self.w.st()["queue"], ["4", "5"])   # as `blockers` reads its own ids

    def test_a_start_that_is_not_confirmed_is_not_tried_again_every_minute(self):
        # the dispatch runs every minute and every start is a fork of a loaded base. produce() held the producing
        # slot to RETRY and said so; the planner, the knowledge base, a review, a brief and a consultation had
        # nothing — on 2026-09-20 two sessions were started and invisible, and a replacement for each would have
        # been started over and over (2026-09-21)
        (self.w.root / "fail-start").write_text("x")   # every start fails: none is ever confirmed
        self.event("Something for the planner")
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("plan-")), 1)
        self.assertIn("start of plan-1 not confirmed", (self.w.state / "v2.log").read_text())
        self.w.v2("dispatch")
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("plan-")), 1)        # not once a minute
        self.assertEqual(self.w.st()["events"][0]["text"], "Something for the planner")   # and they are kept
        os.utime(self.w.state / "start-failed-planner-one", (time.time() - v2.RETRY - 60,) * 2)
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("plan-")), 2)        # and tried again when the time has passed

    def test_the_owner_joins_the_planner_that_lives_rather_than_opening_another(self):
        # talk.sh's whole first step: the planner that lives is joined with everything it holds, woken if it was
        # between its events, and only when none lives is one opened (a fork of the knowledge base)
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json", state="idle")
        self.w.hit("plan-1")
        self.assertEqual(self.w.v2("talk"), "plan-1")
        self.assertTrue(self.s("plan-1")["owner"])
        (resume,) = [c["args"] for c in self.w.calls("--bg") if "--resume" in c["args"] and "-n" not in c["args"]]
        self.assertIn("The owner is here and will speak to you", resume[-1])
        self.assertEqual(self.forks("plan-"), [])          # none was opened
        # one that has ended is not joined: the next is a fork of the knowledge base
        self.w.set_st(sessions={**self.w.st()["sessions"], "plan-1": {**self.s("plan-1"), "released": True}})
        self.assertEqual(self.w.v2("talk"), "plan-2")
        self.assertEqual(len(self.forks("plan-")), 1)
        self.assertIn("The owner started you to speak with you", self.forks("plan-")[0][-1])

    def test_a_task_the_planner_puts_back_to_pending_and_queues_runs_again(self):
        # `done` is terminal bookkeeping that task_state never re-reads, so that a task accepted by its review is
        # not started a second time in the window before the planner completes it in the list. A task the planner
        # puts BACK to pending and names in its order is one it means to run, and nothing would ever start it: it
        # sat in the queue, not startable, and nothing named it (2026-09-21).
        self.w.task("4", description=BRIEF, subject="Done, and wanted again", status="completed")
        self.w.set_st(queue=[], tasks={"4": {"stage": "done", "kind": "build"}})
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.as_("plan-1", "queue", "4")
        self.assertEqual(self.t("4")["stage"], "done")        # the list still calls it completed: it stands
        self.w.task("4", description=BRIEF, subject="Done, and wanted again", status="pending")
        self.as_("plan-1", "queue", "4")
        self.assertEqual(self.w.st()["queue"], ["4"])
        self.w.v2("dispatch")
        self.assertEqual(self.t("4")["stage"], "running")     # read afresh from its brief, and started
        self.assertEqual(len(self.forks("implement-4")), 1)

    def test_a_queued_task_that_is_not_in_the_list_is_no_longer_startable(self):
        # the planner's first message of 2026-09-20 said "startable now: 21 14"; task 21 had been dropped and was
        # not in the list at all. startable() read its blockers off a record that was not there, so an empty list of
        # blockers made it ready for ever, and produce() would have tried to start it with nothing to brief from.
        self.w.task("14", subject="A real one")
        self.w.set_st(queue=["21", "14"], tasks={"21": {"stage": "ready", "kind": "build"},
                                                 "14": {"stage": "ready", "kind": "build"}})
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(' '.join(v2.startable()))"],
                             env=self.w.env, capture_output=True, text=True).stdout.strip()
        self.assertEqual(out, "14")
        self.w.v2("dispatch")
        self.assertEqual(self.forks("implement-21"), [])  # nothing is started for a task with no record

    def test_the_planner_sets_what_a_task_waits_on_and_not_only_adds(self):
        # Claude Code's TaskUpdate offers addBlockedBy and no way back, so until 2026-09-20 a dependency once written
        # could not be taken out: the planner could add edges and delete whole tasks but not move one, while three
        # harness messages told it to "re-point" a blocker. Nothing anywhere had chosen that.
        for tid in ("1", "2", "3"):
            self.w.task(tid, subject=f"Task {tid}")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.as_("plan-1", "blockers", "3", "1", "2")
        self.assertEqual(self.w.read_task("3")["blockedBy"], ["1", "2"])
        said = self.as_("plan-1", "blockers", "3", "2")
        self.assertEqual(self.w.read_task("3")["blockedBy"], ["2"])
        self.assertIn("taken out: 1", said)
        said = self.as_("plan-1", "blockers", "3", "none")
        self.assertEqual(self.w.read_task("3")["blockedBy"], [])
        self.assertIn("startable as soon as it is queued", said)
        # and it is the planner's: the task designer proposes its shape and does not set it
        self.w.session("brief-9", "task-designer", "b9", task="9", settings="worker-settings.json")
        said = self.as_("brief-9", "blockers", "3", "1")
        self.assertIn("the graph's edges are the planner's alone", said)
        self.assertIn("v2.py propose", said)        # and what the designer does instead
        self.assertEqual(self.w.read_task("3")["blockedBy"], [])

    def test_setting_what_a_task_waits_on_refuses_a_cycle_and_a_task_that_is_not_there(self):
        for tid in ("1", "2"):
            self.w.task(tid, subject=f"Task {tid}")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.as_("plan-1", "blockers", "2", "1")
        self.assertIn("would close a cycle", self.as_("plan-1", "blockers", "1", "2"))
        self.assertEqual(self.w.read_task("1")["blockedBy"], [])
        self.assertIn("cannot wait on itself", self.as_("plan-1", "blockers", "1", "1"))
        self.assertIn("no task 9 in the list", self.as_("plan-1", "blockers", "1", "9"))
        self.assertIn("refused: task 7 is not in the task list", self.as_("plan-1", "blockers", "7", "1"))

    def test_a_stage_follows_the_list_when_the_task_is_completed(self):
        # the planner completes a task in the list and the harness's own stage never followed: 5, 9 and 18 read as
        # the planner's long after they were committed, and 48 and 50 stood at `ready` while the list called them
        # done — one queue ordering away from a session started on finished work (2026-09-20)
        self.w.task("4", subject="Finished, and the harness had it with the planner", status="completed")
        self.w.task("5", subject="Really back")
        self.w.task("6", subject="Finished, and the harness had it ready", status="completed")
        self.w.set_st(tasks={"4": {"stage": "planner"}, "5": {"stage": "planner"},
                             "6": {"stage": "ready", "kind": "build"}})
        self.w.v2("dispatch")
        self.assertEqual(self.t("4")["stage"], "done")
        self.assertEqual(self.t("6")["stage"], "done")
        self.assertEqual(self.t("5")["stage"], "planner")  # genuinely with the planner: untouched

    def test_nothing_the_list_calls_finished_is_dispatched(self):
        # the reconciliation runs first, but the guard stands on its own: the stage is the harness's bookkeeping and
        # the list is the graph, so a task the planner has completed is not started whatever the stage says
        self.w.task("4", description=BRIEF, subject="Finished", status="completed")
        self.w.set_st(queue=["4"], tasks={"4": {"stage": "ready", "kind": "build"}})
        self.w.v2("dispatch")
        self.assertEqual(self.forks("implement-"), [])
        self.assertEqual(self.t("4")["stage"], "done")

    def test_a_live_session_on_finished_work_is_a_conflict_the_planner_is_told_of(self):
        # not bookkeeping to tidy: one of the two is wrong and only the planner can say which
        self.w.task("4", description=BRIEF, subject="Finished while it ran", status="completed")
        self.w.set_st(tasks={"4": {"stage": "running", "kind": "build", "session": "implement-4"}})
        self.w.v2("dispatch")
        self.assertEqual(self.t("4")["stage"], "running")  # untouched
        self.assertIn("completed in the task list and the harness has it running", self.heard())

    def test_a_drop_says_what_it_did_even_when_nothing_was_working(self):
        # "dropped nothing" was what it said when the drop had worked and no session was live (2026-09-20)
        self.w.task("4", subject="To drop")
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.w.set_st(queue=["4"], tasks={"4": {"stage": "ready", "kind": "build"}})
        said = self.as_("plan-1", "drop", "4")
        self.assertIn("task 4 is dropped", said)
        self.assertIn("Nothing was working on it", said)
        self.assertNotIn("dropped nothing", said)
        self.assertEqual(self.w.st()["queue"], [])

    def test_a_returned_task_that_holds_the_working_tree_says_so(self):
        # a task that came back may be the one whose installed work stands in the tree, and then it holds the tree:
        # every other producing session is refused it and parks for a task nothing will complete — the
        # blocker-not-in-the-list shape over the tree. On 2026-09-20 the planner dropped task 46 while its theory
        # stood in the tree and the harness said nothing of it.
        self.w.repository()  # changed_paths() asks git what differs from HEAD
        self.w.task("4", subject="Came back holding the tree")
        self.w.session("implement-9", "implementer", "w9", task="9", tree_wait="4")
        self.w.write("theories/Held.thy", "theory Held imports Main begin end\n")
        (self.w.state / "tree-owners.json").write_text(json.dumps({"theories/Held.thy": "4"}))
        self.w.set_st(tasks={"4": {"stage": "planner", "kind": "build"},
                             "9": {"stage": "running", "kind": "build", "session": "implement-9"}})
        self.w.v2("dispatch")
        mark = self.w.state / "returned-4"
        old = time.time() - v2.RETURNED_AFTER - 60
        mark.write_text(str(old))
        os.utime(mark, (old, old))
        self.w.v2("dispatch")
        told = self.heard()
        self.assertIn("It also holds the **working tree**", told)
        self.assertIn("theories/Held.thy", told)
        self.assertIn("implement-9 already waits", told)
        self.assertIn("parks for a task that cannot complete", told)

    def test_a_review_whose_subject_has_finished_is_named_as_unable_to_start(self):
        # pending_reviews only offers a review whose subject is `reviewing`, so one whose subject finished without
        # being reviewed can never start. Tasks 23 and 47 stood `ready` in the queue that way, reviews of 22 and 46,
        # which the planner completed on taking stock — and a ready task with no open blocker is not in the
        # standstill either, so nothing said so (2026-09-20).
        self.w.task("4", subject="Finished without a review", status="completed")
        self.w.task("5", subject="Its review")
        self.w.task("6", subject="A review still waiting")
        self.w.task("7", subject="Its subject, not yet finished")
        # the list alone says 4 is finished; its harness stage still reads `ready`, which is the case the second
        # half of the condition is there for
        self.w.set_st(queue=["5", "6"], tasks={"4": {"stage": "ready", "kind": "build"},
                                               "5": {"stage": "ready", "kind": "review", "reviews": "4"},
                                               "6": {"stage": "ready", "kind": "review", "reviews": "7"},
                                               "7": {"stage": "ready", "kind": "build"}})
        self.w.v2("dispatch")
        for tid in ("5", "6"):
            mark = self.w.state / f"returned-{tid}"
            if mark.exists():
                old_at = time.time() - v2.RETURNED_AFTER - 60
                mark.write_text(str(old_at))
                os.utime(mark, (old_at, old_at))
        self.w.v2("dispatch")
        told = self.heard()
        self.assertIn("Review task 5 has stood", told)
        self.assertIn("which is finished, and a review is only ever started for a task that is in review", told)
        self.assertNotIn("Review task 6 has stood", told)   # its subject has not finished: it simply waits

    def test_a_brief_not_in_form_is_named_again_and_not_only_once(self):
        # task_state said it once, when it first read the brief, and never again; the standstill does not list an
        # unformed task either, so one simply never ran and nothing said so a second time (2026-09-20)
        self.w.task("4", subject="Its brief is not in form", description="Kind: build\nno fields at all\n")
        self.w.set_st(queue=["4"], tasks={})
        self.w.v2("dispatch")
        self.assertEqual(self.t("4")["stage"], "unformed")
        self.assertIn("Task 4 is queued but its brief is not in form", self.heard())
        before = self.heard().count("not in form")
        self.w.v2("dispatch")
        self.assertEqual(self.heard().count("not in form"), before)   # not at every dispatch
        mark = self.w.state / "returned-4"
        old_at = time.time() - v2.RETURNED_AFTER - 60
        mark.write_text(str(old_at))
        os.utime(mark, (old_at, old_at))
        self.w.v2("dispatch")
        self.assertIn("has stood", self.heard())
        self.assertIn("with its brief not in form", self.heard())

    def test_a_design_waiting_for_the_planner_s_verdict_is_named_again(self):
        # pending_reviews starts a reviewer only for a build or a fix, so a finished design or investigation waits
        # for a verdict only the planner can give. It was said once, in the event when it finished (2026-09-21).
        self.w.task("4", subject="A design that is finished", description=BRIEF.replace("Kind: build", "Kind: design"))
        self.w.set_st(tasks={"4": {"stage": "reviewing", "kind": "design", "session": "design-4"}})
        self.w.v2("dispatch")
        self.assertNotIn("for your verdict", self.heard())     # not at once: it may be judged in a moment
        mark = self.w.state / "returned-4"
        old_at = time.time() - v2.RETURNED_AFTER - 60
        mark.write_text(str(old_at))
        os.utime(mark, (old_at, old_at))
        self.w.v2("dispatch")
        said = self.heard()
        self.assertIn("has waited", said)
        self.assertIn("for your verdict", said)
        self.assertIn("v2.py verdict 4 accept|reject", said)
        # and a build in review is the harness's to start a reviewer for, not the planner's to judge
        self.w.set_st(tasks={"4": {"stage": "reviewing", "kind": "build", "session": "implement-4"}})
        os.utime(mark, (old_at, old_at))
        before = said.count("for your verdict")
        self.w.v2("dispatch")
        self.assertEqual(self.heard().count("for your verdict"), before)

    def test_a_task_that_came_back_is_named_on_its_own_and_not_only_in_a_standstill(self):
        # tasks 5, 9, 18 and 21 stood with the planner for hours. The only thing that said so was standstill(),
        # which is suppressed while anything works and while the planner deliberates, so the notice reached the
        # planner 11.5 minutes into the run of 2026-09-20 at the first second its turn ended — and with work still in
        # flight it would not have been said at all.
        self.w.task("4", subject="Came back to the planner")
        self.w.session("implement-9", "implementer", "w9", task="9")  # something works: this is no standstill
        self.w.set_st(tasks={"4": {"stage": "planner", "kind": "build"},
                             "9": {"stage": "running", "kind": "build", "session": "implement-9"}})
        self.w.v2("dispatch")
        self.assertNotIn("has stood with you", self.heard())  # not at once: it may be re-planned in a moment
        mark = self.w.state / "returned-4"
        self.assertTrue(mark.exists())  # first seen, and counted from here
        old = time.time() - v2.RETURNED_AFTER - 60
        mark.write_text(str(old))
        os.utime(mark, (old, old))
        self.w.v2("dispatch")
        self.assertIn("Task 4 has stood with you", self.heard())
        self.assertIn("nothing else moves it", self.heard())

    def test_one_planner_lives_across_its_events_and_each_reaches_it_as_its_own_message(self):
        # 23 of the 48 sessions of 2026-09-20 were planning episodes, each a fork of the knowledge base at about
        # 510K, because an episode was a session and events were batched into it (the owner: one planner, immediately)
        self.event("Task 1 is committed.")
        self.w.v2("dispatch")
        (first,) = self.forks("plan-")
        self.assertIn("Task 1 is committed.", first[-1])
        self.event("Task 2 failed its check.")
        self.event("A question q3 for you.")
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("plan-")), 1)  # no second session: the one that lives is given them
        self.assertEqual(self.w.st()["events"], [])
        self.assertEqual([m["text"] for m in self.w.mail("plan-1")],  # two messages, not one batch
                         ["Task 2 failed its check.", "A question q3 for you."])
        self.assertEqual([e["text"] for e in self.s("plan-1")["events"]],  # all it was given, for a give-back
                         ["Task 1 is committed.", "Task 2 failed its check.", "A question q3 for you."])
        # its turn is running, so its hooks give it the mail; between events it is resumed with what has come
        self.w.set_status("plan-1", "idle")
        st = self.w.st()
        st["sessions"]["plan-1"]["state"] = "idle"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.event("Task 5 is yours again.")
        self.w.v2("dispatch")
        (resumed,) = self.resumes(self.s("plan-1")["sid"])
        for text in ("Task 2 failed its check.", "A question q3 for you.", "Task 5 is yours again."):
            self.assertIn(text, resumed[-1])
        self.assertEqual(resumed[-1].count("Message from"), 3)
        self.assertEqual(self.s("plan-1")["state"], "working")
        self.assertEqual(self.w.mail("plan-1"), [])

    def test_an_event_reaches_the_planner_while_a_producer_works(self):
        # the planner is not a worker: gating it behind the rate would make it answer only in a producer's gaps
        self.w.session("implement-9", "implementer", "w9", task="9")
        self.w.v2("dispatch", env={"ORCH_WORKERS": "1"})
        self.event("Task 9 asks something of you.")
        self.w.v2("dispatch", env={"ORCH_WORKERS": "1"})
        (plan,) = self.forks("plan-")
        self.assertIn("Task 9 asks something of you.", plan[-1])

    def test_the_next_planner_starts_only_from_a_knowledge_base_that_holds_the_last_one_s_notes(self):
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json", origin="kb-1")
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.write(".build/plans/plan-1/notes.md", "Decided: readiness is a path.")
        self.assertIn("planned", self.as_("plan-1", "planned", "--notes", ".build/plans/plan-1/notes.md"))
        self.event("Task 4 is committed.")
        self.w.v2("dispatch")
        self.assertEqual(self.forks("plan-"), [])  # its notes are not in the knowledge base yet
        self.assertEqual(len(self.w.st()["events"]), 1)
        self.w.reply("kbsid", "INTEGRATED")
        self.w.v2("dispatch")
        (second,) = self.forks("plan-")
        self.assertIn("Task 4 is committed.", second[-1])

    def test_the_owner_joins_the_planner_that_lives_rather_than_opening_another(self):
        self.event("Task 1 is committed.")
        self.w.v2("dispatch")
        self.assertEqual(len(self.forks("plan-")), 1)
        self.w.set_status("plan-1", "idle")
        st = self.w.st()
        st["sessions"]["plan-1"]["state"] = "idle"
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.assertEqual(self.w.v2("talk"), "plan-1")
        self.assertEqual(len(self.forks("plan-")), 1)  # no second planner: the owner joins the one that holds it all
        self.assertTrue(self.s("plan-1")["owner"])
        self.assertEqual(self.w.v2("who", "planner"), "plan-1")  # attach.sh finds it between its events
        (resumed,) = self.resumes(self.s("plan-1")["sid"])
        self.assertIn("The owner is here", resumed[-1])

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
        self.assertIn("planned", self.as_("plan-1", "planned", "--notes", ".build/plans/plan-1/notes.md"))
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

    def test_a_session_is_told_where_it_works_and_only_when_it_works_there(self):
        # every role was told "your working tree is your task's own (.build/trees/{ID})": the planner, the task
        # designer, the reviewer and the consultations have no tree, and a task whose work already stands in the one
        # tree keeps working there (2026-09-20)
        for role in ("planner", "task-designer", "reviewer", "consultant", "kb"):
            text = open(Path(v2.PROTOCOLS) / f"{role}.md").read()
            self.assertNotIn("{{tree}}", text, f"the {role} has no working tree of its own")
        # a task with no tree of its own is told it works in the one tree (the prompt of one that has its own is
        # asserted where the tree is made: test_a_producing_session_is_started_in_its_task_s_own_tree)
        self.assertIn("**You work in the repository's one working tree**", self.py_tree("5"))
        self.assertNotIn(".build/trees", self.py_tree("5"))

    def py_tree(self, tid):
        code = (f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; print(v2.tree_text({tid!r}), end='')")
        return subprocess.run([sys.executable, "-c", code], env=self.w.env, capture_output=True, text=True).stdout

    def test_every_role_of_a_base_forks_its_layer_when_one_is_recorded(self):
        # the layer is the stable base with the current frontier on it; a fork of it reads the whole prefix under it
        # from cache (measured 2026-09-20: 538,051 of 538,044 tokens, 62 written)
        self.w.base("xhigh", sid="xhigh-sid")
        st = self.w.st()
        st["sessions"]["xhigh-base"] = {}  # not a session record; the base record is the file
        (self.w.state / "xhigh-base.json").write_text(json.dumps(
            {"sessionId": "xhigh-sid", "model": "claude-opus-5[1m]", "effort": "xhigh", "context": 310_000}))
        self.assertEqual(self.py("print(v2.base_record('xhigh')[1]['sid'])"), "xhigh-sid")
        (self.w.state / "xhigh-layer.json").write_text(json.dumps(
            {"sessionId": "xhigh-layer-sid", "model": "claude-opus-5[1m]", "effort": "xhigh", "context": 525_000,
             "base": "xhigh-sid"}))
        self.assertEqual(self.py("print(v2.base_record('xhigh')[1]['sid'])"), "xhigh-layer-sid")
        # and the room a task is given is what the layer leaves, not what the stable base alone would
        self.assertEqual(self.py("print(v2.room_of('design'))"), str(v2.SOFT - 525_000 - v2.PROTOCOL_ROOM))

    def py(self, code):
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n{code}"],
                             env=self.w.env, capture_output=True, text=True)
        return out.stdout.strip()

    def test_only_the_roles_that_edit_the_graph_are_on_the_shared_task_list(self):
        # one settings file carries CLAUDE_CODE_TASK_LIST_ID, and every session started with it sees the others'
        # edits to that list injected into its context. The knowledge base was on it, could not edit it, and passed
        # what was injected to every session forked from it (2026-09-20).
        listed = json.loads((Path(v2.HERE) / v2.GRAPH_SETTINGS).read_text()).get("env", {})
        self.assertIn("CLAUDE_CODE_TASK_LIST_ID", listed, "the graph settings no longer name a shared list")
        for role, spec in v2.ROLES.items():
            if spec.get("settings") is None:
                continue  # a consultation takes its origin's, and so is on the list only if what it forks is
            self.assertEqual(spec["settings"] == v2.GRAPH_SETTINGS, bool(spec.get("graph")),
                             f"{role} is on the shared graph but may not edit it, or the other way round")
        other = json.loads((Path(v2.HERE) / "worker-settings.json").read_text())
        self.assertNotIn("CLAUDE_CODE_TASK_LIST_ID", other.get("env", {}))
        graph = json.loads((Path(v2.HERE) / v2.GRAPH_SETTINGS).read_text())
        graph.pop("env")
        self.assertEqual(graph, other, "the two settings files differ in more than the shared list")

    def test_the_planner_is_told_when_its_state_has_become_a_log(self):
        # HANDOFF.md went from 6.5K characters to 81K in a day, and the two condensations in it came to 2.6K against
        # 80K added: nothing measured it, so nothing pushed the other way (2026-09-20)
        self.w.write("HANDOFF.md", "# H\n\n## Graph\ng\n\n## Decisions\n" + ("a settled decision, restated. " * 8000)
                     + "\n\n## Delivered\n-\n\n## Open\n-\n\n## Now\nw\n")
        said = self.w.v2("status")
        self.assertRegex(said, r"HANDOFF\.md: \d+K tokens of at most 60K")
        self.assertIn("over it; `## Decisions`", said)
        self.assertIn("your state, not your log", said)
        # it says where each thing goes: the log to its own file, the development's decisions to DECISIONS.md,
        # and a planning decision to the task it governs
        self.assertIn(f"how goes to {v2.PLANNER_LOG}", said)
        self.assertIn("never takes planning, scheduling or anything else operational", said)
        self.assertIn("belongs to the task it governs", said)
        self.w.write("HANDOFF.md", PLANNER_STATE)
        said = self.w.v2("status")
        self.assertIn("HANDOFF.md: 0K tokens of at most 60K", said)
        self.assertNotIn("over it", said)

    def test_the_log_is_the_planner_s_and_no_base_holds_it(self):
        import select_base_load
        self.assertIn(v2.PLANNER_LOG, select_base_load.NEVER)   # never held, so it may grow
        self.assertIn(v2.PLANNER_LOG, v2.EXEMPT)                # and it is never a task's change in the tree
        for who in ("max", "xhigh", "high"):
            self.assertNotIn(v2.PLANNER_LOG, (Path(v2.HERE) / f"base-load-{who}.txt").read_text())

    def test_the_hold_stops_anything_from_starting_a_session(self):
        # starting one by accident costs a cold write of a whole base; the hold is the owner's switch for the time
        # between the machinery being ready and the run beginning (2026-09-20)
        (self.w.state / v2.NO_LAUNCH).write_text("while the bases are built")
        self.assertIn("refused", self.w.v2("start"))
        self.assertIn("while the bases are built", self.w.v2("start"))
        self.w.set_st(events=[{"at": "2026-09-20T10:00:00", "from": "x", "text": "e"}])
        self.w.v2("dispatch")
        self.assertEqual(self.forks(), [])          # nothing was forked at all
        self.assertIn("a session was not started", (self.w.state / "v2.log").read_text())
        (self.w.state / v2.NO_LAUNCH).unlink()
        self.w.v2("dispatch")
        self.assertTrue(self.forks("plan-"))        # and off it goes once the hold is lifted

    def test_a_keep_warm_ping_is_not_work_and_goes_through_the_hold(self):
        (self.w.state / v2.NO_LAUNCH).write_text("held")
        self.w.session("brief-4", "task-designer", "b4", task="4", live=False, settings="planner-settings.json")
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "v2.ping('brief-4')"], env=dict(self.w.env, ORCH_PING_WAIT="0"),
                             capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertTrue([c for c in self.w.calls("--bg") if "warm-brief-4" in c["args"]])

    def test_no_shared_part_is_said_twice_in_one_message(self):
        # _inherited.md and _held.md held the same sentence, and every role but the consultant included both: the
        # same line, with the same value, twice in one first message (2026-09-20)
        import re as _re
        parts = {f.name: f.read_text().strip() for f in Path(v2.PROTOCOLS).glob("_*.md")}
        same = [(a, b) for a in parts for b in parts if a < b and parts[a] == parts[b]]
        self.assertEqual(same, [], "two shared parts hold the same text")
        for role in v2.ROLES:
            named = _re.findall(r"\{\{([\w-]+)\}\}", (Path(v2.PROTOCOLS) / f"{role}.md").read_text())
            self.assertEqual(sorted(named), sorted(set(named)), f"{role} includes a part twice")

    def test_no_message_names_a_command_that_is_not_one(self):
        # `briefed` outlived its command in ctx_gauge's end-of-window instruction, which is what a session is told to
        # run when its window closes — the one moment it cannot afford a refusal (2026-09-20)
        import re as _re
        here = Path(v2.HERE)
        src = "".join(open(here / f).read() for f in ("v2.py", "work_meter.py", "ctx_gauge.py", "finalize.py"))
        cli = set(_re.findall(r'c == "([a-z-]+)"', open(here / "v2.py").read()))
        for cmd in sorted(set(_re.findall(r"v2\.py\s+([a-z-]+)", src))):
            if cmd == "run":       # "v2.py run from there" — prose about running it, not a command
                continue
            self.assertIn(cmd, cli, f"a message names `v2.py {cmd}`, which is not a command")

    def test_the_readme_s_roles_table_names_the_base_each_role_actually_forks(self):
        # the owner's first page: it said a designer forks the knowledge base at max while ROLES has had it fork the
        # middle base, and its own prose two pages down said the middle base (2026-09-21)
        import re as _re
        rows = {}
        for line in open(Path(v2.HERE) / "README.md"):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) == 4 and cells[1].startswith("`"):
                rows[cells[1].strip("`").split("-")[0]] = cells[3]
        for role, spec in v2.ROLES.items():
            origin = spec["origin"]
            while origin and origin not in v2.BASES:      # the planner forks the knowledge base, which forks max
                origin = (v2.ROLES.get(origin) or {}).get("origin")
            cell = rows.get(spec["prefix"])
            self.assertIsNotNone(cell, f"README's roles table has no row for {spec['prefix']}-N ({role})")
            if origin:
                self.assertTrue(_re.search(rf"\b{origin}\b", cell),
                                f"README says {role} forks '{cell}'; ROLES makes it a fork of {origin}")

    def test_no_message_gives_the_graph_to_a_role_that_has_it_not(self):
        # the task designer stopped writing the graph on 2026-09-21 and began proposing it, and `blockers` went on
        # refusing every other role by naming it as one that may — the refusal named the role it was refusing, and
        # the usage banner said so too
        import re as _re
        here = Path(v2.HERE)
        src = "".join(open(here / f).read() for f in ("v2.py", "work_meter.py", "ctx_gauge.py"))
        src += "".join(p.read_text() for p in sorted(Path(v2.PROTOCOLS).glob("*.md")))
        for role, spec in v2.ROLES.items():
            if spec.get("graph"):
                continue
            for line in src.splitlines():
                if "v2.py blockers" in line or "v2.py queue" in line or "v2.py accept" in line:
                    self.assertNotIn(f"{role.replace('-', ' ')}: ", line.lower(),
                                     f"a message gives {role} a command only the graph's role may run: {line.strip()}")

    def test_no_message_or_protocol_names_an_option_its_command_does_not_read(self):
        # the other half of the `briefed` fault: a command that stays and an option that is renamed leaves every
        # instruction naming it refused at the moment it is followed
        import re as _re
        here = Path(v2.HERE)
        src = open(here / "v2.py").read()
        bodies = {}
        for m in _re.finditer(r"\ndef (\w+)\(", src):
            nxt = src.find("\ndef ", m.start() + 1)
            bodies[m.group(1)] = src[m.start():nxt if nxt != -1 else len(src)]
        opts = {}
        for b in _re.split(r'\n    (?:el)?if c == "', bodies["main"])[1:]:
            name, body = b[:b.index('"')], b
            for fn in _re.findall(r"(cmd_\w+)\(", b):   # a command parses its own options inside cmd_X too
                body += bodies.get(fn, "")
            opts[name] = set(_re.findall(r'"(--[a-z-]+)"', body))
        files = [here / f for f in ("v2.py", "work_meter.py", "ctx_gauge.py", "finalize.py")]
        files += sorted(Path(v2.PROTOCOLS).glob("*.md"))
        for f in files:
            text = f.read_text()
            # a protocol writes one command over several lines; in the sources only a single line is a command
            spans = (_re.findall(r"`([^`]*v2\.py[^`]*)`", text.replace("\n", " ")) if f.suffix == ".md"
                     else _re.findall(r"`([^`\n]*v2\.py[^`\n]*)`", text))
            for span in spans:
                m = _re.search(r"v2\.py\s+([a-z-]+)", span)
                if not m:
                    continue
                for o in _re.findall(r"(--[a-z-]+)", span):
                    self.assertIn(o, opts.get(m.group(1), set()),
                                  f"{f.name} names `v2.py {m.group(1)} {o}`, which it does not read")

    def test_every_command_a_protocol_names_exists_and_its_role_may_run_it(self):
        # protocols are what the agents act on, so a command renamed or withdrawn leaves them following an
        # instruction that refuses: `briefed` outlived its command, and the task designer was told to run
        # `v2.py blockers` after its graph rights were taken away (2026-09-20)
        import re as _re
        source = open(Path(v2.HERE) / "v2.py").read()
        cli = set(_re.findall(r'c == "([a-z-]+)"', source))
        graph_only = {"blockers", "queue", "drop", "after", "planned", "carried", "tell", "accept"}
        for f in sorted(os.listdir(Path(v2.PROTOCOLS))):
            if not f.endswith(".md"):
                continue
            named = set(_re.findall(r"v2\.py\s+([a-z-]+)", open(Path(v2.PROTOCOLS) / f).read()))
            for cmd in named:
                self.assertIn(cmd, cli, f"protocols/{f} names `v2.py {cmd}`, which is not a command")
            role = f[:-3]
            if role in v2.ROLES and not v2.ROLES[role].get("graph"):
                self.assertFalse(named & graph_only,
                                 f"protocols/{f}: {role} does not edit the graph and is told to run "
                                 f"{', '.join(sorted(named & graph_only))}")

    def test_every_form_the_harness_checks_is_in_the_protocol_of_who_must_write_it(self):
        # a form checked and never stated is a refusal a session cannot foresee, and for a proposal it costs the
        # whole session: the task designer's protocol never named a brief's fields (2026-09-21)
        def rendered(role):
            import re as _re
            text = open(Path(v2.PROTOCOLS) / f"{role}.md").read()
            for _ in range(2):
                text = _re.sub(r"\{\{([\w-]+)\}\}",
                               lambda m: open(Path(v2.PROTOCOLS) / f"_{m.group(1)}.md").read(), text)
            return text
        for role in v2.PRODUCING:
            text = rendered(role)
            self.assertIn("Status:", text)
            for s in v2.RESULT_SECTIONS:
                self.assertIn(s, text, f"the {role} records a result and its protocol never names `## {s}`")
        review = rendered("reviewer")
        for s in ("## Summary", "## Findings"):
            self.assertIn(s, review, f"a verdict is checked for `{s}` and the reviewer is never told")
        plan = rendered("planner")
        for s in v2.PLANNER_SECTIONS:
            self.assertIn(f"## {s}", plan, f"HANDOFF.md is checked for `## {s}` and the planner is never told")

    def test_every_role_that_writes_a_brief_is_given_the_brief_s_form(self):
        # the task designer's whole production is briefs, and its protocol never stated their form: it had one
        # example, its own brief task, while `propose` refuses a proposal whole when one description is out of
        # form — a refusal that costs a task designer's session (2026-09-21)
        import re as _re
        for role in ("planner", "task-designer"):
            text = open(Path(v2.PROTOCOLS) / f"{role}.md").read()
            for _ in range(2):
                text = _re.sub(r"\{\{([\w-]+)\}\}",
                               lambda m: open(Path(v2.PROTOCOLS) / f"_{m.group(1)}.md").read(), text)
            for f in v2.BRIEF_FIELDS:
                self.assertIn(f"{f}:", text, f"the {role} writes briefs and its protocol never names `{f}:`")
        # and what a proposal is refused for beside the form: a build or fix without its review task
        self.assertIn("review task", open(Path(v2.PROTOCOLS) / "task-designer.md").read())

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

    def test_a_dependency_written_the_wrong_way_round_can_be_taken_back(self):
        # the planner wrote `after 7 48` meaning the other way, could not remove it, and adopted an order it had not
        # chosen rather than deadlock the graph (2026-09-20)
        self.w.task("1", subject="The waiting task")
        self.w.task("2", subject="The fix")
        self.w.set_st(tasks={"1": {"stage": "running"}, "2": {"stage": "ready"}})
        self.w.session("plan-1", "planner", "p1", state="working")
        said = self.as_("plan-1", "after", "1", "2")
        self.assertIn("TASK 1 WAITS FOR TASK 2", said)  # the direction, in full
        self.assertIn("v2.py after 2 1", said)          # and how to say the other one
        self.assertEqual(self.w.st()["tasks"]["1"]["efficiency_fix"], "2")
        back = self.as_("plan-1", "after", "1", "none")
        self.assertIn("waits for nothing now", back)
        self.assertIn("it waited for task 2", back)
        self.assertIsNone(self.w.st()["tasks"]["1"].get("efficiency_fix"))

    def test_state_that_nothing_names_any_more_is_swept(self):
        self.w.session("design-2", "designer", "d2", state="done", live=False)
        self.w.session("design-3", "designer", "d3", state="lost", live=False)
        self.w.session("implement-1", "implementer", "i1", task="1")
        (self.w.state / "mail").mkdir(exist_ok=True)
        for who, text in (("gone-4", ""), ("design-2", ""), ("design-3", '{"from": "x", "text": "y", "at": "t"}\n'),
                          ("implement-1", "")):
            (self.w.state / "mail" / f"{who}.jsonl").write_text(text)
        (self.w.state / "old-session.woken").write_text("x")
        os.utime(self.w.state / "old-session.woken", (time.time() - 200_000, time.time() - 200_000))
        (self.w.state / "fresh.woken").write_text("x")
        (self.w.state / "base-pack-20260101T000000-1").mkdir()
        for who in ("max", "xhigh", "high"):  # every base names its pack, as a built one does
            f = self.w.state / f"{who}-base.json"
            d = json.loads(f.read_text()) if f.exists() else {"sid": who, "model": "m", "effort": who}
            d["pack"] = str(self.w.state / f"base-pack-{who}")
            f.write_text(json.dumps(d))
        gone = eval(subprocess.run(
            [sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
             "print(repr(sorted(v2.tidied())))"], env=self.w.env, capture_output=True, text=True).stdout.strip())
        self.assertIn("base-pack-20260101T000000-1", gone)  # no base names it
        self.assertIn("old-session.woken", gone)
        self.assertNotIn("fresh.woken", gone)              # a wake attach.sh may still read
        self.assertTrue((self.w.state / "fresh.woken").exists())
        self.assertIn("mail/gone-4.jsonl", gone)           # no session of that name is in the state any more
        self.assertIn("mail/design-2.jsonl", gone)         # its session reads nothing ever again, and it is empty
        self.assertNotIn("mail/design-3.jsonl", gone)      # said to have reached nobody, and kept to be read
        self.assertNotIn("mail/implement-1.jsonl", gone)   # its session is still working

    def test_the_planner_cannot_name_a_fix_that_waits_on_the_task_it_fixes(self):
        self.w.task("1", subject="The waiting task")
        self.w.task("2", subject="The fix", blockedBy=["1"])
        self.w.set_st(tasks={"1": {"stage": "running"}, "2": {"stage": "ready"}})
        self.w.session("plan-1", "planner", "p1", state="working")
        self.assertIn("could never land", self.as_("plan-1", "after", "1", "2"))
        self.w.task("3", subject="A fix of its own", blockedBy=[])
        self.assertIn("TASK 1 WAITS FOR TASK 3", self.as_("plan-1", "after", "1", "3"))

    def test_a_fresh_knowledge_base_near_its_limit_asks_for_condensing_and_a_base_rebuild(self):
        self.w.set_st(kb_building="kb-2")
        self.w.session("kb-2", "kb", "k2", kb_state="building", settings="planner-settings.json", started=time.time() - 5)
        self.w.transcript("k2", [fakes.assistant("m1", fakes.iso(time.time()), [{"type": "text", "text": "INTEGRATED"}],
                                                 usage={"input_tokens": 0, "cache_read_input_tokens": v2.KB_MAX - 10_000,
                                                        "cache_creation_input_tokens": 0, "output_tokens": 5})])
        self.w.v2("dispatch")
        self.assertIn("condense HANDOFF.md", self.heard())
        self.assertIn("a base rebuild is due (the owner's)", (self.w.state / "v2.log").read_text())

    def test_events_start_a_planner_and_a_lost_one_gives_them_back(self):
        self.w.set_st(events=[{"at": time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(time.time() - 60)),
                               "from": "review-3", "text": "Task 3 accepted."}])
        self.w.v2("dispatch")
        (plan,) = self.forks("plan-")
        self.assertIn("from review-3: Task 3 accepted.", plan[-1])
        self.assertEqual(self.w.st()["events"], [])
        self.w.set_rows([r for r in self.w.rows() if r["name"] != "plan-1"])
        for _ in range(3):
            self.w.run("watchdog.py")
        again = self.forks("plan-")[1]  # the next planner is given them again
        self.assertIn("Task 3 accepted.", again[-1])
        self.assertIn("The planner plan-1 is gone before it wrote its notes", again[-1])
        self.assertIn("HANDOFF.md is all that carries over", again[-1])

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

    def test_a_task_taken_out_of_the_list_while_the_harness_works_on_it_is_named(self):
        # the planner does take tasks out of the list: 21 and 51 were gone from it on 2026-09-20 while the state
        # still held them. The conflict check read "completed" alone, so a task deleted under a live session — or a
        # parked one, which produce() resumes on its own — was the one case nothing said anything about.
        (self.w.tasks / "1.json").unlink()
        self.w.v2("dispatch")
        self.assertIn("Task 1 is not in the task list at all", self.heard())
        self.assertIn("task 1 is not in the list and running in the harness", (self.w.state / "v2.log").read_text())
        # and the same conflict when it is there and completed, which is the half that was already covered
        self.w.task("1", status="completed")
        (self.w.state / "finished-1").unlink()
        self.w.v2("dispatch")
        self.assertIn("Task 1 is completed in the task list", self.heard())

    def test_a_session_that_ends_with_its_question_open_is_told_where_the_answer_goes(self):
        # six of nineteen answers on 2026-09-20 came to a session that had ended, and the planner carried each
        self.assertIn("asked as q1", self.as_(self.impl, "ask", "--to", "planner", "Which of the two?"))
        said = self.finish()
        self.assertIn("your question q1 is still open", said.lower())
        self.assertIn(".build/tasks/1/answers/", said)
        self.assertIn("what you assumed", said)

    def test_a_check_that_would_leave_the_base_in_the_task_s_own_directory_is_refused(self):
        # task 7's final check was given --output .build/tasks/7/final-check on 2026-09-20, and the repository's base
        # came to stand there: dropping that task or sweeping its run output would have taken it
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.w.write(".build/tasks/1/commit.md", "Add readiness\n\nValidation: checked.\n")
        refusal = self.as_(self.impl, "finalize", "1", "--check",
                           "python3 -B tools/incremental_check.py check --advance-base --output .build/tasks/1/final",
                           "--files", "theories/Ready.thy", "--message", ".build/tasks/1/commit.md")
        self.assertIn("refused", refusal)
        self.assertIn(".build/tasks/1/final", refusal)
        self.assertFalse((self.w.project / ".build/tasks/1/finalize.json").exists())
        # the same check under .build/ directly is the one the repository's own checks use
        self.assertIn("prepared", self.as_(self.impl, "finalize", "1", "--check",
                                           "python3 -B tools/incremental_check.py check --advance-base "
                                           "--output .build/check-20260920z",
                                           "--files", "theories/Ready.thy", "--message", ".build/tasks/1/commit.md"))

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
        # a finished task's own artifacts are sources too, and a fixer or a reviewer opens its step with them
        m["productions"] = 2
        meter.write_text(json.dumps(m))
        self.finish()
        out = self.as_(self.impl, "step", "1", "3", "result", "log", "diff")
        self.assertIn("== result\nStatus: done", out)
        self.assertIn("== log", out)
        self.assertIn("== diff\n", out)
        self.assertIn("theories/Ready.thy", out)        # the new file's own text, which no diff of HEAD shows

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

    def test_a_producing_session_is_started_in_its_task_s_own_tree(self):
        # task 1 is already running in this fixture; task 5 is the one that starts with trees on
        self.w.task("5", description=BRIEF, subject="Another build")
        self.w.set_st(queue=["5"], tasks={"1": {"stage": "done"},
                                          "5": {"stage": "ready", "kind": "build", "queued_at": time.time()}},
                      sessions={k: (v | {"state": "done"} if k == self.impl else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.v2("dispatch", env=dict(self.w.env, ORCH_TREES="1"))
        tree = self.w.project / ".build/trees/5"
        self.assertTrue((tree / "ROOT").exists() or (tree / "README").exists())  # a checkout of its own
        self.assertTrue((tree / ".build").is_symlink())  # one .build, so drafts and checks are where they were
        self.assertEqual(os.path.realpath(tree / ".build"), os.path.realpath(self.w.project / ".build"))
        self.assertIn(".build", (self.w.project / ".git/info/exclude").read_text())  # the link is never committed
        (impl,) = [c["args"] for c in self.w.calls("--bg") if "-n" in c["args"]
                   and c["args"][c["args"].index("-n") + 1] == "implement-5"]
        self.assertIn("Your working tree is your task's own", impl[-1])  # and it is told so, because it is true
        self.assertIn(".build/trees/5", impl[-1])
        self.assertEqual(self.w.st()["sessions"]["implement-5"]["tree"], ".build/trees/5")
        (call,) = [c for c in self.w.calls() if "--fork-session" in c["args"] and "implement-5" in c["args"]]
        self.assertEqual(call["cwd"], str(tree))  # and it is forked there, so it works there

    def test_a_task_whose_work_already_stands_in_the_one_tree_keeps_working_there(self):
        # a tree of its own would be a checkout of HEAD without what it has installed
        self.w.write("theories/Standing.thy", "theory Standing imports Main begin end\n")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.own('5', ['theories/Standing.thy'])"], env=self.w.env, check=True)
        self.w.task("5", description=BRIEF, subject="A build with work already installed")
        self.w.set_st(queue=["5"], tasks={"1": {"stage": "done"},
                                          "5": {"stage": "ready", "kind": "build", "queued_at": time.time()}},
                      sessions={k: (v | {"state": "done"} if k == self.impl else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.v2("dispatch", env=dict(self.w.env, ORCH_TREES="1"))
        self.assertFalse((self.w.project / ".build/trees/5").exists())
        self.assertIsNone(self.w.st()["sessions"]["implement-5"].get("tree"))

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

    def test_trouble_in_a_tasks_own_tree_is_not_reported_as_the_shared_one(self):
        # on 2026-09-20 the planner was told twice, at 20:24 and 20:25, that "the working tree is inconsistent …
        # ROOT declares Development_Loci, which is not in theories/" and that every task's check refuses on it. The
        # shared tree held the file and was consistent throughout; the trouble was task 46's own worktree, branched
        # from a HEAD that declares a theory whose file is untracked, and nothing but task 46 checks that tree.
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n")
        self.w.write("theories/Base.thy", "theory Base imports Main begin end\n")
        self.w.write(".build/trees/46/ROOT", "session S = HOL +\n  theories\n    Base\n    Loci\n")
        self.w.write(".build/trees/46/theories/Base.thy", "theory Base imports Main begin end\n")
        call = (f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2, os; "
                "v2.tree_checked('the harness', \"task 46's check was about to run\", "
                "os.path.join(v2.PROJECT, '.build/trees/46'))")
        subprocess.run([sys.executable, "-c", call], env=self.w.env, capture_output=True, text=True)
        told = " ".join(e["text"] for e in self.w.st()["events"])
        self.assertIn("The working tree of task 46 (.build/trees/46) is inconsistent", told)
        self.assertIn("ROOT declares Loci, which is not in theories/", told)
        self.assertIn("the shared working tree is not affected", told)
        self.assertNotIn("Every task's check refuses", told)
        # and the same trouble in the same tree is not put to it again at the next attempt
        subprocess.run([sys.executable, "-c", call], env=self.w.env, capture_output=True, text=True)
        self.assertEqual(len(self.w.st()["events"]), 1)

    def test_trouble_in_the_shared_tree_still_says_every_check_refuses(self):
        self.w.write("ROOT", "session S = HOL +\n  theories\n    Base\n    Gone\n")
        self.w.write("theories/Base.thy", "theory Base imports Main begin end\n")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.tree_checked('the harness', 'a commit', None)"],
                       env=self.w.env, capture_output=True, text=True)
        told = " ".join(e["text"] for e in self.w.st()["events"])
        self.assertIn("The working tree is inconsistent after a commit", told)
        self.assertIn("Every task's check refuses on this", told)

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
        said = json.dumps(self.w.mail(self.impl))
        self.assertIn("check is running and sees the working tree", said)
        # and it says what becomes of its changes: nothing is taken out of the tree, which is why they stay whole
        self.assertIn("parked and writes nothing meanwhile", said)
        self.assertNotIn("left it", said)
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
        # every event of the whole cycle reached one planner (heard() above), and only one was ever forked for them:
        # 28 of the 59 sessions of 2026-09-20 were planning episodes, one per batch of events
        self.assertEqual(len(self.forks("plan-")), 1)

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
        self.assertIn("TASK 1 WAITS FOR TASK 3", self.as_("plan-2", "after", "1", "3"))
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

    def test_a_question_to_the_planner_reaches_it_at_once(self):
        # questions waited for an episode: 4 to 13 minutes on 2026-09-20, and 84 for two of them, by when their
        # sessions had ended and the answer had to be carried
        self.w.session("plan-3", "planner", "p3", state="idle", live=False, settings="planner-settings.json",
                       origin="kb-1")
        self.w.v2("ask", "--to", "planner", "Split the task?", env=self.w.as_session("i1"))
        self.assertEqual(self.w.st()["events"], [])  # nothing waits: it went straight to the planner
        self.assertIn("Question q1", self.resumes("p3")[-1][-1])
        self.assertEqual(self.forks("plan-"), [])  # and no second planner was forked for it
        self.w.set_status("implement-1", "idle")
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

    def test_a_base_standing_in_a_task_s_directory_is_named(self):
        # the accepted base stood in .build/tasks/7/check2/proof on 2026-09-20, because an advancing check was run
        # with its output there: dropping that task or sweeping its run output would have taken the base with it
        proof = self.w.project / ".build/tasks/7/check2/proof"
        proof.mkdir(parents=True)
        (proof / "accepted-context.json").write_text(json.dumps({"parent": None}))
        (self.w.state / "active-context.json").write_text(json.dumps({"directory": str(proof)}))
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(len(v2.base_lineage()), len(v2.base_at_risk()))"],
                             env=self.w.env, capture_output=True, text=True).stdout
        self.assertEqual(out.strip(), "1 1")

    def test_a_cli_call_that_never_returns_does_not_hold_the_harness(self):
        # the watchdog runs the dispatch and the pings; a claude call that never returned would hold all of it,
        # with the daemon still alive and health.py still saying so
        slow = self.w.root / "bin" / "claude"
        slow.write_text("#!/bin/sh\nsleep 30\n")
        slow.chmod(0o755)
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "r = v2.claude('agents', '--json'); print(r.returncode)"],
                             env=dict(self.w.env, ORCH_CLAUDE_MAX="1"), capture_output=True, text=True, timeout=30)
        self.assertEqual(out.stdout.strip(), "124")
        self.assertIn("did not return within 1s", (self.w.state / "v2.log").read_text())

    def test_a_knowledge_base_that_never_finishes_loading_is_given_up(self):
        self.w.session("kb-2", "kb", "k2", kb_state="building", state="working",
                       started=time.time() - 4000, settings="planner-settings.json")
        self.w.set_st(kb_building="kb-2")
        self.w.v2("dispatch")
        self.assertIn("has been loading", (self.w.state / "v2.log").read_text())
        self.assertIsNone(self.w.st()["kb_building"])
        self.assertEqual(self.s("kb-2")["state"], "lost")

    def test_a_knowledge_base_that_never_finishes_integrating_is_given_up(self):
        # while it integrates, no episode and no consultation can fork it; nothing bounded that wait
        self.w.set_st(sessions={**self.w.st()["sessions"],
                                "kb-1": {**self.w.st()["sessions"]["kb-1"], "kb_state": "integrating",
                                         "integrating_since": time.time() - 3000}})
        self.w.v2("dispatch")
        self.assertIn("has been integrating", (self.w.state / "v2.log").read_text())
        self.assertEqual(self.s("kb-1")["state"], "lost")
        self.assertIn("did not finish integrating", self.heard())
        self.assertTrue(self.forks("kb-"))  # and a new one is built

    def test_the_status_says_which_tasks_could_start_now(self):
        # the width of the graph as the planner drew it: with one, nothing can take the producing slot while the task
        # holding it is parked or checking, which is how 2026-09-20 stood still for six and a half hours
        self.w.task("4", subject="Done already", status="completed")
        self.w.task("5", subject="Waits on a task still open", blockedBy=["6"])
        self.w.task("6", subject="Still open")
        self.w.task("7", subject="Waits on one that is done", blockedBy=["4"])
        self.w.set_st(queue=["5", "6", "7"],
                      tasks={"5": {"stage": "ready"}, "6": {"stage": "running"}, "7": {"stage": "ready"}})
        st = self.w.st()
        self.w.set_st(tasks=dict(st["tasks"]))
        import subprocess as sp
        out = sp.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                      "print(' '.join(v2.startable()))"], env=self.w.env, capture_output=True, text=True).stdout
        self.assertEqual(out.strip(), "7")  # 5 waits on an open task, 6 is already running
        said = self.w.v2("status")
        self.assertIn("startable now: 7", said)
        self.assertIn("only a wider graph changes that", said)

    def test_a_blocker_that_is_not_in_the_task_list_is_named(self):
        # task 6 waited on task 18, which had been dropped; nothing said so and the planner had to find it
        self.w.task("3", subject="Waiting on a task that is gone", blockedBy=["99"])
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.deps_done('3'))"], env=self.w.env, capture_output=True, text=True).stdout
        self.assertEqual(out.strip(), "False")
        self.assertIn("which is not in the task list", json.dumps(self.w.st()["events"]))

    def test_a_blocker_that_came_back_to_the_planner_is_named_too(self):
        # `v2.py drop` leaves the task pending in the list, so a dependent waited on it with nothing to complete it
        self.w.task("4", subject="The dropped one")
        self.w.task("5", subject="Waiting on it", blockedBy=["4"])
        self.w.set_st(tasks={"4": {"stage": "planner"}})
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.deps_done('5'))"], env=self.w.env, capture_output=True, text=True).stdout
        self.assertEqual(out.strip(), "False")
        self.assertIn("came back to you and has not been re-planned", json.dumps(self.w.st()["events"]))
        # and the planner is told at once what a drop leaves waiting
        self.w.session("plan-1", "planner", "p1", state="working")
        self.w.set_st(tasks={"4": {"stage": "running"}})
        self.assertIn("still the blocker of 5", self.as_("plan-1", "drop", "4"))

    def test_mail_is_kept_when_the_resume_that_would_carry_it_fails(self):
        # produce() took the mail into the text of a resume and discarded it when the resume failed; the watchdog's
        # own path kept it, this one did not (2026-09-20)
        self.w.session("implement-3", "implementer", "i3", task="3", state="parked")
        self.w.hit("implement-3", age=v2.WARM_MAX + 60)  # cold: the resume will fail
        self.w.task("3", subject="A parked build")
        self.w.set_st(queue=["3"], tasks={"3": {"stage": "parked", "kind": "build", "session": "implement-3",
                                                "parked": {"since": time.time(), "for": "tree", "holder": None}}})
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.post('implement-3', 'the planner', 'the answer it waited for')"],
                       env=self.w.env, check=True)
        self.w.v2("dispatch")
        self.assertIn("the answer it waited for", json.dumps(self.w.mail("implement-3")))

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

    def test_no_brief_is_detailed_while_the_slots_already_have_independent_work(self):
        # one brief task turned into 26 tasks while a single producing slot finished one build in a day. The cap was
        # on tasks that EXIST, which detained every brief while only 5 of 17 could start (2026-09-20): it is on the
        # work that can START, because a brief is what widens a graph rather than what drains it (the owner).
        for i in range(3):
            self.w.task(f"5{i}", description=BRIEF, subject=f"A build {i}")
        self.w.task("1", blockedBy=["50"])  # the fixture's own build task, out of the width
        self.w.set_st(queue=["2"], tasks={"1": {"stage": "reviewing", "kind": "build", "session": "implement-1"}})
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "3"})
        self.assertEqual(self.forks("brief-"), [])  # nothing is detailed: 3 can start and there are 3 slots
        log = (self.w.state / "v2.log").read_text()
        self.assertIn("no brief is detailed while 3 build and fix tasks can start and there are 3 slots", log)
        status = self.w.v2("status", env={"ORCH_GRAPH_WIDTH": "3"})
        self.assertIn("3 build and fix tasks can start, 3 slots to take them", status)
        self.assertIn("one is admitted again when the slots have taken what can start", status)
        # as the slots take them, briefing resumes (with the review it did instead out of the way)
        for i in range(2):
            self.w.task(f"5{i}", description=BRIEF, subject=f"A build {i}", status="completed")
        self.w.set_st(tasks={"1": {"stage": "done"}},
                      sessions={k: v for k, v in self.w.st()["sessions"].items() if not k.startswith("review-")})
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "3"})
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

    def propose(self, bid, sid, entries):
        d = self.w.project / ".build/tasks" / bid
        d.mkdir(parents=True, exist_ok=True)
        (d / "proposal.json").write_text(json.dumps(entries))
        return self.w.v2("propose", bid, f".build/tasks/{bid}/proposal.json", env=self.w.as_session(sid))

    def test_a_proposal_names_a_review_task_for_every_build(self):
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        (fork,) = self.forks("brief-")
        self.assertIn("## Your brief task", fork[-1])
        self.assertIn("reach is a closure", fork[-1])
        sid = self.s("brief-2")["sid"]
        build = {"key": "b", "subject": "A build", "why": "-", "blockedBy": [], "description": BRIEF}
        refused = self.propose("2", sid, [build])
        self.assertIn("task b is a build task without a review task", refused)
        self.assertEqual(self.t("2").get("stage"), "running")   # nothing recorded, nothing in the graph
        ok = self.propose("2", sid, [build, {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["b"],
                                             "description": REVIEW_TASK.format(task="b")}])
        self.assertIn("proposed 2 task(s)", ok)


    def test_a_new_task_is_allocated_above_claude_codes_own_high_water_mark(self):
        # Claude Code allocates ids from `.highwatermark` beside the task files. Taking one above the files alone
        # hands back an id it is about to use again, and the task written here would be overwritten: on 2026-09-20
        # the mark stood at 51 with task 52 already written (2026-09-20).
        self.w.task("3", subject="the highest file")
        (self.w.tasks / ".highwatermark").write_text("9")
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              "print(v2.create_task('s', 'd', {}, []))"],
                             env=self.w.env, capture_output=True, text=True).stdout.strip()
        self.assertEqual(out, "10")                                        # above the mark, not above the files
        self.assertEqual((self.w.tasks / ".highwatermark").read_text(), "10")   # and the mark is raised to it

    def test_the_designer_proposes_and_only_the_planner_writes_the_graph(self):
        # the task designer held graph rights and wrote straight into the task list, which IS the graph. It proposes
        # now, and the planner decides: the designer never re-authors its text and the planner never re-types it
        # (the owner, 2026-09-20)
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.assertFalse(v2.ROLES["task-designer"].get("graph"))
        proposal = [{"key": "rows", "subject": "The state's own rows", "why": "the verdict reads them",
                     "blockedBy": [], "description": BRIEF},
                    {"key": "rows-review", "subject": "Review the rows", "why": "-",
                     "blockedBy": ["rows"], "description": REVIEW_TASK.format(task="rows")}]
        (self.w.project / ".build/tasks/2").mkdir(parents=True, exist_ok=True)
        (self.w.project / ".build/tasks/2/proposal.json").write_text(json.dumps(proposal))
        said = self.w.v2("propose", "2", ".build/tasks/2/proposal.json", env=self.w.as_session(sid))
        self.assertIn("proposed 2 task(s); the planner places them", said)
        self.assertEqual(self.t("2")["stage"], "proposed")
        self.assertIn("proposes 2 task(s) and where to place them", self.heard())
        self.assertIn("the graph is yours alone to edit", self.heard())
        self.assertEqual([f for f in os.listdir(self.w.tasks) if "own rows" in (self.w.tasks / f).read_text()], [])
        # the planner places them, and the harness writes them as proposed
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        placed = self.as_("plan-1", "accept", "2")
        self.assertIn("placed rows as", placed)
        made = {json.loads((self.w.tasks / f).read_text())["subject"]: json.loads((self.w.tasks / f).read_text())
                for f in os.listdir(self.w.tasks) if f.endswith(".json")}
        rows, review = made["The state's own rows"], made["Review the rows"]
        self.assertEqual(review["blockedBy"], [rows["id"]])   # local keys resolved to the ids it allocated
        self.assertEqual(rows["metadata"]["kind"], "build")
        st = self.w.st()
        self.assertEqual(st["tasks"][review["id"]]["reviews"], rows["id"])
        self.assertEqual(st["queue"][:3], ["2", rows["id"], review["id"]])
        self.assertEqual((st["tasks"]["2"]["stage"], self.w.read_task("2")["status"]), ("done", "completed"))

    def test_placing_a_proposal_is_all_of_it_or_none(self):
        # tasks are written before their edges, so a failure part way would leave tasks with no edges, and placing it
        # again would write every one of them a second time. The failure is injected: allocation is sound enough
        # that a collision cannot be contrived, and this is the path a full disk or a lost permission takes.
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.propose("2", sid, [
            {"key": "a", "subject": "First", "why": "-", "blockedBy": [], "description": BRIEF},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        before = {f for f in os.listdir(self.w.tasks) if f.endswith(".json")}
        said = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n"
                               "done = []\n"
                               "real = v2.create_task\n"
                               "def failing(*a, **k):\n"
                               "    if done: raise RuntimeError('no room')\n"
                               "    done.append(1)\n"
                               "    return real(*a, **k)\n"
                               "v2.create_task = failing\n"
                               "print(v2.cmd_accept('2'))"],
                              env=self.w.env, capture_output=True, text=True).stdout
        self.assertIn("taken back", said)
        self.assertIn("no room", said)
        self.assertEqual({f for f in os.listdir(self.w.tasks) if f.endswith(".json")}, before)  # nothing left behind
        self.assertEqual(self.t("2")["stage"], "proposed")   # and the proposal still stands
        # a splice re-points work already in the graph, and a failure after that left an existing task waiting on
        # an id that had just been taken back: what it waited on before is put back with everything else
        self.w.task("8", subject="Already there", blockedBy=["7"])
        self.propose("2", sid, [
            {"key": "a", "subject": "First", "why": "-", "blockedBy": [], "description": BRIEF, "feeds": ["8"]},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        said = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2\n"
                               "real = v2.update_task\n"
                               "def failing(tid, **k):\n"
                               "    if k.get('blockedBy') and tid == '8': real(tid, **k); raise RuntimeError('no room')\n"
                               "    return real(tid, **k)\n"
                               "v2.update_task = failing\n"
                               "print(v2.cmd_accept('2'))"],
                              env=self.w.env, capture_output=True, text=True).stdout
        self.assertIn("taken back", said)
        self.assertEqual(self.w.read_task("8")["blockedBy"], ["7"])     # as it waited before
        self.assertEqual({f for f in os.listdir(self.w.tasks) if f.endswith(".json")}, before | {"8.json"})

    def test_the_depth_limit_admits_its_own_value_and_refuses_above_it(self):
        # every message says "at most GRAPH_DEPTH" and the rule is that a further goal is refused when the depth is
        # *above* the limit; the code refused at the limit itself, and the live chain stood at exactly 10
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.w.task("7", description=BRIEF, subject="already in the graph")
        goal = [{"key": "a", "subject": "A further goal", "why": "-", "blockedBy": ["7"], "description": BRIEF},
                {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
                 "description": REVIEW_TASK.format(task="a")}]
        for depth, expected in ((v2.GRAPH_DEPTH, "proposed 2 task(s)"),
                                (v2.GRAPH_DEPTH + 1, "refused, and the planner has it")):
            st = self.w.st()
            st["tasks"]["2"].update(stage="running", depth_at_start=depth)
            (self.w.state / "v2.json").write_text(json.dumps(st))
            self.assertIn(expected, self.propose("2", sid, goal), f"at depth {depth}")

    def test_a_proposal_that_needs_further_goals_past_the_limit_never_reaches_the_graph(self):
        # the rejection used to come after the designer had written every task into the list; it comes before now,
        # and what it wrote is a file, not a graph to unpick
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        st = self.w.st()
        st["tasks"]["2"]["depth_at_start"] = v2.GRAPH_DEPTH + 1
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.task("7", description=BRIEF, subject="already in the graph")
        proposal = [{"key": "a", "subject": "Hung past the frontier", "why": "-", "blockedBy": ["7"],
                     "description": BRIEF},
                    {"key": "a-review", "subject": "Its review", "why": "-", "blockedBy": ["a"],
                     "description": REVIEW_TASK.format(task="a")}]
        (self.w.project / ".build/tasks/2").mkdir(parents=True, exist_ok=True)
        (self.w.project / ".build/tasks/2/proposal.json").write_text(json.dumps(proposal))
        said = self.w.v2("propose", "2", ".build/tasks/2/proposal.json", env=self.w.as_session(sid))
        self.assertIn("refused, and the planner has it", said)
        self.assertIn("a are further goals, not further detail", said)
        self.assertIn("Nothing you wrote is lost", said)
        self.assertEqual(self.t("2")["stage"], "planner")
        self.assertEqual([f for f in os.listdir(self.w.tasks) if "Hung past" in (self.w.tasks / f).read_text()], [])

    def test_a_proposal_begun_under_the_depth_limit_may_place_work_anywhere(self):
        # the depth is taken once, when the brief starts: one begun under the limit places what its work needs,
        # without limit, rather than being halted half-drawn
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.assertLess(self.t("2")["depth_at_start"], v2.GRAPH_DEPTH)
        self.w.task("7", description=BRIEF, subject="already in the graph")
        said = self.propose("2", sid, [
            {"key": "a", "subject": "A further goal", "why": "-", "blockedBy": ["7"], "description": BRIEF},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        self.assertIn("proposed 2 task(s)", said)

    def test_a_proposal_past_the_limit_may_still_place_detail_and_work_that_runs_first(self):
        # past the limit a brief may still splice detail in and add work that runs first — that is what widens the
        # graph — and only a further goal hung past its frontier is refused
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        st = self.w.st()
        st["tasks"]["2"]["depth_at_start"] = v2.GRAPH_DEPTH + 1
        (self.w.state / "v2.json").write_text(json.dumps(st))
        said = self.propose("2", sid, [
            {"key": "a", "subject": "Runs at once", "why": "-", "blockedBy": [], "description": BRIEF},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        self.assertIn("proposed 2 task(s)", said)

    def test_detail_spliced_into_the_graph_is_admitted_past_the_depth_limit(self):
        # adding more detail to a task graph is fine; adding further goals is not (the owner, 2026-09-20). Driven
        # through propose, not through the predicate: the rule was once written twice and the weaker copy was the
        # one in force, with a green test covering the dead one.
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        st = self.w.st()
        st["tasks"]["2"]["depth_at_start"] = v2.GRAPH_DEPTH + 1
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.task("7", description=BRIEF, subject="already in the graph")
        self.w.task("8", description=BRIEF, subject="already there, and will wait on the new work")
        spliced = [{"key": "a", "subject": "Spliced in", "why": "-", "blockedBy": ["7"], "feeds": ["8"],
                    "description": BRIEF},
                   {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
                    "description": REVIEW_TASK.format(task="a")}]
        self.assertIn("proposed 2 task(s)", self.propose("2", sid, spliced))   # detail: 8 will wait on it
        hung = [dict(e) for e in spliced]
        hung[0].pop("feeds")                                                   # the same work, waited on by nothing
        self.assertIn("refused, and the planner has it", self.propose("2", sid, hung))

    def test_accept_wires_feeds_so_the_existing_task_waits_on_the_new_work(self):
        # `feeds` is what splices work in rather than hanging it off the end, so it must actually be wired: a task
        # that claims it and is not wired would have dodged the depth rule and changed nothing
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.w.task("7", description=BRIEF, subject="already in the graph")
        self.w.task("8", description=BRIEF, subject="waits on the new work", blockedBy=["2"])
        self.propose("2", sid, [
            {"key": "a", "subject": "Spliced in", "why": "-", "blockedBy": ["7"], "feeds": ["8"], "description": BRIEF},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.as_("plan-1", "accept", "2")
        made = {json.loads((self.w.tasks / f).read_text())["subject"]: json.loads((self.w.tasks / f).read_text())
                for f in os.listdir(self.w.tasks) if f.endswith(".json")}
        new_id = made["Spliced in"]["id"]
        self.assertEqual(made["Spliced in"]["blockedBy"], ["7"])
        self.assertEqual(self.w.read_task("8")["blockedBy"], [new_id])   # 8 waits on it, and no longer on the brief
        self.assertEqual(made["Its review"]["blockedBy"], [new_id])

    def test_a_proposal_key_may_not_shadow_a_task_id(self):
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        self.w.task("7", description=BRIEF, subject="already in the graph")
        said = self.propose("2", sid, [{"key": "7", "subject": "Shadows 7", "why": "-", "blockedBy": [],
                                        "description": BRIEF}])
        self.assertIn("its key is the id of a task already in the list", said)

    def test_a_proposal_cannot_dodge_the_rule_by_feeding_a_task_that_is_not_there(self):
        # `feeds` is the whole of what makes a task detail, so it is checked rather than taken on trust: an
        # unchecked one would exempt the task from the depth rule and then silently not be wired
        self.w.set_st(queue=["2", "7"])
        self.w.v2("dispatch")
        sid = self.s("brief-2")["sid"]
        st = self.w.st()
        st["tasks"]["2"]["depth_at_start"] = v2.GRAPH_DEPTH + 1
        (self.w.state / "v2.json").write_text(json.dumps(st))
        self.w.task("7", description=BRIEF, subject="already in the graph")
        said = self.propose("2", sid, [
            {"key": "a", "subject": "Pretends to be spliced", "why": "-", "blockedBy": ["7"],
             "feeds": ["999"], "description": BRIEF},
            {"key": "r", "subject": "Its review", "why": "-", "blockedBy": ["a"],
             "description": REVIEW_TASK.format(task="a")}])
        self.assertIn("feeds '999', which is not in the task list", said)

    def test_a_brief_is_admitted_when_the_graph_is_narrow_however_many_tasks_exist(self):
        # seven open build tasks in one chain: the old rule detained every brief at six open, while only ONE of them
        # could start — and a brief is what widens a graph, so the count suppressed the cure (2026-09-20)
        ids = [str(n) for n in range(20, 27)]
        for i, tid in enumerate(ids):
            self.w.task(tid, description=BRIEF, metadata={"kind": "build"},
                        blockedBy=[ids[i - 1]] if i else [])
        self.w.task("1", blockedBy=["20"])   # the fixture's own build task, put in the chain so the width is ours
        self.w.set_st(queue=["2"], tasks={**{tid: {"stage": "ready", "kind": "build"} for tid in ids},
                                          "2": {"stage": "ready", "kind": "brief"}})
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "2"})
        self.assertEqual(len(self.forks("brief-")), 1)   # width is 1 of 2: the graph needs widening, not draining

    def test_a_brief_is_admitted_again_once_a_slot_has_taken_the_work(self):
        # what the planner is told: "a brief is admitted again when the slots have taken what can start". The width
        # counted work in flight, so the figure fell only when a task *finished*, and the rule as given was one
        # nothing could satisfy (2026-09-21).
        for tid in ("20", "21"):                          # two that can start at once, and two slots
            self.w.task(tid, description=BRIEF, metadata={"kind": "build"})
        self.w.task("1", blockedBy=["20"])   # the fixture's own build task, out of the width
        self.w.set_st(queue=["2"], tasks={"20": {"stage": "ready", "kind": "build"},
                                          "21": {"stage": "ready", "kind": "build"},
                                          "2": {"stage": "ready", "kind": "brief"}})
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "2"})
        self.assertEqual(self.forks("brief-"), [])        # 2 can start, 2 slots
        self.w.set_st(tasks={"20": {"stage": "running", "kind": "build", "session": "implement-20"}})
        self.assertIn("1 build and fix tasks can start, 2 slots to take them",
                      self.w.v2("status", env={"ORCH_GRAPH_WIDTH": "2"}))
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "2"})
        self.assertEqual(len(self.forks("brief-")), 1)    # one is taken: the graph is widened again

    def test_a_brief_is_detained_once_there_is_as_much_independent_work_as_slots(self):
        for tid in ("20", "21"):                          # two that can start at once, and two slots
            self.w.task(tid, description=BRIEF, metadata={"kind": "build"})
        self.w.task("1", blockedBy=["20"])   # the fixture's own build task, out of the width
        self.w.set_st(queue=["2"], tasks={"20": {"stage": "ready", "kind": "build"},
                                          "21": {"stage": "ready", "kind": "build"},
                                          "2": {"stage": "ready", "kind": "brief"}})
        self.w.v2("dispatch", env={"ORCH_GRAPH_WIDTH": "2"})
        self.assertEqual(self.forks("brief-"), [])
        log = (self.w.state / "v2.log").read_text()
        self.assertIn("2 build and fix tasks can start and there are 2 slots", log)  # said in shape, not in a count


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
        said = (self.w.state / "v2.log").read_text()   # every action of the harness is a line in the log
        self.assertIn("archived 2 piece(s) of state", said)
        self.assertIn("q1", said)
        self.assertIn("review-1", said)


class HealthTests(Flow):
    """health.py is the owner's one window. A stopped run is read hours later and is where every restart begins."""

    def health(self, **env):
        out = subprocess.run([sys.executable, str(fakes.HERE / "health.py")], env=dict(self.w.env, **env),
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        return out.stdout

    def daemon_like(self):
        """A live process whose command line names the daemon, as the daemon's own does."""
        path = self.w.root / "warm_daemon_stub.sh"
        path.write_text("#!/bin/sh\nsleep 30\n")
        p = subprocess.Popen(["sh", str(path)])
        self.addCleanup(p.wait)
        self.addCleanup(p.kill)
        return p.pid

    def test_work_the_graph_calls_done_that_the_repository_does_not_hold(self):
        # a path is its task's until the finalizer commits it, which takes it out of the map. On 2026-09-21 every
        # uncommitted path in the working tree belonged to a task the planner had completed — four tasks' work the
        # graph called done and the repository did not have — and nothing named it anywhere.
        self.w.repository()
        self.w.task("4")
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.own("4", "theories/Ready.thy")
        self.assertNotIn("whose task is completed", self.health())   # while the task is open it is simply its work
        self.w.task("4", status="completed")
        self.assertIn("ATTENTION uncommitted changes whose task is completed: theories/Ready.thy (task 4)",
                      self.health())

    def own(self, tid, *paths):
        out = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                              f"v2.own({tid!r}, {list(paths)!r})"], env=self.w.env, capture_output=True, text=True)
        self.assertEqual(out.returncode, 0, out.stderr)

    def test_the_line_on_each_live_session_is_what_the_owner_reads_during_a_run(self):
        # health's per-session line is most of what the owner reads while a run goes, and no test entered it: a
        # measurement through the subprocesses the tests run showed the whole function unreached (2026-09-21)
        self.w.task("1")
        self.w.session("implement-1", "implementer", "w1", task="1")
        self.w.transcript("w1", [fakes.assistant("m1", fakes.iso(time.time() - 1500), [{"type": "text", "text": "ok"}],
                                                 usage={"input_tokens": 2, "cache_read_input_tokens": 300_000,
                                                        "cache_creation_input_tokens": 1000, "output_tokens": 9})])
        self.w.set_status("implement-1", "idle")
        (self.w.state / f"work-w1.json").write_text(json.dumps(
            {"production_at": v2.iso(time.time() - 600), "read_tokens": 12_000, "productions": 3, "step": 2}))
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json", state="idle", live=False)
        self.w.session("review-9", "reviewer", None, task="9", state="starting", live=False,
                       starting=time.time() - v2.START_MAX - 60)
        self.w.set_st(queue=["1"], tasks={"1": {"stage": "running", "session": "implement-1"}})
        said = self.health()
        self.assertIn("producing: implement-1 on task 1, idle, context 301K, last reply 25 min ago; open it with: "
                      "claude attach id-w1", said)
        self.assertIn("ATTENTION producing: implement-1", said)          # idle for over twenty minutes
        self.assertIn("last production 10 min ago, 12K read since, 3 productions, in step 2", said)
        self.assertIn("planner: plan-1 waits for its next event, sealed and held warm", said)
        self.assertIn("ATTENTION supporting: review-9 starting for", said)

    def test_a_stale_layer_says_whether_anything_will_build_it_again(self):
        # "— it is refreshed" names the watchdog, which does nothing while the run is stopped or its daemon is down:
        # said then, it names something nobody will do (2026-09-21)
        (self.w.state / "max-layer.json").write_text(json.dumps(
            {"sessionId": "max-layer-1", "base": "base-sid", "context": 500_000, "sealed": "2026-09-21T00:00:00"}))
        self.assertIn("it is due to be built again, and nothing runs to do it (start.sh, or base.sh max layer)",
                      self.health(ORCH_LAYER_STALE="0"))
        (self.w.state / "warm.pid").write_text(str(self.daemon_like()))
        self.assertIn("— it is refreshed", self.health(ORCH_LAYER_STALE="0"))
        (self.w.state / "stopped").write_text("2026-09-21T01:00:00")   # a daemon of a stopped run refreshes nothing
        self.assertIn("nothing runs to do it", self.health(ORCH_LAYER_STALE="0"))

    def test_a_stopped_run_still_shows_what_a_restart_meets(self):
        # it returned after "stopped at ...", so the queue, the tasks nothing can move and the questions — the state
        # a restart actually meets — were visible nowhere while the run stood still (2026-09-21)
        self.w.task("1")
        self.w.task("4", description=REVIEW_TASK.format(task="1"), subject="An orphaned review")
        self.w.set_st(queue=["1", "4"], active=False,
                      tasks={"1": {"stage": "parked", "kind": "build", "session": "implement-1",
                                   "parked": {"for": "tree", "since": time.time(), "holder": "9"}},
                             "4": {"stage": "proposed", "kind": "brief", "proposed": 3,
                                   "proposal": ".build/tasks/4/brief/proposal.json"}},
                      asks={"q1": {"from": "implement-1", "state": "open", "text": "Which of the two?",
                                   "asked": time.time(), "target": "planner"}})
        (self.w.state / "stopped").write_text("2026-09-21T01:00:00")
        said = self.health()
        self.assertIn("stopped at 2026-09-21T01:00:00; start.sh resumes", said)
        self.assertIn("queue: 1:parked 4:proposed", said)
        self.assertIn("parked: task 1", said)
        self.assertIn("ATTENTION task 4: 3 task(s) proposed and not placed", said)
        self.assertIn("question q1 from implement-1 to planner", said)

    def test_an_inactive_run_shows_it_too_and_a_running_one_is_unchanged(self):
        self.w.task("1")
        self.w.set_st(queue=["1"], active=False, tasks={"1": {"stage": "ready", "kind": "build"}})
        self.assertIn("queue: 1:ready", self.health())
        self.w.set_st(active=True)
        said = self.health()
        self.assertIn("queue: 1:ready", said)
        self.assertIn("working tree:", said)      # the live lines are still only the live run's
        self.assertIn("knowledge base: kb-1", said)


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
        # a ledger that is there and cannot be read was replaced by a fresh header and the one new entry: every
        # direction the owner had ever given, gone. It is left alone, the words are kept in the log, and the
        # planner is still told (2026-09-21)
        ledger.unlink()
        ledger.mkdir()                                     # there, and no read of it can succeed
        typed("i4", "And keep the ordering notion at its second use.")
        self.assertTrue(ledger.is_dir())
        said = (self.w.state / "v2.log").read_text()
        self.assertIn("the owner ledger could not be read", said)
        self.assertIn("keep the ordering notion at its second use", said)
        self.assertIn("keep the ordering notion", " ".join(e["text"] for e in self.w.st()["events"]))

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


class WalkTests(Flow):
    """The whole run walked once, on the defaults it will start with: a fresh knowledge base, one long-lived planner
    fed its events as they happen, two sessions working at once, and a task carried from queue to commit."""

    def setUp(self):
        self.w = fakes.World()
        self.w.base()
        self.remote = self.w.repository()
        self.w.write("HANDOFF.md", PLANNER_STATE)
        self.w.write("theories/Base.thy", "theory Base imports Main begin\nend\n")
        self.w.set_st(active=False)

    def test_the_run_walks_from_a_fresh_start_to_a_commit_through_one_planner(self):
        # 1. a fresh start: no knowledge base yet, so one is built and nothing plans until it holds the knowledge
        self.assertIn("active", self.w.v2("start", "--fresh"))
        (kb,) = self.forks("kb-")
        self.assertIn("You are kb-1, the knowledge base", kb[-1])
        self.assertEqual(self.forks("plan-"), [])
        self.assertEqual(len(self.w.st()["events"]), 1)          # the charge waits for it

        # 2. it holds the knowledge: the planner forks it, and the charge is in its first message
        self.w.reply(self.s("kb-1")["sid"], "INTEGRATED")
        self.w.v2("dispatch")
        (plan,) = self.forks("plan-")
        self.assertEqual(plan[plan.index("--resume") + 1], self.s("kb-1")["sid"])
        self.assertIn("take stock", plan[-1])
        self.assertIn("PLANNING_LOG.md", plan[-1])

        # 3. it queues a build task and a brief task; at two, both slots take one
        self.w.task("1")
        self.w.task("2", description=BRIEF_TASK, subject="Reach")
        self.assertEqual(self.as_("plan-1", "queue", "1", "2"), "queued")
        (impl,) = self.forks("implement-")
        (brief,) = self.forks("brief-")
        self.assertIn("Deliverable: `theories/Ready.thy`", impl[-1])
        self.assertIn("You work in the repository's one working tree", impl[-1])  # true: no tree of its own here
        self.assertEqual(len(v2.working(self.w.st())), 2)        # a producer and a supporter, side by side

        # 3b. the task designer proposes; it does not edit the graph, and the planner places what it proposed
        bsid = self.s("brief-2")["sid"]
        d = self.w.project / ".build/tasks/2/brief"
        d.mkdir(parents=True, exist_ok=True)
        (d / "proposal.json").write_text(json.dumps([
            {"key": "reach", "subject": "The reach", "why": "it is next", "blockedBy": [], "description": BRIEF},
            {"key": "reach-review", "subject": "Judge the reach", "why": "-", "blockedBy": ["reach"],
             "description": REVIEW_TASK.format(task="reach")}]))
        self.assertIn("proposed 2 task(s)", self.w.v2(
            "propose", "2", ".build/tasks/2/brief/proposal.json", env=self.w.as_session(bsid)))
        self.assertEqual(self.t("2")["stage"], "proposed")
        self.assertIn("proposes 2 task(s) and where to place them", self.heard())
        self.assertIn("placed reach as", self.as_("plan-1", "accept", "2"))
        made = {json.loads((self.w.tasks / f).read_text())["subject"]: json.loads((self.w.tasks / f).read_text())
                for f in os.listdir(self.w.tasks) if f.endswith(".json")}
        reach, judge = made["The reach"], made["Judge the reach"]
        self.assertEqual(judge["blockedBy"], [reach["id"]])              # its local key resolved to the id allocated
        st = self.w.st()
        self.assertEqual(st["tasks"][judge["id"]]["reviews"], reach["id"])
        self.assertIn(reach["id"], st["queue"])                          # queued after the brief that proposed it
        self.assertEqual((st["tasks"]["2"]["stage"], self.w.read_task("2")["status"]), ("done", "completed"))

        # 4. the task finishes, is checked, reviewed and committed
        self.w.write("theories/Ready.thy", "theory Ready imports Main begin end\n")
        self.w.write(".build/tasks/1/commit.md", "Add readiness\n\nValidation: checked.\n")
        self.w.write(".build/tasks/1/result.md", RESULT.format(status="done"))
        self.assertIn("prepared", self.as_("implement-1", "finalize", "1", "--check", "true", "--files",
                                           "theories/Ready.thy", "--message", ".build/tasks/1/commit.md"))
        self.assertIn("recorded", self.as_("implement-1", "result", "1"))
        self.assertEqual(self.t("1")["stage"], "reviewing")
        # the supporting slot holds one: the review waits for the task designer to finish, whatever the rate
        self.assertEqual(self.forks("review-"), [])
        self.w.set_st(sessions={k: (v | {"state": "done"} if k == "brief-2" else v)
                                for k, v in self.w.st()["sessions"].items()})
        self.w.v2("dispatch")
        (review,) = self.forks("review-")
        self.assertIn("produced by implement-1", review[-1])
        self.w.write(".build/tasks/1/review.md", VERDICT.format(v="accept", f=""))
        self.assertIn("accepted", self.as_("review-1", "verdict", "1", "accept", "--file", ".build/tasks/1/review.md"))
        self.assertEqual(self.t("1")["stage"], "done")
        self.assertEqual(self.w.git("log", "-1", "--format=%s"), "Add readiness\n")

        # 5. every event of the whole walk reached the one planner, and no second was ever forked
        self.assertEqual(len(self.forks("plan-")), 1)
        self.assertIn("is committed as", self.heard())
        said = (self.w.state / "v2.log").read_text()
        self.assertNotIn("lost", said)
        # nothing in a walk that went right needs anybody: an ATTENTION here is the harness crying wolf, and a log
        # with one in it is a log the owner learns to skim (a transcript not yet written read as one unreadable,
        # 2026-09-21)
        self.assertNotIn("ATTENTION", said)
