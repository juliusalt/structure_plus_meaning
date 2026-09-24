"""What every base holds, and what none may (the owner, 2026-09-23 evening): "raw memory includes orchestrator session
information which should never be shown to any of the content producing bases"."""
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import manifest  # noqa: E402
import select_base_load as sbl  # noqa: E402


class MemoryTests(unittest.TestCase):
    def test_no_base_holds_the_memory_directory_and_no_harness_session_reads_or_writes_it(self):
        for who, name in manifest.LISTS.items():
            text = (HERE / name).read_text()
            self.assertNotIn("/memory/", text, who)
            # AGENTS.md and DEVELOPMENT_WORKFLOW.md are a solo agent's entry: what they require is the owner's words
            # and problems.txt, which every base holds, carried out by the protocols and the harness (2026-09-23)
            self.assertNotIn("AGENTS.md", text, who)
            self.assertNotIn("DEVELOPMENT_WORKFLOW.md", text, who)
            for held in (".claude/orchestration/codex-owner-directions.md", ".claude/orchestration/owner-directions.md",
                         "problems.txt"):
                self.assertIn(f"\n{held}\n", text, who)
            # the parts in the order of how rarely their cause acts (test_layer.py says it too; the mutation check
            # leaves that file out, so it is said where a mutation is caught)
            self.assertEqual(manifest.layer_names(HERE / name),
                             ["direction", "catalogue"] if who == "high" else ["direction", "inventory", "catalogue"], who)
            start = text.index("# === layer direction ===")
            direction = text[start:text.index("# === layer ", start + 1)]
            # below the reference, first: the owner's words, problems.txt and the practice (none changed in the run)
            stable = text[:start]
            first_theory = stable.index("\ntheories/")
            for held in (".claude/orchestration/codex-owner-directions.md", ".claude/orchestration/owner-directions.md",
                         "problems.txt", f".claude/orchestration/state/held/library-practice-{who}.md"):
                self.assertLess(stable.index(f"\n{held}\n"), first_theory, (who, held))
            # the decisions, appended and never rewritten, over the plan: in the direction, not the catalogue
            self.assertIn(".claude/orchestration/state/held/decisions-index.md", direction, who)
            self.assertNotIn("decisions-index.md", text[text.index("# === layer catalogue ==="):], who)
            # the tool index, appended as tools are made and almost never rewritten, right over the decisions: not
            # reloaded with the theory map, whose rows are rewritten far more than added
            catalogue = text[text.index("# === layer catalogue ==="):]
            self.assertNotIn(f"tool-index-{who}.md", catalogue, who)
            self.assertLess(text.index("decisions-index.md\n"), text.index(f"tool-index-{who}.md\n"), who)
            self.assertLess(text.index(f"tool-index-{who}.md\n"), text.index("# === layer catalogue ==="), who)
            # REASONING_REUSE.md changes with the landings that publish a pattern of reasoning, not with the direction
            self.assertNotIn("REASONING_REUSE.md", direction, who)
            if who != "high":
                inventory = text[text.index("# === layer inventory ==="):text.index("# === layer catalogue ===")]
                self.assertIn("\nREASONING_REUSE.md\n", inventory, who)
        for name in ("base-settings.json", "worker-settings.json", "planner-settings.json"):
            settings = json.loads((HERE / name).read_text())
            self.assertIs(settings["autoMemoryEnabled"], False, name)
            self.assertEqual(settings["env"]["CLAUDE_CODE_DISABLE_AUTO_MEMORY"], "1", name)
            # and git instructions, which carry a git status frozen when the base loaded, mostly the orchestrator's
            self.assertIs(settings["includeGitInstructions"], False, name)
            self.assertEqual(settings["env"]["CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS"], "1", name)

    def test_the_library_practice_holds_the_named_entries_and_nothing_else(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            memory, orch = root / "memory", root / "orch"
            memory.mkdir()
            (orch / "state").mkdir(parents=True)
            (orch / "library-practice.txt").write_text("# a comment naming commit-hold\nisar-keywords\ngone-entry\n")
            (memory / "isar-keywords.md").write_text('---\nname: isar-keywords\ndescription: "Never label a fact '
                                                     'premises"\nmetadata:\n  type: feedback\n---\n\nA label named '
                                                     'premises breaks the parse.\n')
            (memory / "commit-hold.md").write_text("---\nname: commit-hold\ndescription: No commit\n---\n\nThe hold.\n")
            with patch.object(sbl, "HERE", str(orch)), patch.object(sbl, "memory_dir", lambda: str(memory)):
                text = sbl.practice()
            self.assertEqual((orch / "state/held/library-practice.md").read_text(), text)
        self.assertIn("## isar-keywords — Never label a fact premises\n\nA label named premises breaks the parse.", text)
        self.assertNotIn("metadata", text)          # the frontmatter is the memory's, not the practice
        self.assertNotIn("The hold.", text)         # an entry not named is never held
        self.assertNotIn("## #", text)              # nor is a comment of the selection an entry
        self.assertIn("## gone-entry\n\n(not found in the memory directory", text)

    def test_each_base_holds_the_practice_its_roles_concern_and_no_catalogue_line_it_holds_already(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            memory, orch = root / "memory", root / "orch"
            (root / "theories").mkdir()
            memory.mkdir()
            (orch / "state").mkdir(parents=True)
            for name in ("Held", "Other"):
                (root / "theories" / f"{name}.thy").write_text(f"theory {name} imports Main begin end\n")
            (root / "THEORY_MAP.md").write_text("| Theory | Imports | Content |\n|---|---|---|\n| Held | Main | What Held "
                                                "is |\n| Other | Main | What Other is |\n")
            (root / "ROOT").write_text("session Test = HOL +\n  theories\n    Held\n    Other\n")
            (root / "DECISIONS.md").write_text("# Decisions\n")
            (root / "tools").mkdir()
            for name in ("check.py", "other.py"):
                (root / "tools" / name).write_text('"""A tool."""\ndef run():\n    pass\n')
            (orch / "base-load-high.txt").write_text("# founding, as signatures\ntheories/Held.thy\n# tools\ntools/check.py\n")
            (orch / "library-practice.txt").write_text("everyone\nplanning max xhigh\nproving xhigh high\n")
            for name in ("everyone", "planning", "proving"):
                (memory / f"{name}.md").write_text(f"---\nname: {name}\ndescription: {name}\n---\n\nThe {name} entry.\n")
            with patch.object(sbl, "HERE", str(orch)), patch.object(sbl, "PROJECT", str(root)), \
                    patch.object(manifest, "PROJECT", str(root)), patch.object(sbl, "memory_dir", lambda: str(memory)), \
                    patch.dict(os.environ, {"BASE_LOAD_LIST": ""}):
                high = sbl.practice(False, "high")
                maxi = sbl.practice(False, "max")
                index = sbl.theory_map_index(False, "high")
                tools = sbl.tool_index(False, "high")
                sbl.refresh_indexes("high")
                self.assertTrue((orch / "state/held/theory-map-index-high.md").exists())
        self.assertEqual(re.findall(r"^## (\w+)", high, re.M), ["everyone", "proving"])
        self.assertEqual(re.findall(r"^## (\w+)", maxi, re.M), ["everyone", "planning"])
        self.assertIn("Other: What Other is", index)
        self.assertNotIn("Held:", index)            # the base holds it: its line would say it twice
        self.assertIn("tools/other.py", tools)
        self.assertNotIn("tools/check.py", tools)   # held whole

    def test_the_named_entries_exist_and_none_is_the_orchestrators(self):
        names = [ln.split()[0] for ln in (HERE / "library-practice.txt").read_text().splitlines()
                 if ln.strip() and not ln.startswith("#")]
        self.assertTrue(names)
        for name in names:
            self.assertFalse(re.search(r"commit|orchestrat|sandbox|subagent|callback|autonomous", name), name)

    def test_the_base_prompt_says_what_a_base_holds_now(self):
        prompt = (HERE / "library-prompt.md").read_text()
        self.assertIn("given to you with your task", prompt)
        self.assertIn("automatic compaction is off", prompt)
        self.assertIn("(`v2.py ask --to planner`)", prompt)  # the owner's paragraph, stated once for every session
        self.assertNotIn("Run commands in the background", prompt)  # owner-directions.md holds that rule's words
        self.assertIn("AGENTS.md and DEVELOPMENT_WORKFLOW.md are the entry of a session that works alone", prompt)
        self.assertNotIn("the operating rules", prompt)
        # the owner's words of 2026-09-19 verbatim, not the harness's paraphrase under the owner's name; their mechanics
        # are the protocols' (_efficiency.md, _checks.md), as the tools, a check's end and the machine are (_production.md)
        self.assertIn("proper channel through which that needs to be done rather than doing it themselves", prompt)
        self.assertIn("it must\n> become parked so that another worker can then be started to do productive work", prompt)
        self.assertNotIn("a performance problem has its own channel", prompt)
        for said_by_a_protocol in ("Your tools\nare Bash", "Your tools are", "A check runs to its", "60 GiB",
                                   "escalate --efficiency", "the finalizer commits what passes review"):
            self.assertNotIn(said_by_a_protocol, prompt)
        self.assertEqual(prompt.count("automatic compaction is off"), 1)
        self.assertNotIn("the operating rules", (HERE / "protocols" / "base-reasoning.md").read_text())
        self.assertIn("(REASONING_REUSE.md)", prompt)
        reasoning = (HERE / "protocols" / "base-reasoning.md").read_text()
        self.assertIn("You hold the owner's words, problems.txt and the library's working practice", reasoning)
        self.assertIn("the plan and the decisions, the inventory and the catalogue", reasoning)
        self.assertNotIn("DEVELOPMENT_WORKFLOW.md", (HERE / "protocols" / "_finishing.md").read_text())
        self.assertFalse((HERE / "protocols" / "_owner.md").exists())
        self.assertNotIn("material selected by its relation to the current work", prompt)
        # what Claude Code tells every session that does not hold here
        self.assertIn("Claude Code's own guidance for every session says two things that do not hold here", prompt)
        for role in ("designer", "implementer", "fixer", "reviewer", "investigator", "task-designer"):
            self.assertNotIn("working frontier", (HERE / "protocols" / f"{role}.md").read_text(), role)

    def test_the_decisions_index_holds_decisions_not_the_sections_inside_one(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "DECISIONS.md").write_text("# Decisions\n\n## Keep admission apart\n\nAdmission is its own "
                                               "notion. More.\n\n### Follow-ups, for the planner\n\n1. Something.\n")
            with patch.object(sbl, "PROJECT", str(root)):
                text = sbl.decisions_index(write=False)
        self.assertIn("## Keep admission apart — Admission is its own notion.", text)
        self.assertNotIn("Follow-ups", text)
        long = "A first sentence " + "that goes on " * 60 + "to its end. And a second."
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp) / "DECISIONS.md").write_text(f"# Decisions\n\n## A long one\n\n{long}\n")
            with patch.object(sbl, "PROJECT", temp):
                text = sbl.decisions_index(write=False)
        self.assertIn("to its end.", text)            # whole, however long: never cut at a character count
        self.assertNotIn("a second", text)


class EvidenceTests(unittest.TestCase):
    def test_how_sessions_of_another_model_worked_is_not_the_roles_evidence_now(self):
        # the sessions before the fresh start ran under another model and harness: what it cost them and what the
        # harness refused them then is not how the role works now; the reviews' findings are of the content, and stay
        import role_evidence
        import v2
        sessions = {"implement-1": dict(name="implement-1", role="implementer", sid="old", ended=1, started=1,
                                        model="claude-opus-5[1m]"),
                    "implement-2": dict(name="implement-2", role="implementer", sid="new", ended=2, started=2,
                                        model=v2.base_model())}
        found = [dict(at=1, reviewer="review-1", task="1", role="implementer", findings="Re-proved a contract.",
                      source="as it was given")]
        with patch.object(v2, "peek", return_value={"tasks": {}}), \
                patch.object(role_evidence, "all_sessions", return_value=sessions), \
                patch.object(role_evidence, "transcripts", return_value={"old": "o", "new": "n"}), \
                patch.object(role_evidence, "session_facts", return_value=(10, 2, 1000, ["a note"], [], [], 5, 1)), \
                patch.object(role_evidence, "rejections", return_value=found), \
                patch.object(role_evidence, "work_ahead", return_value=("", [])):
            text = role_evidence.evidence_and_ahead("implementer")[0]
        self.assertIn("the last 1 sessions of the implementer", text)
        self.assertIn("implement-2", text)
        self.assertNotIn("implement-1", text)
        self.assertIn("Re-proved a contract.", text)


class GuardTests(unittest.TestCase):
    def test_a_run_session_is_refused_the_memory_and_the_orchestrators_notes(self):
        import fakes
        world = fakes.World()
        try:
            world.session("implement-1", "implementer", "impl-sid", task="1")
            for command in ("cat ~/.claude/projects/-home-julius-structure-and-semantics/memory/commit-push.md",
                            "grep -rn hold /home/julius/.claude/projects/-home-x/memory/",
                            "sed -n 1,40p .claude/orchestration/notes/plan-bases-two-purposes.md"):
                code, reply, error = world.hook("work_meter.py", "guard", {
                    "session_id": "impl-sid", "cwd": str(world.project), "tool_name": "Bash",
                    "tool_input": {"command": command}})
                self.assertEqual(code, 0, error)
                self.assertEqual(reply["hookSpecificOutput"]["permissionDecision"], "deny", command)
                self.assertIn("not the run's to read", reply["hookSpecificOutput"]["permissionDecisionReason"])
            code, reply, error = world.hook("work_meter.py", "guard", {
                "session_id": "impl-sid", "cwd": str(world.project), "tool_name": "Bash",
                "tool_input": {"command": "grep -n notes theories/A.thy"}})
            self.assertNotIn("not the run's to read", json.dumps(reply or {}))
        finally:
            world.close()


if __name__ == "__main__":
    unittest.main()
