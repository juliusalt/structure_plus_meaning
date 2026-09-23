"""What a base holds by its responsibilities, and what a task is given of its own relations. Each test builds a small
project of its own — theories, a map, a plan and a load list — so nothing here reads the repository's sources."""
import json
import os
from pathlib import Path
import sys
import tempfile
import subprocess
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import manifest  # noqa: E402
import select_base_load as sbl  # noqa: E402

THEORIES = {  # name: (lemmas it defines, lines of filler that give it its size)
    "Alpha": (["alpha_one", "alpha_two"], 10),
    "Beta": (["beta_rule"], 200),
    "Gamma": (["gamma_law"], 10),
    "Delta": (["delta_step"], 10),
    "Found_One": (["found_one_def"], 10),
    "Found_Two": (["found_two_def"], 10),
    "Found_Three": (["found_three_def"], 10),
    "Pinned": (["pinned_core"], 10),
}
LIST = """# a test list
# every other founding theory, as signatures (generated: the test's)
theories/Found_One.thy
theories/Found_Two.thy
theories/Found_Three.thy
# pinned idea: the test's pin
theories/Pinned.thy
# === layer direction ===
# pinned: the owner's voice; purpose=steering
notes.md
# === layer catalogue ===
# the generated plan tier
# === relations ===
# === end relations ===
"""


def thy(name, lemmas, filler, imports="Main"):
    body = "\n".join(f"lemma {n}: \"True\"\n  by simp" for n in lemmas)
    pad = "\n".join(f"lemma {name.lower()}_filler_{i}: \"x{i} = x{i} \\<and> True \\<and> True\"\n  by simp" for i in range(filler))
    return f"theory {name}\n  imports {imports}\nbegin\n\n{body}\n\n{pad}\n\nend\n"


class Project:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "theories").mkdir()
        imports = {"Alpha": "Beta Found_One", "Gamma": "Alpha"}
        for name, (lemmas, filler) in THEORIES.items():
            (self.root / "theories" / f"{name}.thy").write_text(thy(name, lemmas, filler, imports.get(name, "Main")))
        rows = "\n".join(f"| {n} | x | {n} holds its lemmas; and more words follow here |" for n in THEORIES)
        (self.root / "THEORY_MAP.md").write_text("| Theory | Imports | Content |\n|---|---|---|\n" + rows + "\n")
        self.orch = self.root / ".claude" / "orchestration"
        (self.orch / "state" / "held").mkdir(parents=True)
        for who in ("max", "xhigh", "high"):
            (self.orch / f"base-load-{who}.txt").write_text(LIST)
        (self.root / "notes.md").write_text("the owner's words\n")
        (self.root / "native_control_plan.md").write_text("## Active\n`Alpha`\n## Later\n`Delta`\n## Still missing\n"
                                                          "No implementation yet.\n")
        (self.root / "problems.txt").write_text("1. Preserve meaning.\n2. Keep every obligation.\n")
        self.tasks = [dict(id="1", status="pending", description="Kind: build\nDeliverable: `theories/Alpha.thy`\n",
                           blockedBy=[])]
        self.state = {"tasks": {"1": {"kind": "build", "stage": "ready"}}}

    def patches(self):
        return [patch.object(sbl, "PROJECT", str(self.root)), patch.object(sbl, "HERE", str(self.orch)),
                patch.object(manifest, "PROJECT", str(self.root)), patch.object(manifest, "HERE", str(self.orch)),
                patch.object(sbl, "forking_roles", lambda who: {"high": {"implementer", "fixer"},
                                                                 "xhigh": {"reviewer", "designer"}}.get(who, {"planner"})),
                patch.dict(sbl.LIBRARY, {}, clear=True)]


class Case(unittest.TestCase):
    def setUp(self):
        self.p = Project()
        self.patches = self.p.patches()
        for p in self.patches:
            p.start()

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.p.temp.cleanup()

    def v2(self, tasks=None, state=None):
        import v2
        return [patch.object(v2, "all_tasks", return_value=self.p.tasks if tasks is None else tasks),
                patch.object(v2, "peek", return_value=self.p.state if state is None else state)]


class VocabularyTests(Case):
    def test_a_name_many_theories_define_says_nothing(self):
        for name in ("Epsilon", "Zeta", "Eta", "Theta"):
            (self.p.root / "theories" / f"{name}.thy").write_text(thy(name, ["shared_name"], 5))
        defined = sbl.defined_names()
        self.assertNotIn("shared_name", defined)
        self.assertEqual(defined["alpha_one"], {"theories/Alpha.thy"})

    def test_ordinary_prose_is_not_a_reference_and_every_quoted_owner_is_retained(self):
        owners = {"ordinary": {"theories/Beta.thy"}, "shared_name": {"theories/Alpha.thy", "theories/Gamma.thy"}}
        paths = {f"theories/{n}.thy": n for n in ("Alpha", "Beta", "Gamma")}
        self.assertEqual(sbl.names_in("ordinary language", owners, paths), set())
        self.assertEqual(sbl.names_in("consume `shared_name`", owners, paths), {"Alpha", "Gamma"})

    def test_the_library_is_read_again_when_a_theory_changes_and_not_otherwise(self):
        first = sbl.library()
        self.assertIs(sbl.library(), first)
        path = self.p.root / "theories" / "Delta.thy"
        path.write_text(thy("Delta", ["delta_step"], 10, "Gamma"))
        os.utime(path, ns=(time.time_ns() + 10**9,) * 2)
        again = sbl.library()
        self.assertIsNot(again, first)
        self.assertIn("Gamma", again["refs"]["Delta"])


class BaseRelationTests(Case):
    def test_the_whole_plan_is_held_by_the_bases_that_steer_by_it_whatever_the_queue(self):
        for tasks in ([], self.p.tasks):
            with self.v2(tasks)[0], self.v2(tasks)[1]:
                c = sbl.relation_choice("xhigh", tasks, self.p.state)
            self.assertEqual([t["relation"] for t in c["tiers"]], ["whole-plan notions"])
            self.assertEqual(c["chosen"], ["theories/Alpha.thy", "theories/Delta.thy"])
            self.assertIn("plan: Still missing", c["unresolved_plan_parts"])
            self.assertIn("condition: 1", c["unresolved_plan_parts"])
        with self.v2()[0], self.v2()[1]:
            self.assertEqual(sbl.relation_choice("high")["chosen"], [])  # high's roles steer by their briefs

    def test_a_plan_notion_the_owner_already_holds_deeper_is_not_held_again(self):
        listed = self.p.orch / "base-load-xhigh.txt"
        listed.write_text(listed.read_text().replace("theories/Pinned.thy", "theories/Pinned.thy\ntheories/Alpha.thy"))
        with self.v2()[0], self.v2()[1]:
            self.assertEqual(sbl.relation_choice("xhigh")["chosen"], ["theories/Delta.thy"])

    def test_projection_is_read_only_and_matches_the_written_block(self):
        listed = self.p.orch / "base-load-xhigh.txt"
        with self.v2()[0], self.v2()[1], patch.dict(os.environ, {"BASE_LOAD_LIST": ""}):
            before = listed.read_text()
            projected = sbl.projection("xhigh")
            self.assertEqual(listed.read_text(), before)
            sbl.frontier("xhigh")
            after = sbl.projection("xhigh")
            self.assertEqual(projected["total"], after["total"])
            self.assertEqual(after["frontier"], {"new": 0, "dropped": 0})
            text = listed.read_text()
            sbl.frontier("xhigh")
            self.assertEqual(listed.read_text(), text)
        self.assertIn("# relation: whole-plan notions; purpose=steering; as signatures\ntheories/Alpha.thy", text)
        self.assertEqual(sbl.without_generated(text), sbl.without_generated(before))  # the owner's pins untouched

    def test_projection_says_what_each_current_task_is_given(self):
        with self.v2()[0], self.v2()[1], patch.dict(os.environ, {"BASE_LOAD_LIST": ""}):
            got = sbl.projection("high")["deliveries"]
        self.assertEqual([d["task"] for d in got], ["1"])
        self.assertGreater(got[0]["tokens"], 0)

    def test_named_material_parts_preserve_their_depths_and_purposes(self):
        text = LIST.replace("# the generated plan tier", "# relation: subjects; purpose=steering; as signatures")
        es = manifest.list_entries(text + "theories/Found_One.thy\n", str(self.p.root))
        self.assertEqual([e["level"] for e in es if e["path"].endswith("Found_One.thy")], ["signatures"])
        es = manifest.list_entries(text + "# consumed contract; purpose=both; as statements\ntheories/Found_One.thy\n",
                                   str(self.p.root))
        self.assertEqual({e["part"] for e in es}, {"stable", "direction", "catalogue"})
        self.assertEqual([(e["part"], e["level"], e["purpose"]) for e in es if e["path"].endswith("Found_One.thy")],
                         [("stable", "signatures", "both"), ("catalogue", "statements", "both")])

    def test_projection_reads_current_catalogue_sources_without_writing_generated_files(self):
        listed = self.p.orch / "base-load-high.txt"
        listed.write_text(listed.read_text() + "# discovery; purpose=steering\n"
                          ".claude/orchestration/state/held/theory-map-index.md\n")
        with self.v2([])[0], self.v2([])[1], patch.dict(os.environ, {"BASE_LOAD_LIST": ""}):
            first = sbl.projection("high")
            (self.p.root / "theories/New_Notion.thy").write_text("theory New_Notion imports Main begin end\n")
            second = sbl.projection("high")
        self.assertGreater(second["total"], first["total"])
        self.assertFalse((self.p.orch / "state/held/theory-map-index.md").exists())
        self.assertIn("No THEORY_MAP description", sbl.theory_map_index(write=False))


class TaskRelationTests(Case):
    def test_a_task_is_given_its_suppliers_at_its_roles_depth_its_subjects_and_consumers_at_signatures(self):
        r = sbl.task_relations("high", self.p.tasks[0]["description"])
        tiers = {t["relation"]: t for t in r["tiers"]}
        self.assertEqual(r["targets"], ["Alpha"])
        self.assertEqual(tiers["supplier contracts"]["level"], "statements")
        # Found_One is held at signatures by the base: its contract is deeper, and given; Beta is held nowhere
        self.assertEqual(tiers["supplier contracts"]["names"], ["Beta", "Found_One"])
        self.assertEqual(tiers["work subjects"]["names"], ["Alpha"])
        self.assertEqual(tiers["direct consumers"]["names"], ["Gamma"])
        middle = {t["relation"]: t for t in sbl.task_relations("xhigh", self.p.tasks[0]["description"])["tiers"]}
        self.assertEqual(middle["supplier meanings"]["level"], "definitions")

    def test_what_the_base_holds_at_that_depth_is_not_given_again(self):
        held = {"Beta": "statements", "Found_One": "definitions", "Gamma": "signatures"}
        tiers = {t["relation"]: t for t in sbl.task_relations("high", "`theories/Alpha.thy`", held=held)["tiers"]}
        self.assertEqual(tiers["supplier contracts"]["names"], ["Found_One"])
        self.assertEqual(tiers["supplier contracts"]["held"], ["Beta"])
        self.assertEqual(tiers["direct consumers"]["names"], [])
        texts = sbl.relations_texts(sbl.task_relations("high", "`theories/Alpha.thy`", held=held))
        self.assertEqual([(n, d) for n, _, d, _ in texts], [("Found_One", "statements"), ("Alpha", "signatures")])
        self.assertIn("found_one_def", texts[0][3])

    def test_the_relations_are_given_as_the_tasks_tree_holds_them(self):
        tree = self.p.root / "tree"
        (tree / "theories").mkdir(parents=True)
        (tree / "theories" / "Beta.thy").write_text(thy("Beta", ["beta_rule", "beta_in_the_tree"], 1))
        texts = sbl.relations_texts(sbl.task_relations("high", "`theories/Alpha.thy`", held={}), tree=str(tree))
        beta = next(text for name, _, _, text in texts if name == "Beta")
        self.assertIn("beta_in_the_tree", beta)

    def test_future_blocked_work_is_current_when_its_prerequisite_is_done(self):
        roles = {"implementer"}
        self.p.tasks[0]["blockedBy"] = ["2"]
        self.p.tasks.append(dict(id="2", status="pending", description="Kind: build\n", blockedBy=[]))
        with self.v2()[0], self.v2()[1]:
            self.assertEqual([t["id"] for t in sbl.current_tasks(roles, self.p.tasks, self.p.state)], ["2"])
            self.p.tasks[1]["status"] = "completed"
            self.assertEqual([t["id"] for t in sbl.current_tasks(roles, self.p.tasks, self.p.state)], ["1"])
            self.p.tasks[1]["status"] = "pending"
            self.p.state["tasks"]["1"]["stage"] = "parked"
            self.assertIn("1", [t["id"] for t in sbl.current_tasks(roles, self.p.tasks, self.p.state)])

    def test_other_current_work_on_the_same_theories_is_named(self):
        self.p.tasks.append(dict(id="2", status="pending", blockedBy=[],
                                 description="Kind: build\nDeliverable: `theories/Beta.thy`\n"))
        self.p.tasks.append(dict(id="3", status="pending", blockedBy=[],
                                 description="Kind: build\nDeliverable: `theories/Pinned.thy`\n"))
        self.p.state["tasks"].update({"2": {"kind": "build", "stage": "running"}, "3": {"kind": "build"}})
        r = sbl.task_relations("high", self.p.tasks[0]["description"])
        with self.v2()[0], self.v2()[1]:
            got = sbl.concurrent_work("1", r, self.p.tasks, self.p.state)
        self.assertEqual(got, [("2", "running", ["Beta"], "suppliers: Beta")])


class DeliveryTests(Case):
    """v2 gives a session its task's own relations: in files of the task's folder, for its first batch."""

    def setUp(self):
        super().setUp()
        import v2
        self.v2mod = v2
        self.build = self.p.root / ".build" / "tasks"
        self.more = [patch.object(v2, "PROJECT", str(self.p.root)), patch.object(v2, "BUILD", str(self.build)),
                     patch.object(v2, "base_record", lambda who: (who, {})), *self.v2()]
        for p in self.more:
            p.start()

    def tearDown(self):
        for p in reversed(self.more):
            p.stop()
        super().tearDown()

    def test_a_session_is_told_to_read_its_relations_in_its_first_batch(self):
        text, given, stated = self.v2mod.relations_read("1", "implementer", self.p.tasks[0]["description"], None)
        files = sorted((self.build / "1" / "relations-high").glob("*.md"))
        self.assertEqual(len(files), 1)
        self.assertIn(f"`cat .build/tasks/1/relations-high/1.md`", text)
        self.assertIn("- supplier contracts, as statements: Beta, Found_One", text)
        self.assertIn("beta_rule", files[0].read_text())
        self.assertGreater(given, 0)
        again, _, _ = self.v2mod.relations_read("1", "reviewer", self.p.tasks[0]["description"], None)
        self.assertIn("supplier meanings, as definitions", again)
        self.assertTrue((self.build / "1" / "relations-xhigh" / "1.md").exists())

    def test_a_fact_the_session_holds_at_statements_is_not_stated_again(self):
        text, given, stated = self.v2mod.relations_read("1", "implementer", self.p.tasks[0]["description"], None)
        self.assertEqual({"Beta", "Found_One"} <= stated, True)      # given at statements with the task
        self.assertIn("Pinned", stated)                              # held at statements by the base
        brief = "Inputs: `Beta.beta_rule`, `found_one_def`\nDecided: nothing\n"
        said = self.v2mod.named_statements(brief, str(self.p.root), stated)
        self.assertIn("Stated already in what you hold", said)
        self.assertIn("`Beta.beta_rule`", said)
        self.assertIn("`found_one_def`", said)

    def test_what_a_session_is_given_is_split_so_each_read_is_shown_whole(self):
        with patch.object(self.v2mod, "RELATIONS_CHUNK", 2000):
            text, _, _ = self.v2mod.relations_read("1", "implementer", self.p.tasks[0]["description"], None)
        files = sorted((self.build / "1" / "relations-high").glob("*.md"))
        self.assertGreater(len(files), 1)
        self.assertTrue(all(len(f.read_bytes()) <= 2000 for f in files))
        self.assertIn(f"{len(files)} files", text)

    def test_a_brief_naming_nothing_is_given_nothing(self):
        text, given, _ = self.v2mod.relations_read("1", "implementer", "Kind: build\n", None)
        self.assertEqual(given, 0)
        self.assertIn("names no theory", text)
        self.assertFalse((self.build / "1" / "relations-high").exists())

    def test_the_brief_form_counts_the_relations_against_the_room(self):
        brief = self.p.tasks[0]["description"]
        given = self.v2mod.relations_size(brief, "build")
        self.assertGreater(given, 0)
        with patch.object(self.v2mod, "room_of", return_value=100_000):
            fits = [p for p in self.v2mod.brief_problems(brief + "Size: about 99K\n") if "Size" in p]
            self.assertTrue(any("of the task's own relations" in p for p in fits), fits)
            self.assertFalse([p for p in self.v2mod.brief_problems(brief + f"Size: about {(100_000 - given) // 1000 - 1}K\n")
                              if "Size" in p])


class CommandTests(unittest.TestCase):
    def test_the_command_runs_as_base_sh_runs_it(self):
        # base.sh runs `select_base_load.py --frontier WHO` at every layer refresh: the command itself, not only its
        # functions — its entry point was once lost with every function's test passing (2026-09-23)
        out = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(sbl.__file__)), "select_base_load.py"),
                              "--frontier", "max", "--dry-run"], capture_output=True, text=True, timeout=120,
                             env={k: v for k, v in os.environ.items() if k not in ("ORCH_LOAD_LIST", "BASE_LOAD_LIST")})
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("max", out.stdout)


if __name__ == "__main__":
    unittest.main()
