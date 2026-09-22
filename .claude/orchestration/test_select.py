"""What a base holds is chosen by use (select_base_load): the evidence a session leaves, the frontier within the layer's
budget, the founding tier by what its roles used, and the indexes that say what is not held. Each test builds a small
project of its own — theories, a map, a load list and transcripts — so nothing here reads the repository's sources."""
import json
import os
from pathlib import Path
import sys
import tempfile
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
# === layer === the frontier layer below
# the working frontier (1 theories for the implementer sessions, chosen by hand), as statements
theories/Delta.thy
# pinned: the owner's voice
notes.md
"""


def thy(name, lemmas, filler):
    body = "\n".join(f"lemma {n}: \"True\"\n  by simp" for n in lemmas)
    pad = "\n".join(f"lemma {name.lower()}_filler_{i}: \"x{i} = x{i} \\<and> True \\<and> True\"\n  by simp" for i in range(filler))
    return f"theory {name}\n  imports Main\nbegin\n\n{body}\n\n{pad}\n\nend\n"


def assistant(text="", command=None):
    content = [{"type": "text", "text": text}] if text else []
    if command:
        content.append({"type": "tool_use", "id": f"t{abs(hash(command)) % 10**8}", "name": "Bash", "input": {"command": command}})
    return {"type": "assistant", "message": {"id": f"m{abs(hash(text + str(command))) % 10**8}", "content": content}}


def user(text):
    return {"type": "user", "message": {"content": [{"type": "text", "text": text}]}}


def result(tool_id, body):
    return {"type": "user", "message": {"content": [{"type": "tool_result", "tool_use_id": tool_id, "content": body}]}}


class Project:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "theories").mkdir()
        for name, (lemmas, filler) in THEORIES.items():
            (self.root / "theories" / f"{name}.thy").write_text(thy(name, lemmas, filler))
        rows = "\n".join(f"| {n} | x | {n} holds its lemmas; and more words follow here |" for n in THEORIES)
        (self.root / "THEORY_MAP.md").write_text("| Theory | Imports | Content |\n|---|---|---|\n" + rows + "\n")
        self.orch = self.root / ".claude" / "orchestration"
        (self.orch / "state" / "held").mkdir(parents=True)
        (self.orch / "base-load-high.txt").write_text(LIST)
        (self.root / "notes.md").write_text("the owner's words\n")
        self.transcripts = self.root / "t"
        self.transcripts.mkdir()
        self.n = 0
        self.changing = set()

    def session(self, *records, fork=True):
        """A transcript: a fork's copy of its base's load first (naming names that are not its own), then its launch."""
        self.n += 1
        lines = []
        if fork:
            lines += [user("Load the reference library; ..."), assistant("gamma_law is held", "echo gamma_law")]
            lines += [user(f"You are implement-{self.n}, working on task {self.n}.")]
        lines += list(records)
        path = self.transcripts / f"s{self.n}.jsonl"
        path.write_text("".join(json.dumps(r) + "\n" for r in lines))
        return str(path)

    def patches(self, sessions):
        return [patch.object(sbl, "PROJECT", str(self.root)), patch.object(sbl, "HERE", str(self.orch)),
                patch.object(manifest, "PROJECT", str(self.root)), patch.object(manifest, "HERE", str(self.orch)),
                patch.object(sbl, "sessions_of", lambda roles, limit=0: sessions[:limit] if limit else sessions),
                patch.object(sbl, "forking_roles", lambda who: {"implementer"}),
                patch.object(sbl, "founding_theories", lambda: ["Found_One", "Found_Two", "Found_Three", "Pinned"]),
                patch.object(sbl, "recently_changed", lambda days=None: self.changing),
                patch.dict(sbl.DEFINED, {}, clear=True), patch.dict(sbl.FACT_THEORY, {}, clear=True)]


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.p = Project()

    def tearDown(self):
        self.p.temp.cleanup()

    def test_a_session_uses_what_it_reads_or_names_itself_and_not_what_it_was_shown(self):
        shown = assistant("", "grep -rn lemma theories/ | head")
        tool = shown["message"]["content"][0]["id"]
        read = assistant("", "sed -n 1,20p theories/Beta.thy")
        s = self.p.session(assistant("I cite alpha_one in the proof", "echo alpha_one"),
                           read, result(read["message"]["content"][0]["id"], "theory Beta ..."),
                           shown, result(tool, "theories/Delta.thy: lemma delta_step"))
        with patch.object(sbl, "PROJECT", str(self.p.root)), patch.dict(sbl.DEFINED, {}, clear=True), \
                patch.dict(sbl.FACT_THEORY, {}, clear=True):
            use = sbl.use_of([s])
        self.assertIn("theories/Alpha.thy", use)          # named in its own writing
        self.assertIn("theories/Beta.thy", use)           # read
        self.assertNotIn("theories/Delta.thy", use)       # only shown to it
        self.assertNotIn("theories/Gamma.thy", use)       # named in the copy of its base's load, not by it

    def test_a_name_many_theories_define_says_nothing(self):
        for name in ("Epsilon", "Zeta", "Eta", "Theta"):
            (self.p.root / "theories" / f"{name}.thy").write_text(thy(name, ["shared_name"], 5))
        with patch.object(sbl, "PROJECT", str(self.p.root)):
            defined = sbl.defined_names()
        self.assertNotIn("shared_name", defined)
        self.assertEqual(defined["alpha_one"], {"theories/Alpha.thy"})


class WindowTests(unittest.TestCase):
    def test_the_sessions_measured_reach_into_the_archive(self):
        # v2 archives a session a day after it was released: a window of 400 sessions was a day of them, not a week
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "v2-archive.jsonl").write_text(
                json.dumps({"session": {"name": "fix-1", "role": "fixer", "sid": "old", "started": 100}}) + "\n"
                + json.dumps({"ask": {"qid": "q1"}}) + "\n"
                + json.dumps({"session": {"name": "review-2", "role": "reviewer", "sid": "other", "started": 150}}) + "\n")
            live = {"fix-3": {"role": "fixer", "sid": "new", "started": 300}, "implement-4": {"role": "implementer",
                                                                                          "sid": "mid", "started": 200}}
            for sid in ("old", "other", "new", "mid"):
                (root / f"{sid}.jsonl").write_text("{}\n")
            import v2
            with patch.object(v2, "STATE", str(root)), patch.object(v2, "peek", lambda: {"sessions": live}), \
                    patch.object(v2, "transcript", lambda sid: str(root / f"{sid}.jsonl")):
                got = sbl.sessions_of({"fixer", "implementer"}, limit=10)
                self.assertEqual([os.path.basename(p) for p in got], ["new.jsonl", "mid.jsonl", "old.jsonl"])
                self.assertEqual(len(sbl.sessions_of({"fixer", "implementer"}, limit=2)), 2)


class ChoiceTests(unittest.TestCase):
    def test_ranked_by_use_per_token_within_the_room_and_over_the_floor(self):
        use = {"a": {1, 2, 3, 4}, "b": {1, 2, 3, 4, 5, 6}, "c": {1, 2}, "d": {1}, "e": {1, 2, 3}}
        sizes = {"a": 100, "b": 600, "c": 50, "d": 10, "e": 1000}
        chosen, spent = sbl.ranked_within(use, sizes, room=800, need=2)
        # c: 0.04/token, a: 0.04, b: 0.01, e: 0.003; d under the floor; e does not fit after the others
        self.assertEqual(chosen, ["a", "c", "b"])
        self.assertEqual(spent, 750)
        chosen, _ = sbl.ranked_within(use, sizes, room=160, need=2)
        self.assertEqual(chosen, ["a", "c"])               # b passed over, smaller ones still taken

    def test_the_room_is_the_target_less_what_else_the_base_holds(self):
        self.assertEqual(sbl.layer_room(200_000, 100_000, target=530_000, factor=1.1), int(330_000 / 1.1 - 100_000))
        self.assertEqual(sbl.layer_room(600_000, 0, target=530_000, factor=1.0), 0)

    def test_an_index_line_keeps_the_first_clause_cut_at_a_word(self):
        self.assertEqual(sbl.clause("Short clause; the rest"), "Short clause")
        long = "An index notion over rows whose every key is placed once and read back by its position in the store"
        cut = sbl.clause(long, cap=40)
        self.assertTrue(cut.endswith(" …") and len(cut) <= 42, cut)
        self.assertTrue(long.startswith(cut[:-2]))
        self.assertEqual(sbl.clause("Version 2.1 holds; more"), "Version 2.1 holds")  # a dot inside a word is no end


class FrontierTests(unittest.TestCase):
    def setUp(self):
        self.p = Project()

    def tearDown(self):
        self.p.temp.cleanup()

    def run_frontier(self, sessions, target, dry=False):
        ps = self.p.patches(sessions) + [patch.object(sbl, "TARGET", target), patch.object(sbl, "FRONTIER_EVIDENCE", 3)]
        for q in ps:
            q.start()
        try:
            return sbl.frontier("high", dry_run=dry)
        finally:
            for q in reversed(ps):
                q.stop()

    def tier(self):
        text = (self.p.orch / "base-load-high.txt").read_text()
        lines = text[text.index(sbl.FRONTIER_HEAD):].splitlines()
        entries = []
        for l in lines[1:]:
            if l.startswith("# "):
                break
            if l.strip():
                entries.append(l.split("  #")[0])
        return lines[0], entries

    def test_the_frontier_is_what_the_roles_used_by_use_per_token_within_the_layer_s_room(self):
        s = []
        for i in range(10):
            names = ["alpha_one"] + (["gamma_law"] if i < 6 else []) + (["beta_rule"] if i < 8 else []) + \
                    (["delta_step"] if i < 1 else []) + (["found_one_def"] if i < 9 else [])
            s.append(self.p.session(assistant("working with " + " ".join(names), "echo " + " ".join(names))))
        self.run_frontier(s, target=10_000_000)
        head, entries = self.tier()
        # Found_One is held in the stable part, Delta used by one session only (under the floor of 2)
        self.assertEqual(entries, ["theories/Alpha.thy", "theories/Gamma.thy", "theories/Beta.thy"])
        self.assertIn("(3 theories", head)
        self.assertIn("as statements", head)

    def test_what_the_rest_of_the_list_holds_is_never_chosen_again(self):
        # a theory the founding tier now keeps, which the frontier held before, stays the stable part's alone: counted
        # by name it was chosen again and held in both parts (2026-09-22)
        text = (self.p.orch / "base-load-high.txt").read_text()
        (self.p.orch / "base-load-high.txt").write_text(
            text.replace("theories/Delta.thy\n", "theories/Delta.thy\ntheories/Found_One.thy\ntheories/Gamma.thy\n"))
        s = [self.p.session(assistant("x", "echo found_one_def alpha_one gamma_law")) for _ in range(6)]
        self.run_frontier(s, target=10_000_000)
        _, entries = self.tier()
        self.assertEqual(sorted(entries), ["theories/Alpha.thy", "theories/Gamma.thy"])  # Gamma, held before, again

    def test_too_few_sessions_leave_it_as_it_stands(self):
        before = (self.p.orch / "base-load-high.txt").read_text()
        self.run_frontier([self.p.session(assistant("alpha_one", "echo alpha_one"))], target=10_000_000)
        self.assertEqual((self.p.orch / "base-load-high.txt").read_text(), before)

    def test_the_layer_s_room_bounds_it(self):
        s = [self.p.session(assistant("x", "echo alpha_one gamma_law beta_rule")) for _ in range(5)]
        ps = self.p.patches(s)
        for q in ps:
            q.start()
        try:
            stable = sbl.estimate(sbl.held_by("high", "stable"))
            fixed = sbl.estimate([e for e in sbl.held_by("high", "layer") if not e[1].endswith("Delta.thy")])
            alpha = sbl.tokens(str(self.p.root / "theories/Alpha.thy"))[0]
            gamma = sbl.tokens(str(self.p.root / "theories/Gamma.thy"))[0]
        finally:
            for q in reversed(ps):
                q.stop()
        target = int((stable + (fixed + alpha + gamma) * sbl.LAYER_FACTOR)) + 5  # room for Alpha and Gamma, not Beta
        self.run_frontier(s, target=target)
        _, entries = self.tier()
        self.assertEqual(sorted(entries), ["theories/Alpha.thy", "theories/Gamma.thy"])


class FoundingTests(unittest.TestCase):
    def setUp(self):
        self.p = Project()

    def tearDown(self):
        self.p.temp.cleanup()

    def test_the_founding_tier_keeps_what_its_roles_used_and_the_index_says_the_rest(self):
        s = [self.p.session(assistant("x", "echo found_one_def")) for _ in range(3)]
        rd = assistant("x", "sed -n 1,5p theories/Found_Two.thy")
        s += [self.p.session(rd, result(rd["message"]["content"][1]["id"], "theory Found_Two"))]  # read by one only
        s += [self.p.session(assistant("x", "echo alpha_one")) for _ in range(6)]
        ps = self.p.patches(s) + [patch.object(sbl, "FRONTIER_EVIDENCE", 3)]
        for q in ps:
            q.start()
        try:
            sbl.founding("high")
            text = (self.p.orch / "base-load-high.txt").read_text()
            head = text[text.index(sbl.FOUNDING_HEAD):].splitlines()
            tier = [l for l in head[1:head.index("# pinned idea: the test's pin")] if l]
            self.assertEqual(tier, ["theories/Found_One.thy"])       # Found_Two by one session, Found_Three by none
            self.assertIn("as signatures", head[0])                   # the level the tier's header gives stays
            self.assertIn("the 1 that at least 2 of the last 10", head[0])
            self.assertIn("theories/Pinned.thy", text)               # the central ideas are not the tier's
            held = {os.path.basename(p)[:-4] for _, p, _ in sbl.held_by("high") if p.endswith(".thy")}
            sbl.founding_index(held)
            index = (self.p.orch / "state/held/founding-index.md").read_text()
            self.assertIn("Found_Two: Found_Two holds its lemmas", index)
            self.assertIn("Found_Three:", index)
            self.assertNotIn("Found_One:", index)                    # held
            self.assertNotIn("Pinned:", index)
            # a founding theory in use that main is changing is the frontier's, not the stable part's
            self.p.changing = {"Found_One"}
            sbl.founding("high")
            text = (self.p.orch / "base-load-high.txt").read_text()
            head = text[text.index(sbl.FOUNDING_HEAD):].splitlines()
            self.assertEqual([l for l in head[1:head.index("# pinned idea: the test's pin")] if l], [])
            self.assertIn("1 more in use are changing", head[0])
        finally:
            for q in reversed(ps):
                q.stop()


if __name__ == "__main__":
    unittest.main()
