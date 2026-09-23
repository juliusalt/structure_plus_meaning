"""`v2.py change`: the one way a session changes files (the owner, 2026-09-21) — any number of changes to any number of
files in one call, judged whole, written all or none, and what refuses it said; run as a session runs it, through
bash with its changes in a quoted heredoc, in a throwaway world (fakes.py)."""
import os
from pathlib import Path
import stat
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
import v2  # noqa: E402

THEORY = 'theory A imports Main begin\nlemma x: "True"\n  by simp\nend\n'


class ChangeTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.a = self.w.write("theories/A.thy", THEORY)

    def tearDown(self):
        self.w.close()

    def change(self, blocks, cwd=None):
        """What the command says, run through bash as a session runs it."""
        script = f"{sys.executable} {HERE / 'v2.py'} change <<'EOF'\n{blocks}EOF\n"
        out = subprocess.run(["bash", "-c", script], cwd=cwd or self.w.project, env=self.w.env, capture_output=True,
                             text=True, timeout=60)
        self.assertEqual(out.stderr, "")
        return out.stdout

    def test_an_append_adds_its_text_at_the_end_with_nothing_to_match(self):
        # plan-47's append to PLANNING_LOG.md by SEARCH/REPLACE was refused for a text that recurred there, and its
        # mail and HANDOFF.md with it (2026-09-22 21:14)
        (self.w.project / "LOG.md").write_text("# Log\n\nsame line\nsame line")
        said = self.change("=== append LOG.md\n\nthe next entry\n=== write NOTES.md\nnotes\n")
        self.assertIn("LOG.md (appended at line 5)", said)
        self.assertEqual((self.w.project / "LOG.md").read_text(), "# Log\n\nsame line\nsame line\n\nthe next entry\n")
        said = self.change("=== append NEW.md\nfirst\n")        # a file not there yet begins with it
        self.assertEqual((self.w.project / "NEW.md").read_text(), "first\n")
        # the note that a call made one change: said of an edit of the repository's files, not of a session's own record
        self.assertIn("[one change in this call", said)
        self.assertNotIn("[one change in this call", self.change("=== write .build/tasks/1/result.md\nStatus: done\n"))

    def test_many_changes_to_many_files_in_one_call_in_order(self):
        said = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\n=======\n  by auto\n>>>>>>> REPLACE\n"
                           "<<<<<<< SEARCH\n  by auto\n=======\n  by (auto simp: x_def)\n>>>>>>> REPLACE\n"
                           "=== write theories/sub/B.thy\ntheory B imports A begin\nend\n\n")
        self.assertIn("theories/A.thy (2 replaced, at lines 3, 3)", said)  # the second saw what the first left
        self.assertIn("theories/sub/B.thy (written anew)", said)
        self.assertNotIn("one change in this call", said)
        self.assertEqual(self.a.read_text(), THEORY.replace("by simp", "by (auto simp: x_def)"))
        self.assertEqual((self.w.project / "theories/sub/B.thy").read_text(), "theory B imports A begin\nend\n")

    def test_a_theory_is_written_in_escapes_whatever_glyphs_the_change_uses(self):
        # the digests show glyphs, a theory takes escapes: fix-249 wrote a script of its own to turn one into the
        # other (2026-09-22)
        said = self.change("=== write theories/G.thy\ntheory G imports A begin\nlemma g: \"\u2200x. P x \u27f9 P x\" by simp\n"
                           "text \u2039a \u2014 b\u203a\nend\n"
                           "=== write NOTES.md\n\u2200 as it is\n")
        self.assertEqual((self.w.project / "theories/G.thy").read_text(),
                         "theory G imports A begin\nlemma g: \"\\<forall>x. P x \\<Longrightarrow> P x\" by simp\n"
                         "text \\<open>a \u2014 b\\<close>\nend\n")           # no symbol of Isabelle's: as it is
        self.assertIn("4 glyphs written into a theory as their escape", said)
        self.assertEqual((self.w.project / "NOTES.md").read_text(), "\u2200 as it is\n")  # a document keeps its own
        said = self.change("=== replace theories/G.thy\n<<<<<<< SEARCH\n\u2200x. P x\n=======\n\u2200y. P y\n>>>>>>> REPLACE\n")
        self.assertIn("theories/G.thy (1 replaced", said)                 # its search as the file holds it too
        self.assertIn("\\<forall>y. P y", (self.w.project / "theories/G.thy").read_text())

    def test_the_text_reaches_the_file_as_written(self):
        # a quoted heredoc passes Isabelle's symbols, a shell's `$` and backquotes, and backslashes untouched
        text = 'lemma y: "\\<forall>x. x = x \\<longrightarrow> True"  (* $HOME `date` \\n *)\n'
        self.change(f"=== replace theories/A.thy\n<<<<<<< SEARCH\nend\n=======\n{text}end\n>>>>>>> REPLACE\n")
        self.assertIn(text, self.a.read_text())

    def test_what_refuses_it_is_said_and_nothing_is_written(self):
        said = self.change("=== write theories/New.thy\nnew\n"
                           "=== replace theories/A.thy\n<<<<<<< SEARCH\n  by blast\n=======\n  by simp\n>>>>>>> REPLACE\n")
        self.assertIn("refused, and nothing was changed", said)
        self.assertIn("change 2 (replace theories/A.thy): its SEARCH text occurs 0 times", said)
        self.assertFalse((self.w.project / "theories/New.thy").exists())  # the write before it is not made either
        self.assertEqual(self.a.read_text(), THEORY)
        near = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\nend \n=======\nx\n>>>>>>> REPLACE\n")
        self.assertIn("its first line stands at line 3: compare the rest, whitespace included", near)

    def test_a_replacement_must_be_unique_and_replace_all_takes_every_one(self):
        self.w.write("theories/A.thy", "a\nb\na\n")
        said = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\na\n=======\nc\n>>>>>>> REPLACE\n")
        self.assertIn("occurs 2 times", said)
        self.assertIn("widen it until it is unique, or use `=== replace-all`", said)
        self.change("=== replace-all theories/A.thy\n<<<<<<< SEARCH\na\n=======\nc\n>>>>>>> REPLACE\n")
        self.assertEqual((self.w.project / "theories/A.thy").read_text(), "c\nb\nc\n")

    def test_a_call_that_makes_one_change_is_told_to_batch(self):
        # the owner, 2026-09-21: encourage batching by saying so when a session makes a single change
        said = self.change("=== write theories/One.thy\none\n")
        self.assertIn("one change in this call. When several are ready", said)

    def test_its_form_is_said_when_it_is_wrong(self):
        for blocks, wrong in (("some text\n", "stands outside any change"),
                              ("=== replace theories/A.thy\nloose\n", "stands outside a block"),
                              ("=== replace theories/A.thy\n<<<<<<< SEARCH\nx\n", "has no `=======` line"),
                              ("=== replace theories/A.thy\n<<<<<<< SEARCH\nx\n=======\ny\n", "has no `>>>>>>> REPLACE`"),
                              ("=== replace theories/A.thy\n<<<<<<< SEARCH\n=======\ny\n>>>>>>> REPLACE\n",
                               "searches for nothing"),
                              ("=== replace theories/A.thy\n", "has no <<<<<<< SEARCH block"),
                              ("", "it names no change")):
            said = self.change(blocks)
            self.assertIn("refused, and nothing was changed", said, blocks)
            self.assertIn(wrong, said, blocks)
        self.assertEqual(self.a.read_text(), THEORY)

    def test_a_block_that_lost_a_line_of_its_own_is_refused_rather_than_written_into_the_file(self):
        # design-66, 2026-09-21: the first of eight blocks had no `>>>>>>> REPLACE` line, the next block's markers and
        # texts were written into its entry.md as the replacement, and five requests went to finding and repairing it
        lost_replace = ("=== replace theories/A.thy\n<<<<<<< SEARCH\nlemma x\n=======\nlemma y\n=======\n"
                        "<<<<<<< SEARCH\nby simp\n=======\nby auto\n>>>>>>> REPLACE\n")
        said = self.change(lost_replace)
        self.assertIn("refused, and nothing was changed", said)
        self.assertIn("the block at line 2: its replacement text holds a", said)
        self.assertIn("`=======` line at line 6", said)                 # which line, so it need not count them
        self.assertIn("its own `>>>>>>> REPLACE` line is missing", said)
        self.assertIn("make two blocks", said)                          # and the way out that costs nothing:
        self.assertIn("write the file whole", said)                     # the file's whole text is the other
        lost_divider = ("=== replace theories/A.thy\n<<<<<<< SEARCH\nlemma x\n>>>>>>> REPLACE\n<<<<<<< SEARCH\n"
                        "by simp\n=======\nby auto\n>>>>>>> REPLACE\n")
        self.assertIn("its search text holds a `>>>>>>> REPLACE` line at line 4, so either its own `=======` line "
                      "is missing", self.change(lost_divider))
        self.assertEqual(self.a.read_text(), THEORY)
        whole = "<<<<<<< SEARCH\nold\n=======\nnew\n>>>>>>> REPLACE\n"   # a whole file may hold them
        self.assertIn("written anew", self.change(f"=== write docs/format.md\n{whole}"))
        self.assertEqual((self.w.project / "docs/format.md").read_text(), whole)

    def test_a_failure_part_way_puts_back_what_was_written(self):
        locked = self.w.project / "locked"
        locked.mkdir()
        self.w.write("locked/L.md", "kept\n")
        locked.chmod(stat.S_IRUSR | stat.S_IXUSR)  # its file cannot be replaced
        try:
            said = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\n=======\n  by auto\n"
                               ">>>>>>> REPLACE\n=== write theories/Fresh.thy\nfresh\n=== write locked/L.md\nnew\n")
        finally:
            locked.chmod(stat.S_IRWXU)
        self.assertIn("refused: the change could not be written", said)
        self.assertEqual(self.a.read_text(), THEORY)  # the first file, written before the failure, put back
        self.assertFalse((self.w.project / "theories/Fresh.thy").exists())  # and the one it made taken out
        self.assertEqual((locked / "L.md").read_text(), "kept\n")

    def test_a_file_keeps_its_mode_and_an_unchanged_one_is_not_touched(self):
        script = self.w.write("tools/run.sh", "echo a\n")
        script.chmod(0o755)
        self.change("=== replace tools/run.sh\n<<<<<<< SEARCH\necho a\n=======\necho b\n>>>>>>> REPLACE\n")
        self.assertTrue(os.access(script, os.X_OK))
        before = self.a.stat().st_mtime_ns
        said = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\n=======\n  by simp\n>>>>>>> REPLACE\n")
        self.assertIn("as it was", said)
        self.assertEqual(self.a.stat().st_mtime_ns, before)

    def test_paths_are_the_session_s_own(self):
        tree = self.w.project / ".build/trees/2/theories"
        tree.mkdir(parents=True)
        (tree / "A.thy").write_text(THEORY)
        self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\n=======\n  by auto\n>>>>>>> REPLACE\n",
                    cwd=tree.parent)
        self.assertIn("by auto", (tree / "A.thy").read_text())  # where the session stands
        self.assertEqual(self.a.read_text(), THEORY)

    def test_the_guard_and_the_command_read_the_same_changes(self):
        blocks = ("=== write a.md\nx\n=== replace b.md\n<<<<<<< SEARCH\ny\n=======\nz\n>>>>>>> REPLACE\n"
                  "=== replace-all a.md\n<<<<<<< SEARCH\nx\n=======\nw\n>>>>>>> REPLACE\n")
        ops, problems = v2.change_blocks(blocks)
        self.assertEqual(problems, [])
        self.assertEqual([(o["op"], o["path"], o["n"]) for o in ops],
                         [("write", "a.md", 1), ("replace", "b.md", 2), ("replace-all", "a.md", 3)])



ROOT_TEXT = ('session S = HOL +\n  options [document = false]\n  directories "theories"\n  theories\n'
             '    A\n    C\n')
MAP = ("# Active theory graph\n\n| Theory | Direct imports | Content |\n|---|---|---|\n"
       "| A | Main | The first. |\n| C | A | The third. |\n\nAfter the table.\n")


class KeyedTests(unittest.TestCase):
    """The index files edited by the theory they index: a THEORY_MAP.md row (`=== row`), its imports read from the
    theory, and a ROOT declaration (`=== root`) — 161 requests of the implementers and fixers of 2026-09-21/22 did
    nothing but quote and rewrite a row — and what the source checks say of a change, told with it."""

    def setUp(self):
        self.w = fakes.World()
        self.w.write("theories/A.thy", THEORY)
        self.w.write("theories/C.thy", "theory C imports A begin\nend\n")
        self.w.write("ROOT", ROOT_TEXT)
        self.w.write("THEORY_MAP.md", MAP)

    def tearDown(self):
        self.w.close()

    change = ChangeTests.change

    def read(self, name):
        return (self.w.project / name).read_text()

    def test_a_new_theory_is_declared_and_given_its_row_in_one_call(self):
        said = self.change('=== write theories/B.thy\ntheory B\n  imports A (* the first *) "HOL-Library.FSet"\nbegin\nend\n'
                           "=== row B\nThe second,\n  over the first.\n=== root B\n")
        self.assertIn("ROOT (B declared at line 6)", said)
        self.assertIn("THEORY_MAP.md (the row of B written anew, at line 6)", said)
        self.assertNotIn("the sources", said)                           # declared and with its row: nothing to say
        self.assertEqual(self.read("ROOT"), ROOT_TEXT.replace("    A\n", "    A\n    B\n"))   # after its import
        rows = [l for l in self.read("THEORY_MAP.md").splitlines() if l.startswith("| ")]
        self.assertEqual(rows[1:], ["| A | Main | The first. |", '| B | A, HOL-Library.FSet | The second, over the first. |',
                                    "| C | A | The third. |"])          # in ROOT's order, imports as the theory has them

    def test_a_row_alone_reads_its_imports_again_and_keeps_its_content(self):
        self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\nimports A\n=======\nimports A Main\n>>>>>>> REPLACE\n")
        said = self.change("=== row C\n")
        self.assertIn("the row of C replaced, at line 6", said)
        self.assertIn("| C | A, Main | The third. |", self.read("THEORY_MAP.md"))
        self.change("=== row C\nThe third, anew.\n")
        self.assertIn("| C | A, Main | The third, anew. |", self.read("THEORY_MAP.md"))
        self.assertEqual(self.read("THEORY_MAP.md").count("| C |"), 1)

    def test_a_new_row_goes_beside_the_row_named_the_map_being_in_sections(self):
        self.w.write("THEORY_MAP.md", MAP + "\n## A section\n\n| Theory | Imports | Responsibility |\n|---|---|---|\n"
                                            "| Y | A | The first of it. |\n| Z | A | The last. |\n")
        self.w.write("theories/B.thy", "theory B imports A begin\nend\n")
        said = self.change("=== row B after Y\nIn the section.\n")
        self.assertIn("the row of B written anew", said)
        rows = [l for l in self.read("THEORY_MAP.md").splitlines() if l.startswith("| ")]
        self.assertEqual(rows[-3:], ["| Y | A | The first of it. |", "| B | A | In the section. |", "| Z | A | The last. |"])

    def test_a_declaration_goes_where_it_is_named_and_is_made_once(self):
        self.w.write("theories/D.thy", "theory D imports C begin\nend\n")
        self.assertIn("D declared at line 6", self.change("=== root D after A\n"))
        said = self.change("=== root D\n")
        self.assertIn("D declared already, at line 6", said)
        self.assertIn("as it was", said)
        self.assertEqual(self.read("ROOT").count("    D\n"), 1)

    def test_what_refuses_an_index_edit_is_said_and_nothing_is_written(self):
        before = (self.read("ROOT"), self.read("THEORY_MAP.md"))
        for blocks, said in (("=== row Nowhere\nIts row.\n", "theories/Nowhere.thy is not there"),
                             ("=== row B\n", None),
                             ("=== root New after Nowhere\n", "ROOT declares no Nowhere"),
                             ("=== root C\nsome text\n", "a declaration is its head line alone"),
                             ("=== row C\nA | B\n", "holds a `|`"),
                             ("=== row C after A\nx\n", "`after` places a new row"),
                             ("=== row New after Nowhere\nx\n", "holds no row of Nowhere")):
            out = self.change("=== write theories/New.thy\ntheory New imports A begin\nend\n" + blocks)
            self.assertTrue(out.startswith("refused, and nothing was changed"), out)
            if said:
                self.assertIn(said, out)
            self.assertFalse((self.w.project / "theories/New.thy").exists())
        self.assertIn("B has no row yet", self.change("=== write theories/B.thy\ntheory B imports A begin\nend\n=== row B\n"))
        self.w.write("THEORY_MAP.md", MAP.replace("| C | A | The third. |", "| C | A | The third. |\n| C | A | Again. |"))
        self.assertIn("holds the row of C 2 times", self.change("=== row C\nOnce.\n"))
        self.assertEqual(before[0], self.read("ROOT"))

    def test_the_sources_are_told_with_the_change_that_concerns_them(self):
        said = self.change("=== write theories/B.thy\ntheory B imports A begin\nlemma b: True sorry\nend\n")
        self.assertIn("theories/B.thy is not declared in ROOT (`=== root B`)", said)
        self.assertIn("theories/B.thy:2 escapes its proof: lemma b: True sorry", said)
        self.assertIn("B has no row in THEORY_MAP.md", said)
        # a theory whose imports change is told its row names others; a proof changed is not told its row again
        said = self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\nimports A\n=======\nimports A B\n>>>>>>> REPLACE\n")
        self.assertIn("the row of C names the imports A, and the theory imports A, B", said)
        said = self.change("=== replace theories/A.thy\n<<<<<<< SEARCH\n  by simp\n=======\n  by auto\n>>>>>>> REPLACE\n")
        self.assertNotIn("the sources", said)
        # a declaration taken out of ROOT whose theory stays: told; a change elsewhere than a tree's top: nothing
        said = self.change("=== replace ROOT\n<<<<<<< SEARCH\n    C\n=======\n>>>>>>> REPLACE\n")
        self.assertIn("theories/C.thy is not declared in ROOT", said)
        (self.w.project / "sub/theories").mkdir(parents=True)
        self.assertNotIn("the sources", self.change("=== write theories/E.thy\ntheory E imports A begin\nend\n",
                                                    cwd=self.w.project / "sub"))

    def test_a_name_or_statement_the_library_has_is_told_when_it_is_written_again(self):
        # 14 of the 31 rejections whose findings the state held on 2026-09-23 were a notion or fact the library
        # already had; three were a row offering what the task had removed
        long = "finite_carrier S \\<Longrightarrow> card (image f S) \\<le> card S"
        self.w.write("theories/C.thy", f'theory C imports A begin\nlemma carrier_card_image: "{long}"\n  by simp\n'
                                       'lemma short: "True" by simp\nlemma carrier_only_here: "True" by simp\n'
                                       'definition cell_result where "cell_result c = (case c of None \\<Rightarrow> None | Some (r, a) \\<Rightarrow> r)"\nend\n')
        self.w.write("THEORY_MAP.md", MAP.replace("The third.", "Offers `carrier_card_image`, `short` and `carrier_only_here`; "
                                                  "the superseded `carrier_old_bound` is removed."))
        said = self.change(f'=== write theories/D.thy\ntheory D imports C begin\nlemma carrier_card_image: "True" by simp\n'
                           f'lemma image_card_bound:\n  "{long}"\n  by simp\nlemma short: "True" by simp\n'
                           'definition history_result :: "(nat \\<times> nat) option \\<Rightarrow> nat option" where\n'
                           '  "history_result x = (case x of None \\<Rightarrow> None | Some (r, a) \\<Rightarrow> r)"\nend\n'
                           "=== root D\n=== row D\nThe fourth.\n")
        self.assertIn("`carrier_card_image`, new in D, is declared in C too", said)
        self.assertIn("`image_card_bound` states what C.carrier_card_image states, word for word", said)
        self.assertIn("`history_result` defines what C.cell_result defines, its arguments aside", said)
        self.assertNotIn("`short`", said)                                  # a name that says little is left alone
        # written again, what it already declared is not told again
        said = self.change("=== replace theories/D.thy\n<<<<<<< SEARCH\nlemma short\n=======\nlemma short'\n>>>>>>> REPLACE\n")
        self.assertNotIn("carrier_card_image", said)
        # a fact taken out that the theory's row still offers, and that a decision cites
        self.w.write("DECISIONS.md", "# Decisions\n\n## The carrier's bound\n\nIt rests on `carrier_only_here` and "
                                     "`carrier_card_image`.\n")
        said = self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\nlemma carrier_only_here\n=======\nlemma carrier_card_bound\n>>>>>>> REPLACE\n")
        self.assertIn("the row of C offers `carrier_only_here`, which this change took out of C", said)
        self.assertIn('DECISIONS.md cites `carrier_only_here`, which this change took out of C, in "The carrier\'s bound"',
                      said)
        # one that another theory still declares has moved, and its mention cites it there; a removal note offers nothing
        said = self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\nlemma carrier_card_image\n=======\nlemma carrier_image_bound\n>>>>>>> REPLACE\n")
        self.assertNotIn("carrier_card_image", said)                     # D declares it
        self.w.write("theories/C.thy", open(self.w.project / "theories/C.thy").read().replace("end\n", 'lemma carrier_old_bound: "True" by simp\nend\n'))
        said = self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\nlemma carrier_old_bound\n=======\nlemma carrier_new_bound\n>>>>>>> REPLACE\n")
        self.assertNotIn("carrier_old_bound", said)                      # its row says it is removed
        # a definition made an input abbreviation is still declared (task 272's rule patterns, told taken out)
        self.w.write("theories/C.thy", open(self.w.project / "theories/C.thy").read().replace(
            "end\n", 'definition carrier_input_form :: bool where "carrier_input_form = True"\nend\n'))
        self.w.write("THEORY_MAP.md", open(self.w.project / "THEORY_MAP.md").read().replace("and `carrier_only_here`",
                                                                                          "`carrier_input_form` and `carrier_only_here`"))
        said = self.change("=== replace theories/C.thy\n<<<<<<< SEARCH\ndefinition carrier_input_form :: bool where \"carrier_input_form = True\"\n"
                           "=======\nabbreviation (input) carrier_input_form :: bool where \"carrier_input_form \\<equiv> True\"\n>>>>>>> REPLACE\n")
        self.assertNotIn("carrier_input_form", said)

    def test_the_import_graph_is_told_with_the_change_that_writes_a_theory(self):
        # the planner's standing last step ran the repository's import graph by hand before every hand-over: the tree's
        # own tool says it now, with the change (here a stand-in that names what the real one refuses)
        self.w.write("tools/execution_support.py",
                     "def source_graph(project, overlays, roots):\n"
                     "    if 'Loop' in roots:\n"
                     "        raise ValueError('Cyclic theory import: Loop; Loop imports Loop.')\n"
                     "    return {}, {}\n")
        said = self.change("=== write theories/Loop.thy\ntheory Loop imports Loop begin\nend\n=== root Loop\n"
                           "=== row Loop\nA loop.\n")
        self.assertIn("the import graph: Cyclic theory import: Loop; Loop imports Loop.", said)
        said = self.change("=== write theories/Fine.thy\ntheory Fine imports A begin\nend\n=== root Fine\n=== row Fine\nFine.\n")
        self.assertNotIn("import graph", said)

    def test_what_the_harness_tells_beside_a_change_never_breaks_it(self):
        # the information parts fail soft (v2.softly): a launch failed on one before its test, 2026-09-23
        from unittest.mock import patch
        with patch.object(v2, "STATE", str(self.w.state)), \
                patch.object(v2, "sources_said", side_effect=RuntimeError("boom")):
            said = v2.cmd_change("=== write theories/B.thy\ntheory B imports A begin\nend\n", base=str(self.w.project))
            self.assertEqual(v2.softly("x", lambda: 1 / 0, default="none"), "none")  # logged in the fake's state only
        self.assertTrue(said.startswith("changed: theories/B.thy (written anew)"), said)
        self.assertTrue((self.w.project / "theories/B.thy").exists())
        self.assertIn("ATTENTION what the sources say after the change could not be had: RuntimeError('boom')",
                      (self.w.state / "v2.log").read_text())

    def test_the_guard_reads_an_index_edit_as_a_write_of_its_file(self):
        ops, problems = v2.change_blocks("=== row B\nIts row.\n=== root B after A\n")
        self.assertEqual(problems, [])
        self.assertEqual([(o["op"], o["path"], o["theory"], o["after"]) for o in ops],
                         [("row", "THEORY_MAP.md", "B", None), ("root", "ROOT", "B", "A")])

if __name__ == "__main__":
    unittest.main()
