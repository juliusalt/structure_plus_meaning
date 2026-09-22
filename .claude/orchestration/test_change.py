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


if __name__ == "__main__":
    unittest.main()
