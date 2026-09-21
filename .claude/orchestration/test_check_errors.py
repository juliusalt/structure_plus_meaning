"""A check a session runs goes to its end and ends by listing every error it reported, one line each with where it
stands (the owner, 2026-09-21: all the errors at once, dealt with at once): check_errors.py, run as the guard runs it,
on commands standing in for checks."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_errors  # noqa: E402

FAILURE = '*** Failed to finish proof (line {n} of "/p/{t}.thy"):\n*** goal (1 subgoal):\n***  1. False\n'


class CheckErrorsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.dir = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def run_check(self, script, *watch, keep=None):
        args = [sys.executable, str(HERE / "check_errors.py")] + [a for w in watch for a in ("--watch", str(w))] + (
            ["--keep", str(keep)] if keep else []) + ["--", "bash", "-c", script]
        out = subprocess.run(args, capture_output=True, text=True, timeout=60)
        return out.returncode, out.stdout

    def test_it_runs_to_its_end_and_lists_every_error_last(self):
        (self.dir / "f.txt").write_text(FAILURE.format(n=7, t="A") + "noise\n" + FAILURE.format(n=40, t="B"))
        code, out = self.run_check(f"cat {self.dir}/f.txt; sleep 0.5; echo the end; exit 1")
        self.assertEqual(code, 1)                                            # its own status
        self.assertIn("the end\n[this check reported 2 errors, listed here with where each stands. Fix them all", out)
        self.assertTrue(out.endswith("- A.thy:7: Failed to finish proof\n- B.thy:40: Failed to finish proof\n"))

    def test_the_errors_of_the_logs_it_wrote_are_gathered_and_an_old_log_is_not(self):
        # the repository's checks log Isabelle's messages and print only a summary at their end
        (self.dir / "out/proof").mkdir(parents=True)
        old = self.dir / "out/old.log"
        old.write_text(FAILURE.format(n=1, t="Old"))
        os.utime(old, (time.time() - 60, time.time() - 60))
        code, out = self.run_check(f"echo '{FAILURE.format(n=12, t='C')}' >> {self.dir}/out/proof/build.log; "
                                   f"echo '*** Undefined fact: \"x\"' >> {self.dir}/out/proof/build.log; "
                                   "echo '{\"status\": \"failed\"}'", self.dir / "out")
        self.assertEqual(code, 0)
        self.assertIn("- C.thy:12: Failed to finish proof\n- Undefined fact: \"x\"\n", out)
        self.assertNotIn("Old.thy", out)                                     # another run's
        self.assertIn("reported 2 errors", out)

    def test_an_error_in_the_output_and_in_a_log_is_one_error(self):
        code, out = self.run_check(f"echo '{FAILURE.format(n=3, t='D')}' | tee {self.dir}/p.log", self.dir / "p.log")
        self.assertIn("reported 1 error,", out)

    def test_a_long_list_shows_what_fits_and_is_kept_whole(self):
        many = "".join(FAILURE.format(n=i, t="LongTheoryName_" + "x" * 30) for i in range(1, 60))
        (self.dir / "f.txt").write_text(many)
        code, out = self.run_check(f"cat {self.dir}/f.txt", keep=self.dir / "keep")
        listing = out[out.index("[this check reported"):]
        self.assertLessEqual(len(listing.encode()), check_errors.ROOM + 300)
        self.assertIn("reported 59 errors", listing)
        kept = listing.split("the whole list is kept in ")[1].split("]")[0]
        self.assertEqual(len(Path(kept).read_text().splitlines()), 59)

    def test_where_an_error_stands_is_its_command_in_the_theory(self):
        # as Isabelle writes it: a first line naming an ML file, the message, and the command it stands at
        text = ('*** exception THM 0 raised (line 308 of "drule.ML"):\n*** OF: multiple unifiers\n***  \\<lbrakk>x\n'
                '*** At command "by" (line 158 of "/p/Positioned.thy")\n'
                '*** Failed to apply initial proof method (line 106 of "/p/Positioned.thy"):\n*** using this:\n'
                '*** At command "by" (line 106 of "/p/Positioned.thy")\n')
        self.assertEqual(check_errors.errors_in(text), ["Positioned.thy:158: exception THM 0 raised",
                                                        "Positioned.thy:106: Failed to apply initial proof method"])

    def test_a_failed_check_lists_what_else_failed_native_or_not(self):
        # a native controller's error, a recipe's exception, a check's own summary: no Isabelle message among them
        out_dir = self.dir / "out"
        (out_dir / "recipes").mkdir(parents=True)
        script = (f"cd {self.dir}; printf 'Traceback (most recent call last):\\n  File x\\nKeyError: missing field\\n' > "
                  "out/recipes/controller.log; printf 'fine\\n' > out/recipes/other.log; "
                  "printf 'thread main panicked at src/run.rs:12: index out of bounds\\n' > out/native.log; "
                  """echo '{"recipe": "controller", "status": "failed", "exit_code": 1}'; """
                  """echo '{"recipe": "other", "status": "accepted"}'; """
                  """echo '{"status": "failed", "error": "AssertionError: Failed recipes: controller"}'; exit 1""")
        code, out = self.run_check(script, out_dir)
        self.assertEqual(code, 1)
        listing = out.split("[this check reported")[1]
        self.assertIn("- controller failed (exit 1): KeyError: missing field [", listing)
        self.assertIn("- the check: AssertionError: Failed recipes: controller\n", listing)
        self.assertIn("- thread main panicked at src/run.rs:12: index out of bounds [", listing)
        self.assertNotIn("other", listing)
        # a check that passed has nothing to fix, whatever its logs end on
        code, out = self.run_check(f"echo 'ValueError: an expected one' > {self.dir}/out/t.log", out_dir)
        self.assertEqual((code, "reported" in out), (0, False))

    def test_a_message_without_a_place_of_its_own_ends_with_the_one_before(self):
        text = ('*** Failed to finish proof (line 3 of "/p/A.thy"):\n*** At command "by" (line 3 of "/p/A.thy")\n'
                '*** Undefined fact: "x"\n*** At command "by" (line 9 of "/p/A.thy")\n')
        self.assertEqual(check_errors.errors_in(text), ["A.thy:3: Failed to finish proof", 'A.thy:9: Undefined fact: "x"'])

    def test_a_check_without_errors_says_nothing_more(self):
        self.assertEqual(self.run_check("echo fine; echo '### a warning'; exit 3"), (3, "fine\n### a warning\n"))

    def test_it_is_refused_without_a_command(self):
        out = subprocess.run([sys.executable, str(HERE / "check_errors.py"), "--watch", "x"], capture_output=True)
        self.assertEqual(out.returncode, 2)


if __name__ == "__main__":
    unittest.main()
