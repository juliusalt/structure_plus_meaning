"""show.py: named commands whole, the planner's statement views, and theory-qualified names."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fakes  # noqa: E402

READY = r"""theory Ready
  imports Main
begin

text \<open>Readiness of calls.\<close>

definition ready :: "nat \<Rightarrow> bool" where
  "ready n = (n > 0)"

lemma ready_suc: "ready (Suc n)"
  unfolding ready_def by simp

lemma ready_pos:
  assumes "n > 0"
  shows "ready n"
proof -
  show ?thesis using assms by (simp add: ready_def)
qed

ML \<open>
  val x = 1
  val y = 2
  val z = 3
\<close>

end
"""


class ShowTests(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.w.write("theories/Ready.thy", READY)
        self.w.write("theories/Other.thy", "theory Other imports Ready begin\n\nlemma ready_pos: \"True\" by simp\n\nend\n")
        self.w.write(".build/tasks/2/Draft.thy", "theory Draft imports Ready begin\nlemma drafted: \"ready 1\"\n  by (simp add: ready_def)\nend\n")

    def tearDown(self):
        self.w.close()

    def show(self, *args):
        return self.w.run("show.py", *args)

    def test_a_name_is_shown_whole_with_its_proof_and_place(self):
        code, out, _ = self.show("ready_suc", "ready")
        self.assertEqual(code, 0)
        self.assertIn("== theories/Ready.thy:10\nlemma ready_suc: \"ready (Suc n)\"\n  unfolding ready_def by simp\n", out)
        self.assertIn("== theories/Ready.thy:7\ndefinition ready", out)

    def test_a_theory_qualifies_a_name(self):
        _, out, _ = self.show("ready_pos")
        self.assertEqual(out.count("== theories/"), 2)
        _, out, _ = self.show("Ready.ready_pos")
        self.assertEqual(out.count("== theories/"), 1)
        self.assertIn("proof -", out)

    def test_candidates_outside_theories_are_searched_when_named(self):
        self.assertEqual(self.show("drafted")[0], 1)
        code, out, _ = self.show("--in", str(self.w.project / ".build/tasks/2/Draft.thy"), "drafted")
        self.assertEqual(code, 0)
        self.assertIn("by (simp add: ready_def)", out)

    def test_the_planners_views_leave_proofs_out(self):
        _, out, _ = self.show("--statement", "Ready.ready_pos")
        self.assertIn('lemma ready_pos:\n  assumes "n > 0"\n  shows "ready n"', out)
        self.assertNotIn("proof", out)
        code, out, _ = self.show("--statements", "Ready")
        self.assertEqual(code, 0)
        self.assertIn("(* proof omitted: 2 lines *)", out)
        self.assertIn("(* proof omitted: 4 lines *)", out)
        self.assertNotIn("show ?thesis", out)
        self.assertNotIn("val y = 2", out)
        self.assertIn("definition ready", out)
        self.assertIn("== Nope: no such theory", self.show("--statements", "Nope")[1])

    def test_a_missing_name_says_where_it_is_mentioned(self):
        code, out, _ = self.show("ready_def")
        self.assertEqual(code, 1)
        self.assertIn("== ready_def: no command introduces it; theories mentioning it: Ready", out)


if __name__ == "__main__":
    unittest.main()
