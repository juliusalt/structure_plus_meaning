theory Factor_Ordered_Target_Equality
  imports Factor_Executable_Artifact_Values Finite_Sorted_Set_Execution
begin

fun ordered_target_equal :: "finite_exact_target \<Rightarrow> finite_exact_target \<Rightarrow> bool" where
  "ordered_target_equal (Finite_Whole R) (Finite_Whole S)=(finite_artifact_rows R=finite_artifact_rows S)"
| "ordered_target_equal (Finite_Anchor R r) (Finite_Anchor S s)=
    (r=s \<and> finite_artifact_rows R=finite_artifact_rows S)"
| "ordered_target_equal (Finite_Whole R) (Finite_Anchor S s)=False"
| "ordered_target_equal (Finite_Anchor R r) (Finite_Whole S)=False"

theorem ordered_target_equal_exact:
  "ordered_target_equal x y \<longleftrightarrow> x=y"
  by (cases x; cases y) (auto simp: finite_artifact_rows_injective)

lemma finite_target_equal_ordered_code [code]:
  "HOL.equal (x::finite_exact_target) y=ordered_target_equal x y"
  by (simp only: equal_eq ordered_target_equal_exact)

text \<open>Target equality compares the existing complete canonical artifact
  rows. Carrier, incidence, every counted occurrence and functional binding
  remain part of equality, and anchored targets retain their exact address.
  The universal equation requires neither formation nor bounded word values.\<close>

end
