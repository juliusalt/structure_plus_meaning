theory Factor_Ordered_Target_Equality
  imports Factor_Executable_Artifact_Values Finite_Sorted_Set_Execution
begin

definition ordered_artifact_equal :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> bool" where
  "ordered_artifact_equal R S \<longleftrightarrow>
    sorted_list_of_fset (finite_carrier (finite_structure R))=sorted_list_of_fset (finite_carrier (finite_structure S)) \<and>
    sorted_list_of_fset (finite_incidence (finite_structure R))=sorted_list_of_fset (finite_incidence (finite_structure S)) \<and>
    sorted_list_of_multiset (finite_bag (finite_data R))=sorted_list_of_multiset (finite_bag (finite_data S)) \<and>
    sorted_list_of_fset (finite_bindings (finite_data R))=sorted_list_of_fset (finite_bindings (finite_data S))"

lemma ordered_artifact_equal_rows:
  "ordered_artifact_equal R S \<longleftrightarrow> finite_artifact_rows R=finite_artifact_rows S"
  by (simp add: ordered_artifact_equal_def finite_artifact_rows_def)

lemma ordered_artifact_equal_exact:
  "ordered_artifact_equal R S \<longleftrightarrow> R=S"
  by (simp only: ordered_artifact_equal_rows finite_artifact_rows_injective)

fun ordered_target_equal :: "finite_exact_target \<Rightarrow> finite_exact_target \<Rightarrow> bool" where
  "ordered_target_equal (Finite_Whole R) (Finite_Whole S)=ordered_artifact_equal R S"
| "ordered_target_equal (Finite_Anchor R r) (Finite_Anchor S s)=(r=s \<and> ordered_artifact_equal R S)"
| "ordered_target_equal (Finite_Whole R) (Finite_Anchor S s)=False"
| "ordered_target_equal (Finite_Anchor R r) (Finite_Whole S)=False"

theorem ordered_target_equal_exact:
  "ordered_target_equal x y \<longleftrightarrow> x=y"
  by (cases x; cases y) (auto simp: ordered_artifact_equal_exact)

lemma finite_target_equal_ordered_code [code]:
  "HOL.equal (x::finite_exact_target) y=ordered_target_equal x y"
  by (simp only: equal_eq ordered_target_equal_exact)

text \<open>Target equality compares the complete canonical fields of the two
  artifacts in row order and stops at the first differing field, so a differing
  carrier needs no incidence, counted data or binding listing. Carrier,
  incidence, every counted occurrence and functional binding remain part of
  equality, and anchored targets retain their exact address. The universal
  equation requires neither formation nor bounded word values.\<close>

end
