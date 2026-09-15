theory Nested_Artifact_Value_Identity
  imports Factor_Executable_Artifact_Values Generation_Identity_Maps
    RRA_Finite_Generations Finite_Reader_Identity_Maps
begin

fun nested_target_rows :: "finite_exact_target \<Rightarrow> artifact_value_rows \<times> local_address option" where
  "nested_target_rows (Finite_Whole R)=(finite_artifact_rows R,None)"
| "nested_target_rows (Finite_Anchor R r)=(finite_artifact_rows R,Some r)"

lemma nested_target_rows_injective:
  "nested_target_rows x=nested_target_rows y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp_all add: finite_artifact_rows_injective)

definition nested_generation_rows where
  "nested_generation_rows=map_generation_structure nested_target_rows"

lemma nested_generation_rows_injective:
  "nested_generation_rows G=nested_generation_rows H \<longleftrightarrow> G=H"
  by (simp only: nested_generation_rows_def
      generation_identity_map_injective[OF nested_target_rows_injective])

definition nested_generation_member where
  "nested_generation_member row=(fst row,nested_generation_rows (snd row))"

lemma nested_generation_member_injective:
  "nested_generation_member x=nested_generation_member y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: nested_generation_member_def nested_generation_rows_injective)

definition nested_placed_artifact where
  "nested_placed_artifact row=(fst row,finite_artifact_rows (snd row))"

lemma nested_placed_artifact_injective:
  "nested_placed_artifact x=nested_placed_artifact y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: nested_placed_artifact_def finite_artifact_rows_injective)

definition nested_environment_rows where
  "nested_environment_rows E=(fimage nested_placed_artifact (finite_environment_artifacts E),
    finite_environment_bindings E,finite_artifact_environment.more E)"

lemma nested_environment_rows_injective:
  "nested_environment_rows E=nested_environment_rows F \<longleftrightarrow> E=F"
proof -
  have injective: "inj nested_placed_artifact"
    by (auto simp: inj_def nested_placed_artifact_injective)
  show ?thesis by (cases E; cases F)
    (simp add: nested_environment_rows_def fset_image_equality[OF injective])
qed

text \<open>Complete canonical artifact fields remain nested values. Placed
  artifacts retain their uses, environments retain every binding, targets
  retain whole-versus-anchor distinctions, and generations retain all four
  fields recursively. No flattening into a framed word is needed for these
  injective maps. Count multiplicities and malformed values remain present.\<close>

end
