theory Ordered_Complete_Artifacts
  imports Factor_Executable_Artifact_Values
begin

datatype ordered_complete_artifact = Ordered_Complete_Artifact finite_exact_artifact

fun ordered_complete_artifact_rows where
  "ordered_complete_artifact_rows (Ordered_Complete_Artifact R)=finite_artifact_rows R"

fun unordered_complete_artifact where
  "unordered_complete_artifact (Ordered_Complete_Artifact R)=R"

lemma ordered_complete_artifact_rows_injective:
  "ordered_complete_artifact_rows x=ordered_complete_artifact_rows y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: finite_artifact_rows_injective)

lemma unordered_complete_artifact_rows [simp]:
  "finite_artifact_rows (unordered_complete_artifact x)=ordered_complete_artifact_rows x"
  by (cases x) simp

instantiation ordered_complete_artifact :: linorder
begin

definition "x\<le>y \<longleftrightarrow> ordered_complete_artifact_rows x\<le>ordered_complete_artifact_rows y"
definition "x<y \<longleftrightarrow> ordered_complete_artifact_rows x<ordered_complete_artifact_rows y"

instance
  by standard
    (auto simp: less_eq_ordered_complete_artifact_def less_ordered_complete_artifact_def
      less_le_not_le ordered_complete_artifact_rows_injective
      intro: order_trans dest: order_antisym)

end

text \<open>The wrapper retains the original complete artifact. Its order is
  exactly the existing complete canonical-row order; equality requires no
  formation or word bound and preserves every counted occurrence.\<close>

end
