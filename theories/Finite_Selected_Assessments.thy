theory Finite_Selected_Assessments
  imports Finite_Assessed_Investigation Finite_Singleton_Selection
begin

lemma singleton_adequate_conditions:
  assumes chosen: "list_singleton_option (subject_investigation_adequate cs fs ws observe)=Some c"
  shows "c\<in>set cs" "w\<in>set ws \<Longrightarrow> f\<in>set fs \<Longrightarrow> observe c w f"
proof -
  have member: "c\<in>set (subject_investigation_adequate cs fs ws observe)"
    using chosen by (simp only: list_singleton_option_some; blast)
  show "c\<in>set cs" "w\<in>set ws \<Longrightarrow> f\<in>set fs \<Longrightarrow> observe c w f"
    using member by (auto simp: subject_investigation_adequate_def)
qed

text \<open>
  A unique adequate index inherits every original computed condition. Absence
  and ambiguity remain None; no empty scope or manually chosen index replaces
  either result. Each subject use still supplies its observation equation.
\<close>

end
