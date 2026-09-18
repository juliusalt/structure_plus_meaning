theory Admitted_Conditional_Applications
  imports Conditional_Application_Review
begin

definition admitted_conditional_applications where
  "admitted_conditional_applications methods facets S q obs report = map_option
    (\<lambda>m. conditional_application_run m S q obs)
    (native_admitted_choice methods (faceted_native_question methods facets
      (conditional_application_observation S q obs)) report)"

theorem admitted_conditional_applications_original:
  assumes result: "admitted_conditional_applications methods facets S q obs report=Some A"
    and requested: "Requested_Result\<in>set facets" and original: "Original_Rule\<in>set facets"
  shows "A\<noteq>{||}"
    "(t,V,H) |\<in>| A \<Longrightarrow> t=q"
    "(t,V,H) |\<in>| A \<Longrightarrow> finite_schema_instance S V t H"
    "(t,V,H) |\<in>| A \<Longrightarrow> finite_schema_material_satisfied S V"
proof -
  obtain m where choice: "native_admitted_choice methods (faceted_native_question methods facets
      (conditional_application_observation S q obs)) report=Some m"
    and actual: "A=conditional_application_run m S q obs"
    using result by (auto simp: admitted_conditional_applications_def split: option.splits)
  have head: "conditional_application_observation S q obs m Requested_Result"
    by (rule faceted_native_choice[OF choice requested])
  have rule: "conditional_application_observation S q obs m Original_Rule"
    by (rule faceted_native_choice[OF choice original])
  have wanted: "A\<noteq>{||} \<and> fBall A (\<lambda>(t,V,H). t=q)"
    using head by (simp only: actual conditional_application_observation.simps Let_def; blast)
  have checked: "fBall A (\<lambda>(t,V,H). finite_schema_instance S V t H \<and>
    finite_schema_material_satisfied S V)"
    using rule by (simp only: actual conditional_application_observation.simps; blast)
  show "A\<noteq>{||}" using wanted by blast
  show "(t,V,H) |\<in>| A \<Longrightarrow> t=q"
    using wanted by (auto simp: Ball_def; blast)
  show "(t,V,H) |\<in>| A \<Longrightarrow> finite_schema_instance S V t H"
    using checked by (auto simp: Ball_def; blast)
  show "(t,V,H) |\<in>| A \<Longrightarrow> finite_schema_material_satisfied S V"
    using checked by (auto simp: Ball_def; blast)
qed

lemma original_application_preserves_sockets:
  "finite_schema_instance S V t H \<Longrightarrow>
    fimage fst H=fimage fst (finite_schema_premises S)"
  by (simp add: finite_schema_instance_def finite_schema_premise_instance_def)

text \<open>The admitted method itself produces the applications. Success
  retains the original requested head and every original premise socket.
  This reusable result supplies conditional applications, not proofs for their
  calls. A nonempty output does not discharge any ordinary premise.\<close>

end
