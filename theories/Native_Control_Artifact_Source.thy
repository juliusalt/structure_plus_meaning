theory Native_Control_Artifact_Source
  imports Native_Control_Artifact_Comparison Native_Control_Quoted_Judgment
begin

locale admitted_judgment_artifacts =
  fixes report rows i d F u P
  assumes installed: "judgment_bridge_install report=Some rows"
    and selected: "(i,Some (d,F,u))\<in>set rows"
    and package: "native_package_at (decode_finite_environment F) u [] P"
begin

abbreviation bridge where "bridge \<equiv> judgment_bridge_candidates!i"

lemma original_fields:
  obtains Q accepted where "judgment_bridge_question ()=Some Q"
    "native_development_admission Q report=Some accepted"
    "i<length judgment_bridge_candidates"
    "finite_path (first_occurrence_key judgment_bridge_candidates bridge)\<in>set accepted"
    "judgment_bridge_source bridge=Some (d,F,u)"
  by (rule judgment_bridge_install_fields[OF installed selected]) (rule that; assumption)

lemma body_source: "judgment_bridge_source bridge=Some (d,F,u)"
  by (rule original_fields) assumption

lemma body_condition: "judgment_bridge_condition bridge syntax_judgment_cases"
proof (rule original_fields)
  fix Q accepted
  assume question: "judgment_bridge_question ()=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and inside: "i<length judgment_bridge_candidates"
    and path: "finite_path (first_occurrence_key judgment_bridge_candidates bridge)\<in>set accepted"
    and source: "judgment_bridge_source bridge=Some (d,F,u)"
  show ?thesis by (rule judgment_bridge_admission[OF question admission path nth_mem[OF inside]])
qed

sublocale receiver: installed_quoted_judgment syntax_judgment_data syntax_judgment_cases
    "judgment_bridge_result bridge" d F u P
  by (rule installed_quoted_judgment.intro)
    (simp_all add: body_source[unfolded judgment_bridge_source_def] package)

lemma installed_term_truth:
  "(d,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s)"
proof
  assume called: "(d,t)\<in>positive_meaning P"
  obtain s where within: "s\<in>set syntax_judgment_cases"
    and result: "judgment_bridge_result bridge s"
    and data_eq: "t=decode_finite_term (syntax_judgment_data s)"
    using called by (auto simp only: receiver.installed_body_meaning filtered_judgment_rows_def
      set_map set_filter image_iff mem_Collect_eq)
  have truth: "syntax_judgment_truth s"
    using body_condition within result unfolding judgment_bridge_condition_def by blast
  show "\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s"
    by (rule exI[of _ s], rule conjI[OF data_eq truth])
next
  assume "\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s"
  then obtain s where data_eq: "t=decode_finite_term (syntax_judgment_data s)"
    and truth: "syntax_judgment_truth s" by blast
  have within: "s\<in>set syntax_judgment_cases" by (rule syntax_truth_has_case[OF truth])
  have result: "judgment_bridge_result bridge s"
    using body_condition within truth unfolding judgment_bridge_condition_def by blast
  have row: "syntax_judgment_data s\<in>set
      (filtered_judgment_rows syntax_judgment_data syntax_judgment_cases (judgment_bridge_result bridge))"
    by (simp only: filtered_judgment_rows_def set_map; rule imageI)
      (use within result in simp)
  show "(d,t)\<in>positive_meaning P"
    by (simp only: receiver.installed_body_meaning data_eq; rule imageI[OF row])
qed

theorem whole_artifact_truth:
  "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning receiver.artifact.artifact_system
    \<longleftrightarrow> (\<exists>r s. complete_data_quoted_at R r (decode_finite_term (syntax_judgment_data s))
      \<and> syntax_judgment_truth s)"
  by (simp only: receiver.installed_artifact_meaning installed_term_truth factor_term.inject exact_target.inject; blast)

theorem exact_statement_body:
  assumes quote: "complete_data_quoted_at R r
    (decode_finite_term (syntax_judgment_data (C,syntax_proposition m)))"
  shows "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning receiver.artifact.artifact_system
    \<longleftrightarrow> C=syntax_checked_rooted_context \<and> syntax_join_refinement m"
  by (simp only: receiver.installed_artifact_body[OF quote]
    judgment_bridge_installed_truth[OF installed selected package])

corollary refuses_wrong_statement_body:
  assumes quote: "complete_data_quoted_at R r
    (decode_finite_term (syntax_judgment_data (C,syntax_proposition m)))"
    and refused: "C\<noteq>syntax_checked_rooted_context \<or> \<not>syntax_join_refinement m"
  shows "(369,Target_Term (Whole_Artifact R))\<notin>positive_meaning receiver.artifact.artifact_system"
  using refused by (simp only: exact_statement_body[OF quote]; blast)

corollary refuses_unquoted_material:
  assumes "\<And>r t. \<not>complete_data_quoted_at R r t"
  shows "(369,Target_Term (Whole_Artifact R))\<notin>positive_meaning receiver.artifact.artifact_system"
  using assms by (simp only: whole_artifact_truth; blast)

theorem original_policy_cause_truth:
  assumes injective: "inj_on g (system_definitions receiver.artifact.artifact_system)"
    and variant: "system_alpha_variant (rename_system g receiver.artifact.artifact_system) T"
    and original_policy: "native_package_at K pu pr T"
    and cause: "certified_policy_cause_at K pu pr (g 369) E gu gr G H root R"
  shows "\<exists>r s. complete_data_quoted_at R r (decode_finite_term (syntax_judgment_data s))
    \<and> syntax_judgment_truth s"
  using receiver.policy_cause_body[OF injective variant original_policy cause]
  by (simp only: installed_term_truth; blast)

text \<open>The original installed judgment report and its actual package are
  retained in this instance. The natural-coordinate guard is proved formed;
  relocation into the policy's actual native package is a separate mandatory
  premise. No conclusion asserts existence of a policy cause, authority for a
  generation, or that the two local refinements encode the owner's policy.\<close>

end

end
