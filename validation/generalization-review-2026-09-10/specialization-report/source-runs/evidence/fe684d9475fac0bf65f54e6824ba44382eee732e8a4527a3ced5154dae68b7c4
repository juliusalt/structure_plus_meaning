theory Factor_Observation_Scope_Contracts
  imports Factor_Observation_Scope_Admission
begin

section \<open>One native input admits exactly the complete scoped presentation class\<close>

theorem observation_scope_admitted_class:
  "(311,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    (\<exists>z. observation_scope_presents z t)"
  by (simp only: observation_scope_presented presented_predicate_def; blast)

theorem observation_scope_complete_quotation:
  assumes "(311,t)\<in>positive_meaning observation_scope_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  obtain C U F rows where data: "data_elements C" "data_elements U" "data_elements F" "observation_rows_data rows"
    and shape: "t=observation_scope_argument (data_list_term C) (data_list_term U) (data_list_term F)
      (data_list_term (map observation_row_term rows))"
    by (rule observation_scope_input[OF assms]) blast
  have formed: "term_formed t" "self_contained_term t"
    using data by (auto simp: shape data_list_term_formed data_list_term_self_contained split: prod.splits)
  show ?thesis using complete_data_quotation_total[OF formed] by blast
qed

theorem native_observation_scope:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {311::nat} \<and>
    (\<forall>d\<in>{311}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (\<exists>z. observation_scope_presents z t)) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{311}\<subseteq>system_definitions observation_scope_system" by auto
  have calls: "schema_call_formed observation_scope_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{311}" for d t using observation_scope_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
      (\<exists>z. observation_scope_presents z t)" if "d\<in>{311}" for d t
    using that by (simp only: singleton_iff observation_scope_admitted_class; blast)
  show ?thesis by (rule compiled_exact_operations[OF observation_scope_system_formed selected calls result])
qed

text \<open>
  The native predicate preserves and reflects the independently stated scope
  domain at every presentation of the complete input record. Accepted inputs
  have full data quotations. One closed package is fixed before all future
  arguments; each application retains its actual input and original package.

  This operation checks candidate and facet declarations, the selection, and
  every observation row. The comparison relation, investigation result, and
  mathematical evidence are further boundaries with their own obligations.
\<close>

end
