theory Factor_Observation_Table_Native
  imports Factor_Observation_Table_Contracts
begin

section \<open>The complete admitted input and output have native data quotations\<close>

theorem observation_tables_complete_quotation:
  assumes entry: "d\<in>{330,335}" and run: "(d,t)\<in>positive_meaning observation_table_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  obtain p q w where parts: "t=Pair_Term p q"
    "(311,p)\<in>positive_meaning observation_scope_system"
    "(317,Pair_Term w q)\<in>positive_meaning keyed_set_system"
    using entry run
    by (auto simp only: insert_iff singleton_iff observation_table_profile_comparison.exact
      observation_table_loss_comparison.exact observation_table_profile_admitted.at_input
      observation_table_loss_admitted.at_input observation_table_components)
  have first: "complete_data_quoted_at (term_syntax p) [] p"
    by (rule observation_scope_complete_quotation[OF parts(2)])
  have second: "complete_data_quoted_at (term_syntax (Pair_Term w q)) [] (Pair_Term w q)"
    by (rule keyed_sets_complete_quotation[OF parts(3)])
  have data: "term_formed t" "self_contained_term t"
    using complete_data_quotation_formed[OF first] complete_data_quotation_formed[OF second]
    by (auto simp only: parts(1) term_formed.simps self_contained_term.simps)
  show ?thesis using complete_data_quotation_total[OF data] by blast
qed

section \<open>One fixed native package provides both complete table operations\<close>

theorem native_observation_tables:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {330::nat,335} \<and>
    (\<forall>d\<in>{330,335}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (if d=330 then observation_profile_table_result t else observation_loss_table_result t)) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{330,335}\<subseteq>system_definitions observation_table_system" by auto
  have calls: "schema_call_formed observation_table_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{330,335}" for d t using observation_table_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning observation_table_system \<longleftrightarrow>
      (if d=330 then observation_profile_table_result t else observation_loss_table_result t)"
    if "d\<in>{330,335}" for d t using that observation_profile_table_exact[of t] observation_loss_table_exact[of t] by auto
  show ?thesis by (rule compiled_exact_operations[OF observation_table_system_formed selected calls result])
qed

text \<open>
  The two complete table operations share one fixed closed native package
  before any future operand is supplied. Each application preserves that
  package, its artifacts, and its bindings. The admitted query and result
  have complete data quotations. These mathematical contracts are checked
  in Isabelle; a native checker of those mathematical proofs remains a
  separate part of the self-contained system.
\<close>

end
