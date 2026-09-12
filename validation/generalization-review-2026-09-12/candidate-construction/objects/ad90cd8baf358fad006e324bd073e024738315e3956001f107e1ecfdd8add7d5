theory Factor_Keyed_Set_Contracts
  imports Factor_Keyed_Set_Clauses Factor_Data_Set_Comparison_Contracts Factor_Observation_Profiles
begin

section \<open>The unchanged components supply their complete local meanings\<close>

lemma keyed_set_components:
  "(2,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow> data_term_boundary t"
  "(219,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    (219,t)\<in>positive_meaning data_set_comparison_system"
  "(303,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    (\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and> x\<in>set xs)"
  using keyed_set_base_meaning[of 2 t] keyed_set_base_meaning[of 219 t] keyed_set_base_meaning[of 303 t]
    observation_collection_meaning[of 2 t] observation_collection_meaning[of 303 t]
    observation_collection_set_meaning[of t] observation_components(1)[of t]
    observation_member_exact[of t] observation_base_roots
  by auto

interpretation keyed_set_rows: keyed_comparison_profile keyed_set_system 2 219 312
  by (rule keyed_comparison_profile.intro[OF keyed_set_system_formed])
    (auto simp: keyed_set_clause keyed_set_clause_family_def keyed_set_call)

interpretation keyed_set_members: compared_member_profile keyed_set_system 303 312 313 315
  by (rule compared_member_profile.intro[OF keyed_set_system_formed])
    (auto simp: keyed_set_clause keyed_set_clause_family_def keyed_set_call keyed_set_components)

interpretation keyed_set_left: context_list_profile keyed_set_system 313 314
  by (rule context_list_profile.intro[OF keyed_set_system_formed])
    (auto simp: keyed_set_clause keyed_set_clause_family_def keyed_set_call)

interpretation keyed_set_right: context_list_profile keyed_set_system 315 316
  by (rule context_list_profile.intro[OF keyed_set_system_formed])
    (auto simp: keyed_set_clause keyed_set_clause_family_def keyed_set_call)

interpretation keyed_sets: related_set_profile keyed_set_system 303 312 313 315 314 316 317
  by (rule related_set_profile.intro[OF keyed_set_members.compared_member_profile_axioms
    keyed_set_left.context_list_profile_axioms keyed_set_right.context_list_profile_axioms])
    (auto simp: keyed_set_clause keyed_set_clause_family_def keyed_set_call)

section \<open>Both independent finite-set levels retain every allowed presentation\<close>

abbreviation keyed_set_row_presents where
  "keyed_set_row_presents \<equiv> factor_pair_presents data_term_presents data_finite_set_presents"

abbreviation keyed_set_row_domain where
  "keyed_set_row_domain z \<equiv> data_term_boundary (fst z) \<and> data_finite_set_domain (snd z)"

abbreviation keyed_sets_presents where
  "keyed_sets_presents \<equiv> data_list_fset_presents keyed_set_row_presents"

abbreviation keyed_sets_domain where
  "keyed_sets_domain S \<equiv> \<forall>z\<in>fset S. keyed_set_row_domain z"

abbreviation keyed_sets_admitted where
  "keyed_sets_admitted p \<equiv> \<exists>ps. (\<forall>r\<in>set ps. \<exists>z. keyed_set_row_presents z r) \<and>
    p=data_list_term ps"

lemma keyed_set_row_class:
  "presentation_class keyed_set_row_presents keyed_set_row_domain (\<lambda>p. \<exists>z. keyed_set_row_presents z p)"
  by (rule presentation_class.recovered_admission[OF factor_pair_class[OF data_term_class data_finite_set_class]])

lemma keyed_sets_class:
  "presentation_class keyed_sets_presents keyed_sets_domain keyed_sets_admitted"
  by (rule data_list_fset_presentation_class[OF keyed_set_row_class])

lemma keyed_set_row_data:
  assumes "keyed_set_row_presents z p"
  shows "data_term_boundary p"
proof -
  obtain q where fields: "data_term_boundary (fst z)" "data_finite_set_presents (snd z) q"
    "p=Pair_Term (fst z) q" using assms by (auto simp only: factor_pair_presents_def)
  have tail: "data_term_boundary q" by (rule data_finite_set_presented_data[OF fields(2)])
  show ?thesis using fields(1) tail by (simp only: fields(3) term_formed.simps self_contained_term.simps)
qed

lemma keyed_set_row_identity_contract:
  "presented_relation_contract keyed_set_row_presents keyed_set_row_domain (\<lambda>p. \<exists>z. keyed_set_row_presents z p)
    keyed_set_row_presents keyed_set_row_domain (\<lambda>p. \<exists>z. keyed_set_row_presents z p)
    (=) (\<lambda>p q. (312,Pair_Term p q)\<in>positive_meaning keyed_set_system)"
proof -
  have values_exact: "(219,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
      presented_relation data_finite_set_presents data_finite_set_presents (=) p q" for p q
    using presented_relation_contract.exact[OF data_set_comparison_finite_set_contract, of p q]
    by (simp only: keyed_set_components)
  have meaning: "(312,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
      presented_relation keyed_set_row_presents keyed_set_row_presents (=) p q" for p q
    by (auto simp: keyed_set_rows.exact keyed_set_components(1) values_exact
      presented_relation_def factor_pair_presents_def; blast)
  show ?thesis using keyed_set_row_class meaning
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem keyed_sets_identity_contract:
  "presented_relation_contract keyed_sets_presents keyed_sets_domain keyed_sets_admitted
    keyed_sets_presents keyed_sets_domain keyed_sets_admitted
    (=) (\<lambda>p q. (317,Pair_Term p q)\<in>positive_meaning keyed_set_system)"
  by (rule keyed_sets.presented_identity_contract[OF keyed_set_row_identity_contract keyed_set_row_data])

interpretation keyed_sets_contract: presented_relation_contract keyed_sets_presents keyed_sets_domain keyed_sets_admitted
  keyed_sets_presents keyed_sets_domain keyed_sets_admitted
  "(=)" "\<lambda>p q. (317,Pair_Term p q)\<in>positive_meaning keyed_set_system"
  by (rule keyed_sets_identity_contract)

corollary keyed_sets_output:
  assumes "keyed_sets_presents S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning keyed_set_system \<longleftrightarrow> keyed_sets_presents S q"
  using presented_relation_contract.at_source[OF keyed_sets_identity_contract assms, of q] by auto

theorem keyed_sets_exact:
  "(317,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
    (\<exists>S p q. t=Pair_Term p q \<and> keyed_sets_presents S p \<and> keyed_sets_presents S q)"
proof -
  have paired: "\<exists>p q. t=Pair_Term p q" if "(317,t)\<in>positive_meaning keyed_set_system"
    using that by (auto simp only: keyed_sets.exact)
  show ?thesis using paired presented_relation_contract.exact[OF keyed_sets_identity_contract]
    by (auto simp only: presented_relation_def; blast)
qed

section \<open>The compiled comparison is fixed before every future argument\<close>

theorem keyed_sets_complete_quotation:
  assumes "(317,t)\<in>positive_meaning keyed_set_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have data: "term_formed t" "self_contained_term t"
    using assms by (auto simp: keyed_sets.exact data_list_term_formed data_list_term_self_contained)
  show ?thesis using complete_data_quotation_total[OF data] by blast
qed

theorem native_keyed_sets:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {317::nat} \<and>
    (\<forall>d\<in>{317}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>S p q. t=Pair_Term p q \<and> keyed_sets_presents S p \<and> keyed_sets_presents S q)) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{317}\<subseteq>system_definitions keyed_set_system" by auto
  have calls: "schema_call_formed keyed_set_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{317}" for d t using keyed_set_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning keyed_set_system \<longleftrightarrow>
      (\<exists>S p q. t=Pair_Term p q \<and> keyed_sets_presents S p \<and> keyed_sets_presents S q)"
    if "d\<in>{317}" for d t using that keyed_sets_exact[of t] by simp
  show ?thesis by (rule compiled_exact_operations[OF keyed_set_system_formed selected calls result])
qed

text \<open>
  The independent subject is a finite set of pairs of a complete data key
  and a finite set of complete data values. A finite map condition is not
  imposed: distinct values at the same key remain distinct rows. The
  presentation class retains all outer and inner enumerations and repetitions.

  Every native clause calls the existing data, membership, or comparison
  definitions, or an earlier generic traversal constructor. Complete local
  contracts compose into identity of the two-level subject over every term.
  Observation profile graphs and directed-loss graphs are uses of this
  broader native comparison and retain their own independent domains.
\<close>

end
