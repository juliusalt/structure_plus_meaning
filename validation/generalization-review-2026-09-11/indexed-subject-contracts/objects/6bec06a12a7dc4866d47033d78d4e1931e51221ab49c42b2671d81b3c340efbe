theory Factor_Replay_Coverage
  imports Factor_Replay_Slot_Reading
begin

section \<open>Every supplied key is checked in one shared context\<close>

abbreviation replay_source_list_result :: "factor_term \<Rightarrow> bool" where
  "replay_source_list_result z \<equiv> \<exists>c xs. z=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. replay_source_reading_result (Pair_Term c x))"


definition replay_source_list_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_source_list_system=add_view_definition replay_slot_reading_system 108 data_x (context_list_clauses 106 108)"

lemma replay_source_list_system_formed [simp]: "schema_system_formed replay_source_list_system"
  unfolding replay_source_list_system_def
  by (rule add_recursive_definition_formed[OF replay_slot_reading_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma replay_source_list_definitions [simp]:
  "system_definitions replay_source_list_system=insert 108 (system_definitions replay_slot_reading_system)"
  by (simp add: replay_source_list_system_def)

lemma replay_source_list_call:
  "schema_call_formed replay_source_list_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_source_list_system \<and> term_formed t"
  using added_variable_calls[OF replay_slot_reading_system_formed
    replay_source_list_system_formed[unfolded replay_source_list_system_def] replay_slot_reading_call]
  by (simp only: replay_source_list_system_def[symmetric])

lemma replay_source_list_old_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning replay_source_list_system \<longleftrightarrow> (d,t)\<in>positive_meaning replay_slot_reading_system"
  using added_definition_preserves_old(2)[OF replay_slot_reading_system_formed
    replay_source_list_system_formed[unfolded replay_source_list_system_def], of d t] assms
  by (auto simp: replay_source_list_system_def)

lemma replay_source_list_clause [simp]:
  "((108,c),S)\<in>system_clauses replay_source_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 106 108)"
proof -
  have owned: "((d,c),S)\<in>system_clauses replay_slot_reading_system \<Longrightarrow>
    d\<in>system_definitions replay_slot_reading_system" for d c S
    using replay_slot_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((108,c),S)\<notin>system_clauses replay_slot_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: replay_source_list_system_def)
qed

lemma replay_source_list_element:
  "(106,t)\<in>positive_meaning replay_source_list_system \<longleftrightarrow>
    (106,t)\<in>positive_meaning replay_source_reading_system"
  using replay_source_list_old_meaning[of 106 t] replay_slot_reading_old_meaning[of 106 t] by auto

interpretation replay_source_list_profile: context_list_profile replay_source_list_system 106 108
  by (rule context_list_profile.intro) (auto simp: replay_source_list_call)

theorem replay_source_list_exact:
  "(108,z)\<in>positive_meaning replay_source_list_system \<longleftrightarrow> replay_source_list_result z"
  by (simp only: replay_source_list_profile.exact replay_source_list_element replay_source_reading_exact)

corollary replay_source_list_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(108,Pair_Term (replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au)
    (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) (data_list_term xs))\<in>positive_meaning replay_source_list_system
    \<longleftrightarrow> (\<forall>x\<in>set xs. \<exists>v. x=use_data_term v \<and> v\<in>native_replay_sources E pu pr au G\<union>rel_ran (environment_bindings E))"
  by (simp only: replay_source_list_profile.lists replay_source_list_element
    replay_source_reading_at_reads[OF source package app graph] replay_context_formed[OF source package app graph]; simp)

abbreviation replay_slot_list_result :: "factor_term \<Rightarrow> bool" where
  "replay_slot_list_result z \<equiv> \<exists>c xs. z=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. replay_slot_reading_result (Pair_Term c x))"


definition replay_slot_list_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_slot_list_system=add_view_definition replay_source_list_system 109 data_x (context_list_clauses 107 109)"

lemma replay_slot_list_system_formed [simp]: "schema_system_formed replay_slot_list_system"
  unfolding replay_slot_list_system_def
  by (rule add_recursive_definition_formed[OF replay_source_list_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma replay_slot_list_definitions [simp]:
  "system_definitions replay_slot_list_system=insert 109 (system_definitions replay_source_list_system)"
  by (simp add: replay_slot_list_system_def)

lemma replay_slot_list_call:
  "schema_call_formed replay_slot_list_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_slot_list_system \<and> term_formed t"
  using added_variable_calls[OF replay_source_list_system_formed
    replay_slot_list_system_formed[unfolded replay_slot_list_system_def] replay_source_list_call]
  by (simp only: replay_slot_list_system_def[symmetric])

lemma replay_slot_list_old_meaning:
  assumes "d\<in>system_definitions replay_source_list_system"
  shows "(d,t)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow> (d,t)\<in>positive_meaning replay_source_list_system"
  using added_definition_preserves_old(2)[OF replay_source_list_system_formed
    replay_slot_list_system_formed[unfolded replay_slot_list_system_def], of d t] assms
  by (auto simp: replay_slot_list_system_def)

lemma replay_slot_list_clause [simp]:
  "((109,c),S)\<in>system_clauses replay_slot_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 107 109)"
proof -
  have owned: "((d,c),S)\<in>system_clauses replay_source_list_system \<Longrightarrow>
    d\<in>system_definitions replay_source_list_system" for d c S
    using replay_source_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((109,c),S)\<notin>system_clauses replay_source_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: replay_slot_list_system_def)
qed

lemma replay_slot_list_element:
  "(107,t)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow>
    (107,t)\<in>positive_meaning replay_slot_reading_system"
  using replay_slot_list_old_meaning[of 107 t] replay_source_list_old_meaning[of 107 t] by auto

interpretation replay_slot_list_profile: context_list_profile replay_slot_list_system 107 109
  by (rule context_list_profile.intro) (auto simp: replay_slot_list_call)

theorem replay_slot_list_exact:
  "(109,z)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow> replay_slot_list_result z"
  by (simp only: replay_slot_list_profile.exact replay_slot_list_element replay_slot_reading_exact)

corollary replay_slot_list_at_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "(109,Pair_Term (replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au)
    (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) (data_list_term xs))\<in>positive_meaning replay_slot_list_system
    \<longleftrightarrow> (\<forall>x\<in>set xs. \<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and>
      (u,k)\<in>native_replay_demands E pu pr au ar G)"
  by (simp only: replay_slot_list_profile.lists replay_slot_list_element
    replay_slot_reading_at_reads[OF source package app graph] replay_context_formed[OF source package app graph]; simp)

lemma replay_lists_previous_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_slot_reading_system"
  using replay_slot_list_old_meaning[of d t] replay_source_list_old_meaning[OF assms, of t] assms by auto

lemma replay_stored_coverage:
  assumes source: "environment_value_presents E (Pair_Term a b)" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
    and artifact_keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    and binding_keys: "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
  shows "((108,Pair_Term (replay_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)
      (use_data_term au) (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) us)\<in>positive_meaning replay_source_list_system \<and>
    (109,Pair_Term (replay_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)
      (use_data_term au) (Payload_Term ar) (use_data_term ru) (Payload_Term rr)) ks)\<in>positive_meaning replay_slot_list_system)
    \<longleftrightarrow> environment_closed E {pu,au,ru} (native_replay_demands E pu pr au ar G)"
proof -
  obtain xs where uses: "us=data_list_term xs" "set xs=image use_data_term (environment_uses E)"
    using environment_artifact_keys[OF source artifact_keys] by blast
  obtain ys where slots: "ks=data_list_term ys" "set ys=image definition_site_value (rel_dom (environment_bindings E))"
    using environment_binding_keys[OF source binding_keys] by blast
  have closed: "environment_closed E {pu,au,ru} (native_replay_demands E pu pr au ar G) \<longleftrightarrow>
    rel_dom (environment_bindings E)\<subseteq>native_replay_demands E pu pr au ar G \<and>
    environment_uses E\<subseteq>native_replay_sources E pu pr au G\<union>rel_ran (environment_bindings E)"
    using native_replay_closed_coverage[OF package app graph] by simp
  show ?thesis
    by (simp only: uses(1) slots(1) replay_source_list_at_reads[OF source package app graph]
      replay_slot_list_at_reads[OF source package app graph] closed
      fst_conv uses(2) slots(2))
      (auto simp: site_data_term_def inj_eq[OF use_data_term_injective] subset_iff)
qed

corollary replay_source_list_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(108,Pair_Term (replay_context_term e pu pr au ar ru rr) xs)\<in>positive_meaning replay_source_list_system \<longleftrightarrow>
    (108,Pair_Term (replay_context_term f pu pr au ar ru rr) xs)\<in>positive_meaning replay_source_list_system"
proof -
  have lists: "(108,Pair_Term c xs)\<in>positive_meaning replay_source_list_system \<longleftrightarrow>
    (\<exists>ys. xs=data_list_term ys \<and> term_formed c \<and>
      (\<forall>x\<in>set ys. (106,Pair_Term c x)\<in>positive_meaning replay_source_reading_system))" for c
    by (simp only: replay_source_list_profile.exact factor_term.inject replay_source_list_element; blast)
  have formed: "term_formed (replay_context_term e pu pr au ar ru rr) \<longleftrightarrow>
    term_formed (replay_context_term f pu pr au ar ru rr)"
    using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)] by auto
  show ?thesis by (simp only: lists formed replay_source_reading_presentation_invariance[OF assms])
qed

corollary replay_slot_list_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(109,Pair_Term (replay_context_term e pu pr au ar ru rr) xs)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow>
    (109,Pair_Term (replay_context_term f pu pr au ar ru rr) xs)\<in>positive_meaning replay_slot_list_system"
proof -
  have lists: "(109,Pair_Term c xs)\<in>positive_meaning replay_slot_list_system \<longleftrightarrow>
    (\<exists>ys. xs=data_list_term ys \<and> term_formed c \<and>
      (\<forall>x\<in>set ys. (107,Pair_Term c x)\<in>positive_meaning replay_slot_reading_system))" for c
    by (simp only: replay_slot_list_profile.exact factor_term.inject replay_slot_list_element; blast)
  have formed: "term_formed (replay_context_term e pu pr au ar ru rr) \<longleftrightarrow>
    term_formed (replay_context_term f pu pr au ar ru rr)"
    using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)] by auto
  show ?thesis by (simp only: lists formed replay_slot_reading_presentation_invariance[OF assms])
qed

text \<open>
  Both ordinary list profiles inspect every element and the final boundary.
  With the actual environment's complete key projections, they characterize
  exactly closed retention for the three native readings. A chosen sublist
  cannot replace either stored list. List order does not select a different
  retention boundary.
\<close>

end
