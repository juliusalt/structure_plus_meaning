theory Factor_Retention_Admission
  imports Factor_Replay_Coverage
begin

section \<open>Actual roles and complete stored coverage admit retention\<close>

abbreviation retention_admission_result :: "factor_term \<Rightarrow> bool" where
  "retention_admission_result z \<equiv> \<exists>E pu pr au ar root c d t I K P G.
    z=Pair_Term c (Pair_Term (definition_site_value d) t) \<and>
    replay_value_presents E pu pr au ar root c \<and>
    native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and> native_schema_graph_at E root G \<and>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"

definition retention_admission_schema :: "(nat,nat,nat) factor_schema" where
  "retention_admission_schema=data_rule
    (Pattern_Pair (replay_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)))
    {(0,80,source_root_pattern (Pattern_Pair data_x data_y) data_z data_w),
     (1,58,application_reading_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)),
     (2,97,source_root_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 6) (Pattern_Variable 7)),
     (3,51,Pattern_Pair data_x (Pattern_Variable 12)),
     (4,51,Pattern_Pair data_y (Pattern_Variable 13)),
     (5,108,Pattern_Pair (replay_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 12)),
     (6,109,Pattern_Pair (replay_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 13))}"


definition retention_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "retention_admission_system=add_view_definition replay_slot_list_system 110 data_x {(0,retention_admission_schema)}"

lemma retention_admission_system_formed [simp]: "schema_system_formed retention_admission_system"
  unfolding retention_admission_system_def
  by (rule add_recursive_definition_formed[OF replay_slot_list_system_formed])
    (auto simp:  retention_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma retention_admission_definitions [simp]:
  "system_definitions retention_admission_system=insert 110 (system_definitions replay_slot_list_system)"
  by (simp add: retention_admission_system_def)

lemma retention_admission_call:
  "schema_call_formed retention_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions retention_admission_system \<and> term_formed t"
  using added_variable_calls[OF replay_slot_list_system_formed
    retention_admission_system_formed[unfolded retention_admission_system_def] replay_slot_list_call]
  by (simp only: retention_admission_system_def[symmetric])

lemma retention_admission_old_meaning:
  assumes "d\<in>system_definitions replay_slot_list_system"
  shows "(d,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning replay_slot_list_system"
  using added_definition_preserves_old(2)[OF replay_slot_list_system_formed
    retention_admission_system_formed[unfolded retention_admission_system_def], of d t] assms
  by (auto simp: retention_admission_system_def)

lemma retention_admission_clause [simp]:
  "((110,c),S)\<in>system_clauses retention_admission_system \<longleftrightarrow> (c,S)\<in>{(0,retention_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses replay_slot_list_system \<Longrightarrow>
    d\<in>system_definitions replay_slot_list_system" for d c S
    using replay_slot_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((110,c),S)\<notin>system_clauses replay_slot_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: retention_admission_system_def)
qed

lemma retention_admission_slot_meaning:
  assumes "d\<in>system_definitions replay_slot_reading_system"
  shows "(d,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_slot_reading_system"
  using retention_admission_old_meaning[of d t] replay_lists_previous_meaning[OF assms, of t] assms by auto

lemma retention_admission_components:
  "(80,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (80,t)\<in>positive_meaning package_admission_system"
  "(58,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (58,t)\<in>positive_meaning application_reading_system"
  "(97,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (97,t)\<in>positive_meaning proof_graph_admission_system"
  "(51,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(108,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (108,t)\<in>positive_meaning replay_source_list_system"
  "(109,t)\<in>positive_meaning retention_admission_system \<longleftrightarrow> (109,t)\<in>positive_meaning replay_slot_list_system"
  using retention_admission_slot_meaning[of 80 t] replay_slot_reading_old_meaning[of 80 t]
    replay_source_reading_graph_meaning[of 80 t] proof_graph_membership_node_meaning[of 80 t]
    proof_node_reading_base_meaning[of 80 t] admitted_instantiation_previous_meaning[of 80 t]
    retention_admission_slot_meaning[of 58 t] replay_slot_reading_components(7)[of t]
    retention_admission_slot_meaning[of 97 t] replay_slot_reading_old_meaning[of 97 t]
    replay_source_reading_graph_meaning[of 97 t] proof_graph_membership_old_meaning[of 97 t]
    retention_admission_slot_meaning[of 51 t] replay_slot_reading_pattern_meaning[of 51 t]
    pattern_instantiation_old_meaning[of 51 t] binder_admission_old_meaning[of 51 t]
    diagonal_rows_old_meaning[of 51 t] binding_admission_old_meaning[of 51 t]
    retention_admission_old_meaning[of 108 t] replay_slot_list_old_meaning[of 108 t]
    retention_admission_old_meaning[of 109 t] by auto

lemma retention_admission_step:
  assumes read:
    "(80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system"
    "(58,application_reading_argument (Pair_Term a b) au ar d t i slots)\<in>positive_meaning application_reading_system"
    "(97,source_root_argument (Pair_Term a b) ru rr)\<in>positive_meaning proof_graph_admission_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(108,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) us)\<in>positive_meaning replay_source_list_system"
    "(109,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) ks)\<in>positive_meaning replay_slot_list_system"
  shows "(110,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) (Pair_Term d t))\<in>positive_meaning retention_admission_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then a else if j=1 then b else if j=2 then pu else if j=3 then pr else if j=4 then au else if j=5 then ar else if j=6 then ru else if j=7 then rr else if j=8 then d else if j=9 then t else if j=10 then i else if j=11 then slots else if j=12 then us else ks"
  have result: "(110,evaluate_pattern ?h (schema_conclusion retention_admission_schema))\<in>positive_meaning retention_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use read schema_call_formed_target[OF positive_meaning_formed[OF read(1)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(3)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(4)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(5)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(6)]]
        schema_call_formed_target[OF positive_meaning_formed[OF read(7)]] in
        \<open>auto simp: retention_admission_schema_def schema_variables_def retention_admission_call retention_admission_components\<close>)
  show ?thesis using result by (simp add: retention_admission_schema_def)
qed

lemma retention_admission_fields:
  "(110,z)\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    (\<exists>a b pu pr au ar ru rr d t i slots us ks. z=Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) (Pair_Term d t) \<and>
      (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
      (58,application_reading_argument (Pair_Term a b) au ar d t i slots)\<in>positive_meaning application_reading_system \<and>
      (97,source_root_argument (Pair_Term a b) ru rr)\<in>positive_meaning proof_graph_admission_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (108,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) us)\<in>positive_meaning replay_source_list_system \<and>
      (109,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) ks)\<in>positive_meaning replay_slot_list_system)"
proof
  assume holds: "(110,z)\<in>positive_meaning retention_admission_system"
  have ordinary: "schema_material_premises S={}" if "((110,c),S)\<in>system_clauses retention_admission_system" for c S
    using that by (auto simp: retention_admission_schema_def)
  have valuation: "(110,z)\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    (\<exists>c S f. ((110,c),S)\<in>system_clauses retention_admission_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion S) \<and>
      schema_call_formed retention_admission_system 110 z \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning retention_admission_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S h where clause: "((110,c),S)\<in>system_clauses retention_admission_system"
    and shape: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning retention_admission_system"
    using iffD1[OF valuation holds] by blast
  have schema: "S=retention_admission_schema" using clause by simp
  have read_0: "(80,source_root_argument (Pair_Term (h 0) (h 1)) (h 2) (h 3))\<in>positive_meaning package_admission_system"
    using support[rule_format, of 0 80 "source_root_pattern (Pattern_Pair data_x data_y) data_z data_w"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_1: "(58,application_reading_argument (Pair_Term (h 0) (h 1)) (h 4) (h 5) (h 8) (h 9) (h 10) (h 11))\<in>positive_meaning application_reading_system"
    using support[rule_format, of 1 58 "application_reading_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_2: "(97,source_root_argument (Pair_Term (h 0) (h 1)) (h 6) (h 7))\<in>positive_meaning proof_graph_admission_system"
    using support[rule_format, of 2 97 "source_root_pattern (Pattern_Pair data_x data_y) (Pattern_Variable 6) (Pattern_Variable 7)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_3: "(51,Pair_Term (h 0) (h 12))\<in>positive_meaning row_keys_system"
    using support[rule_format, of 3 51 "Pattern_Pair data_x (Pattern_Variable 12)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_4: "(51,Pair_Term (h 1) (h 13))\<in>positive_meaning row_keys_system"
    using support[rule_format, of 4 51 "Pattern_Pair data_y (Pattern_Variable 13)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_5: "(108,Pair_Term (replay_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)) (h 12))\<in>positive_meaning replay_source_list_system"
    using support[rule_format, of 5 108 "Pattern_Pair (replay_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 12)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have read_6: "(109,Pair_Term (replay_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)) (h 13))\<in>positive_meaning replay_slot_list_system"
    using support[rule_format, of 6 109 "Pattern_Pair (replay_context_pattern (Pattern_Pair data_x data_y) data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7)) (Pattern_Variable 13)"]
    by (simp add: schema retention_admission_schema_def retention_admission_components)
  have encoded: "z=Pair_Term (replay_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3)
    (h 4) (h 5) (h 6) (h 7)) (Pair_Term (h 8) (h 9))"
    using shape by (simp add: schema retention_admission_schema_def)
  show "\<exists>a b pu pr au ar ru rr d t i slots us ks. z=Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) (Pair_Term d t) \<and>
    (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
    (58,application_reading_argument (Pair_Term a b) au ar d t i slots)\<in>positive_meaning application_reading_system \<and>
    (97,source_root_argument (Pair_Term a b) ru rr)\<in>positive_meaning proof_graph_admission_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (108,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) us)\<in>positive_meaning replay_source_list_system \<and>
    (109,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) ks)\<in>positive_meaning replay_slot_list_system"
    by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"], rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"], rule exI[of _ "h 6"], rule exI[of _ "h 7"], rule exI[of _ "h 8"], rule exI[of _ "h 9"], rule exI[of _ "h 10"], rule exI[of _ "h 11"], rule exI[of _ "h 12"], rule exI[of _ "h 13"])
      (use encoded read_0 read_1 read_2 read_3 read_4 read_5 read_6 in blast)
next
  assume "\<exists>a b pu pr au ar ru rr d t i slots us ks. z=Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) (Pair_Term d t) \<and>
    (80,source_root_argument (Pair_Term a b) pu pr)\<in>positive_meaning package_admission_system \<and>
    (58,application_reading_argument (Pair_Term a b) au ar d t i slots)\<in>positive_meaning application_reading_system \<and>
    (97,source_root_argument (Pair_Term a b) ru rr)\<in>positive_meaning proof_graph_admission_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (108,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) us)\<in>positive_meaning replay_source_list_system \<and>
    (109,Pair_Term (replay_context_term (Pair_Term a b) pu pr au ar ru rr) ks)\<in>positive_meaning replay_slot_list_system"
  then show "(110,z)\<in>positive_meaning retention_admission_system" by (blast intro: retention_admission_step)
qed

theorem retention_admission_sound:
  assumes holds: "(110,z)\<in>positive_meaning retention_admission_system"
  shows "retention_admission_result z"
proof -
  obtain a b p q v w n r d t i slots us ks where shape:
    "z=Pair_Term (replay_context_term (Pair_Term a b) p q v w n r) (Pair_Term d t)"
    and calls: "(80,source_root_argument (Pair_Term a b) p q)\<in>positive_meaning package_admission_system"
    "(58,application_reading_argument (Pair_Term a b) v w d t i slots)\<in>positive_meaning application_reading_system"
    "(97,source_root_argument (Pair_Term a b) n r)\<in>positive_meaning proof_graph_admission_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system" "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(108,Pair_Term (replay_context_term (Pair_Term a b) p q v w n r) us)\<in>positive_meaning replay_source_list_system"
    "(109,Pair_Term (replay_context_term (Pair_Term a b) p q v w n r) ks)\<in>positive_meaning replay_slot_list_system"
    using holds by (simp only: retention_admission_fields) blast
  obtain E pu pr P where source: "environment_value_presents E (Pair_Term a b)" and program:
    "p=use_data_term pu" "q=Payload_Term pr" "native_package_at E pu pr P"
    using calls(1) by (simp only: package_admission_exact factor_term.inject) blast
  obtain au ar du dr Is Ks where app:
    "v=use_data_term au" "w=Payload_Term ar" "d=site_data_term du dr"
    "native_application_at E au ar (du,dr) t (set Is) (set Ks)"
    using calls(2) by (simp only: application_reading_at_source[OF source]) blast
  obtain ru rr G where graph: "n=use_data_term ru" "r=Payload_Term rr" "native_schema_graph_at E (ru,rr) G"
    using calls(3) by (simp only: proof_graph_admission_at_source[OF source]) blast
  let ?c="replay_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)
    (use_data_term au) (Payload_Term ar) (use_data_term ru) (Payload_Term rr)"
  have covered: "(108,Pair_Term ?c us)\<in>positive_meaning replay_source_list_system \<and>
    (109,Pair_Term ?c ks)\<in>positive_meaning replay_slot_list_system"
    using calls(6,7) by (simp only: program(1,2) app(1,2) graph(1,2); blast)
  have closed: "environment_closed E {pu,au,ru} (native_replay_demands E pu pr au ar G)"
    by (rule iffD1[OF replay_stored_coverage[OF source program(3) app(4) graph(3) calls(4,5)] covered])
  have presented: "replay_value_presents E pu pr au ar (ru,rr) ?c"
    by (rule replay_context_presents[OF source program(3) app(4) graph(3)])
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ au], rule exI[of _ ar],
    rule exI[of _ "(ru,rr)"], rule exI[of _ ?c], rule exI[of _ "(du,dr)"], rule exI[of _ t],
    rule exI[of _ "set Is"], rule exI[of _ "set Ks"], rule exI[of _ P], rule exI[of _ G])
    (use presented program(3) app(4) graph(3) closed shape in \<open>simp add: program(1,2) app(1-3) graph(1,2)\<close>)
qed

theorem retention_admission_complete:
  assumes presented: "replay_value_presents E pu pr au ar root c"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
    and closed: "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
  shows "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system"
proof -
  obtain a b where source: "environment_value_presents E (Pair_Term a b)"
    and shape: "c=replay_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)
      (use_data_term au) (Payload_Term ar) (use_data_term (fst root)) (Payload_Term (snd root))"
    using presented by (auto simp: replay_value_presents_def judgment_value_presents_def
      environment_value_presents_def site_data_term_def)
  have program: "(80,source_root_argument (Pair_Term a b) (use_data_term pu) (Payload_Term pr))\<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source package])
  obtain i slots where call: "(58,application_reading_argument (Pair_Term a b) (use_data_term au) (Payload_Term ar)
    (definition_site_value d) t i slots)\<in>positive_meaning application_reading_system"
    using application_reading_value[OF source app] by blast
  have actual_graph: "native_schema_graph_at E (fst root,snd root) G" using graph by simp
  have proof_read: "(97,source_root_argument (Pair_Term a b) (use_data_term (fst root)) (Payload_Term (snd root)))
    \<in>positive_meaning proof_graph_admission_system" by (rule proof_graph_admission_complete[OF source actual_graph])
  obtain us ks where keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system" using environment_keys_total[OF source] by blast
  have coverage: "(108,Pair_Term c us)\<in>positive_meaning replay_source_list_system"
    "(109,Pair_Term c ks)\<in>positive_meaning replay_slot_list_system"
  proof -
    have both: "(108,Pair_Term c us)\<in>positive_meaning replay_source_list_system \<and>
      (109,Pair_Term c ks)\<in>positive_meaning replay_slot_list_system"
      by (simp only: shape replay_stored_coverage[OF source package app actual_graph keys])
        (use closed in simp)
    show "(108,Pair_Term c us)\<in>positive_meaning replay_source_list_system"
      "(109,Pair_Term c ks)\<in>positive_meaning replay_slot_list_system" using both by blast+
  qed
  show ?thesis using retention_admission_step[OF program call proof_read keys coverage[unfolded shape]]
    by (simp only: shape)
qed

theorem retention_admission_exact:
  "(110,z)\<in>positive_meaning retention_admission_system \<longleftrightarrow> retention_admission_result z"
  using retention_admission_sound retention_admission_complete by blast

corollary retention_admission_on_values:
  assumes presented: "replay_value_presents E pu pr au ar root c"
  shows "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    (\<exists>P G I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      native_schema_graph_at E root G \<and> environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G))"
proof -
  have unique: "F=E \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar \<and> other=root"
    if "replay_value_presents F qu qr bu br other c" for F qu qr bu br other
    by (rule replay_value_presents_unique[OF that presented])
  show ?thesis by (simp only: retention_admission_exact factor_term.inject definition_site_value_eq)
    (use presented unique in blast)
qed

corollary retention_admission_at_reads:
  assumes presented: "replay_value_presents E pu pr au ar root c"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
  by (simp only: retention_admission_on_values[OF presented])
    (use package app graph native_schema_graph_unique[OF _ graph] in blast)

corollary retention_admission_presentation_invariance:
  assumes "replay_value_presents E pu pr au ar root c" "replay_value_presents E pu pr au ar root b"
  shows "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system \<longleftrightarrow>
    (110,Pair_Term b (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system"
  by (simp only: retention_admission_on_values[OF assms(1)] retention_admission_on_values[OF assms(2)])

corollary retention_admission_canonical:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
    and presented: "replay_value_presents (native_replay_environment E pu pr au ar G) pu pr au ar root c"
  shows "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system"
  by (rule retention_admission_complete[OF presented native_replay_environment_recovers(1-3)[OF package app graph]
    native_replay_environment_closed[OF package app graph]])

text \<open>
  One ordinary clause admits the actual package, application, and graph, then
  projects the two complete stored key lists and checks every key. Its meaning
  is exactly closed retention with those independent readings. It also exposes
  the application's actual call for the following derivation join.

  Admission permits all complete environment presentations and shared uses.
  It does not require that the application belongs to the package, that the
  graph derives that call, or that any call is true. Those are separate roles.
  Restriction to the grammar's canonical environment always admits retention.
\<close>

end
