theory Factor_Replay_Admission
  imports Factor_Retention_Admission Factor_Replay
begin

section \<open>The retained application's actual call is the derivation's root call\<close>

abbreviation replay_admission_result :: "factor_term \<Rightarrow> bool" where
  "replay_admission_result z \<equiv> \<exists>E pu pr au ar root c hs.
    z=Pair_Term c (positioned_call_rows_term hs) \<and> replay_value_presents E pu pr au ar root c \<and>
    distinct hs \<and> native_replay_at E pu pr au ar root (set hs)"

definition replay_admission_schema :: "(nat,nat,nat) factor_schema" where
  "replay_admission_schema=data_rule
    (Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)
      (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 7))
    {(0,110,Pattern_Pair (replay_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)
       (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))),
     (1,102,derivation_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))
       (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 7))}"


definition replay_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "replay_admission_system=add_view_definition retention_admission_system 111 data_x {(0,replay_admission_schema)}"

lemma replay_admission_system_formed [simp]: "schema_system_formed replay_admission_system"
  unfolding replay_admission_system_def
  by (rule add_recursive_definition_formed[OF retention_admission_system_formed])
    (auto simp:  replay_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma replay_admission_definitions [simp]:
  "system_definitions replay_admission_system=insert 111 (system_definitions retention_admission_system)"
  by (simp add: replay_admission_system_def)

lemma replay_admission_call:
  "schema_call_formed replay_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions replay_admission_system \<and> term_formed t"
  using added_variable_calls[OF retention_admission_system_formed
    replay_admission_system_formed[unfolded replay_admission_system_def] retention_admission_call]
  by (simp only: replay_admission_system_def[symmetric])

lemma replay_admission_old_meaning:
  assumes "d\<in>system_definitions retention_admission_system"
  shows "(d,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (d,t)\<in>positive_meaning retention_admission_system"
  using added_definition_preserves_old(2)[OF retention_admission_system_formed
    replay_admission_system_formed[unfolded replay_admission_system_def], of d t] assms
  by (auto simp: replay_admission_system_def)

lemma replay_admission_clause [simp]:
  "((111,c),S)\<in>system_clauses replay_admission_system \<longleftrightarrow> (c,S)\<in>{(0,replay_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses retention_admission_system \<Longrightarrow>
    d\<in>system_definitions retention_admission_system" for d c S
    using retention_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((111,c),S)\<notin>system_clauses retention_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: replay_admission_system_def)
qed

lemma replay_admission_components:
  "(110,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (110,t)\<in>positive_meaning retention_admission_system"
  "(102,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (102,t)\<in>positive_meaning derivation_admission_system"
  using replay_admission_old_meaning[of 110 t] replay_admission_old_meaning[of 102 t]
    retention_admission_slot_meaning[of 102 t] replay_slot_reading_old_meaning[of 102 t]
    replay_source_reading_old_meaning[of 102 t] definition_slot_reading_old_meaning[of 102 t]
    schema_slot_reading_old_meaning[of 102 t] premise_slot_reading_old_meaning[of 102 t] by auto

lemma replay_admission_step:
  assumes retention: "(110,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term d t))
      \<in>positive_meaning retention_admission_system"
    and derivation: "(102,derivation_argument e pu pr (Pair_Term ru rr) d t h)\<in>positive_meaning derivation_admission_system"
  shows "(111,Pair_Term (replay_context_term e pu pr au ar ru rr) h)\<in>positive_meaning replay_admission_system"
proof -
  let ?f="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au
    else if j=4 then ar else if j=5 then ru else if j=6 then rr else if j=7 then h else if j=8 then d else t"
  have result: "(111,evaluate_pattern ?f (schema_conclusion replay_admission_schema))\<in>positive_meaning replay_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use retention derivation schema_call_formed_target[OF positive_meaning_formed[OF retention]]
        schema_call_formed_target[OF positive_meaning_formed[OF derivation]] in
        \<open>auto simp: replay_admission_schema_def schema_variables_def replay_admission_call replay_admission_components\<close>)
  show ?thesis using result by (simp add: replay_admission_schema_def)
qed

lemma replay_admission_fields:
  "(111,z)\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    (\<exists>e pu pr au ar ru rr h d t. z=Pair_Term (replay_context_term e pu pr au ar ru rr) h \<and>
      (110,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term d t))\<in>positive_meaning retention_admission_system \<and>
      (102,derivation_argument e pu pr (Pair_Term ru rr) d t h)\<in>positive_meaning derivation_admission_system)"
proof
  assume holds: "(111,z)\<in>positive_meaning replay_admission_system"
  have ordinary: "schema_material_premises S={}" if "((111,c),S)\<in>system_clauses replay_admission_system" for c S
    using that by (auto simp: replay_admission_schema_def)
  have valuation: "(111,z)\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    (\<exists>c S f. ((111,c),S)\<in>system_clauses replay_admission_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and> z=evaluate_pattern f (schema_conclusion S) \<and>
      schema_call_formed replay_admission_system 111 z \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning replay_admission_system))"
    by (rule ordinary_positive_entry_valuation) (rule ordinary; assumption)
  obtain c S f where clause: "((111,c),S)\<in>system_clauses replay_admission_system"
    and shape: "z=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning replay_admission_system"
    using iffD1[OF valuation holds] by blast
  have schema: "S=replay_admission_schema" using clause by simp
  have retention: "(110,Pair_Term (replay_context_term (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6))
    (Pair_Term (f 8) (f 9)))\<in>positive_meaning retention_admission_system"
    using support[rule_format, of 0 110 "Pattern_Pair (replay_context_pattern data_x data_y data_z data_w
      (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9))"]
    by (simp add: schema replay_admission_schema_def replay_admission_components)
  have derivation: "(102,derivation_argument (f 0) (f 1) (f 2) (Pair_Term (f 5) (f 6)) (f 8) (f 9) (f 7))
    \<in>positive_meaning derivation_admission_system"
    using support[rule_format, of 1 102 "derivation_pattern data_x data_y data_z
      (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)) (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 7)"]
    by (simp add: schema replay_admission_schema_def replay_admission_components)
  have encoded: "z=Pair_Term (replay_context_term (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)) (f 7)"
    using shape by (simp add: schema replay_admission_schema_def)
  show "\<exists>e pu pr au ar ru rr h d t. z=Pair_Term (replay_context_term e pu pr au ar ru rr) h \<and>
    (110,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term d t))\<in>positive_meaning retention_admission_system \<and>
    (102,derivation_argument e pu pr (Pair_Term ru rr) d t h)\<in>positive_meaning derivation_admission_system"
    by (rule exI[of _ "f 0"], rule exI[of _ "f 1"], rule exI[of _ "f 2"], rule exI[of _ "f 3"], rule exI[of _ "f 4"], rule exI[of _ "f 5"], rule exI[of _ "f 6"], rule exI[of _ "f 7"], rule exI[of _ "f 8"], rule exI[of _ "f 9"])
      (use encoded retention derivation in blast)
next
  assume "\<exists>e pu pr au ar ru rr h d t. z=Pair_Term (replay_context_term e pu pr au ar ru rr) h \<and>
    (110,Pair_Term (replay_context_term e pu pr au ar ru rr) (Pair_Term d t))\<in>positive_meaning retention_admission_system \<and>
    (102,derivation_argument e pu pr (Pair_Term ru rr) d t h)\<in>positive_meaning derivation_admission_system"
  then show "(111,z)\<in>positive_meaning replay_admission_system" by (blast intro: replay_admission_step)
qed

theorem replay_admission_sound:
  assumes holds: "(111,z)\<in>positive_meaning replay_admission_system"
  shows "replay_admission_result z"
proof -
  obtain e p q v w n r h d t where shape: "z=Pair_Term (replay_context_term e p q v w n r) h"
    and calls: "(110,Pair_Term (replay_context_term e p q v w n r) (Pair_Term d t))\<in>positive_meaning retention_admission_system"
    "(102,derivation_argument e p q (Pair_Term n r) d t h)\<in>positive_meaning derivation_admission_system"
    using holds by (simp only: replay_admission_fields) blast
  obtain E pu pr au ar root f I K P G where retained:
    "replay_value_presents E pu pr au ar root (replay_context_term e p q v w n r)"
    "d=definition_site_value f" "native_package_at E pu pr P" "native_application_at E au ar f t I K"
    "native_schema_graph_at E root G" "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
    using calls(1) by (simp only: retention_admission_exact factor_term.inject) blast
  have source: "environment_value_presents E e" and fields:
    "p=use_data_term pu" "q=Payload_Term pr" "v=use_data_term au" "w=Payload_Term ar"
    "n=use_data_term (fst root)" "r=Payload_Term (snd root)"
    using retained(1) by (auto simp: replay_value_presents_def judgment_value_presents_def site_data_term_def)
  obtain hs where boundary: "h=positioned_call_rows_term hs" "distinct hs"
    and derived: "schema_graph_derives (positioned_program P) G root f t (set hs)"
    using calls(2)[unfolded fields retained(2)]
      native_package_unique[OF _ retained(3)] native_schema_graph_unique[OF _ retained(5)]
    by (simp only: derivation_admission_at_source[OF source] inj_eq[OF use_data_term_injective]
      factor_term.inject definition_site_value_eq site_data_term_def; auto)
  have replay: "native_replay_at E pu pr au ar root (set hs)"
    by (simp only: native_replay_with_reads[OF retained(3-5)]) (use derived retained(6) in blast)
  show ?thesis using shape retained(1) boundary replay by blast
qed

theorem replay_admission_complete:
  assumes presented: "replay_value_presents E pu pr au ar root c" and order: "distinct hs"
    and replay: "native_replay_at E pu pr au ar root (set hs)"
  shows "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system"
proof -
  obtain P d t I K G where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "native_schema_graph_at E root G" and derived: "schema_graph_derives (positioned_program P) G root d t (set hs)"
    and closed: "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
    using replay by (auto simp: native_replay_at_def)
  obtain e where source: "environment_value_presents E e"
    and shape: "c=replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)
      (use_data_term (fst root)) (Payload_Term (snd root))"
    using presented by (auto simp: replay_value_presents_def judgment_value_presents_def site_data_term_def)
  have retention: "(110,Pair_Term c (Pair_Term (definition_site_value d) t))\<in>positive_meaning retention_admission_system"
    by (rule retention_admission_complete[OF presented reads closed])
  have derivation: "(102,derivation_argument e (use_data_term pu) (Payload_Term pr)
    (Pair_Term (use_data_term (fst root)) (Payload_Term (snd root))) (definition_site_value d) t (positioned_call_rows_term hs))
      \<in>positive_meaning derivation_admission_system"
    using derivation_admission_complete[OF source reads(1,3) order derived] by (simp add: site_data_term_def)
  show ?thesis using replay_admission_step[OF retention[unfolded shape] derivation] by (simp only: shape)
qed

theorem replay_admission_exact:
  "(111,z)\<in>positive_meaning replay_admission_system \<longleftrightarrow> replay_admission_result z"
  using replay_admission_sound replay_admission_complete by blast

corollary replay_admission_on_values:
  assumes presented: "replay_value_presents E pu pr au ar root c"
  shows "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    distinct hs \<and> native_replay_at E pu pr au ar root (set hs)"
proof -
  have unique: "F=E \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar \<and> other=root"
    if "replay_value_presents F qu qr bu br other c" for F qu qr bu br other
    by (rule replay_value_presents_unique[OF that presented])
  show ?thesis by (simp only: replay_admission_exact factor_term.inject positioned_call_rows_term_injective)
    (use presented unique in blast)
qed

corollary replay_admission_at_reads:
  assumes presented: "replay_value_presents E pu pr au ar root c"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    distinct hs \<and> schema_graph_derives (positioned_program P) G root d t (set hs) \<and>
    environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
  by (simp only: replay_admission_on_values[OF presented] native_replay_with_reads[OF package app graph])

corollary replay_admission_presentation_invariance:
  assumes "replay_value_presents E pu pr au ar root c" "replay_value_presents E pu pr au ar root b"
  shows "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    (111,Pair_Term b (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system"
  by (simp only: replay_admission_on_values[OF assms(1)] replay_admission_on_values[OF assms(2)])

corollary replay_admission_orders:
  assumes presented: "replay_value_presents E pu pr au ar root c" and order: "mset hs=mset ks"
  shows "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system \<longleftrightarrow>
    (111,Pair_Term c (positioned_call_rows_term ks))\<in>positive_meaning replay_admission_system"
  using mset_eq_imp_distinct_iff[OF order] mset_eq_setD[OF order] by (simp only: replay_admission_on_values[OF presented])

corollary replay_admission_boundary_unique:
  assumes presented: "replay_value_presents E pu pr au ar root c"
    and first: "(111,Pair_Term c (positioned_call_rows_term hs))\<in>positive_meaning replay_admission_system"
    and second: "(111,Pair_Term c (positioned_call_rows_term ks))\<in>positive_meaning replay_admission_system"
  shows "mset hs=mset ks"
proof -
  have left: "distinct hs" "native_replay_at E pu pr au ar root (set hs)"
    using first by (simp only: replay_admission_on_values[OF presented]; blast)+
  have right: "distinct ks" "native_replay_at E pu pr au ar root (set ks)"
    using second by (simp only: replay_admission_on_values[OF presented]; blast)+
  have same: "set hs=set ks" by (rule native_replay_assumptions_unique[OF left(2) right(2)])
  show ?thesis by (simp only: distinct_source_mset[OF left(1)]) (use right(1) same in auto)
qed

corollary replay_admission_closed_sound:
  assumes presented: "replay_value_presents E pu pr au ar root c"
    and checked: "(111,Pair_Term c (Payload_Term []))\<in>positive_meaning replay_admission_system"
  shows "native_positive_holds E pu pr au ar"
proof -
  have replay: "native_replay_at E pu pr au ar root {}"
    using replay_admission_on_values[OF presented, where hs="[]"] checked by simp
  show ?thesis by (rule native_replay_closed_sound[OF replay])
qed

section \<open>One fixed native program admits every future replay operand\<close>

lemma replay_operation_components:
  "(106,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (106,t)\<in>positive_meaning replay_source_reading_system"
  "(107,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (107,t)\<in>positive_meaning replay_slot_reading_system"
  "(108,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (108,t)\<in>positive_meaning replay_source_list_system"
  "(109,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (109,t)\<in>positive_meaning replay_slot_list_system"
  "(110,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> (110,t)\<in>positive_meaning retention_admission_system"
  using replay_admission_old_meaning[of 106 t] retention_admission_slot_meaning[of 106 t] replay_slot_reading_old_meaning[of 106 t]
    replay_admission_old_meaning[of 107 t] retention_admission_slot_meaning[of 107 t]
    replay_admission_old_meaning[of 108 t] retention_admission_components(5)[of t]
    replay_admission_old_meaning[of 109 t] retention_admission_components(6)[of t]
    replay_admission_old_meaning[of 110 t] by auto

abbreviation replay_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "replay_operation_result d t \<equiv>
    if d=106 then replay_source_reading_result t else if d=107 then replay_slot_reading_result t
    else if d=108 then replay_source_list_result t else if d=109 then replay_slot_list_result t
    else if d=110 then retention_admission_result t else replay_admission_result t"

lemma replay_operations_exact:
  assumes "d\<in>{106,107,108,109,110,111}"
  shows "(d,t)\<in>positive_meaning replay_admission_system \<longleftrightarrow> replay_operation_result d t"
proof -
  consider (source) "d=106" | (slot) "d=107" | (sources) "d=108" | (slots) "d=109" |
    (retention) "d=110" | (replay) "d=111" using assms by auto
  then show ?thesis
  proof cases
    case source
    show ?thesis by (simp only: source replay_operation_components replay_source_reading_exact; simp)
  next
    case slot
    show ?thesis by (simp only: slot replay_operation_components replay_slot_reading_exact; simp)
  next
    case sources
    show ?thesis by (simp only: sources replay_operation_components replay_source_list_exact; simp)
  next
    case slots
    show ?thesis by (simp only: slots replay_operation_components replay_slot_list_exact; simp)
  next
    case retention
    show ?thesis by (simp only: retention replay_operation_components retention_admission_exact; simp)
  next
    case replay
    show ?thesis by (simp only: replay replay_admission_exact; simp)
  qed
qed

theorem native_replay_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {106::nat,107,108,109,110,111} \<and>
    (\<forall>d\<in>{106,107,108,109,110,111}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> replay_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions replay_admission_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions replay_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed replay_admission_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning replay_admission_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF replay_admission_system_formed] by blast
  have sites: "inj_on g {106,107,108,109,110,111}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {106,107,108,109,110,111}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{106,107,108,109,110,111}" and tf: "term_formed t"
    have member: "d\<in>system_definitions replay_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed replay_admission_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning replay_admission_system"
      using future[rule_format, OF member tf] by blast
    have app_formed: "native_application_formed F pu [] au []"
      using parts(7) member tf by (simp add: replay_admission_call)
    have meaning: "native_positive_holds F pu [] au [] \<longleftrightarrow> replay_operation_result d t"
      by (simp only: parts(8) replay_operations_exact[OF selected])
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> replay_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts app_formed meaning in blast)
  qed
qed

text \<open>
  Retention supplies the actual application's callee and operand to derivation
  admission. Both calls share the same complete environment and all selected
  sites. The exact result is native replay with every distinct enumeration of
  its unique assumption boundary. No derived program, graph, or call is stored
  in the existing replay value. A closed admitted replay establishes the
  selected application's native positive meaning.

  Six new entries add fifteen ordinary clauses and preserve all earlier
  meanings. One closed native program fixes six distinct sites before every
  future formed operand and retains its canonical environment. It has one
  hundred and twelve definitions and one hundred and eighty-eight clauses.
  Full transition-protocol admission, reflection, genesis, and general quotation
  determination are separate remaining obligations.
\<close>

end
