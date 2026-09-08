theory Factor_Single_Clause_Reading
  imports Factor_Schema_Reading Factor_Scope_Admission
begin

section \<open>A complete variable interface and one arbitrary schema\<close>

definition native_single_clause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u native_schema \<Rightarrow> bool" where
  "native_single_clause_at E u r S \<longleftrightarrow>
    (\<exists>i c. native_definition_at E u r (Pattern_Variable i) {(c,S)})"

lemma native_single_clause_unique:
  assumes "native_single_clause_at E u r S" "native_single_clause_at E u r T"
  shows "S=T"
proof -
  obtain i c where first: "native_definition_at E u r (Pattern_Variable i) {(c,S)}"
    using assms(1) by (auto simp: native_single_clause_at_def)
  obtain j d where second: "native_definition_at E u r (Pattern_Variable j) {(d,T)}"
    using assms(2) by (auto simp: native_single_clause_at_def)
  have "{(c,S)}={(d,T)}" by (rule conjunct2[OF native_definition_unique[OF first second]])
  then show ?thesis by simp
qed

lemma native_single_clause_position:
  assumes "native_single_clause_at E u r S"
  shows "(u,r)\<in>environment_positions E"
  using assms native_definition_position by (auto simp: native_single_clause_at_def)

lemma native_single_clause_schema:
  assumes "native_single_clause_at E u r S"
  shows "\<exists>a. native_schema_at E u a S"
proof -
  obtain i c where raw: "native_definition_at E u r (Pattern_Variable i) {(c,S)}"
    using assms by (auto simp: native_single_clause_at_def)
  show ?thesis by (rule native_definition_clause_origin[OF raw, of c S]) simp
qed

lemma native_single_clause_call:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_single_clause_at E (fst d) (snd d) S"
  shows "schema_call_formed P d t \<longleftrightarrow> term_formed t"
proof -
  obtain i c where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i) {(c,S)}"
    using read by (auto simp: native_single_clause_at_def)
  show ?thesis
    by (simp only: schema_call_formed_def native_package_system_formed[OF package]
      native_package_complete_at(1)[OF package member raw]) auto
qed

lemma native_single_clause_dependencies:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_single_clause_at E (fst d) (snd d) S"
  shows "schema_dependencies S\<subseteq>system_definitions P"
proof -
  obtain i c where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i) {(c,S)}"
    using read by (auto simp: native_single_clause_at_def)
  have clause: "((d,c),S)\<in>system_clauses P"
    by (simp only: native_package_complete_at(2)[OF package member raw]) simp
  show ?thesis using native_package_system_formed[OF package] clause
    unfolding schema_system_formed_def by blast
qed

theorem native_single_clause_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_single_clause_at E (fst d) (snd d) S"
  shows "(d,t)\<in>positive_meaning P \<longleftrightarrow> schema_rule_instance S (positive_meaning P) t"
proof -
  obtain i c where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i) {(c,S)}"
    using read by (auto simp: native_single_clause_at_def)
  have family: "system_clause_family P d={(c,S)}"
    by (rule set_eqI; rename_tac q; case_tac q)
      (simp only: system_clause_member native_package_complete_at(2)[OF package member raw])
  have formed_call: "schema_call_formed P (fst q) (snd q)" if "q\<in>positive_meaning P" for q
    using that positive_meaning_formed by (cases q) auto
  have support: "{q\<in>positive_meaning P. schema_call_formed P (fst q) (snd q)}=positive_meaning P"
    using formed_call by auto
  have formed: "term_formed t" if "schema_rule_instance S (positive_meaning P) t"
    using that schema_instance_formed by (auto simp: schema_rule_instance_def)
  show ?thesis
    by (subst positive_meaning_unfold)
      (simp only: schema_consequence_rule family support native_single_clause_call[OF package member read];
        use formed in auto)
qed

lemma native_schema_family_singleton_source:
  assumes family: "native_schema_family_at E u r {(c,S)}" and source: "artifact_at E u R"
  shows "\<exists>a. family_at R r {(c,a)} \<and> native_schema_at E u a S"
proof -
  obtain A M a where origin: "artifact_at E u A" "family_at A r M" "(c,a)\<in>M" "native_schema_at E u a S"
    using native_schema_family_origin[OF family, of c S] by auto
  have formed: "environment_formed E" using family by (simp add: native_schema_family_at_def)
  have same: "A=R" by (rule environment_artifact_unique[OF formed origin(1) source])
  have graph: "family_at R r M" using origin(2) same by simp
  have functional: "single_valued M" using graph by (simp add: family_at_def)
  have key: "d=c" if "(d,w)\<in>M" for d w
    using native_schema_family_at_graph(2)[OF family source graph, rule_format, OF that] by auto
  have point: "q=(c,a)" if "q\<in>M" for q
  proof -
    obtain d w where shape: "q=(d,w)" by (cases q)
    have row: "(d,w)\<in>M" using that shape by simp
    have first: "d=c" by (rule key[OF row])
    have second: "w=a" using single_valued_outputs[OF functional row] origin(3) first by blast
    show ?thesis by (simp only: shape first second)
  qed
  have singleton: "M={(c,a)}"
  proof (rule equalityI)
    show "M\<subseteq>{(c,a)}"
    proof
      fix q assume member: "q\<in>M"
      have "q=(c,a)" by (rule point[OF member])
      then show "q\<in>{(c,a)}" by simp
    qed
    show "{(c,a)}\<subseteq>M" using origin(3) by simp
  qed
  show ?thesis by (rule exI[of _ a]) (use graph origin(4) singleton in simp)
qed

theorem native_single_clause_compilation:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema" and i :: 'a
    and E :: "local_address option artifact_environment"
  assumes formed: "schema_formed S" and environment: "environment_formed E"
    and callees: "\<forall>d\<in>schema_dependencies S. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  shows "\<exists>F u T. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and> schema_alpha_variant S T \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  let ?C="{((),S)}"
  have patterns: "pattern_formed (Pattern_Variable i)" and finite: "finite ?C" by simp_all
  have functional: "single_valued ?C" by (simp add: single_valued_def)
  have schemas: "\<forall>T\<in>rel_ran ?C. schema_formed T" using formed by (auto simp: rel_ran_def)
  have dependencies: "\<forall>d\<in>(\<Union>T\<in>rel_ran ?C. schema_dependencies T).
      \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
    using callees by (auto simp: rel_ran_def)
  obtain F u f h D where compiled:
    "environment_formed F" "environment_included E F" "u\<notin>environment_uses E"
    "native_definition_at F u [] (rename_pattern f (Pattern_Variable i)) D"
    "schema_family_variant h ?C D"
    "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R"
    "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x"
    using definition_environment_compilation[OF patterns finite functional schemas environment dependencies] by blast
  obtain T where family: "D={(h (),T)}" "schema_alpha_variant S T"
    using schema_family_variant_singleton[OF compiled(5)] by blast
  have read: "native_single_clause_at F u [] T"
    using compiled(4) family(1) by (auto simp: native_single_clause_at_def)
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ T])
    (use compiled(1-3,6,7) read family(2) schema_alpha_rule_instance[OF family(2)] in blast)
qed

section \<open>Ordinary admission checks the whole enclosing definition\<close>

definition single_clause_reading_schema :: "(nat,nat,nat) factor_schema" where
  "single_clause_reading_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y data_z)) data_w)
    {(0,72,citation_observation_pattern data_x data_y data_z (Pattern_Payload [])),
     (1,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 4)),
     (2,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7),
         Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 8)])),
     (3,32,Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8))
       (data_list_pattern [Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 10)])),
     (4,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 7)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 11) (Pattern_Variable 11)])
       (Pattern_Variable 11) (Pattern_Variable 12) (Pattern_Variable 13)),
     (5,56,scoped_instantiation_pattern data_x data_y (Pattern_Variable 7)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 11) (Pattern_Target (Whole_Artifact empty_artifact))])
       (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Variable 12) (Pattern_Variable 13)),
     (6,126,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Variable 10))) data_w)}"

definition single_clause_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "single_clause_reading_system=add_view_definition schema_reading_system 127 data_x {(0,single_clause_reading_schema)}"

interpretation single_clause_reading_view: positive_view schema_reading_system 127 data_x "{(0,single_clause_reading_schema)}"
  by (rule positive_view.intro)
    (auto simp: single_clause_reading_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma single_clause_reading_system_formed [simp]: "schema_system_formed single_clause_reading_system"
  using single_clause_reading_view.formed by (simp only: single_clause_reading_system_def)

lemma single_clause_reading_definitions [simp]:
  "system_definitions single_clause_reading_system=insert 127 (system_definitions schema_reading_system)"
  by (simp add: single_clause_reading_system_def)

lemma single_clause_reading_call:
  "schema_call_formed single_clause_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions single_clause_reading_system \<and> term_formed t"
  using added_variable_calls[OF schema_reading_system_formed
    single_clause_reading_system_formed[unfolded single_clause_reading_system_def] schema_reading_call]
  by (simp only: single_clause_reading_system_def[symmetric])

lemma single_clause_reading_old_meaning:
  assumes "d\<in>system_definitions schema_reading_system"
  shows "(d,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning schema_reading_system"
  using single_clause_reading_view.old_meaning[OF assms]
  by (simp only: single_clause_reading_system_def)

lemma single_clause_reading_clause [simp]:
  "((127,c),S)\<in>system_clauses single_clause_reading_system \<longleftrightarrow>
    c=0 \<and> S=single_clause_reading_schema"
  using single_clause_reading_view.no_old_clause
  by (auto simp: single_clause_reading_system_def)

lemma single_clause_reading_base_meaning:
  assumes "d\<in>system_definitions definition_call_admission_system"
  shows "(d,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning definition_call_admission_system"
  using assms single_clause_reading_old_meaning[of d t] schema_reading_old_meaning[of d t]
    reference_bindings_old_meaning[of d t] by auto

lemma single_clause_reading_components:
  "(72,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (72,t)\<in>positive_meaning definition_call_admission_system"
  "(37,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (34,t)\<in>positive_meaning record_admission_system"
  "(32,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (32,t)\<in>positive_meaning family_admission_system"
  "(56,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (56,t)\<in>positive_meaning scoped_instantiation_system"
  "(126,t)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (126,t)\<in>positive_meaning schema_reading_system"
  using single_clause_reading_base_meaning[of 72 t] single_clause_reading_base_meaning[of 37 t]
    single_clause_reading_base_meaning[of 34 t] single_clause_reading_base_meaning[of 32 t]
    single_clause_reading_base_meaning[of 56 t] single_clause_reading_old_meaning[of 126 t]
    definition_call_admission_components(1-3)[of t]
    definition_call_admission_old_meaning[of 32 t] schema_family_admission_components(2)[of t] by auto

lemma single_clause_reading_valuation:
  "(127,z)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13}. term_formed (h j)) \<and>
      z=schema_reference_argument (h 0) (h 1) (h 2) (h 3) \<and>
      (72,citation_observation_argument (h 0) (h 1) (h 2) (Payload_Term []))
        \<in>positive_meaning definition_call_admission_system \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 4) (h 2) (pair_list_term [(h 5,h 7),(h 6,h 8)]))
        \<in>positive_meaning record_admission_system \<and>
      (32,rooted_rows_argument (h 4) (h 8) (pair_list_term [(h 9,h 10)]))
        \<in>positive_meaning family_admission_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 7) (pair_list_term [(h 11,h 11)])
        (h 11) (h 12) (h 13))\<in>positive_meaning scoped_instantiation_system \<and>
      (56,scoped_instantiation_argument (h 0) (h 1) (h 7)
        (pair_list_term [(h 11,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact)) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system \<and>
      (126,schema_reference_argument (h 0) (h 1) (h 10) (h 3))\<in>positive_meaning schema_reading_system)"
proof -
  have ordinary: "schema_material_premises single_clause_reading_schema={}"
    by (simp add: single_clause_reading_schema_def)
  have accepts: "schema_call_formed single_clause_reading_system 127
      (evaluate_pattern h (schema_conclusion single_clause_reading_schema))"
    if "\<forall>a\<in>schema_variables single_clause_reading_schema. term_formed (h a)" for h
    using that by (auto simp: single_clause_reading_call single_clause_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF single_clause_reading_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: single_clause_reading_schema_def schema_variables_def single_clause_reading_components
      conj_ac all_conj_distrib imp_conjL)
    done
qed

abbreviation single_clause_reading_result :: "factor_term \<Rightarrow> bool" where
  "single_clause_reading_result z \<equiv> \<exists>E u r S p v.
    z=Pair_Term p v \<and> site_value_presents E u r p \<and>
    native_single_clause_at E u r S \<and> schema_reference_presents S v"

theorem single_clause_reading_sound:
  assumes holds: "(127,z)\<in>positive_meaning single_clause_reading_system"
  shows "single_clause_reading_result z"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where
    formed: "\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13}. term_formed (h j)"
    and shape: "z=schema_reference_argument (h 0) (h 1) (h 2) (h 3)"
    and reads:
      "(72,citation_observation_argument (h 0) (h 1) (h 2) (Payload_Term []))
        \<in>positive_meaning definition_call_admission_system"
      "(37,artifact_lookup_argument (h 0) (h 1) (h 4))\<in>positive_meaning artifact_lookup_system"
      "(34,rooted_rows_argument (h 4) (h 2) (pair_list_term [(h 5,h 7),(h 6,h 8)]))
        \<in>positive_meaning record_admission_system"
      "(32,rooted_rows_argument (h 4) (h 8) (pair_list_term [(h 9,h 10)]))
        \<in>positive_meaning family_admission_system"
      "(56,scoped_instantiation_argument (h 0) (h 1) (h 7) (pair_list_term [(h 11,h 11)])
        (h 11) (h 12) (h 13))\<in>positive_meaning scoped_instantiation_system"
      "(56,scoped_instantiation_argument (h 0) (h 1) (h 7)
        (pair_list_term [(h 11,Target_Term (Whole_Artifact empty_artifact))])
        (Target_Term (Whole_Artifact empty_artifact)) (h 12) (h 13))
        \<in>positive_meaning scoped_instantiation_system"
      "(126,schema_reference_argument (h 0) (h 1) (h 10) (h 3))\<in>positive_meaning schema_reading_system"
    using holds by (simp only: single_clause_reading_valuation) blast
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 4)"
    using reads(2) by (simp only: artifact_lookup_exact factor_term.inject) blast
  obtain r p q i m where rec:
    "h 2=Payload_Term r" "h 5=Payload_Term p" "h 7=Payload_Term i"
    "h 6=Payload_Term q" "h 8=Payload_Term m" "record_at R r [p,q] [i,m]"
    using reads(3) by (simp only: list.map prod.case record_admission_pair_fields[OF source(4)]) blast
  obtain pat C where raw: "native_definition_at E u r pat C"
    using reads(1) by (simp only: source(2) rec(1) definition_call_admission_on_values[OF source(1)]) blast
  obtain xs where rows:
    "pair_list_term [(h 9,h 10)]=data_list_term (map address_pair_data xs)" "family_at R m (set xs)"
    using reads(4) by (simp only: rec(5) family_admission_at_source[OF source(4)] factor_term.inject) blast
  have row_values: "[Pair_Term (h 9) (h 10)]=map address_pair_data xs"
    using rows(1) by (simp only: list.map prod.case data_list_term_injective)
  obtain c a where row: "h 9=Payload_Term c" "h 10=Payload_Term a" "xs=[(c,a)]"
    using row_values by (cases xs) (auto simp: address_pair_data_def split: prod.splits)
  have family: "family_at R m {(c,a)}" using rows(2) row(3) by simp
  obtain bs Is Ks where interface_rows:
    "pair_list_term [(h 11,h 11)]=binding_rows_term bs"
    "h 12=data_list_term (map Payload_Term Is)" "h 13=data_list_term (map Payload_Term Ks)"
    "distinct Is" "distinct Ks"
    using reads(5) by (simp only: source(2) rec(3) scoped_instantiation_at_source[OF source(1)]
      factor_term.inject inj_eq[OF use_data_term_injective]) blast
  obtain ib where interface_binder: "h 11=Payload_Term ib"
    using interface_rows(1)[symmetric] by (simp only: binding_rows_singleton_iff) blast
  have address: "octets_formed ib" using formed interface_binder by auto
  have interface: "scoped_pattern_at E u i (Pattern_Variable ib) (set Is) (set Ks)"
    using reads(5,6)[unfolded source(2) rec(3) interface_binder interface_rows(2,3)]
    by (simp only: scoped_variable_readings[OF source(1) address interface_rows(4,5)]) simp
  obtain S where schema: "native_schema_at E u a S" "schema_reference_presents S (h 3)"
    using reads(7) by (simp only: source(2) row(2) schema_reading_on_values[OF source(1)]) blast
  obtain I K where other: "scoped_pattern_at E u i pat I K"
    using native_definition_record_interface[OF raw source(3) rec(6)] by blast
  have pat: "pat=Pattern_Variable ib" using scoped_pattern_unique[OF other interface] by blast
  have full: "native_schema_family_at E u m C"
    by (rule native_definition_record_family[OF raw source(3) rec(6)])
  have unique: "native_schema_at E u a T \<longleftrightarrow> T=S" for T
    using native_schema_unique[OF _ schema(1)] schema(1) by blast
  have clauses: "(d,T)\<in>C \<longleftrightarrow> d=c \<and> T=S" for d T
    by (simp only: native_schema_family_at_graph(1)[OF full source(3) family]) (simp add: unique)
  have singleton: "C={(c,S)}"
    by (rule set_eqI; rename_tac q; case_tac q) (simp only: clauses; simp)
  have reading: "native_single_clause_at E u r S" using raw pat singleton by (auto simp: native_single_clause_at_def)
  have site: "site_value_presents E u r (Pair_Term (h 0) (site_data_term u r))"
    using source(1) native_single_clause_position[OF reading] by (auto simp: site_value_presents_def)
  show ?thesis by (rule exI[of _ E], rule exI[of _ u], rule exI[of _ r], rule exI[of _ S],
      rule exI[of _ "Pair_Term (h 0) (site_data_term u r)"], rule exI[of _ "h 3"])
    (use shape source(2) rec(1) site reading schema(2) in \<open>simp add: site_data_term_def\<close>)
qed

theorem single_clause_reading_complete:
  assumes source: "environment_value_presents E e" and read: "native_single_clause_at E u r S"
    and reference: "schema_reference_presents S z"
  shows "(127,schema_reference_argument e (use_data_term u) (Payload_Term r) z)
    \<in>positive_meaning single_clause_reading_system"
proof -
  obtain ib c where raw: "native_definition_at E u r (Pattern_Variable ib) {(c,S)}"
    using read by (auto simp: native_single_clause_at_def)
  obtain R ps i m I K where parts:
    "artifact_at E u R" "record_at R r ps [i,m]" "scoped_pattern_at E u i (Pattern_Variable ib) I K"
    "native_schema_family_at E u m {(c,S)}"
    using raw by (auto simp: native_definition_at_def)
  obtain a where family: "family_at R m {(c,a)}" "native_schema_at E u a S"
    using native_schema_family_singleton_source[OF parts(4,1)] by blast
  have address: "octets_formed ib" using scoped_pattern_variables_formed[OF parts(3)] by simp
  obtain Is where Is: "set Is=I" "distinct Is"
    using scoped_pattern_formed[OF parts(3)] finite_distinct_list[of I] by blast
  obtain Ks where Ks: "set Ks=K" "distinct Ks"
    using scoped_pattern_formed[OF parts(3)] finite_distinct_list[of K] by blast
  have interface: "scoped_pattern_at E u i (Pattern_Variable ib) (set Is) (set Ks)"
    using parts(3) Is(1) Ks(1) by simp
  have interface_reads:
    "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i)
      (binding_rows_term [(ib,Payload_Term ib)]) (Payload_Term ib)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
    "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term i)
      (binding_rows_term [(ib,Target_Term (Whole_Artifact empty_artifact))])
      (Target_Term (Whole_Artifact empty_artifact))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
    using interface by (simp_all only: scoped_variable_readings[OF source address Is(2) Ks(2)])
  have schema: "(126,schema_reference_argument e (use_data_term u) (Payload_Term a) z)
      \<in>positive_meaning schema_reading_system"
    by (rule schema_reading_complete[OF source family(2) reference])
  have environment: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have artifact: "exact_formed R" using environment parts(1) by (auto simp: environment_formed_def)
  obtain v where presented: "artifact_value_presents R v" using artifact_value_presents_total[OF artifact] by blast
  obtain p q where ports: "ps=[p,q]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  have admitted: "(72,citation_observation_argument e (use_data_term u) (Payload_Term r) (Payload_Term []))
      \<in>positive_meaning definition_call_admission_system"
    by (rule definition_call_admission_complete[OF source raw]) (simp add: octets_formed_def)
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) v)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument v (Payload_Term r)
      (pair_list_term [(Payload_Term p,Payload_Term i),(Payload_Term q,Payload_Term m)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: list.map prod.case record_admission_pair_fields[OF presented]) (use parts(2) ports in auto)
  have family_read: "(32,rooted_rows_argument v (Payload_Term m)
      (pair_list_term [(Payload_Term c,Payload_Term a)]))\<in>positive_meaning family_admission_system"
    using family_admission_rows[OF presented, of m "[(c,a)]"] family(1)
    by (simp add: address_pair_data_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then use_data_term u else if j=2 then Payload_Term r
    else if j=3 then z else if j=4 then v else if j=5 then Payload_Term p else if j=6 then Payload_Term q
    else if j=7 then Payload_Term i else if j=8 then Payload_Term m else if j=9 then Payload_Term c
    else if j=10 then Payload_Term a else if j=11 then Payload_Term ib
    else if j=12 then data_list_term (map Payload_Term Is) else data_list_term (map Payload_Term Ks)"
  show ?thesis by (simp only: single_clause_reading_valuation; rule exI[of _ ?h])
    (use admitted lookup rec family_read interface_reads schema
      schema_call_formed_target[OF positive_meaning_formed[OF admitted]]
      schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF family_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF interface_reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF schema]] in auto)
qed

theorem single_clause_reading_exact:
  "(127,z)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow> single_clause_reading_result z"
proof
  show "(127,z)\<in>positive_meaning single_clause_reading_system \<Longrightarrow> single_clause_reading_result z"
    by (rule single_clause_reading_sound)
next
  assume "single_clause_reading_result z"
  then obtain E u r S p v where parts: "z=Pair_Term p v" "site_value_presents E u r p"
    "native_single_clause_at E u r S" "schema_reference_presents S v" by blast
  obtain e where source: "environment_value_presents E e" "p=Pair_Term e (site_data_term u r)"
    using parts(2) by (auto simp: site_value_presents_def)
  show "(127,z)\<in>positive_meaning single_clause_reading_system"
    using single_clause_reading_complete[OF source(1) parts(3,4)] parts(1) source(2)
    by (simp only: site_data_term_def)
qed

theorem single_clause_reading_presented_relation:
  "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    presented_relation (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      schema_reference_presents
      (\<lambda>z S. native_single_clause_at (fst z) (fst (snd z)) (snd (snd z)) S) p v"
  by (auto simp: single_clause_reading_exact presented_relation_def; metis fst_conv snd_conv)

theorem single_clause_reading_joint_class:
  "presentation_class
    (\<lambda>z t. factor_pair_presents
      (\<lambda>a p. site_value_presents (fst a) (fst (snd a)) (snd (snd a)) p)
      schema_reference_presents z t \<and> (127,t)\<in>positive_meaning single_clause_reading_system)
    (\<lambda>z. native_single_clause_at (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z))
    (\<lambda>t. (127,t)\<in>positive_meaning single_clause_reading_system)"
proof -
  let ?R="\<lambda>a p. site_value_presents (fst a) (fst (snd a)) (snd (snd a)) p"
  let ?D="\<lambda>a::local_address option artifact_environment \<times> (local_address option\<times>local_address).
    environment_formed (fst a) \<and> snd a\<in>environment_positions (fst a)"
  let ?link="\<lambda>a::local_address option artifact_environment \<times> (local_address option\<times>local_address).
    \<lambda>S::local_address option native_schema. native_single_clause_at (fst a) (fst (snd a)) (snd (snd a)) S"
  let ?observe="\<lambda>t. (127,t)\<in>positive_meaning single_clause_reading_system"
  have generic: "presentation_class (\<lambda>z t. factor_pair_presents ?R schema_reference_presents z t \<and> ?observe t)
      (\<lambda>z. (?D (fst z) \<and> schema_data_formed (snd z)) \<and> ?link (fst z) (snd z)) ?observe"
    by (rule factor_relation_presentation_class[OF site_presentations.presentation_class_axioms
      schema_reference_presentations.presentation_class_axioms single_clause_reading_presented_relation])
      (auto simp: single_clause_reading_exact)
  have bounded: "?D a \<and> schema_data_formed S" if read: "?link a S" for a S
  proof -
    obtain r where schema: "native_schema_at (fst a) (fst (snd a)) r S"
      using native_single_clause_schema[OF read] by blast
    show ?thesis using schema native_schema_data_formed[OF schema] native_single_clause_position[OF read]
      by (auto simp: native_schema_at_def)
  qed
  have domain: "(\<lambda>z. (?D (fst z) \<and> schema_data_formed (snd z)) \<and> ?link (fst z) (snd z)) =
      (\<lambda>z. ?link (fst z) (snd z))"
    by (rule ext) (use bounded in blast)
  show ?thesis using generic by (simp only: domain)
qed

theorem single_clause_reading_at_reference:
  assumes source: "site_value_presents E u r p" and reference: "schema_reference_presents S v"
  shows "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    native_single_clause_at E u r S"
proof -
  have site: "site_value_presents (fst (E,u,r)) (fst (snd (E,u,r))) (snd (snd (E,u,r))) p"
    using source by simp
  have result: "presented_relation
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t) schema_reference_presents
      (\<lambda>z S. native_single_clause_at (fst z) (fst (snd z)) (snd (snd z)) S) p v \<longleftrightarrow>
      native_single_clause_at (fst (E,u,r)) (fst (snd (E,u,r))) (snd (snd (E,u,r))) S"
    by (rule presented_relation_at[OF site_presentations.presentation_class_axioms
      schema_reference_presentations.presentation_class_axioms site reference])
  show ?thesis using result by (simp only: single_clause_reading_presented_relation fst_conv snd_conv)
qed

corollary single_clause_reading_at_schema:
  assumes reference: "schema_reference_presents S v"
  shows "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S)"
proof
  assume holds: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
  obtain E u r T q w where actual:
    "Pair_Term p v=Pair_Term q w" "site_value_presents E u r q"
    "native_single_clause_at E u r T" "schema_reference_presents T w"
    using single_clause_reading_sound[OF holds]
    by (elim exE conjE) (rule that; assumption)
  have fields: "q=p" "w=v" using actual(1) by simp_all
  have other: "schema_reference_presents T v" using actual(4) fields(2) by simp
  have schema: "S=T" by (rule schema_reference_presentations.recovery[OF reference other])
  show "\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S"
    by (rule exI[of _ E], rule exI[of _ u], rule exI[of _ r])
      (use actual(2,3) fields schema in simp)
next
  assume "\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S"
  then obtain E u r where site: "site_value_presents E u r p" and raw: "native_single_clause_at E u r S"
    by blast
  show "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using raw by (simp only: single_clause_reading_at_reference[OF site reference])
qed

corollary single_clause_reading_presentation_invariance:
  assumes first: "site_value_presents E u r p" "schema_reference_presents S v"
    and second: "site_value_presents E u r q" "schema_reference_presents S w"
  shows "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<longleftrightarrow>
    (127,Pair_Term q w)\<in>positive_meaning single_clause_reading_system"
  by (simp only: single_clause_reading_at_reference[OF first] single_clause_reading_at_reference[OF second])

theorem single_clause_reading_total:
  assumes read: "native_single_clause_at E u r S"
  shows "\<exists>p v. site_value_presents E u r p \<and> schema_reference_presents S v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
proof -
  obtain a where schema: "native_schema_at E u a S" using native_single_clause_schema[OF read] by blast
  have formed: "environment_formed E" using schema by (simp add: native_schema_at_def)
  obtain p where site: "site_value_presents E u r p"
    using site_value_presents_total[OF formed native_single_clause_position[OF read]] by blast
  obtain v where reference: "schema_reference_presents S v" using native_schema_reference_total[OF schema] by blast
  have admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using read by (simp only: single_clause_reading_at_reference[OF site reference])
  show ?thesis using site reference admitted by blast
qed

theorem single_clause_reading_compilation:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
    and E :: "local_address option artifact_environment"
  assumes formed: "schema_formed S" and environment: "environment_formed E"
    and callees: "\<forall>d\<in>schema_dependencies S. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  shows "\<exists>F u T p v. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and> schema_alpha_variant S T \<and>
    site_value_presents F u [] p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance S X t) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  obtain F u T where compiled: "environment_formed F" "environment_included E F" "u\<notin>environment_uses E"
    "native_single_clause_at F u [] T" "schema_alpha_variant S T"
    "\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance S X t"
    "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R"
    "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x"
    using native_single_clause_compilation[OF formed environment callees] by blast
  obtain p v where presentations: "site_value_presents F u [] p" "schema_reference_presents T v"
    "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using single_clause_reading_total[OF compiled(4)] by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ T], rule exI[of _ p], rule exI[of _ v])
    (use compiled presentations in blast)
qed

section \<open>A fixed reference becomes ordinary checking code\<close>

definition reference_contract_schema :: "factor_term \<Rightarrow> (nat,nat,nat) factor_schema" where
  "reference_contract_schema v=data_rule data_x {(0,127,Pattern_Pair data_x (exact_term_pattern v))}"

lemma reference_contract_schema_formed [simp]:
  "schema_formed (reference_contract_schema v) \<longleftrightarrow> term_formed v"
  by (simp add: reference_contract_schema_def schema_formed_def single_valued_def)

lemma reference_contract_schema_variables [simp]:
  "schema_variables (reference_contract_schema v)={0}"
  by (simp add: reference_contract_schema_def schema_variables_def)

lemma reference_contract_schema_dependencies [simp]:
  "schema_dependencies (reference_contract_schema v)={127}"
  by (auto simp: reference_contract_schema_def schema_dependencies_def rel_ran_def)

lemma reference_contract_rule:
  "schema_rule_instance (reference_contract_schema v) X p \<longleftrightarrow>
    term_formed v \<and> term_formed p \<and> (127,Pair_Term p v)\<in>X"
proof
  assume rule: "schema_rule_instance (reference_contract_schema v) X p"
  obtain V Q where inst: "schema_instance (reference_contract_schema v) V p Q"
    and support: "\<forall>s d x. (s,d,x)\<in>Q \<longrightarrow> (d,x)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  have formed: "term_formed v" and bound: "(0,p)\<in>V"
    and bindings: "term_bindings_formed {0} V"
    using inst by (auto simp: schema_instance_def reference_contract_schema_def schema_variables_def schema_formed_def)
  have premise: "(0,127,Pair_Term p v)\<in>Q"
    using schema_instance_premise_iff[OF inst, of 0 127 "Pair_Term p v"] bound formed
    by (simp add: reference_contract_schema_def)
  show "term_formed v \<and> term_formed p \<and> (127,Pair_Term p v)\<in>X"
    using formed bindings bound support premise by (auto simp: term_bindings_formed_def)
next
  assume parts: "term_formed v \<and> term_formed p \<and> (127,Pair_Term p v)\<in>X"
  have inst: "schema_instance (reference_contract_schema v) {(0,p)} p {(0,127,Pair_Term p v)}"
    using parts by (auto simp: schema_instance_def reference_contract_schema_def schema_variables_def
      schema_formed_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)
  have material: "schema_material_satisfied (reference_contract_schema v) {(0,p)}"
    by (simp add: schema_material_satisfied_def reference_contract_schema_def)
  show "schema_rule_instance (reference_contract_schema v) X p"
    using inst material parts by (auto simp: schema_rule_instance_def)
qed

lemma reference_contract_view_exists:
  assumes "term_formed v"
  shows "\<exists>d. positive_view single_clause_reading_system d data_x {(0,reference_contract_schema v)}"
  by (rule positive_view_exists[OF single_clause_reading_system_formed])
    (use assms in \<open>auto simp: single_valued_def\<close>)

theorem reference_contract_view_meaning:
  assumes view: "positive_view single_clause_reading_system d data_x {(0,reference_contract_schema v)}"
    and reference: "schema_reference_presents S v"
  shows "(d,p)\<in>positive_meaning
      (add_view_definition single_clause_reading_system d data_x {(0,reference_contract_schema v)}) \<longleftrightarrow>
    (\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S)"
proof -
  interpret view: positive_view single_clause_reading_system d data_x "{(0,reference_contract_schema v)}"
    by (rule view)
  have formation: "term_formed p" if "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  have equation: "(d,p)\<in>positive_meaning view.extended \<longleftrightarrow>
      (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using view.view_meaning[of p] schema_reference_presents_formed[OF reference] formation
    by (auto simp: reference_contract_rule)
  show ?thesis by (simp only: equation single_clause_reading_at_schema[OF reference])
qed

theorem native_single_clause_reference_checker:
  assumes subject: "schema_data_formed S"
  shows "\<exists>v entry. \<exists>g :: nat\<Rightarrow>local_address option definition_site. \<exists>C cu Q.
    schema_reference_presents S v \<and>
    positive_view single_clause_reading_system entry data_x {(0,reference_contract_schema v)} \<and>
    inj_on g (insert entry (system_definitions single_clause_reading_system)) \<and>
    closed_native_package_at C cu [] Q \<and>
    system_alpha_variant (rename_system g
      (add_view_definition single_clause_reading_system entry data_x {(0,reference_contract_schema v)})) Q \<and>
    (\<forall>p. term_formed p \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g entry) p I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow>
          (\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S)) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)))"
proof -
  obtain v where reference: "schema_reference_presents S v"
    using schema_reference_presentations.total[OF subject] by blast
  obtain entry where view: "positive_view single_clause_reading_system entry data_x {(0,reference_contract_schema v)}"
    using reference_contract_view_exists[OF schema_reference_presents_formed[OF reference]] by blast
  interpret view: positive_view single_clause_reading_system entry data_x "{(0,reference_contract_schema v)}"
    by (rule view)
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q
    where compiled: "inj_on g (system_definitions view.extended)" "closed_native_package_at C cu [] Q"
      "system_alpha_variant (rename_system g view.extended) Q"
    and future: "\<forall>d\<in>system_definitions view.extended. \<forall>p. term_formed p \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) p I K \<and>
        native_package_environment F cu []=C \<and>
        (native_application_formed F cu [] au [] \<longleftrightarrow> schema_call_formed view.extended d p) \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> (d,p)\<in>positive_meaning view.extended) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
        (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x))"
    using compiled_program_with_future_applications[OF view.formed]
    by (elim exE conjE) (rule that; assumption)
  have member: "entry\<in>system_definitions view.extended" by simp
  have calls: "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
      native_package_at F cu [] Q \<and> native_application_at F au [] (g entry) p I K \<and>
      native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
      (native_positive_holds F cu [] au [] \<longleftrightarrow>
        (\<exists>E u r. site_value_presents E u r p \<and> native_single_clause_at E u r S)) \<and>
      (\<forall>w\<in>environment_uses C. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at C w R) \<and>
      (\<forall>w\<in>environment_uses C. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot C w s x)"
    if formed: "term_formed p" for p
    using future[rule_format, OF member formed] formed
    by (simp only: view.view_call reference_contract_view_meaning[OF view reference]) auto
  have injective: "inj_on g (insert entry (system_definitions single_clause_reading_system))"
    using compiled(1) by (simp only: added_view_definitions)
  show ?thesis
    apply (rule exI[of _ v], rule exI[of _ entry], rule exI[of _ g],
      rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q])
    apply (rule conjI[OF reference])
    apply (rule conjI[OF view])
    apply (rule conjI[OF injective])
    apply (rule conjI[OF compiled(2)])
    apply (rule conjI[OF compiled(3)])
    apply (intro allI impI)
    apply (rule calls)
    apply assumption
    done
qed

section \<open>Omitted alternatives and changed interface profiles fail admission\<close>

theorem single_clause_reading_rejects_changed_definition:
  assumes source: "site_value_presents E u r p" and reference: "schema_reference_presents S v"
    and actual: "native_definition_at E u r q C"
    and changed: "\<not>(\<exists>i c. q=Pattern_Variable i \<and> C={(c,S)})"
  shows "(127,Pair_Term p v)\<notin>positive_meaning single_clause_reading_system"
proof
  assume admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
  obtain i c where read: "native_definition_at E u r (Pattern_Variable i) {(c,S)}"
    using admitted by (simp only: single_clause_reading_at_reference[OF source reference] native_single_clause_at_def) blast
  show False using native_definition_unique[OF actual read] changed by blast
qed

text \<open>
  The subject is a complete definition with a variable interface and exactly
  one schema. Its schema may contain arbitrary ordinary and material
  premises. Native admission checks the complete definition record, its
  singleton clause family, both determining readings of the interface,
  and the referenced schema through the general report reader.

  The site retains the actual private interface binder and clause socket.
  Their coordinates need not be repeated in the schema report. The
  complete native definition recovers them, while the independently proved
  profile establishes acceptance of every formed argument and the whole
  schema rule. Extra clauses, a different interface, or a changed expected
  schema cannot pass. No execution sample establishes those properties.

  Every formed schema over supplied callee anchors has a compiled definition
  and admitted reports, with its private coordinates renamed injectively.
  Existing artifacts and all outgoing bindings are preserved. For any
  fixed exact reference, a fresh ordinary view stores the reference as
  literal pattern data. Its native compilation then checks all future
  source sites against that same expected schema. The expected contract
  receives force through actual clauses and their proved semantics.

  The profile is sufficient for these definitions. It does not decide
  semantic equivalence of arbitrary programs, check an unspecified contract,
  or discard the package boundary required for meaning.
\<close>

end
