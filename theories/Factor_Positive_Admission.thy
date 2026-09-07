theory Factor_Positive_Admission
  imports Factor_Environment_Inclusion Factor_Native_Proofs
begin

section \<open>Positive meaning supplies a closed proof in an extension\<close>

lemma positive_native_graph_extension:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and positive: "(d,t)\<in>positive_meaning P"
  shows "\<exists>F root G. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_schema_graph_at F root G \<and>
    schema_graph_derives (positioned_program P) G root d t {} \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  have formed: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have located: "(d,t)\<in>positive_meaning (positioned_program P)"
    using positive positioned_program_meaning[OF formed] by simp
  obtain G :: "(local_address option definition_site,local_address option definition_site,
      local_address option definition_site,local_address) schema_derivation_graph"
    and root where derived: "schema_graph_derives (positioned_program P) G root d t {}"
    using addressed_schema_graph_complete[OF located] by blast
  obtain F h where built: "environment_formed F" "environment_included E F"
    "native_package_at F pu pr P" "native_schema_graph_at F (h root) (rename_schema_graph h G)"
    "schema_graph_derives (positioned_program P) (rename_schema_graph h G) (h root) d t {}"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    using derived_graph_native_realization[OF package derived] by auto
  show ?thesis by (rule exI[of _ F], rule exI[of _ "h root"], rule exI[of _ "rename_schema_graph h G"])
    (use built in blast)
qed

section \<open>The supplied program and call are ordinary input data\<close>

abbreviation positive_query_result :: "factor_term \<Rightarrow> bool" where
  "positive_query_result z \<equiv> \<exists>E e pu pr P d t.
    z=package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) t) \<and>
    environment_value_presents E e \<and> native_package_at E pu pr P \<and> (d,t)\<in>positive_meaning P"

definition positive_query_schema :: "(nat,nat,nat) factor_schema" where
  "positive_query_schema=data_rule
    (package_subject_pattern data_x data_y data_z (Pattern_Pair data_w (Pattern_Variable 4)))
    {(0,80,source_root_pattern data_x data_y data_z),
     (1,113,Pattern_Pair data_x (Pattern_Variable 5)),
     (2,102,derivation_pattern (Pattern_Variable 5) data_y data_z (Pattern_Variable 6)
       data_w (Pattern_Variable 4) (Pattern_Payload []))}"

definition positive_query_system :: "(nat,nat,nat,nat) schema_system" where
  "positive_query_system=add_view_definition environment_inclusion_system 114 data_x {(0,positive_query_schema)}"

lemma positive_query_system_formed [simp]: "schema_system_formed positive_query_system"
  unfolding positive_query_system_def
  by (rule add_recursive_definition_formed[OF environment_inclusion_system_formed])
    (auto simp: positive_query_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma positive_query_definitions [simp]:
  "system_definitions positive_query_system=insert 114 (system_definitions environment_inclusion_system)"
  by (simp add: positive_query_system_def)

lemma positive_query_call:
  "schema_call_formed positive_query_system d t \<longleftrightarrow>
    d\<in>system_definitions positive_query_system \<and> term_formed t"
  using added_variable_calls[OF environment_inclusion_system_formed
    positive_query_system_formed[unfolded positive_query_system_def] environment_inclusion_call]
  by (simp only: positive_query_system_def[symmetric])

lemma positive_query_old_meaning:
  assumes "d\<in>system_definitions environment_inclusion_system"
  shows "(d,t)\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_inclusion_system"
  using added_definition_preserves_old(2)[OF environment_inclusion_system_formed
    positive_query_system_formed[unfolded positive_query_system_def], of d t] assms
  by (auto simp: positive_query_system_def)

lemma positive_query_clause [simp]:
  "((114,c),S)\<in>system_clauses positive_query_system \<longleftrightarrow> (c,S)\<in>{(0,positive_query_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses environment_inclusion_system \<Longrightarrow>
    d\<in>system_definitions environment_inclusion_system" for d c S
    using environment_inclusion_system_formed unfolding schema_system_formed_def by blast
  have absent: "((114,c),S)\<notin>system_clauses environment_inclusion_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: positive_query_system_def)
qed

lemma positive_query_components:
  "(80,t)\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (80,t)\<in>positive_meaning package_admission_system"
  "(113,t)\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  "(102,t)\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (102,t)\<in>positive_meaning derivation_admission_system"
  using positive_query_old_meaning[of 80 t] environment_inclusion_old_meaning[of 80 t]
    artifact_inclusion_old_meaning[of 80 t] replay_admission_old_meaning[of 80 t]
    retention_admission_components(1)[of t] positive_query_old_meaning[of 113 t]
    positive_query_old_meaning[of 102 t] environment_inclusion_old_meaning[of 102 t]
    artifact_inclusion_old_meaning[of 102 t] replay_admission_components(2)[of t] by auto

lemma positive_query_valuation:
  "(114,z)\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6}. term_formed (h j)) \<and>
      z=package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4)) \<and>
      (80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system \<and>
      (113,Pair_Term (h 0) (h 5))\<in>positive_meaning environment_inclusion_system \<and>
      (102,derivation_argument (h 5) (h 1) (h 2) (h 6) (h 3) (h 4) (Payload_Term []))
        \<in>positive_meaning derivation_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: positive_query_schema_def schema_variables_def positive_query_call positive_query_components)

lemma positive_query_step:
  assumes package: "(80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system"
    and extension: "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
    and derivation: "(102,derivation_argument f pu pr root d t (Payload_Term []))
      \<in>positive_meaning derivation_admission_system"
  shows "(114,package_subject_argument e pu pr (Pair_Term d t))\<in>positive_meaning positive_query_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr
    else if j=3 then d else if j=4 then t else if j=5 then f else root"
  show ?thesis by (simp only: positive_query_valuation, rule exI[of _ ?h])
    (use assms schema_call_formed_target[OF positive_meaning_formed[OF package]]
      schema_call_formed_target[OF positive_meaning_formed[OF extension]]
      schema_call_formed_target[OF positive_meaning_formed[OF derivation]] in auto)
qed

theorem positive_query_sound:
  assumes holds: "(114,z)\<in>positive_meaning positive_query_system"
  shows "positive_query_result z"
proof -
  obtain h :: "nat \<Rightarrow> factor_term" where shape: "z=package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 3) (h 4))"
    and calls: "(80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system"
    "(113,Pair_Term (h 0) (h 5))\<in>positive_meaning environment_inclusion_system"
    "(102,derivation_argument (h 5) (h 1) (h 2) (h 6) (h 3) (h 4) (Payload_Term []))
      \<in>positive_meaning derivation_admission_system"
    using holds by (auto simp: positive_query_valuation)
  obtain E pu pr P where source: "environment_value_presents E (h 0)"
    and coordinates: "h 1=use_data_term pu" "h 2=Payload_Term pr"
    and package: "native_package_at E pu pr P"
    using calls(1) by (auto simp: package_admission_exact)
  obtain F where target: "environment_value_presents F (h 5)" and included: "environment_included E F"
    using calls(2) by (simp only: environment_inclusion_at_source[OF source]) blast
  have ff: "environment_formed F" using environment_value_presents_formed[OF target] by blast
  have copied: "native_package_at F pu pr P" by (rule native_package_included[OF package included ff])
  obtain root d hs T G where callee_value: "h 3=definition_site_value d"
    and root: "h 6=definition_site_value root" and boundary: "Payload_Term []=positioned_call_rows_term hs"
    and reads: "native_package_at F pu pr T" "native_schema_graph_at F root G"
    and derived: "schema_graph_derives (positioned_program T) G root d (h 4) (set hs)"
    using calls(3) by (simp only: coordinates derivation_admission_at_source[OF target]
      factor_term.inject inj_eq[OF use_data_term_injective]) blast
  have no_assumptions: "hs=[]" using boundary by (cases hs) auto
  have same: "T=P" by (rule native_package_unique[OF reads(1) copied])
  have closed: "schema_graph_derives (positioned_program P) G root d (h 4) {}"
    using derived no_assumptions same by simp
  have positive: "(d,h 4)\<in>positive_meaning P"
    using schema_graph_closed_sound[OF closed]
    by (simp only: positioned_program_meaning[OF native_package_system_formed[OF package]])
  show ?thesis by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ pu], rule exI[of _ pr],
      rule exI[of _ P], rule exI[of _ d], rule exI[of _ "h 4"])
    (use shape source coordinates callee_value package positive in auto)
qed

theorem positive_query_complete:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and positive: "(d,t)\<in>positive_meaning P"
  shows "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr)
    (Pair_Term (definition_site_value d) t))\<in>positive_meaning positive_query_system"
proof -
  obtain F root G where built: "environment_formed F" "environment_included E F"
    "native_package_at F pu pr P" "native_schema_graph_at F root G"
    "schema_graph_derives (positioned_program P) G root d t {}"
    using positive_native_graph_extension[OF package positive] by blast
  obtain f where target: "environment_value_presents F f"
    using environment_value_presents_total[OF built(1)] by blast
  have admitted: "(80,source_root_argument e (use_data_term pu) (Payload_Term pr))
      \<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source package])
  have extension: "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
    by (rule environment_inclusion_complete[OF source target built(2)])
  have checked: "(102,derivation_argument f (use_data_term pu) (Payload_Term pr) (definition_site_value root)
      (definition_site_value d) t (Payload_Term []))\<in>positive_meaning derivation_admission_system"
    using derivation_admission_complete[OF target built(3,4), where hs="[]" and d=d and t=t] built(5) by simp
  show ?thesis by (rule positive_query_step[OF admitted extension checked])
qed

theorem positive_query_exact:
  "(114,z)\<in>positive_meaning positive_query_system \<longleftrightarrow> positive_query_result z"
proof
  assume "(114,z)\<in>positive_meaning positive_query_system"
  then show "positive_query_result z" by (rule positive_query_sound)
next
  assume "positive_query_result z"
  then obtain E e pu pr P d t where shape:
    "z=package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) t)"
    and source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and positive: "(d,t)\<in>positive_meaning P"
    by (elim exE conjE) (rule that; assumption)
  show "(114,z)\<in>positive_meaning positive_query_system"
    using positive_query_complete[OF source package positive] by (simp only: shape)
qed

corollary positive_query_at_source:
  assumes source: "environment_value_presents E e"
  shows "(114,package_subject_argument e u r (Pair_Term d t))\<in>positive_meaning positive_query_system
    \<longleftrightarrow> (\<exists>pu pr P f. u=use_data_term pu \<and> r=Payload_Term pr \<and>
      d=definition_site_value f \<and> native_package_at E pu pr P \<and> (f,t)\<in>positive_meaning P)"
proof -
  have unique: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  show ?thesis by (simp only: positive_query_exact factor_term.inject) (use source unique in blast)
qed

corollary positive_query_at_package:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) t))\<in>positive_meaning positive_query_system
    \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  by (simp only: positive_query_at_source[OF source] factor_term.inject
    inj_eq[OF use_data_term_injective] definition_site_value_eq)
    (use package native_package_unique[OF _ package] in blast)

corollary positive_query_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(114,package_subject_argument e u r (Pair_Term d t))\<in>positive_meaning positive_query_system
    \<longleftrightarrow> (114,package_subject_argument f u r (Pair_Term d t))\<in>positive_meaning positive_query_system"
  by (simp only: positive_query_at_source[OF assms(1)] positive_query_at_source[OF assms(2)])

corollary positive_query_extension_invariance:
  assumes source: "environment_value_presents E e" and target: "environment_value_presents F f"
    and package: "native_package_at E pu pr P" and included: "environment_included E F"
  shows "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) t))\<in>positive_meaning positive_query_system \<longleftrightarrow>
    (114,package_subject_argument f (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) t))\<in>positive_meaning positive_query_system"
proof -
  have formed: "environment_formed F" using environment_value_presents_formed[OF target] by blast
  have copied: "native_package_at F pu pr P" by (rule native_package_included[OF package included formed])
  show ?thesis by (simp only: positive_query_at_package[OF source package] positive_query_at_package[OF target copied])
qed

section \<open>The existing judgment value selects the actual application\<close>

abbreviation native_positive_admission_result :: "factor_term \<Rightarrow> bool" where
  "native_positive_admission_result z \<equiv> \<exists>E pu pr au ar.
    judgment_value_presents E pu pr au ar z \<and> native_positive_holds E pu pr au ar"

definition native_positive_admission_schema :: "(nat,nat,nat) factor_schema" where
  "native_positive_admission_schema=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4))))
    {(0,58,application_reading_pattern data_x data_w (Pattern_Variable 4) (Pattern_Variable 5)
       (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)),
     (1,114,package_subject_pattern data_x data_y data_z (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6)))}"

definition native_positive_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "native_positive_admission_system=add_view_definition positive_query_system 115 data_x {(0,native_positive_admission_schema)}"

lemma native_positive_admission_system_formed [simp]: "schema_system_formed native_positive_admission_system"
  unfolding native_positive_admission_system_def
  by (rule add_recursive_definition_formed[OF positive_query_system_formed])
    (auto simp: native_positive_admission_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma native_positive_admission_definitions [simp]:
  "system_definitions native_positive_admission_system=insert 115 (system_definitions positive_query_system)"
  by (simp add: native_positive_admission_system_def)

lemma native_positive_admission_call:
  "schema_call_formed native_positive_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions native_positive_admission_system \<and> term_formed t"
  using added_variable_calls[OF positive_query_system_formed
    native_positive_admission_system_formed[unfolded native_positive_admission_system_def] positive_query_call]
  by (simp only: native_positive_admission_system_def[symmetric])

lemma native_positive_admission_old_meaning:
  assumes "d\<in>system_definitions positive_query_system"
  shows "(d,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning positive_query_system"
  using added_definition_preserves_old(2)[OF positive_query_system_formed
    native_positive_admission_system_formed[unfolded native_positive_admission_system_def], of d t] assms
  by (auto simp: native_positive_admission_system_def)

lemma native_positive_admission_clause [simp]:
  "((115,c),S)\<in>system_clauses native_positive_admission_system \<longleftrightarrow> (c,S)\<in>{(0,native_positive_admission_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses positive_query_system \<Longrightarrow>
    d\<in>system_definitions positive_query_system" for d c S
    using positive_query_system_formed unfolding schema_system_formed_def by blast
  have absent: "((115,c),S)\<notin>system_clauses positive_query_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: native_positive_admission_system_def)
qed

lemma native_positive_admission_components:
  "(58,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (58,t)\<in>positive_meaning application_reading_system"
  "(114,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (114,t)\<in>positive_meaning positive_query_system"
  using native_positive_admission_old_meaning[of 58 t] positive_query_old_meaning[of 58 t]
    environment_inclusion_old_meaning[of 58 t] artifact_inclusion_old_meaning[of 58 t]
    replay_admission_old_meaning[of 58 t] retention_admission_components(2)[of t]
    native_positive_admission_old_meaning[of 114 t] by auto

lemma native_positive_admission_valuation:
  "(115,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8}. term_formed (h j)) \<and>
      z=Pair_Term (h 0) (Pair_Term (Pair_Term (h 1) (h 2)) (Pair_Term (h 3) (h 4))) \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8))
        \<in>positive_meaning application_reading_system \<and>
      (114,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 5) (h 6)))
        \<in>positive_meaning positive_query_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: native_positive_admission_schema_def schema_variables_def
      native_positive_admission_call native_positive_admission_components)

lemma native_positive_admission_step:
  assumes app: "(58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system"
    and positive: "(114,package_subject_argument e pu pr (Pair_Term d t))\<in>positive_meaning positive_query_system"
  shows "(115,Pair_Term e (Pair_Term (Pair_Term pu pr) (Pair_Term au ar)))
    \<in>positive_meaning native_positive_admission_system"
proof -
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au
    else if j=4 then ar else if j=5 then d else if j=6 then t else if j=7 then i else k"
  show ?thesis by (simp only: native_positive_admission_valuation, rule exI[of _ ?h])
    (use assms schema_call_formed_target[OF positive_meaning_formed[OF app]]
      schema_call_formed_target[OF positive_meaning_formed[OF positive]] in auto)
qed

theorem native_positive_admission_sound:
  assumes holds: "(115,z)\<in>positive_meaning native_positive_admission_system"
  shows "native_positive_admission_result z"
proof -
  obtain h :: "nat \<Rightarrow> factor_term" where shape: "z=Pair_Term (h 0) (Pair_Term (Pair_Term (h 1) (h 2)) (Pair_Term (h 3) (h 4)))"
    and calls: "(58,application_reading_argument (h 0) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8))
      \<in>positive_meaning application_reading_system"
    "(114,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 5) (h 6)))
      \<in>positive_meaning positive_query_system"
    using holds by (auto simp: native_positive_admission_valuation)
  obtain E e pu pr P d t where encoded:
    "package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 5) (h 6))=
      package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term (definition_site_value d) t)"
    and source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and positive: "(d,t)\<in>positive_meaning P"
    using positive_query_sound[OF calls(2)] by (elim exE conjE) (rule that; assumption)
  have fields: "h 0=e" "h 1=use_data_term pu" "h 2=Payload_Term pr"
    "h 5=definition_site_value d" "h 6=t" using encoded by simp_all
  obtain au ar du da Is Ks where coordinates: "h 3=use_data_term au" "h 4=Payload_Term ar"
    and site: "definition_site_value d=site_data_term du da"
    and app: "native_application_at E au ar (du,da) t (set Is) (set Ks)"
    using calls(1) by (simp only: fields application_reading_at_source[OF source]) blast
  have same: "d=(du,da)" using site by (cases d) simp
  have actual: "native_application_at E au ar d t (set Is) (set Ks)" using app same by simp
  have places: "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    by (rule native_judgment_positions[OF package actual])+
  have actual_shape: "z=Pair_Term e (Pair_Term (site_data_term pu pr) (site_data_term au ar))"
    using shape by (simp only: fields coordinates site_data_term_def)
  have present: "judgment_value_presents E pu pr au ar z"
    using source places actual_shape by (auto simp: judgment_value_presents_def)
  have truth: "native_positive_holds E pu pr au ar"
    by (simp only: native_positive_holds_with_reads[OF package actual]; rule positive)
  show ?thesis using present truth by blast
qed

theorem native_positive_admission_complete:
  assumes present: "judgment_value_presents E pu pr au ar z"
    and positive: "native_positive_holds E pu pr au ar"
  shows "(115,z)\<in>positive_meaning native_positive_admission_system"
proof -
  obtain e where source: "environment_value_presents E e"
    and shape: "z=Pair_Term e (Pair_Term (site_data_term pu pr) (site_data_term au ar))"
    using present unfolding judgment_value_presents_def by blast
  obtain P d t I K where parts: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "(d,t)\<in>positive_meaning P" using positive by (auto simp: native_positive_holds_def)
  obtain i k where app: "(58,application_reading_argument e (use_data_term au) (Payload_Term ar)
      (definition_site_value d) t i k)\<in>positive_meaning application_reading_system"
    using application_reading_value[OF source parts(2)] by blast
  have query: "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr)
      (Pair_Term (definition_site_value d) t))\<in>positive_meaning positive_query_system"
    by (rule positive_query_complete[OF source parts(1,3)])
  show ?thesis using native_positive_admission_step[OF app query] by (simp add: shape site_data_term_def)
qed

theorem native_positive_admission_exact:
  "(115,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow> native_positive_admission_result z"
  using native_positive_admission_sound native_positive_admission_complete by blast

corollary native_positive_admission_on_values:
  assumes present: "judgment_value_presents E pu pr au ar z"
  shows "(115,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    native_positive_holds E pu pr au ar"
  by (simp only: native_positive_admission_exact)
    (use present judgment_value_presents_unique[OF _ present] in blast)

corollary native_positive_admission_presentation_invariance:
  assumes "judgment_value_presents E pu pr au ar z" "judgment_value_presents E pu pr au ar w"
  shows "(115,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (115,w)\<in>positive_meaning native_positive_admission_system"
  by (simp only: native_positive_admission_on_values[OF assms(1)] native_positive_admission_on_values[OF assms(2)])

theorem native_positive_admission_previous_meaning:
  assumes "d\<in>system_definitions replay_admission_system"
  shows "(d,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning replay_admission_system"
  using native_positive_admission_old_meaning[of d t] positive_query_old_meaning[of d t]
    environment_inclusion_old_meaning[of d t] artifact_inclusion_old_meaning[OF assms, of t] assms by auto

section \<open>One fixed native program precedes every supplied program\<close>

abbreviation positive_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "positive_operation_result d t \<equiv>
    if d=112 then artifact_inclusion_result t else if d=113 then environment_inclusion_result t
    else if d=114 then positive_query_result t else native_positive_admission_result t"

lemma positive_operations_exact:
  assumes "d\<in>{112,113,114,115}"
  shows "(d,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow> positive_operation_result d t"
proof -
  have first: "(112,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
      (112,t)\<in>positive_meaning artifact_inclusion_system"
    using native_positive_admission_old_meaning[of 112 t] positive_query_old_meaning[of 112 t]
      environment_inclusion_old_meaning[of 112 t] by auto
  have second: "(113,t)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
      (113,t)\<in>positive_meaning environment_inclusion_system"
    using native_positive_admission_old_meaning[of 113 t] positive_query_old_meaning[of 113 t] by auto
  consider (rows) "d=112" | (scope_pair) "d=113" | (direct_call) "d=114" | (actual_call) "d=115"
    using assms by auto
  then show ?thesis
  proof cases
    case rows
    show ?thesis by (simp only: rows first artifact_inclusion_exact; simp)
  next
    case scope_pair
    show ?thesis by (simp only: scope_pair second environment_inclusion_exact; simp)
  next
    case direct_call
    show ?thesis by (simp only: direct_call native_positive_admission_components positive_query_exact; simp)
  next
    case actual_call
    show ?thesis by (simp only: actual_call native_positive_admission_exact; simp)
  qed
qed

theorem native_positive_operations:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu Q g.
    closed_native_package_at C cu [] Q \<and> inj_on g {112::nat,113,114,115} \<and>
    (\<forall>d\<in>{112,113,114,115}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> positive_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q
    where injective: "inj_on g (system_definitions native_positive_admission_system)"
    and closed: "closed_native_package_at C cu [] Q"
    and future: "\<forall>d\<in>system_definitions native_positive_admission_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F cu []=C \<and>
        (native_application_formed F cu [] au [] \<longleftrightarrow> schema_call_formed native_positive_admission_system d t) \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning native_positive_admission_system) \<and>
        (\<forall>u\<in>environment_uses C. \<forall>R. artifact_at F u R \<longleftrightarrow> artifact_at C u R) \<and>
        (\<forall>u\<in>environment_uses C. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot C u k v))"
    using compiled_program_future_applications[OF native_positive_admission_system_formed] by blast
  have sites: "inj_on g {112,113,114,115}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at C cu [] Q" by (rule closed)
    show "inj_on g {112,113,114,115}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{112,113,114,115}" and tf: "term_formed t"
    have member: "d\<in>system_definitions native_positive_admission_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included C F" "au\<notin>environment_uses C"
      "native_package_at F cu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F cu []=C"
      "native_application_formed F cu [] au [] \<longleftrightarrow> schema_call_formed native_positive_admission_system d t"
      "native_positive_holds F cu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning native_positive_admission_system"
      using future[rule_format, OF member tf] by blast
    have app_formed: "native_application_formed F cu [] au []"
      using parts(7) member tf by (simp add: native_positive_admission_call)
    have meaning: "native_positive_holds F cu [] au [] \<longleftrightarrow> positive_operation_result d t"
      by (simp only: parts(8) positive_operations_exact[OF selected])
    show "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
      native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
      (native_positive_holds F cu [] au [] \<longleftrightarrow> positive_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts app_formed meaning in blast)
  qed
qed

corollary native_positive_interpreter:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu Q entry.
    closed_native_package_at C cu [] Q \<and>
    (\<forall>E pu pr bu br z. judgment_value_presents E pu pr bu br z \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] entry z I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> native_positive_holds E pu pr bu br)))"
proof -
  obtain C :: "local_address option artifact_environment" and cu Q g where closed: "closed_native_package_at C cu [] Q"
    and future: "\<forall>d\<in>{112::nat,113,114,115}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
        native_package_at F cu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
        (native_positive_holds F cu [] au [] \<longleftrightarrow> positive_operation_result d t))"
    using native_positive_operations by (elim exE conjE) (rule that; assumption)
  show ?thesis
  proof (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q], rule exI[of _ "g 115"], rule conjI[OF closed],
      intro allI impI)
    fix E pu pr bu br z assume present: "judgment_value_presents E pu pr bu br z"
    have formed: "term_formed z" using judgment_value_presents_formed[OF present] by blast
    have exact: "positive_operation_result 115 z \<longleftrightarrow> native_positive_holds E pu pr bu br"
      using native_positive_admission_on_values[OF present] by (simp only: native_positive_admission_exact; simp)
    show "\<exists>F au I K. environment_formed F \<and> environment_included C F \<and> au\<notin>environment_uses C \<and>
      native_package_at F cu [] Q \<and> native_application_at F au [] (g 115) z I K \<and>
      native_package_environment F cu []=C \<and> native_application_formed F cu [] au [] \<and>
      (native_positive_holds F cu [] au [] \<longleftrightarrow> native_positive_holds E pu pr bu br)"
      using future[rule_format, of 115 z] formed by (simp only: exact; simp)
  qed
qed

text \<open>
  The supplied environment is retained in full while a private extension
  realizes a closed proof. Its package reading stays fixed. The independently
  defined least fixed point supplies such a finite proof for every positive
  call, and closed proof soundness recovers exactly that meaning. Proof
  existence is a derived characterization, not the definition of truth.

  The final entry reads the actual application and sends its callee and
  operand to the query in the same represented environment. It uses the
  existing judgment value, with no stored proof or derived-call field.
  Every complete presentation is permitted, including environments containing
  material beyond the selected judgment's dependency restriction.

  Four entries add five ordinary clauses and preserve every earlier meaning.
  One closed native program with one hundred and sixteen definitions and one
  hundred and ninety-three clauses fixes its entry before all future supplied
  programs and operands. Exact positive recognition does not assert termination
  on false calls. Universal correctness of a submitted interpreter, the full
  transition protocol, general reflection, genesis, and quotation determination
  remain separate obligations.
\<close>

end
