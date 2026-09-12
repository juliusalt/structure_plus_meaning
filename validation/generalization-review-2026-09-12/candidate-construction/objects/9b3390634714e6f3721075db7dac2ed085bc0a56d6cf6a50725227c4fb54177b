theory Factor_Amendment_Programs
  imports Factor_Native_Amendment Factor_Current_Entry_Construction
begin

section \<open>Two explicit entries with different ordinary meanings\<close>

definition entry_choice_system :: "(nat,unit,bool,unit) schema_system" where
  "entry_choice_system =
    \<lparr>system_interfaces={(False,Pattern_Variable 0),(True,Pattern_Variable 0)},
     system_clauses={((True,()),recognizer_schema (Pattern_Variable 0))}\<rparr>"

lemma entry_choice_system_formed:
  "schema_system_formed entry_choice_system"
  by (auto simp: entry_choice_system_def schema_system_formed_def recognizer_schema_def
      schema_formed_def schema_dependencies_def system_definitions_def rel_dom_def rel_ran_def single_valued_def)

lemma entry_choice_definitions [simp]: "system_definitions entry_choice_system=UNIV"
  by (auto simp: entry_choice_system_def system_definitions_def rel_dom_def)

lemma entry_choice_call:
  "schema_call_formed entry_choice_system b t\<longleftrightarrow>term_formed t"
  using entry_choice_system_formed by (cases b) (simp_all add: schema_call_formed_def entry_choice_system_def)

theorem entry_choice_meaning:
  "(b,t)\<in>positive_meaning entry_choice_system\<longleftrightarrow>b \<and> term_formed t"
proof
  assume truth: "(b,t)\<in>positive_meaning entry_choice_system"
  obtain c V Q where inst: "admitted_schema_instance entry_choice_system b c V t Q"
    using truth by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have selected: "b" using inst by (auto simp: admitted_schema_instance_def entry_choice_system_def)
  have tf: "term_formed t" using positive_meaning_formed[OF truth] by (simp add: entry_choice_call)
  show "b \<and> term_formed t" using selected tf by blast
next
  assume parts: "b \<and> term_formed t"
  let ?V="{(0::nat,t)}"
  have call: "schema_call_formed entry_choice_system b t" using parts by (simp add: entry_choice_call)
  have inst: "admitted_schema_instance entry_choice_system b () ?V t {}"
    using parts call by (auto simp: admitted_schema_instance_def entry_choice_call entry_choice_system_def
      schema_instance_def recognizer_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def schema_material_satisfied_def term_bindings_formed_def
      single_valued_def rel_dom_def)
  show "(b,t)\<in>positive_meaning entry_choice_system"
    by (rule positive_meaning_step[OF inst]) simp
qed

lemma entry_choice_invariant: "amendment_permission_invariant entry_choice_system b"
  using amendment_value_presents_formed
  by (auto simp: amendment_permission_invariant_def entry_choice_call entry_choice_meaning)

theorem entry_choice_native_program:
  "\<exists>g :: bool \<Rightarrow> local_address option definition_site. \<exists>E pu P.
    inj g \<and> closed_native_package_at E pu [] P \<and> native_package_environment E pu []=E \<and>
    (\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b)))"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site" and E pu P where compiled:
    "inj_on g (system_definitions entry_choice_system)" "closed_native_package_at E pu [] P"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g entry_choice_system) P"
    "positive_meaning P=image (map_prod g id) (positive_meaning entry_choice_system)"
    using program_compilation_total[OF entry_choice_system_formed] by metis
  have injective: "inj g" using compiled(1) by simp
  have member: "\<And>b. b\<in>system_definitions entry_choice_system" by simp
  have boundary: "\<And>b t. schema_call_formed P (g b) t\<longleftrightarrow>schema_call_formed entry_choice_system b t"
    by (rule compiled_system_call_boundary[OF entry_choice_system_formed compiled(1,4) member])
  have meaning: "\<And>b t. (g b,t)\<in>positive_meaning P\<longleftrightarrow>(b,t)\<in>positive_meaning entry_choice_system"
    by (rule compiled_system_meaning_at[OF compiled(1) member compiled(5)])
  have admitted: "\<And>b. amendment_permission_invariant P (g b)"
    using amendment_permission_invariant_transport[OF boundary meaning] entry_choice_invariant by blast
  have inside: "\<And>b. g b\<in>system_definitions P"
    using compiled(4) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have every: "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using inside admitted boundary meaning by (simp add: entry_choice_call entry_choice_meaning)
  show ?thesis by (rule exI[of _ g], rule exI[of _ E], rule exI[of _ pu], rule exI[of _ P])
    (use injective compiled(2,3) every in blast)
qed

section \<open>A true auxiliary call cannot replace the entry selected by adoption\<close>

theorem current_entry_choice_witness:
  assumes authority: "target_formed A" and locus: "target_formed l"
    and candidate: "generation_formed H" and certificate: "target_formed c"
  shows "\<exists>C G p E pu P d e t F au I K M bu J L.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and> d\<noteq>e \<and>
    e\<in>system_definitions P \<and> amendment_permission_invariant P d \<and> amendment_permission_invariant P e \<and>
    (\<exists>D qu qr cu cr N v root. current_frame_quoted_at C [] D qu qr cu cr N v root \<and>
      amendment_value_presents D qu qr cu cr N v root H c t) \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu [] P \<and>
    native_package_environment F pu []=E \<and> native_application_at F au [] d t I K \<and>
    native_application_formed F pu [] au [] \<and> (current_accepts_at C [] F au [] H c\<longleftrightarrow>b) \<and>
    environment_formed M \<and> environment_included E M \<and> native_package_at M pu [] P \<and>
    native_package_environment M pu []=E \<and> native_application_at M bu [] e t J L \<and>
    native_application_formed M pu [] bu [] \<and> (native_positive_holds M pu [] bu []\<longleftrightarrow>\<not>b) \<and>
    \<not>current_accepts_at C [] M bu [] H c"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site" and E pu P where program:
    "inj g" "closed_native_package_at E pu [] P" "native_package_environment E pu []=E"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have member: "g b\<in>system_definitions P" "g (\<not>b)\<in>system_definitions P"
    and invariant: "amendment_permission_invariant P (g b)" "amendment_permission_invariant P (g (\<not>b))"
    using program(4) by blast+
  have different: "g b\<noteq>g (\<not>b)" using program(1) by (auto dest: injD)
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P (g b)"
    using current_entry_scope_construction[OF program(2) member(1) authority locus] by blast
  obtain D qu qr cu cr N v root where scope: "current_scope_quoted_at C [] D qu qr cu cr A N v root l G p"
    using current_entry_scope_frame[OF current] by blast
  have frame: "current_frame_quoted_at C [] D qu qr cu cr N v root"
    using scope by (simp add: current_scope_quoted_at_def)
  have fields: "environment_formed D" "(qu,qr)\<in>environment_positions D"
    "(cu,cr)\<in>environment_positions D" "environment_formed N" "(v,root)\<in>environment_positions N"
    using current_frame_quoted_formed[OF frame] by auto
  obtain t where present: "amendment_value_presents D qu qr cu cr N v root H c t"
    using amendment_value_presents_total[OF fields candidate certificate] by blast
  have tf: "term_formed t" using amendment_value_presents_formed[OF present] by blast
  have chosen_policy: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
      ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b)"
    using program(4)[rule_format, of b] by blast
  have auxiliary_policy: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g (\<not>b)) t \<and>
      ((g (\<not>b),t)\<in>positive_meaning P\<longleftrightarrow>\<not>b)"
    using program(4)[rule_format, of "\<not>b"] by blast
  have chosen: "schema_call_formed P (g b) t" "(g b,t)\<in>positive_meaning P\<longleftrightarrow>b"
    using chosen_policy[rule_format, OF tf] by auto
  have auxiliary: "schema_call_formed P (g (\<not>b)) t" "(g (\<not>b),t)\<in>positive_meaning P\<longleftrightarrow>\<not>b"
    using auxiliary_policy[rule_format, OF tf] by auto
  have permission: "factor_accepts P (g b) D qu qr cu cr N v root H c\<longleftrightarrow>b"
    by (simp only: factor_acceptance_at_presentation[OF invariant(1) present] chosen(2))
  obtain F au I K where selected: "environment_formed F" "environment_included E F"
    "native_package_at F pu [] P" "native_package_environment F pu []=E"
    "native_application_at F au [] (g b) t I K"
    "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed P (g b) t"
    "current_accepts_at C [] F au [] H c\<longleftrightarrow>factor_accepts P (g b) D qu qr cu cr N v root H c"
    using current_acceptance_application_total[OF current frame invariant(1) present] by blast
  have package: "native_package_at E pu [] P" using program(2) by (simp add: closed_native_package_at_def)
  obtain M bu J L where other: "environment_formed M" "environment_included E M"
    "native_package_at M pu [] P" "native_package_environment M pu []=native_package_environment E pu []"
    "native_application_at M bu [] (g (\<not>b)) t J L"
    "native_application_formed M pu [] bu []\<longleftrightarrow>schema_call_formed P (g (\<not>b)) t"
    "native_positive_holds M pu [] bu []\<longleftrightarrow>(g (\<not>b),t)\<in>positive_meaning P"
    using native_application_extension_total[OF package member(2) tf] by blast
  have rejected: "\<not>current_accepts_at C [] M bu [] H c"
  proof
    assume accepted: "current_accepts_at C [] M bu [] H c"
    have "g (\<not>b)=g b" by (rule current_acceptance_requires_selected_entry[OF current other(5) accepted])
    then show False using different by simp
  qed
  have fixed: "native_package_environment M pu []=E" using other(4) program(3) by simp
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ G], rule exI[of _ p], rule exI[of _ E], rule exI[of _ pu],
        rule exI[of _ P], rule exI[of _ "g b"], rule exI[of _ "g (\<not>b)"], rule exI[of _ t],
        rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K],
        rule exI[of _ M], rule exI[of _ bu], rule exI[of _ J], rule exI[of _ L])
       (use current different member(2) invariant frame present selected chosen permission other auxiliary
          fixed rejected in blast)
qed

text \<open>
  One ordinary finite system has two fully formed interfaces. One entry has
  no clauses; the other has a variable conclusion and no premises. Their exact
  meanings follow from the positive operator. Both policies are invariant on
  complete amendment data, and one closed compilation retains both entries for
  every future argument.

  Choosing the refusing entry gives an actual current frame and formed native
  calls on the same complete argument: the chosen call refuses, the auxiliary
  call is true, and the latter is still not current acceptance. Choosing the
  accepting entry gives actual acceptance under the same explicit construction.
  The Boolean chooses an entry of this displayed program; it is no semantic
  callback. Neither example establishes certificate validity or succession.
\<close>

end
