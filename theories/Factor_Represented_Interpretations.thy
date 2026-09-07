theory Factor_Represented_Interpretations
  imports Factor_Program_Reflection Factor_Amendment_Interpretations Factor_Scope_Forwarding
begin

section \<open>A supplied scope becomes ordinary fixed argument data\<close>

definition scope_formation_system ::
  "factor_term \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "scope_formation_system e u r=add_view_definition native_positive_admission_system 116 data_x
    {(0,scope_call_schema 0 0 84 e (use_data_term u) (Payload_Term r))}"

definition scope_interpretation_system ::
  "factor_term \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "scope_interpretation_system e u r=add_view_definition (scope_formation_system e u r) 117 data_x
    {(0,scope_call_schema 0 0 114 e (use_data_term u) (Payload_Term r))}"

lemma scope_query_positive_argument:
  assumes "(k,package_subject_argument e u r z)\<in>positive_meaning Q"
  shows "term_formed z"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by auto

locale represented_program_interpretation =
  fixes E :: "local_address option artifact_environment" and e :: factor_term
    and pu :: "local_address option" and pr :: local_address
    and P :: "local_address option native_system"
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
begin

lemma source_fields:
  "term_formed e" "term_formed (use_data_term pu)" "term_formed (Payload_Term pr)"
  using schema_call_formed_target[OF positive_meaning_formed[OF package_admission_complete[OF source package]]]
  by auto

sublocale admission: positive_view native_positive_admission_system 116 data_x
  "{(0,scope_call_schema 0 0 84 e (use_data_term pu) (Payload_Term pr))}"
  by (rule positive_view.intro) (use source_fields in \<open>auto simp: single_valued_def\<close>)

sublocale truth: positive_view "scope_formation_system e pu pr" 117 data_x
  "{(0,scope_call_schema 0 0 114 e (use_data_term pu) (Payload_Term pr))}"
  by (rule positive_view.intro)
     (use source_fields admission.formed in \<open>auto simp: scope_formation_system_def single_valued_def\<close>)

lemma formed: "schema_system_formed (scope_interpretation_system e pu pr)"
  using truth.formed by (simp only: scope_interpretation_system_def)

lemma definitions [simp]:
  "system_definitions (scope_interpretation_system e pu pr)=
    insert 117 (insert 116 (system_definitions native_positive_admission_system))"
  by (simp add: scope_interpretation_system_def scope_formation_system_def)

lemma calls:
  "schema_call_formed (scope_interpretation_system e pu pr) 116 z \<longleftrightarrow> term_formed z"
  "schema_call_formed (scope_interpretation_system e pu pr) 117 z \<longleftrightarrow> term_formed z"
  using truth.old_calls[of 116 z] admission.view_call[of z] truth.view_call[of z]
  by (auto simp: scope_formation_system_def scope_interpretation_system_def)

lemma previous_calls:
  assumes "k\<in>system_definitions native_positive_admission_system"
  shows "schema_call_formed (scope_interpretation_system e pu pr) k z \<longleftrightarrow>
    schema_call_formed native_positive_admission_system k z"
  using truth.old_calls[of k z] admission.old_calls[OF assms, of z] assms
  by (auto simp: scope_formation_system_def scope_interpretation_system_def)

lemma previous_meaning:
  assumes "k\<in>system_definitions native_positive_admission_system"
  shows "(k,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (k,z)\<in>positive_meaning native_positive_admission_system"
  using truth.old_meaning[of k z] admission.old_meaning[OF assms, of z] assms
  by (auto simp: scope_formation_system_def scope_interpretation_system_def)

lemma formation_equation:
  "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (84,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
proof -
  have first: "(116,z)\<in>positive_meaning (scope_formation_system e pu pr) \<longleftrightarrow>
    term_formed z \<and> (84,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
    using admission.view_meaning[of z] source_fields
    by (simp add: scope_formation_system_def scope_call_schema_rule)
  have kept: "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (116,z)\<in>positive_meaning (scope_formation_system e pu pr)"
    using truth.old_meaning[of 116 z]
    by (simp add: scope_interpretation_system_def scope_formation_system_def)
  have argument: "term_formed z"
    if "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
    by (rule scope_query_positive_argument[OF that])
  show ?thesis using first kept argument by blast
qed

lemma meaning_equation:
  "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (114,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
proof -
  have kept: "(114,w)\<in>positive_meaning (scope_formation_system e pu pr) \<longleftrightarrow>
    (114,w)\<in>positive_meaning native_positive_admission_system" for w
    using admission.old_meaning[of 114 w] by (simp add: scope_formation_system_def)
  have view: "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    term_formed z \<and> (114,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
    using truth.view_meaning[of z] source_fields
    by (simp add: scope_interpretation_system_def scope_call_schema_rule kept)
  have argument: "term_formed z"
    if "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system"
    by (rule scope_query_positive_argument[OF that])
  show ?thesis using view argument by blast
qed

theorem formation_meaning:
  "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (definition_site_value d) t)"
  by (simp only: formation_equation program_formation_reflection[OF source package])

theorem truth_meaning:
  "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
    (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (definition_site_value d) t)"
  by (simp only: meaning_equation program_meaning_reflection[OF source package])

theorem native_total:
  "\<exists>F v T a b g.
    closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and> a\<noteq>b \<and>
    inj_on g (insert 117 (insert 116 (system_definitions native_positive_admission_system))) \<and>
    a=g 116 \<and> b=g 117 \<and>
    system_definitions T=g ` (insert 117 (insert 116 (system_definitions native_positive_admission_system))) \<and>
    native_package_roots F v []=system_definitions T \<and>
    (\<forall>k\<in>system_definitions native_positive_admission_system. \<forall>z.
      (schema_call_formed T (g k) z \<longleftrightarrow> schema_call_formed native_positive_admission_system k z) \<and>
      ((g k,z)\<in>positive_meaning T \<longleftrightarrow> (k,z)\<in>positive_meaning native_positive_admission_system))"
proof -
  let ?S="scope_interpretation_system e pu pr"
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and F :: "local_address option artifact_environment" and v T where compiled:
    "inj_on g (system_definitions ?S)" "closed_native_package_at F v [] T"
    "native_package_environment F v []=F" "system_alpha_variant (rename_system g ?S) T"
    "positive_meaning T=map_prod g id ` positive_meaning ?S"
    "native_package_roots F v []=system_definitions T"
    using program_compilation_total_with_roots[OF formed]
    by (elim exE conjE) (rule that; assumption)
  have members: "116\<in>system_definitions ?S" "117\<in>system_definitions ?S" by simp_all
  have distinct: "g 116\<noteq>g 117" using inj_onD[OF compiled(1) _ members(1,2)] by auto
  have target_defs: "system_definitions T=g ` system_definitions ?S"
    using compiled(4) unfolding system_alpha_variant_def renamed_system_definitions by blast
  have entries: "g 116\<in>system_definitions T" "g 117\<in>system_definitions T"
    using target_defs members by blast+
  have admission_call: "schema_call_formed T (g 116) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF formed compiled(1,4) members(1)] calls)
  have meaning_call: "schema_call_formed T (g 117) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF formed compiled(1,4) members(2)] calls)
  have admission: "(g 116,z)\<in>positive_meaning T \<longleftrightarrow>
    (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (definition_site_value d) t)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) members(1) compiled(5)] formation_meaning)
  have meaning: "(g 117,z)\<in>positive_meaning T \<longleftrightarrow>
    (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (definition_site_value d) t)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) members(2) compiled(5)] truth_meaning)
  have target_formed: "schema_system_formed T"
    using compiled(4) unfolding system_alpha_variant_def by blast
  have bridge: "program_interpretation P T (g 116) (g 117)"
    using native_package_system_formed[OF package] target_formed entries
      admission_call meaning_call admission meaning
    by (auto simp: program_interpretation_def)
  have prior: "\<forall>k\<in>system_definitions native_positive_admission_system. \<forall>z.
    (schema_call_formed T (g k) z \<longleftrightarrow> schema_call_formed native_positive_admission_system k z) \<and>
    ((g k,z)\<in>positive_meaning T \<longleftrightarrow> (k,z)\<in>positive_meaning native_positive_admission_system)"
  proof (intro ballI allI)
    fix k z assume member: "k\<in>system_definitions native_positive_admission_system"
    have inside: "k\<in>system_definitions ?S" using member by simp
    have boundary: "schema_call_formed T (g k) z \<longleftrightarrow> schema_call_formed native_positive_admission_system k z"
      by (simp only: compiled_system_call_boundary[OF formed compiled(1,4) inside] previous_calls[OF member])
    have result: "(g k,z)\<in>positive_meaning T \<longleftrightarrow> (k,z)\<in>positive_meaning native_positive_admission_system"
      by (simp only: compiled_system_meaning_at[OF compiled(1) inside compiled(5)] previous_meaning[OF member])
    show "(schema_call_formed T (g k) z \<longleftrightarrow> schema_call_formed native_positive_admission_system k z) \<and>
      ((g k,z)\<in>positive_meaning T \<longleftrightarrow> (k,z)\<in>positive_meaning native_positive_admission_system)"
      using boundary result by blast
  qed
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ T], rule exI[of _ "g 116"],
        rule exI[of _ "g 117"], rule exI[of _ g])
       (use compiled(1-3,6) target_defs bridge distinct prior in \<open>simp only: definitions; blast\<close>)
qed

end

section \<open>Complete source presentations and extensions preserve the bridge\<close>

theorem scope_interpretation_presentation_invariance:
  assumes first: "environment_value_presents E e" and second: "environment_value_presents E f"
    and package: "native_package_at E pu pr P"
  shows "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (116,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    and "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (117,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
proof -
  interpret left: represented_program_interpretation E e pu pr P
    by (rule represented_program_interpretation.intro[OF first package])
  interpret right: represented_program_interpretation E f pu pr P
    by (rule represented_program_interpretation.intro[OF second package])
  show "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (116,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    by (simp only: left.formation_meaning right.formation_meaning)
  show "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (117,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    by (simp only: left.truth_meaning right.truth_meaning)
qed

theorem scope_interpretation_extension_invariance:
  assumes source: "environment_value_presents E e" and target: "environment_value_presents F f"
    and package: "native_package_at E pu pr P" and included: "environment_included E F"
  shows "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (116,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    and "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (117,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
proof -
  have formed: "environment_formed F" using environment_value_presents_formed[OF target] by blast
  have copied: "native_package_at F pu pr P" by (rule native_package_included[OF package included formed])
  interpret left: represented_program_interpretation E e pu pr P
    by (rule represented_program_interpretation.intro[OF source package])
  interpret right: represented_program_interpretation F f pu pr P
    by (rule represented_program_interpretation.intro[OF target copied])
  show "(116,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (116,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    by (simp only: left.formation_meaning right.formation_meaning)
  show "(117,z)\<in>positive_meaning (scope_interpretation_system e pu pr) \<longleftrightarrow>
      (117,z)\<in>positive_meaning (scope_interpretation_system f pu pr)"
    by (simp only: left.truth_meaning right.truth_meaning)
qed

theorem represented_program_interpretation_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P"
  shows "\<exists>F v T a b.
    closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and> a\<noteq>b \<and> native_package_roots F v []=system_definitions T"
proof -
  have formed: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain e where source: "environment_value_presents E e"
    using environment_value_presents_total[OF formed] by blast
  interpret scope: represented_program_interpretation E e pu pr P
    by (rule represented_program_interpretation.intro[OF source package])
  show ?thesis using scope.native_total by (elim exE conjE) metis
qed

section \<open>The constructed bridge supplies actual amendment material\<close>

theorem current_represented_interpretation_material:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>F v T a b M.
    closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and> a\<noteq>b \<and> native_package_roots F v []=system_definitions T \<and>
    interpretation_support_at M None [] a b N nu nr \<and>
    (\<forall>H. generation_program_scope H F v [] T \<longrightarrow> amendment_interpretation_at C q H M None [])"
proof -
  have package: "native_package_at E pu pr P"
    using current_entry_scope_closed[OF current] by (simp add: closed_native_package_at_def)
  obtain F v T a b where compiled:
    "closed_native_package_at F v [] T" "native_package_environment F v []=F"
    "program_interpretation P T a b" "a\<noteq>b" "native_package_roots F v []=system_definitions T"
    using represented_program_interpretation_total[OF package]
    by (elim exE conjE) (rule that; assumption)
  have native: "native_package_at F v [] T" using compiled(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed F"
    using native_package_projection(1)[OF native] by (simp add: native_package_formed_def)
  have members: "a\<in>system_definitions T" "b\<in>system_definitions T"
    using compiled(3) by (auto simp: program_interpretation_def)
  have addresses: "octets_formed (snd a)" "octets_formed (snd b)"
    using environment_position_address[OF formed native_package_entry_position[OF native members(1)]]
      environment_position_address[OF formed native_package_entry_position[OF native members(2)]] by auto
  obtain M where support: "interpretation_support_at M None [] a b N nu nr"
    using interpretation_support_total[OF addresses remainder] by blast
  have future: "amendment_interpretation_at C q H M None []"
    if candidate: "generation_program_scope H F v [] T" for H
    using compiled(3) by (simp only: amendment_interpretation_with_scopes[OF current candidate support])
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ T],
        rule exI[of _ a], rule exI[of _ b], rule exI[of _ M])
       (use compiled support future in blast)
qed

text \<open>
  Two ordinary clauses specialize the fixed formation and meaning entries.
  The entire represented environment and actual package coordinates are
  literal patterns in their premises. Each conclusion keeps one arbitrary
  future operand. No source definition is installed as an additional active
  rule: the resulting definition set is exactly the fixed checker and these
  two entries, transported by native compilation.

  Every native source package has this interpretation, including packages
  read in containing environments. Both entries have exact output contracts
  over all terms. Changing a complete presentation or extending its formed
  environment preserves those contracts. Earlier checker calls and meanings
  are unchanged, and all compiled definitions are actual public roots.

  The existing interpretation contract supplies future native bridge calls.
  The actual current frame also receives complete supporting material before
  candidate history, cause, or adoption is chosen. This construction class
  does not replace the earlier construction that additionally retains direct
  copies of independent source programs. Nor does construction by this proof
  admit arbitrary submitted correctness evidence inside the predecessor.
  That admission and the full transition protocol remain separate obligations.
\<close>

end
