theory Factor_Program_Reflection
  imports Factor_Positive_Admission Factor_Native_Equality
begin

section \<open>Formation and meaning retain separate ordinary entries\<close>

lemma program_reflection_components:
  "(84,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (84,z)\<in>positive_meaning program_call_admission_system"
  "(114,z)\<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (114,z)\<in>positive_meaning positive_query_system"
  by (simp_all add: native_positive_admission_old_meaning positive_query_old_meaning
    environment_inclusion_old_meaning artifact_inclusion_old_meaning
    replay_admission_old_meaning retention_admission_old_meaning
    replay_slot_list_old_meaning replay_source_list_old_meaning
    replay_slot_reading_old_meaning replay_source_reading_old_meaning
    definition_slot_reading_old_meaning schema_slot_reading_old_meaning
    premise_slot_reading_old_meaning derivation_admission_old_meaning
    proof_claim_checking_old_meaning keyed_row_join_old_meaning row_qualification_old_meaning
    proof_graph_membership_old_meaning proof_graph_admission_old_meaning
    proof_bound_checking_old_meaning proof_link_checking_old_meaning proof_node_reading_old_meaning
    discharge_table_reading_old_meaning binding_table_reading_old_meaning site_link_vector_old_meaning
    application_vector_old_meaning site_link_reading_old_meaning site_citation_reading_old_meaning
    admitted_instantiation_old_meaning program_call_list_old_meaning application_admission_old_meaning)

theorem program_formation_reflection:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(84,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (definition_site_value d) t)"
proof -
  have same_source: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  have same_program: "Q=P" if "native_package_at E pu pr Q" for Q
    by (rule native_package_unique[OF that package])
  show ?thesis
    by (simp only: program_reflection_components program_call_admission_exact factor_term.inject
        inj_eq[OF use_data_term_injective])
       (use source package same_source same_program in blast)
qed

theorem program_meaning_reflection:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(114,package_subject_argument e (use_data_term pu) (Payload_Term pr) z)
      \<in>positive_meaning native_positive_admission_system \<longleftrightarrow>
    (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (definition_site_value d) t)"
proof -
  have same_source: "F=E" if "environment_value_presents F e" for F
    by (rule environment_value_presents_unique[OF that source])
  have same_program: "Q=P" if "native_package_at E pu pr Q" for Q
    by (rule native_package_unique[OF that package])
  show ?thesis
    by (simp only: program_reflection_components positive_query_exact factor_term.inject
        inj_eq[OF use_data_term_injective])
       (use source package same_source same_program in blast)
qed

lemma reflected_truth_requires_formation:
  assumes "(114,z)\<in>positive_meaning native_positive_admission_system"
  shows "(84,z)\<in>positive_meaning native_positive_admission_system"
  using assms
  by (simp only: program_reflection_components positive_query_exact program_call_admission_exact)
     (blast dest: positive_meaning_formed)

section \<open>One native program reflects every supplied program\<close>

theorem native_program_reflection:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu Q a b.
    closed_native_package_at C cu [] Q \<and> native_package_environment C cu []=C \<and>
    a\<noteq>b \<and> a\<in>system_definitions Q \<and> b\<in>system_definitions Q \<and>
    (\<forall>z. schema_call_formed Q a z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (a,z)\<in>positive_meaning Q \<longleftrightarrow> program_call_admission_result z) \<and>
    (\<forall>z. (b,z)\<in>positive_meaning Q \<longleftrightarrow> positive_query_result z)"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu Q where compiled:
    "inj_on g (system_definitions native_positive_admission_system)"
    "closed_native_package_at C cu [] Q" "native_package_environment C cu []=C"
    "system_alpha_variant (rename_system g native_positive_admission_system) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning native_positive_admission_system"
    using program_compilation_total[OF native_positive_admission_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have members: "84\<in>system_definitions native_positive_admission_system"
    "114\<in>system_definitions native_positive_admission_system" by auto
  have distinct: "g 84\<noteq>g 114"
    using inj_onD[OF compiled(1) _ members(1,2)] by auto
  have definitions: "system_definitions Q=g ` system_definitions native_positive_admission_system"
    using compiled(4) unfolding system_alpha_variant_def renamed_system_definitions by blast
  have entries: "g 84\<in>system_definitions Q" "g 114\<in>system_definitions Q"
    using members definitions by blast+
  have admission_call: "schema_call_formed Q (g 84) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF native_positive_admission_system_formed
        compiled(1,4) members(1)] native_positive_admission_call; simp)
  have meaning_call: "schema_call_formed Q (g 114) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF native_positive_admission_system_formed
        compiled(1,4) members(2)] native_positive_admission_call; simp)
  have admission: "(g 84,z)\<in>positive_meaning Q \<longleftrightarrow> program_call_admission_result z" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) members(1) compiled(5)]
        program_reflection_components program_call_admission_exact)
  have meaning: "(g 114,z)\<in>positive_meaning Q \<longleftrightarrow> positive_query_result z" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) members(2) compiled(5)]
        program_reflection_components positive_query_exact)
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ Q],
        rule exI[of _ "g 84"], rule exI[of _ "g 114"])
       (use compiled(2,3) distinct entries admission_call meaning_call admission meaning in blast)
qed

section \<open>Generic equality witnesses an infinite reflected domain\<close>

theorem program_reflection_equality:
  assumes source: "environment_value_presents equality_environment e"
    and operands: "term_formed x" "term_formed y"
  shows "(84,package_subject_argument e (use_data_term None) (Payload_Term [0])
      (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term x y)))
        \<in>positive_meaning native_positive_admission_system"
    and "(114,package_subject_argument e (use_data_term None) (Payload_Term [0])
      (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term x y)))
        \<in>positive_meaning native_positive_admission_system \<longleftrightarrow> x=y"
proof -
  show "(84,package_subject_argument e (use_data_term None) (Payload_Term [0])
      (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term x y)))
        \<in>positive_meaning native_positive_admission_system"
    by (simp only: program_reflection_components
        program_call_admission_at_package[OF source native_equality_package])
       (use operands native_equality_system_formed in \<open>simp add: schema_call_formed_def native_equality_program_def\<close>)
  show "(114,package_subject_argument e (use_data_term None) (Payload_Term [0])
      (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term x y)))
        \<in>positive_meaning native_positive_admission_system \<longleftrightarrow> x=y"
    by (simp only: program_reflection_components
        positive_query_at_package[OF source native_equality_package] native_equality_exact)
       (use operands in auto)
qed

theorem program_reflection_infinite:
  "infinite {z. (84,z)\<in>positive_meaning native_positive_admission_system}"
  "infinite {z. (114,z)\<in>positive_meaning native_positive_admission_system}"
proof -
  obtain e where source: "environment_value_presents equality_environment e"
    using environment_value_presents_total[OF equality_environment_formed] by blast
  let ?q="\<lambda>n. package_subject_argument e (use_data_term None) (Payload_Term [0])
    (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term (term_tower n) (term_tower n)))"
  have injective: "inj ?q" by (auto simp: inj_on_def inj_eq[OF term_tower_injective])
  have inside: "range ?q \<subseteq> {z. (114,z)\<in>positive_meaning native_positive_admission_system}"
    using program_reflection_equality(2)[OF source term_tower_formed term_tower_formed] by auto
  have meaning: "infinite {z. (114,z)\<in>positive_meaning native_positive_admission_system}"
  proof
    assume finite: "finite {z. (114,z)\<in>positive_meaning native_positive_admission_system}"
    have image: "finite (range ?q)" by (rule finite_subset[OF inside finite])
    have "finite (UNIV :: nat set)" by (rule finite_imageD[OF image injective])
    then show False by simp
  qed
  show "infinite {z. (114,z)\<in>positive_meaning native_positive_admission_system}" by (rule meaning)
  have subset: "{z. (114,z)\<in>positive_meaning native_positive_admission_system}
      \<subseteq> {z. (84,z)\<in>positive_meaning native_positive_admission_system}"
    using reflected_truth_requires_formation by blast
  show "infinite {z. (84,z)\<in>positive_meaning native_positive_admission_system}"
    using finite_subset[OF subset] meaning by blast
qed

theorem program_reflection_formed_false:
  "\<exists>z. term_formed z \<and> (84,z)\<in>positive_meaning native_positive_admission_system \<and>
    (114,z)\<notin>positive_meaning native_positive_admission_system"
proof -
  obtain e where source: "environment_value_presents equality_environment e"
    using environment_value_presents_total[OF equality_environment_formed] by blast
  let ?z="package_subject_argument e (use_data_term None) (Payload_Term [0])
    (Pair_Term (definition_site_value (None,[Suc 0])) (Pair_Term (term_tower 0) (term_tower 1)))"
  have formed: "(84,?z)\<in>positive_meaning native_positive_admission_system"
    by (rule program_reflection_equality(1)[OF source term_tower_formed term_tower_formed])
  have false: "(114,?z)\<notin>positive_meaning native_positive_admission_system"
    using program_reflection_equality(2)[OF source term_tower_formed term_tower_formed, of 0 1]
    by (simp add: inj_eq[OF term_tower_injective])
  have argument: "term_formed ?z" using schema_call_formed_target[OF positive_meaning_formed[OF formed]] by blast
  show ?thesis using argument formed false by blast
qed

text \<open>
  Both public relations precede their representation: call formation uses the
  actual package interface, and positive truth is the independent least fixed
  point. Their separate ordinary entries belong to one closed finite native
  program fixed before every supplied program, complete environment
  presentation, and future operand. The all-term equations exclude extra
  output shapes and include every finite positive program admitted by the
  existing native grammar.

  Generic equality provides infinitely many reflected true calls and a
  formed call that is false. Formation is not identified with truth.
  The remaining reflection strata, universal correctness admission for
  submitted interpreters, and the full genesis theorem are separate joins.
\<close>

end
