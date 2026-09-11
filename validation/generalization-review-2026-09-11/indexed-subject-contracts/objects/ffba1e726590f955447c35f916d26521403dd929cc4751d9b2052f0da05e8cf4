theory Factor_Construction_Contracts
  imports Factor_Construction_Admission
begin

section \<open>Every complete fragment and material presentation is accepted\<close>

theorem selected_fragment_all_presentations:
  assumes input: "selection_query_presents z p" and "output": "fragment_value_presents (selection_query_fragment z) q"
  shows "(245,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  using "output" by (simp only: selected_fragment_reading.output[OF input])

theorem selected_material_all_presentations:
  assumes input: "selection_query_presents z p"
    and "output": "artifact_value_presents (selection_material (fst z) (snd z)) q"
  shows "(246,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  using "output" by (simp only: selected_material_reading.output[OF input])

theorem selected_operations_presentation_invariance:
  assumes first: "selection_query_presents z p" and second: "selection_query_presents z u"
  shows "(245,Pair_Term p q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
      (245,Pair_Term u q)\<in>positive_meaning construction_admission_system"
    "(246,Pair_Term p q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
      (246,Pair_Term u q)\<in>positive_meaning construction_admission_system"
  by (simp_all only: selected_fragment_reading.output[OF first] selected_fragment_reading.output[OF second]
    selected_material_reading.output[OF first] selected_material_reading.output[OF second])

lemma selected_operations_require_context:
  assumes entry: "d\<in>{245,246,249}"
    and accepted: "(d,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system"
  shows "(242,c)\<in>positive_meaning source_system"
  using entry accepted source_operations_require_context[of 244]
  by (auto simp: selected_fragment_calls selected_material_composition.at_pair selected_piece_table_calls)

theorem selected_missing_source_rejected:
  assumes "context": "source_context_presents (xs,B) c"
    and absent: "\<not>(\<exists>R. construction_source_at xs B j R)"
  shows "(245,Pair_Term (Pair_Term c (Pair_Term (construction_source_term j) a)) q)
      \<notin>positive_meaning construction_admission_system"
    "(246,Pair_Term (Pair_Term c (Pair_Term (construction_source_term j) a)) q)
      \<notin>positive_meaning construction_admission_system"
  using source_missing_rejected(2)[OF "context" absent]
  by (auto simp: selected_fragment_calls selected_material_composition.at_pair)

corollary selected_empty_set_still_needs_source:
  "(245,Pair_Term
      (Pair_Term (Pair_Term (artifact_list_term []) (enumeration_term []))
        (Pair_Term (natural_term 0) (enumeration_term []))) q)
    \<notin>positive_meaning construction_admission_system"
proof -
  have base: "source_base_presents {} (enumeration_term [])"
    by (simp only: source_base_fields)
      (simp add: finite_table_presents_def finite_collection_presents_def single_valued_def)
  have "context": "source_context_presents ([],{}) (Pair_Term (artifact_list_term []) (enumeration_term []))"
    using base by simp
  show ?thesis using selected_missing_source_rejected(1)[OF "context", where j="Inl 0"] by simp
qed

section \<open>Slot identity survives equal material and duplicate slots fail\<close>

theorem selected_equal_material_distinct_slots:
  assumes read: "selection_context_presents z p"
    and first: "(k,u)\<in>snd z" and second: "(l,v)\<in>snd z"
    and distinct: "k\<noteq>l" and equal: "selection_material (fst z) u=selection_material (fst z) v"
  shows "\<exists>q. (249,Pair_Term p q)\<in>positive_meaning construction_admission_system \<and>
    data_table_presents payload_value_presents artifact_value_presents (selection_context_value z) q \<and>
    (k,selection_material (fst z) u)\<in>selection_context_value z \<and>
    (l,selection_material (fst z) u)\<in>selection_context_value z \<and> k\<noteq>l"
proof -
  obtain q where run: "(249,Pair_Term p q)\<in>positive_meaning construction_admission_system"
    using selected_piece_tables.total read by blast
  have result: "data_table_presents payload_value_presents artifact_value_presents (selection_context_value z) q"
    by (rule selected_piece_tables.sound[OF read run])
  have left: "(k,selection_material (fst z) u)\<in>selection_context_value z"
    using imageI[OF first, of "map_prod id (selection_material (fst z))"] by simp
  have right: "(l,selection_material (fst z) u)\<in>selection_context_value z"
    using imageI[OF second, of "map_prod id (selection_material (fst z))"] equal by simp
  show ?thesis
    by (rule exI[of _ q], intro conjI, rule run, rule result, rule left, rule right, rule distinct)
qed

theorem selected_duplicate_slot_rejected:
  "(249,Pair_Term (Pair_Term c
      (enumeration_term [Pair_Term (Payload_Term k) u,Pair_Term (Payload_Term k) v])) q)
    \<notin>positive_meaning construction_admission_system"
proof -
  let ?rows="[Pair_Term (Payload_Term k) u,Pair_Term (Payload_Term k) v]"
  have expected: "enumeration_retermination (data_list_term ?rows) (enumeration_term ?rows)"
    unfolding enumeration_retermination_def by (rule exI[of _ ?rows]) simp
  have unique: "p=data_list_term ?rows" if "enumeration_retermination p (enumeration_term ?rows)" for p
    by (rule presentation_class.recovery[OF enumeration_retermination_class that expected])
  have keys: "(21,data_list_term ?rows)\<notin>positive_meaning keyed_list_system"
  proof -
    have rows: "data_list_term ?rows=pair_list_term [(Payload_Term k,u),(Payload_Term k,v)]" by simp
    show ?thesis by (simp only: rows keyed_list_exact pair_list_term_injective) simp
  qed
  show ?thesis using unique keys by (auto simp only: selected_piece_table_calls factor_term.inject)
qed

theorem selected_empty_table_context_exact:
  "(\<exists>q. (249,Pair_Term (Pair_Term c (enumeration_term [])) q)
      \<in>positive_meaning construction_admission_system) \<longleftrightarrow>
    (\<exists>C. source_context_presents C c)"
proof
  assume "\<exists>q. (249,Pair_Term (Pair_Term c (enumeration_term [])) q)\<in>positive_meaning construction_admission_system"
  then show "\<exists>C. source_context_presents C c"
    using selected_operations_require_context[of 249 c] by (auto simp only: source_context_exact)
next
  assume "\<exists>C. source_context_presents C c"
  then obtain C where "context": "source_context_presents C c" by blast
  have empty: "selection_table_presents C {} (enumeration_term [])"
    by (simp add: selection_table_fields finite_table_presents_def finite_collection_presents_def single_valued_def)
  have read: "selection_context_presents (C,{}) (Pair_Term c (enumeration_term []))"
    using "context" empty by (simp only: selection_context_at)
  show "\<exists>q. (249,Pair_Term (Pair_Term c (enumeration_term [])) q)\<in>positive_meaning construction_admission_system"
    using selected_piece_tables.total read by blast
qed

theorem selected_two_equal_empty_pieces:
  "\<exists>p q. (249,Pair_Term p q)\<in>positive_meaning construction_admission_system \<and>
    data_table_presents payload_value_presents artifact_value_presents
      {([],empty_artifact),([0],empty_artifact)} q"
proof -
  let ?C="([empty_artifact],{}) :: construction_source_context"
  let ?Q="{([],(Inl 0,{})),([0],(Inl 0,{}))} :: construction_selection_table"
  have actual: "\<exists>R. construction_source_at [empty_artifact]
      ({} :: (local_address\<times>exact_artifact) set) (Inl 0) R"
    by (rule exI[of _ empty_artifact]) simp
  have valid: "selection_valid ?C (Inl 0,{})"
    unfolding source_selection_valid_def
    by (simp only: fst_conv snd_conv; intro conjI) (rule actual, simp, simp)
  have domain: "selection_context_domain (?C,?Q)"
    using valid by (simp add: construction_sources_formed_def single_valued_def octets_formed_def)
  obtain p where read: "selection_context_presents (?C,?Q) p"
    using selection_contexts.total[OF domain] by blast
  obtain q where run: "(249,Pair_Term p q)\<in>positive_meaning construction_admission_system"
    using selected_piece_tables.total read by blast
  have material: "selection_material ?C (Inl 0,{})=empty_artifact"
    by (simp add: construction_fragment_def fragment_material_def restrict_object_def restrict_structure_def
      internal_incidence_def restrict_basis_def empty_artifact_def empty_basis_def)
  have image: "selection_context_value (?C,?Q)={([],empty_artifact),([0],empty_artifact)}"
    using material by simp
  have result: "data_table_presents payload_value_presents artifact_value_presents
      {([],empty_artifact),([0],empty_artifact)} q"
    using selected_piece_tables.sound[OF read run] by (simp only: image)
  show ?thesis using run result by blast
qed

section \<open>Complete construction boundaries retain the unused context\<close>

theorem construction_empty_output_all_presentations:
  assumes sources: "source_context_domain (xs,B)"
    and claim: "construction_claim_presents xs B empty_source_construction empty_artifact t"
  shows "(250,t)\<in>positive_meaning construction_admission_system"
proof (rule construction_admission_complete[OF _ _ claim])
  show "source_constructs xs B empty_source_construction empty_artifact"
    by (rule source_constructs_empty) (use sources in simp)
  show "construction_coordinates_formed B empty_source_construction"
    using sources by (simp add: construction_coordinates_formed_def empty_source_construction_def)
qed

corollary construction_admission_inhabited:
  "(250,construction_claim_term [] {} empty_source_construction empty_artifact)
    \<in>positive_meaning construction_admission_system"
proof -
  have sources: "source_context_domain ([],{})" by (simp add: construction_sources_formed_def single_valued_def)
  have built: "source_constructs [] {} (empty_source_construction :: addressed_construction) empty_artifact"
    by (rule source_constructs_empty) (use sources in simp)
  show ?thesis by (rule construction_empty_output_all_presentations[OF sources construction_claim_term_presents[OF built]])
qed

theorem construction_invalid_unused_source_rejected:
  assumes claim: "construction_claim_presents xs B W R t"
    and unused_invalid: "S\<in>set xs" "\<not>exact_formed S"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  using unused_invalid by (auto simp: construction_admission_at_claim[OF claim]
    source_constructs_def construction_selection_formed_def construction_sources_formed_def)

theorem construction_invalid_unused_base_rejected:
  assumes claim: "construction_claim_presents xs B W R t"
    and unused_invalid: "(b,S)\<in>B" "\<not>octets_formed b \<or> \<not>exact_formed S"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  using unused_invalid by (auto simp: construction_admission_at_claim[OF claim] construction_coordinates_formed_def
    source_constructs_def construction_selection_formed_def construction_sources_formed_def)

theorem construction_wrong_output_rejected:
  assumes claim: "construction_claim_presents xs B W R t"
    and wrong: "R\<noteq>assembly_output (construction_assembly xs B W)"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  using wrong by (simp only: construction_admission_at_claim[OF claim] source_constructs_iff_K2; blast)

theorem construction_incomplete_origins_rejected:
  assumes claim: "construction_claim_presents xs B W R t"
    and incomplete: "rel_dom (construction_origins W)\<noteq>copied_carrier (construction_pieces xs B W)"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  using incomplete by (auto simp: construction_admission_at_claim[OF claim]
    source_constructs_def assembly_relation_def exact_map_def)

corollary construction_missing_origin_rejected:
  assumes "construction_claim_presents xs B W R t"
    "a\<in>copied_carrier (construction_pieces xs B W)" "a\<notin>rel_dom (construction_origins W)"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  by (rule construction_incomplete_origins_rejected[OF assms(1)]) (use assms(2,3) in blast)

corollary construction_extra_origin_rejected:
  assumes "construction_claim_presents xs B W R t"
    "a\<in>rel_dom (construction_origins W)" "a\<notin>copied_carrier (construction_pieces xs B W)"
  shows "(250,t)\<notin>positive_meaning construction_admission_system"
  by (rule construction_incomplete_origins_rejected[OF assms(1)]) (use assms(2,3) in blast)

theorem construction_admission_presentation_invariance:
  assumes first: "construction_claim_presents xs B W R t" and second: "construction_claim_presents xs B W R u"
  shows "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (250,u)\<in>positive_meaning construction_admission_system"
  by (simp only: construction_admission_at_claim[OF first] construction_admission_at_claim[OF second])

theorem construction_structural_permission_invariant:
  "construction_permission_invariant construction_admission_system 250"
proof -
  have site: "250\<in>system_definitions construction_admission_system"
    by (simp only: construction_admission_system_definitions; rule UnI2) simp
  have calls: "schema_call_formed construction_admission_system 250 p \<longleftrightarrow> term_formed p" for p
    using construction_admission_call[of 250 p] site by blast
  show ?thesis
    unfolding construction_permission_invariant_def
  proof (intro allI impI)
    fix xs B W R t u assume built: "source_constructs xs B W R"
      and coords: "construction_coordinates_formed B W"
      and first: "construction_claim_presents xs B W R t"
      and second: "construction_claim_presents xs B W R u"
    have formed: "term_formed t" "term_formed u"
      using construction_claim_presents_formed[OF built coords first]
        construction_claim_presents_formed[OF built coords second] by blast+
    have truth: "(250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
      (250,u)\<in>positive_meaning construction_admission_system"
      by (rule construction_admission_presentation_invariance[OF first second])
    show "(schema_call_formed construction_admission_system 250 t \<longleftrightarrow>
        schema_call_formed construction_admission_system 250 u) \<and>
      ((250,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
        (250,u)\<in>positive_meaning construction_admission_system)"
      using formed truth by (simp only: calls; blast)
  qed
qed

section \<open>One fixed program precedes every future complete claim\<close>

abbreviation construction_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "construction_operation_result d t \<equiv>
    if d=245 then (\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
      fragment_value_presents (selection_query_fragment z) q)
    else if d=246 then (\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
      artifact_value_presents (selection_material (fst z) (snd z)) q)
    else (\<exists>a. construction_account_presents a t)"

lemma construction_operations_exact:
  assumes "d\<in>{245,246,250}"
  shows "(d,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow> construction_operation_result d t"
  using assms by (auto simp: selected_fragment_exact selected_material_exact construction_admission_exact; blast)

theorem native_construction_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {245::nat,246,250} \<and>
    (\<forall>d\<in>{245,246,250}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> construction_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{245,246,250}\<subseteq>system_definitions construction_admission_system" by auto
  have calls: "schema_call_formed construction_admission_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{245,246,250}" for d t using construction_admission_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF construction_admission_system_formed selected calls construction_operations_exact])
qed

text \<open>
  The three public operations return every selected fragment or material form
  and admit every complete valid construction claim. One native program is
  fixed before all future operands, with its artifacts and bindings preserved.

  This concrete structural admission is invariant on complete claim
  presentations. It is one independently specified policy. The result does
  not supply a native checker for the global invariance condition on an
  arbitrary supplied permission program. Recorded causes and that general
  permission obligation remain separate work.
\<close>

end
