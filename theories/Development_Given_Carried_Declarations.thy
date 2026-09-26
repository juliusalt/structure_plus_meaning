theory Development_Given_Carried_Declarations
  imports Factor_Artifact_Citation_Declarations Factor_Row_Selection_Socket_Declarations
    Development_Given_Declarations Development_Given_Extensions Development_Given_Registrations
begin

text \<open>
  The given's record carried to the numbered programs the route resolves (R6b of DECISIONS.md "The native evaluator
  constructs the missing witnesses by resolution", its addition "The given's remaining producers: views, carriers and
  narrowed sockets", its carrying part). R6's pieces (@{text given_notion_declarations_discharged}) and R6b's records
  (the root family's, @{text Factor_Root_Family_Declarations}; the artifacts' and citations',
  @{text Factor_Artifact_Citation_Declarations}) each stand discharged at their notion's system. Every such system is a
  view of the one lineage the given's readers extend, so it agrees with the given's readers on its whole domain; a
  record discharged there is carried, once for any record, to the given's joined program and to its rooted readers by
  the one transfer by agreement (@{text declarations_agree_read_discharged}) at their common definitions (its instance
  @{text declarations_shared_discharged}): a consumer record's producer site need not stand in the consumer's own
  system (37 above 34, 35 and 54 on the lineage, 42 above 41, 54 above 6 and 48), and the transfer reads only the sites
  the obligations read. No record is discharged again, and no clause of any program changes. 32's kept sockets
  (@{text Factor_Row_Value_Socket_Declarations} at 71, 75 and 505; @{text Factor_Row_Selection_Socket_Declarations} at
  81, 104, 105 and 119) are carried the same way from the systems where their clauses stand: the payload audit's,
  a part of the given's readers, and views of the package and replay readers the given's readers extend.
\<close>

section \<open>Each notion's system agrees with the given's readers on its whole domain\<close>

text \<open>
  The systems stand on one lineage of views, each adding one fresh definition to the one below it
  (@{thm [source] systems_agree_on_added}): each agrees with the next declared one above it, and the top ones with the
  additions' system (@{thm [source] given_reader_agreements}), which agrees with the given's readers
  (@{thm [source] additions_guard_agreement}).
\<close>

lemma lineage_segments:
  "systems_agree_on bag_comparison_system artifact_comparison_system (system_definitions bag_comparison_system)"
  "systems_agree_on artifact_comparison_system artifact_projection_system (system_definitions artifact_comparison_system)"
  "systems_agree_on artifact_projection_system artifact_admission_system (system_definitions artifact_projection_system)"
  "systems_agree_on artifact_admission_system artifact_identity_system (system_definitions artifact_admission_system)"
  "systems_agree_on artifact_identity_system headed_material_system (system_definitions artifact_identity_system)"
  "systems_agree_on headed_material_system family_admission_system (system_definitions headed_material_system)"
  "systems_agree_on family_admission_system record_admission_system (system_definitions family_admission_system)"
  "systems_agree_on record_admission_system target_admission_system (system_definitions record_admission_system)"
  "systems_agree_on target_admission_system citation_admission_system (system_definitions target_admission_system)"
  "systems_agree_on citation_admission_system artifact_lookup_system (system_definitions citation_admission_system)"

  "systems_agree_on citation_resolution_system citation_interpretation_system
    (system_definitions citation_resolution_system)"
  "systems_agree_on citation_interpretation_system citation_location_system
    (system_definitions citation_interpretation_system)"
  "systems_agree_on citation_location_system citation_reading_system (system_definitions citation_location_system)"
  "systems_agree_on citation_reading_system target_projection_system (system_definitions citation_reading_system)"
  "systems_agree_on target_projection_system data_subset_system (system_definitions target_projection_system)"

  "systems_agree_on data_union_system payload_disjoint_system (system_definitions data_union_system)"
  "systems_agree_on payload_disjoint_system quotation_admission_system (system_definitions payload_disjoint_system)"
  "systems_agree_on quotation_admission_system binder_admission_system (system_definitions quotation_admission_system)"
  "systems_agree_on binder_admission_system pattern_instantiation_system (system_definitions binder_admission_system)"
  by (simp_all add: systems_agree_on_added artifact_comparison_system_def artifact_projection_system_def
    material_data_system_def atom_lookup_system_def artifact_admission_system_def artifact_identity_system_def
    headed_material_system_def key_fibre_system_def environment_identity_system_def environment_admission_system_def
    binding_entries_system_def binding_entry_system_def artifact_entries_system_def
    artifact_entry_admission_system_def keyed_list_system_def key_absence_system_def coordinate_admission_system_def
    natural_list_system_def natural_admission_system_def environment_comparison_system_def environment_bag_system_def
    environment_selection_system_def environment_entry_system_def family_admission_system_def
    family_sockets_system_def family_socket_system_def record_admission_system_def socket_chain_system_def
    target_admission_system_def citation_admission_system_def artifact_lookup_system_def
    citation_resolution_system_def binding_lookup_system_def citation_interpretation_system_def
    citation_location_system_def citation_reading_system_def target_projection_system_def
    located_admission_system_def anchored_admission_system_def data_subset_system_def data_append_system_def
    data_union_system_def payload_disjoint_system_def binder_admission_system_def diagonal_rows_system_def
    binding_admission_system_def row_keys_system_def quotation_admission_system_def pattern_instantiation_system_def)

text \<open>
  From the pattern instantiation to the package closure's admission the lineage is taken one view step at a time, so
  that every system between them has its own agreement with the given's readers below, each read where it is needed
  (the rooted readers' sites, R6c's record) rather than the steps run again.
\<close>

lemma closure_segments:
  "systems_agree_on pattern_instantiation_system scoped_instantiation_system
    (system_definitions pattern_instantiation_system)"
  "systems_agree_on scoped_instantiation_system prospective_instantiation_system
    (system_definitions scoped_instantiation_system)"
  "systems_agree_on prospective_instantiation_system application_reading_system
    (system_definitions prospective_instantiation_system)"
  "systems_agree_on application_reading_system row_values_system (system_definitions application_reading_system)"
  "systems_agree_on row_values_system vector_instantiation_system (system_definitions row_values_system)"
  "systems_agree_on vector_instantiation_system record_instantiation_system
    (system_definitions vector_instantiation_system)"
  "systems_agree_on record_instantiation_system material_instantiation_system
    (system_definitions record_instantiation_system)"
  "systems_agree_on material_instantiation_system premise_rows_system (system_definitions material_instantiation_system)"
  "systems_agree_on premise_rows_system premise_family_instantiation_system (system_definitions premise_rows_system)"
  "systems_agree_on premise_family_instantiation_system schema_instantiation_system
    (system_definitions premise_family_instantiation_system)"
  "systems_agree_on schema_instantiation_system material_checking_system (system_definitions schema_instantiation_system)"
  "systems_agree_on material_checking_system material_rows_checking_system (system_definitions material_checking_system)"
  "systems_agree_on material_rows_checking_system schema_material_checking_system
    (system_definitions material_rows_checking_system)"
  "systems_agree_on schema_material_checking_system schema_admission_system
    (system_definitions schema_material_checking_system)"
  "systems_agree_on schema_admission_system schema_root_list_system (system_definitions schema_admission_system)"
  "systems_agree_on schema_root_list_system schema_family_admission_system (system_definitions schema_root_list_system)"
  "systems_agree_on schema_family_admission_system definition_call_admission_system
    (system_definitions schema_family_admission_system)"
  "systems_agree_on definition_call_admission_system schema_callee_inclusion_system
    (system_definitions definition_call_admission_system)"
  "systems_agree_on schema_callee_inclusion_system schema_callee_list_system
    (system_definitions schema_callee_inclusion_system)"
  "systems_agree_on schema_callee_list_system definition_callee_inclusion_system
    (system_definitions schema_callee_list_system)"
  "systems_agree_on definition_callee_inclusion_system definition_callee_list_system
    (system_definitions definition_callee_inclusion_system)"
  "systems_agree_on definition_callee_list_system package_closure_admission_system
    (system_definitions definition_callee_list_system)"
  by (simp_all add: systems_agree_on_added package_closure_admission_system_def definition_callee_list_system_def
    definition_callee_inclusion_system_def schema_callee_list_system_def schema_callee_inclusion_system_def
    definition_call_admission_system_def schema_family_admission_system_def schema_root_list_system_def
    schema_admission_system_def schema_material_checking_system_def material_rows_checking_system_def
    material_checking_system_def schema_instantiation_system_def premise_family_instantiation_system_def
    premise_rows_system_def material_instantiation_system_def record_instantiation_system_def
    vector_instantiation_system_def row_values_system_def application_reading_system_def
    prospective_instantiation_system_def scoped_instantiation_system_def)

lemmas guard_definition_callee_list_agreement =
  whole_agreement_transitive[OF closure_segments(22) guard_closure_agreement]
lemmas guard_definition_callee_inclusion_agreement =
  whole_agreement_transitive[OF closure_segments(21) guard_definition_callee_list_agreement]
lemmas guard_schema_callee_list_agreement =
  whole_agreement_transitive[OF closure_segments(20) guard_definition_callee_inclusion_agreement]
lemmas guard_schema_callee_inclusion_agreement =
  whole_agreement_transitive[OF closure_segments(19) guard_schema_callee_list_agreement]
lemmas guard_definition_call_agreement =
  whole_agreement_transitive[OF closure_segments(18) guard_schema_callee_inclusion_agreement]
lemmas guard_schema_family_agreement =
  whole_agreement_transitive[OF closure_segments(17) guard_definition_call_agreement]
lemmas guard_schema_root_list_agreement =
  whole_agreement_transitive[OF closure_segments(16) guard_schema_family_agreement]
lemmas guard_schema_admission_agreement =
  whole_agreement_transitive[OF closure_segments(15) guard_schema_root_list_agreement]
lemmas guard_schema_material_checking_agreement =
  whole_agreement_transitive[OF closure_segments(14) guard_schema_admission_agreement]
lemmas guard_material_rows_checking_agreement =
  whole_agreement_transitive[OF closure_segments(13) guard_schema_material_checking_agreement]
lemmas guard_material_checking_agreement =
  whole_agreement_transitive[OF closure_segments(12) guard_material_rows_checking_agreement]
lemmas guard_schema_instantiation_agreement =
  whole_agreement_transitive[OF closure_segments(11) guard_material_checking_agreement]
lemmas guard_premise_family_agreement =
  whole_agreement_transitive[OF closure_segments(10) guard_schema_instantiation_agreement]
lemmas guard_premise_rows_agreement =
  whole_agreement_transitive[OF closure_segments(9) guard_premise_family_agreement]
lemmas guard_material_instantiation_agreement =
  whole_agreement_transitive[OF closure_segments(8) guard_premise_rows_agreement]
lemmas guard_record_instantiation_agreement =
  whole_agreement_transitive[OF closure_segments(7) guard_material_instantiation_agreement]
lemmas guard_vector_instantiation_agreement =
  whole_agreement_transitive[OF closure_segments(6) guard_record_instantiation_agreement]
lemmas guard_row_values_agreement =
  whole_agreement_transitive[OF closure_segments(5) guard_vector_instantiation_agreement]
lemmas guard_application_reading_agreement =
  whole_agreement_transitive[OF closure_segments(4) guard_row_values_agreement]
lemmas guard_prospective_agreement =
  whole_agreement_transitive[OF closure_segments(3) guard_application_reading_agreement]
lemmas guard_scoped_agreement = whole_agreement_transitive[OF closure_segments(2) guard_prospective_agreement]
lemmas guard_instantiation_agreement = whole_agreement_transitive[OF closure_segments(1) guard_scoped_agreement]
lemmas guard_binder_agreement = whole_agreement_transitive[OF lineage_segments(19) guard_instantiation_agreement]
lemmas guard_quotation_agreement = whole_agreement_transitive[OF lineage_segments(18) guard_binder_agreement]
lemmas guard_disjoint_agreement = whole_agreement_transitive[OF lineage_segments(17) guard_quotation_agreement]
lemmas guard_union_agreement = whole_agreement_transitive[OF lineage_segments(16) guard_disjoint_agreement]
lemmas guard_projection_agreement = whole_agreement_transitive[OF lineage_segments(15) guard_subset_agreement]
lemmas guard_reading_agreement = whole_agreement_transitive[OF lineage_segments(14) guard_projection_agreement]
lemmas guard_location_agreement = whole_agreement_transitive[OF lineage_segments(13) guard_reading_agreement]
lemmas guard_interpretation_agreement = whole_agreement_transitive[OF lineage_segments(12) guard_location_agreement]
lemmas guard_resolution_agreement = whole_agreement_transitive[OF lineage_segments(11) guard_interpretation_agreement]
lemmas guard_citation_agreement = whole_agreement_transitive[OF lineage_segments(10) guard_lookup_agreement]
lemmas guard_target_agreement = whole_agreement_transitive[OF lineage_segments(9) guard_citation_agreement]
lemmas guard_record_agreement = whole_agreement_transitive[OF lineage_segments(8) guard_target_agreement]
lemmas guard_family_agreement = whole_agreement_transitive[OF lineage_segments(7) guard_record_agreement]
lemmas guard_headed_agreement = whole_agreement_transitive[OF lineage_segments(6) guard_family_agreement]
lemmas guard_identity_agreement = whole_agreement_transitive[OF lineage_segments(5) guard_headed_agreement]
lemmas guard_admission_agreement = whole_agreement_transitive[OF lineage_segments(4) guard_identity_agreement]
lemmas guard_artifact_agreement = whole_agreement_transitive[OF lineage_segments(3) guard_admission_agreement]
lemmas guard_comparison_agreement = whole_agreement_transitive[OF lineage_segments(2) guard_artifact_agreement]
lemmas guard_bag_agreement = whole_agreement_transitive[OF lineage_segments(1) guard_comparison_agreement]

text \<open>
  The systems of 32's kept sockets: the payload audit is a part of the given's readers
  (@{thm [source] readers_agreement}); the clause reading and the retention admission agree with the additions'
  system (@{thm [source] given_reader_agreements}); the package slot reading and its list lie below the retention
  admission, the definition slot reading below the package slot reading
  (@{thm [source] judgment_retention_slot_agreement}) and the schema slot reading below the definition slot reading,
  each a chain of views.
\<close>

lemma guard_audit_agreement:
  "systems_agree_on payload_audit_system guard_readers_system (system_definitions payload_audit_system)"
  unfolding guard_readers_system_def
  by (rule system_union_agree_right[OF use_additions_system_formed readers_agreement])

lemma reader_segments:
  "systems_agree_on package_slot_reading_system package_retention_admission_system
    (system_definitions package_slot_reading_system)"
  "systems_agree_on package_slot_list_system package_retention_admission_system
    (system_definitions package_slot_list_system)"
  "systems_agree_on schema_slot_reading_system definition_slot_reading_system
    (system_definitions schema_slot_reading_system)"
  subgoal by (simp add: systems_agree_on_added package_retention_admission_system_def package_slot_list_system_def
    package_source_list_system_def)
  subgoal by (simp add: systems_agree_on_added package_retention_admission_system_def)
  subgoal by (simp add: systems_agree_on_added definition_slot_reading_system_def)
  done

lemmas guard_clause_reading_agreement =
  whole_agreement_transitive[OF given_reader_agreements(5) additions_guard_agreement]
lemmas guard_package_retention_agreement =
  whole_agreement_transitive[OF given_reader_agreements(9) additions_guard_agreement]
lemmas guard_package_slot_agreement =
  whole_agreement_transitive[OF reader_segments(1) guard_package_retention_agreement]
lemmas guard_package_slot_list_agreement =
  whole_agreement_transitive[OF reader_segments(2) guard_package_retention_agreement]
lemmas guard_definition_slot_agreement =
  whole_agreement_transitive[OF judgment_retention_slot_agreement guard_package_slot_agreement]
lemmas guard_schema_slot_agreement = whole_agreement_transitive[OF reader_segments(3) guard_definition_slot_agreement]

section \<open>A record discharged at its notion's system, carried to the given's programs\<close>

text \<open>
  A record is discharged at a notion's system when that system agrees with the given's readers on its whole domain,
  holds the sites its producers and consumers read, discharges it there, and holds each socket's schema as a clause at
  the socket's site (so it holds the sites the socket reads too). Such a record is discharged at the given's joined program and at its rooted readers, and each socket's schema
  is the programs' own clause there: stated once for any record, so that a later record (R6c's) and a later program
  (the installed ones) take it as it stands.
\<close>

text \<open>
  A socket's schema is the clause of its notion's system at the socket's site; that system agrees with the given's
  readers on its whole domain, so the clause is the given's joined program's there, and the rooted readers', a rooting
  of the joined program, wherever they hold the site. The finite programs present these systems exactly
  (@{thm [source] finite_given_program_exact}, @{thm [source] finite_rooted_given_readers_exact}).
\<close>

lemma given_socket_clause:
  assumes Pf: "schema_system_formed P" and agree: "systems_agree_on P guard_readers_system (system_definitions P)"
    and clause: "((d,c),decode_finite_schema S) \<in> system_clauses P"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_given_program"
    and "d \<in> system_definitions given_rooted_readers_system \<Longrightarrow>
      ((d,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
proof -
  have dP: "d \<in> system_definitions P" using Pf clause unfolding schema_system_formed_def by blast
  have program: "systems_agree_on P given_program_system (system_definitions P)"
    by (rule whole_agreement_transitive[OF agree guard_program_agreement])
  have inprog: "((d,c),decode_finite_schema S) \<in> system_clauses given_program_system"
    using program dP clause unfolding systems_agree_on_def by blast
  show "((d,c),S) |\<in>| finite_system_clauses finite_given_program"
    using inprog by (simp only: finite_system_clause_decoded finite_given_program_exact)
  assume r: "d \<in> system_definitions given_rooted_readers_system"
  have "((d,c),decode_finite_schema S) \<in> system_clauses given_rooted_readers_system"
    using rooted_system_agreement[of given_program_system "fset given_reader_entries",
        folded given_rooted_readers_system_def] given_program_formed inprog r
    unfolding systems_agree_on_def by blast
  then show "((d,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    by (simp only: finite_system_clause_decoded finite_rooted_given_readers_exact)
qed

abbreviation given_socket_selected :: "(nat,nat,nat) finite_factor_schema \<Rightarrow> nat \<Rightarrow> bool" where
  "given_socket_selected S e \<equiv> \<exists>c. ((e,c),S) |\<in>| finite_system_clauses finite_given_program \<and>
    (e \<in> system_definitions given_rooted_readers_system \<longrightarrow>
      ((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers)"

definition given_notion_discharged ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "given_notion_discharged D corr \<longleftrightarrow> (\<exists>P. schema_system_formed P \<and>
    systems_agree_on P guard_readers_system (system_definitions P) \<and>
    (\<forall>d V hs. (d,V,hs) |\<in>| declared_producers D \<longrightarrow> d \<in> system_definitions P) \<and>
    (\<forall>d e V i. (d,e,V,i) |\<in>| declared_consumers D \<longrightarrow> e \<in> system_definitions P) \<and>
    declarations_discharged (positive_meaning P) D corr \<and>
    (\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<longrightarrow>
      (\<exists>c. ((e,c),decode_finite_schema S) \<in> system_clauses P)))"

theorem given_notion_carried:
  assumes "given_notion_discharged D corr"
  shows "declarations_discharged (positive_meaning given_program_system) D corr"
    and "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    and "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow> given_socket_selected S e"
proof -
  obtain P where Pf: "schema_system_formed P" and agree: "systems_agree_on P guard_readers_system (system_definitions P)"
    and prods: "\<forall>d V hs. (d,V,hs) |\<in>| declared_producers D \<longrightarrow> d \<in> system_definitions P"
    and cons: "\<forall>d e V i. (d,e,V,i) |\<in>| declared_consumers D \<longrightarrow> e \<in> system_definitions P"
    and discharged: "declarations_discharged (positive_meaning P) D corr"
    and clauses: "\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<longrightarrow>
      (\<exists>c. ((e,c),decode_finite_schema S) \<in> system_clauses P)"
    using assms unfolding given_notion_discharged_def by blast
  show "given_socket_selected S e" if m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
  proof -
    obtain c where "((e,c),decode_finite_schema S) \<in> system_clauses P" using clauses m by blast
    then show ?thesis using given_socket_clause[OF Pf agree] by blast
  qed
  have program: "systems_agree_on P given_program_system (system_definitions P)"
    by (rule whole_agreement_transitive[OF agree guard_program_agreement])
  have socks: "schema_dependencies (decode_finite_schema S) \<subseteq> system_definitions P"
    if m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" for e S s keep Vp Vh
  proof -
    obtain c where "((e,c),decode_finite_schema S) \<in> system_clauses P" using clauses m by blast
    then show ?thesis using Pf unfolding schema_system_formed_def by blast
  qed
  have shared: "systems_agree_on P given_program_system (system_definitions P \<inter> system_definitions given_program_system)"
    by (rule systems_agree_on_subdomain[OF program Int_lower1])
  show "declarations_discharged (positive_meaning given_program_system) D corr"
    by (rule declarations_shared_discharged[OF Pf given_program_formed shared _ _ socks discharged])
      (use prods cons in blast)+
  have rooted: "systems_agree_on P given_rooted_readers_system
      (system_definitions P \<inter> system_definitions given_rooted_readers_system)"
    unfolding given_rooted_readers_system_def by (rule rooted_intersection_agreement[OF program])
  show "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    by (rule declarations_shared_discharged[OF Pf given_rooted_readers_formed rooted _ _ socks discharged])
      (use prods cons in blast)+
qed

text \<open>
  The union lemma: a union of records each so discharged is discharged at both programs, and each of its sockets'
  schemas is the programs' clause at the socket's site.
\<close>

theorem given_notions_carried:
  assumes "\<And>D. D \<in> set Ds \<Longrightarrow> given_notion_discharged D corr"
  shows "declarations_discharged (positive_meaning given_program_system) (declarations_list Ds) corr"
    and "declarations_discharged (positive_meaning given_rooted_readers_system) (declarations_list Ds) corr"
    and "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_list Ds) \<Longrightarrow> given_socket_selected S e"
proof -
  show "declarations_discharged (positive_meaning given_program_system) (declarations_list Ds) corr"
    by (rule declarations_list_discharged) (rule given_notion_carried(1)[OF assms])
  show "declarations_discharged (positive_meaning given_rooted_readers_system) (declarations_list Ds) corr"
    by (rule declarations_list_discharged) (rule given_notion_carried(2)[OF assms])
  assume "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_list Ds)"
  then obtain D where "D \<in> set Ds" "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" by (rule declarations_list_sockets)
  then show "given_socket_selected S e" by (rule given_notion_carried(3)[OF assms])
qed

section \<open>The given's record\<close>

text \<open>
  One correspondence for every record: the root family's at 79, the artifacts' and citations' elsewhere, which is R6's
  at R6's producers. Each record's own correspondence agrees with it where the record reads it.
\<close>

definition given_declarations_correspondence :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "given_declarations_correspondence d = (if d = 79 then (\<lambda>i. root_family_correspondence)
    else artifact_citation_correspondence d)"

lemma given_notion_dischargedI:
  assumes Pf: "schema_system_formed P" and agree: "systems_agree_on P guard_readers_system (system_definitions P)"
    and prods: "\<And>d V hs. (d,V,hs) |\<in>| declared_producers D \<Longrightarrow> d \<in> system_definitions P"
    and cons: "\<And>d e V i. (d,e,V,i) |\<in>| declared_consumers D \<Longrightarrow> e \<in> system_definitions P"
    and discharged: "declarations_discharged (positive_meaning P) D corr"
    and producers: "\<And>d. d |\<in>| fst |`| declared_producers D \<Longrightarrow> given_declarations_correspondence d = corr d"
    and consumers: "\<And>d. d |\<in>| fst |`| declared_consumers D \<Longrightarrow> given_declarations_correspondence d = corr d"
    and clauses: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      \<exists>c. ((e,c),decode_finite_schema S) \<in> system_clauses P"
  shows "given_notion_discharged D given_declarations_correspondence"
proof -
  have "declarations_discharged (positive_meaning P) D given_declarations_correspondence"
    using discharged producers consumers by (rule declarations_discharged_correspondence)
  then show ?thesis unfolding given_notion_discharged_def using Pf agree prods cons clauses by blast
qed

lemmas given_correspondence_unfold = given_declarations_correspondence_def artifact_citation_correspondence_def
  root_family_correspondences_def fun_eq_iff

lemma given_notion_given_bag: "given_notion_discharged given_bag_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF bag_comparison_system_formed guard_bag_agreement _ _ given_notion_declarations_discharged(1)])
  apply (auto simp: given_bag_declarations_def)[2]
  apply (auto simp: given_bag_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_bag_declarations_def given_bag_socket_decoded bag_comparison_clauses_def)
  done

lemma given_notion_given_artifact: "given_notion_discharged given_artifact_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF artifact_projection_system_formed guard_artifact_agreement _ _ given_notion_declarations_discharged(2)])
  apply (auto simp: given_artifact_declarations_def)[2]
  apply (auto simp: given_artifact_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_artifact_declarations_def given_artifact_socket_decoded)
  done

lemma given_notion_given_family: "given_notion_discharged given_family_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF family_admission_system_formed guard_family_agreement _ _ given_notion_declarations_discharged(3)])
  apply (auto simp: given_family_declarations_def)[2]
  apply (auto simp: given_family_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_family_declarations_def )
  done

lemma given_notion_given_target: "given_notion_discharged given_target_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF target_projection_system_formed guard_projection_agreement _ _ given_notion_declarations_discharged(4)])
  apply (auto simp: given_target_declarations_def)[2]
  apply (auto simp: given_target_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_target_declarations_def given_target_socket_decoded target_projection_clauses_def)
  done

lemma given_notion_given_disjoint: "given_notion_discharged given_disjoint_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF payload_disjoint_system_formed guard_disjoint_agreement _ _ given_notion_declarations_discharged(5)])
  apply (auto simp: given_disjoint_declarations_def)[2]
  apply (auto simp: given_disjoint_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_disjoint_declarations_def )
  done

lemma given_notion_given_binder: "given_notion_discharged given_binder_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF binder_admission_system_formed guard_binder_agreement _ _ given_notion_declarations_discharged(6)])
  apply (auto simp: given_binder_declarations_def)[2]
  apply (auto simp: given_binder_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: given_binder_declarations_def )
  done

lemma given_notion_root_family_producer: "given_notion_discharged root_family_producer_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF root_family_reading_system_formed guard_root_family_agreement _ _ root_family_producer_record_discharged])
  apply (auto simp: root_family_producer_record_def)[2]
  apply (auto simp: root_family_producer_record_def given_correspondence_unfold)[2]
  apply (auto simp: root_family_producer_record_def root_family_socket_decoded)
  done

lemma given_notion_root_family_closure: "given_notion_discharged root_family_closure_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF package_closure_admission_system_formed guard_closure_agreement _ _ root_family_closure_record_discharged])
  apply (auto simp: root_family_closure_record_def)[2]
  apply (auto simp: root_family_closure_record_def given_correspondence_unfold)[2]
  apply (auto simp: root_family_closure_record_def )
  done

lemma given_notion_root_family_bound: "given_notion_discharged root_family_bound_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF data_subset_system_formed guard_subset_agreement _ _ root_family_bound_record_discharged])
  apply (auto simp: root_family_bound_record_def)[2]
  apply (auto simp: root_family_bound_record_def given_correspondence_unfold)[2]
  apply (auto simp: root_family_bound_record_def )
  done

lemma given_notion_root_family_membership: "given_notion_discharged root_family_membership_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF package_membership_system_formed guard_membership_agreement _ _ root_family_membership_record_discharged])
  apply (auto simp: root_family_membership_record_def)[2]
  apply (auto simp: root_family_membership_record_def given_correspondence_unfold)[2]
  apply (auto simp: root_family_membership_record_def membership_socket_decoded package_membership_clauses_def)
  done

lemma given_notion_lookup: "given_notion_discharged lookup_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF artifact_lookup_system_formed guard_lookup_agreement _ _ lookup_declarations_discharged])
  apply (auto simp: lookup_declarations_def)[2]
  apply (auto simp: lookup_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: lookup_declarations_def lookup_socket_decoded)
  done

lemma given_notion_identity: "given_notion_discharged identity_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF artifact_identity_system_formed guard_identity_agreement _ _ identity_declarations_discharged])
  apply (auto simp: identity_declarations_def)[2]
  apply (auto simp: identity_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: identity_declarations_def identity_socket_decoded)
  done

lemma given_notion_comparison: "given_notion_discharged comparison_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF artifact_comparison_system_formed guard_comparison_agreement _ _ comparison_declarations_discharged])
  apply (auto simp: comparison_declarations_def)[2]
  apply (auto simp: comparison_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: comparison_declarations_def comparison_socket_decoded)
  done

lemma given_notion_fields_admission: "given_notion_discharged fields_admission_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF artifact_admission_system_formed guard_admission_agreement _ _ fields_admission_declarations_discharged])
  apply (auto simp: fields_admission_declarations_def)[2]
  apply (auto simp: fields_admission_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: fields_admission_declarations_def )
  done

lemma given_notion_headed: "given_notion_discharged headed_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF headed_material_system_formed guard_headed_agreement _ _ headed_declarations_discharged])
  apply (auto simp: headed_declarations_def)[2]
  apply (auto simp: headed_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: headed_declarations_def headed_socket_decoded)
  done

lemma given_notion_family_rows: "given_notion_discharged family_rows_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF family_admission_system_formed guard_family_agreement _ _ family_rows_declarations_discharged])
  apply (auto simp: family_rows_declarations_def)[2]
  apply (auto simp: family_rows_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: family_rows_declarations_def family_rows_socket_decoded)
  done

lemma given_notion_record_artifact: "given_notion_discharged record_artifact_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF record_admission_system_formed guard_record_agreement _ _ record_artifact_declarations_discharged])
  apply (auto simp: record_artifact_declarations_def)[2]
  apply (auto simp: record_artifact_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: record_artifact_declarations_def )
  done

lemma given_notion_target_artifact: "given_notion_discharged target_artifact_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF target_admission_system_formed guard_target_agreement _ _ target_artifact_declarations_discharged])
  apply (auto simp: target_artifact_declarations_def)[2]
  apply (auto simp: target_artifact_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: target_artifact_declarations_def )
  done

lemma given_notion_admission: "given_notion_discharged admission_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF citation_admission_system_formed guard_citation_agreement _ _ admission_declarations_discharged])
  apply (auto simp: admission_declarations_def)[2]
  apply (auto simp: admission_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: admission_declarations_def external_socket_decoded citation_admission_clauses_def)
  done

lemma given_notion_reading: "given_notion_discharged reading_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF citation_reading_system_formed guard_reading_agreement _ _ reading_declarations_discharged])
  apply (auto simp: reading_declarations_def)[2]
  apply (auto simp: reading_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: reading_declarations_def)
  done

lemma given_notion_location: "given_notion_discharged location_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF citation_location_system_formed guard_location_agreement _ _ location_declarations_discharged])
  apply (auto simp: location_declarations_def)[2]
  apply (auto simp: location_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: location_declarations_def )
  done

lemma given_notion_resolution_site: "given_notion_discharged resolution_site_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF citation_resolution_system_formed guard_resolution_agreement _ _ resolution_site_declarations_discharged])
  apply (auto simp: resolution_site_declarations_def)[2]
  apply (auto simp: resolution_site_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: resolution_site_declarations_def )
  done

lemma given_notion_interpretation: "given_notion_discharged interpretation_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF citation_interpretation_system_formed guard_interpretation_agreement _ _ interpretation_declarations_discharged])
  apply (auto simp: interpretation_declarations_def)[2]
  apply (auto simp: interpretation_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: interpretation_declarations_def interpretation_socket_decoded)
  done

lemma given_notion_projection_target: "given_notion_discharged projection_target_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF target_projection_system_formed guard_projection_agreement _ _ projection_target_declarations_discharged])
  apply (auto simp: projection_target_declarations_def)[2]
  apply (auto simp: projection_target_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: projection_target_declarations_def )
  done

lemma given_notion_binder: "given_notion_discharged binder_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF binder_admission_system_formed guard_binder_agreement _ _ binder_declarations_discharged])
  apply (auto simp: binder_declarations_def)[2]
  apply (auto simp: binder_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: binder_declarations_def binder_socket_decoded)
  done

lemma given_notion_bag_binder: "given_notion_discharged bag_binder_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF bag_comparison_system_formed guard_bag_agreement _ _ bag_binder_declarations_discharged])
  apply (auto simp: bag_binder_declarations_def)[2]
  apply (auto simp: bag_binder_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: bag_binder_declarations_def )
  done

lemma given_notion_union_binder: "given_notion_discharged union_binder_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF data_union_system_formed guard_union_agreement _ _ union_binder_declarations_discharged])
  apply (auto simp: union_binder_declarations_def)[2]
  apply (auto simp: union_binder_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: union_binder_declarations_def )
  done

lemma given_notion_instantiation_binder: "given_notion_discharged instantiation_binder_declarations given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF pattern_instantiation_system_formed guard_instantiation_agreement _ _ instantiation_binder_declarations_discharged])
  apply (auto simp: instantiation_binder_declarations_def)[2]
  apply (auto simp: instantiation_binder_declarations_def given_correspondence_unfold)[2]
  apply (auto simp: instantiation_binder_declarations_def )
  done

text \<open>
  32's kept sockets: each record holds one socket and no producer or consumer, discharged at the system where its
  clause stands.
\<close>

lemma given_notion_schema_family_socket:
  "given_notion_discharged schema_family_socket_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF schema_family_admission_system_formed guard_schema_family_agreement _ _
    schema_family_socket_record_discharged])
  apply (auto simp: schema_family_socket_record_def)[4]
  apply (auto simp: schema_family_socket_record_def schema_family_socket_decoded)
  done

lemma given_notion_callee_inclusion_socket:
  "given_notion_discharged callee_inclusion_socket_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF definition_callee_inclusion_system_formed
    guard_definition_callee_inclusion_agreement _ _ callee_inclusion_socket_record_discharged])
  apply (auto simp: callee_inclusion_socket_record_def)[4]
  apply (auto simp: callee_inclusion_socket_record_def callee_inclusion_socket_decoded)
  done

lemma given_notion_payload_audit_socket:
  "given_notion_discharged payload_audit_socket_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF payload_audit_system_formed guard_audit_agreement _ _
    payload_audit_socket_record_discharged])
  apply (auto simp: payload_audit_socket_record_def)[4]
  apply (auto simp: payload_audit_socket_record_def payload_audit_socket_decoded)
  done

lemma given_notion_clause_reading_row:
  "given_notion_discharged clause_reading_row_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF definition_clause_reading_system_formed guard_clause_reading_agreement _ _
    clause_reading_row_record_discharged])
  apply (auto simp: clause_reading_row_record_def)[4]
  apply (auto simp: clause_reading_row_record_def clause_reading_row_decoded)
  done

lemma given_notion_premise_slot_row:
  "given_notion_discharged premise_slot_row_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF schema_slot_reading_system_formed guard_schema_slot_agreement _ _
    premise_slot_row_record_discharged])
  apply (auto simp: premise_slot_row_record_def)[4]
  apply (auto simp: premise_slot_row_record_def premise_slot_row_decoded schema_slot_reading_clauses_def)
  done

lemma given_notion_schema_slot_row:
  "given_notion_discharged schema_slot_row_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF definition_slot_reading_system_formed guard_definition_slot_agreement _ _
    schema_slot_row_record_discharged])
  apply (auto simp: schema_slot_row_record_def)[4]
  apply (auto simp: schema_slot_row_record_def schema_slot_row_decoded definition_slot_reading_clauses_def)
  done

lemma given_notion_root_slot_row:
  "given_notion_discharged root_slot_row_record given_declarations_correspondence"
  apply (rule given_notion_dischargedI[OF package_slot_reading_system_formed guard_package_slot_agreement _ _
    root_slot_row_record_discharged])
  apply (auto simp: root_slot_row_record_def)[4]
  apply (auto simp: root_slot_row_record_def root_slot_row_decoded package_slot_reading_clauses_def)
  done

lemmas given_records_discharged =
  given_notion_given_bag
  given_notion_given_artifact
  given_notion_given_family
  given_notion_given_target
  given_notion_given_disjoint
  given_notion_given_binder
  given_notion_root_family_producer
  given_notion_root_family_closure
  given_notion_root_family_bound
  given_notion_root_family_membership
  given_notion_lookup
  given_notion_identity
  given_notion_comparison
  given_notion_fields_admission
  given_notion_headed
  given_notion_family_rows
  given_notion_record_artifact
  given_notion_target_artifact
  given_notion_admission
  given_notion_reading
  given_notion_location
  given_notion_resolution_site
  given_notion_interpretation
  given_notion_projection_target
  given_notion_binder
  given_notion_bag_binder
  given_notion_union_binder
  given_notion_instantiation_binder
  given_notion_schema_family_socket
  given_notion_callee_inclusion_socket
  given_notion_payload_audit_socket
  given_notion_clause_reading_row
  given_notion_premise_slot_row
  given_notion_schema_slot_row
  given_notion_root_slot_row

text \<open>
  The given's record: R6's six pieces, R6b's records of the root family and of the artifacts and citations, and 32's
  kept sockets at 71, 75, 505, 81, 104, 105 and 119, one union read by the committed search over the given's rooted
  readers.
\<close>

definition given_declarations :: "(nat,nat,nat) resolution_declarations" where
  "given_declarations = declarations_list [given_bag_declarations, given_artifact_declarations,
    given_family_declarations, given_target_declarations, given_disjoint_declarations, given_binder_declarations,
    root_family_producer_record, root_family_closure_record, root_family_bound_record, root_family_membership_record,
    lookup_declarations, identity_declarations, comparison_declarations, fields_admission_declarations,
    headed_declarations, family_rows_declarations, record_artifact_declarations, target_artifact_declarations,
    admission_declarations, reading_declarations, location_declarations, resolution_site_declarations,
    interpretation_declarations, projection_target_declarations, binder_declarations, bag_binder_declarations,
    union_binder_declarations, instantiation_binder_declarations, schema_family_socket_record,
    callee_inclusion_socket_record, payload_audit_socket_record, clause_reading_row_record, premise_slot_row_record,
    schema_slot_row_record, root_slot_row_record]"

theorem given_declarations_discharged:
  "declarations_discharged (positive_meaning given_program_system) given_declarations given_declarations_correspondence"
  "declarations_discharged (positive_meaning given_rooted_readers_system) given_declarations
    given_declarations_correspondence"
  unfolding given_declarations_def
  by (rule given_notions_carried; use given_records_discharged in auto)+

theorem given_declarations_selected:
  assumes "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
  shows "given_socket_selected S e"
  by (rule given_notions_carried(3)[OF _ assms[unfolded given_declarations_def]])
    (use given_records_discharged in auto)

end
