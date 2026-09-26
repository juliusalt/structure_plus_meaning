theory Development_Given_Installed_Declarations
  imports Development_Given_Carried_Declarations Development_Installed_Presentations Factor_Varied_Declarations
begin

text \<open>
  The given's record carried to the installed programs (R6b of DECISIONS.md "The native evaluator constructs the
  missing witnesses by resolution", its addition "The given's remaining producers: views, carriers and narrowed
  sockets", its carrying part to the installed programs). A record the previous part discharges at the given's rooted
  readers (@{text given_notion_carried}) is relocated by the installation's placement to the placed presentation
  (@{text declarations_relocated_discharged}) and carried by the clause match to the program the native package reader
  returns at the installation (@{text declarations_varied_discharged_variant}): the given's, and every extension's.
  The record is discharged once, at its notions' systems, and carried; no clause of any program changes. The
  relocation is injective at the record's sites because every site stands in the rooted readers, which the callee
  closure from their entries shows through the notions' own clauses.
\<close>

section \<open>The record's sites stand in the rooted readers\<close>

text \<open>
  A callee of a clause of a system agreeing with the given's readers on its domain, at a rooted site, is rooted; so is
  a callee of a socket's schema of the given's record at a rooted site, the rooted readers' own clause there
  (@{thm [source] given_declarations_selected}).
\<close>

lemma given_rooted_clause_reaches:
  assumes Xf: "schema_system_formed X" and agree: "systems_agree_on X guard_readers_system (system_definitions X)"
    and member: "d \<in> system_definitions given_rooted_readers_system"
    and clause: "\<exists>c. ((d,c),S) \<in> system_clauses X" and callee: "e \<in> schema_dependencies S"
  shows "e \<in> system_definitions given_rooted_readers_system"
proof -
  obtain c where c: "((d,c),S) \<in> system_clauses X" using clause by blast
  have dX: "d \<in> system_definitions X" using Xf c unfolding schema_system_formed_def by blast
  have "d \<in> system_definitions guard_readers_system" using whole_agreement_definitions[OF agree] dX by blast
  moreover have "((d,c),S) \<in> system_clauses guard_readers_system"
    using agree dX c unfolding systems_agree_on_def by blast
  ultimately show ?thesis by (rule given_rooted_reaches[OF member _ _ callee])
qed

lemma finite_premise_callee:
  assumes "x |\<in>| fimage (\<lambda>q. fst (snd q)) (finite_schema_premises S)"
  shows "x \<in> schema_dependencies (decode_finite_schema S)"
proof -
  obtain s p where m: "(s,x,p) |\<in>| finite_schema_premises S" using assms by auto
  have "(s,x,decode_finite_pattern p) \<in> schema_premises (decode_finite_schema S)"
    using m by (force simp: decode_finite_schema_def)
  then show ?thesis by (rule schema_dependencies_premise)
qed

lemma given_socket_reaches:
  assumes sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    and member: "e \<in> system_definitions given_rooted_readers_system"
    and callee: "x \<in> schema_dependencies (decode_finite_schema S)"
  shows "x \<in> system_definitions given_rooted_readers_system"
proof -
  obtain c where "((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    using given_declarations_selected[OF sock] member by blast
  then have "((e,c),decode_finite_schema S) \<in> system_clauses given_rooted_readers_system"
    by (simp only: finite_system_clause_decoded finite_rooted_given_readers_exact)
  then show ?thesis using given_rooted_readers_formed callee unfolding schema_system_formed_def by blast
qed

lemmas given_record_defs = given_bag_declarations_def given_artifact_declarations_def given_family_declarations_def
  given_target_declarations_def given_disjoint_declarations_def given_binder_declarations_def
  root_family_producer_record_def root_family_closure_record_def root_family_bound_record_def
  root_family_membership_record_def lookup_declarations_def identity_declarations_def comparison_declarations_def
  fields_admission_declarations_def headed_declarations_def family_rows_declarations_def
  record_artifact_declarations_def target_artifact_declarations_def admission_declarations_def
  reading_declarations_def location_declarations_def resolution_site_declarations_def
  interpretation_declarations_def projection_target_declarations_def binder_declarations_def
  bag_binder_declarations_def union_binder_declarations_def instantiation_binder_declarations_def
  schema_family_socket_record_def callee_inclusion_socket_record_def payload_audit_socket_record_def
  clause_reading_row_record_def premise_slot_row_record_def schema_slot_row_record_def root_slot_row_record_def

abbreviation given_records where
  "given_records \<equiv> [given_bag_declarations, given_artifact_declarations,
    given_family_declarations, given_target_declarations, given_disjoint_declarations, given_binder_declarations,
    root_family_producer_record, root_family_closure_record, root_family_bound_record, root_family_membership_record,
    lookup_declarations, identity_declarations, comparison_declarations, fields_admission_declarations,
    headed_declarations, family_rows_declarations, record_artifact_declarations, target_artifact_declarations,
    admission_declarations, reading_declarations, location_declarations, resolution_site_declarations,
    interpretation_declarations, projection_target_declarations, binder_declarations, bag_binder_declarations,
    union_binder_declarations, instantiation_binder_declarations, schema_family_socket_record,
    callee_inclusion_socket_record, payload_audit_socket_record, clause_reading_row_record, premise_slot_row_record,
    schema_slot_row_record, root_slot_row_record]"

lemma given_declarations_records: "given_declarations = declarations_list given_records"
  by (simp only: given_declarations_def)

lemma declarations_list_socket_member:
  assumes "D \<in> set Ds" "z |\<in>| declared_sockets D"
  shows "z |\<in>| declared_sockets (declarations_list Ds)"
  using assms by (induction Ds) (auto simp: declarations_union_def no_declarations_def)

lemma declarations_list_members:
  "(d,V,hs) |\<in>| declared_producers (declarations_list Ds) \<Longrightarrow> \<exists>D\<in>set Ds. (d,V,hs) |\<in>| declared_producers D"
  "(d,e,V,i) |\<in>| declared_consumers (declarations_list Ds) \<Longrightarrow> \<exists>D\<in>set Ds. (d,e,V,i) |\<in>| declared_consumers D"
  by (induction Ds) (auto simp: declarations_union_def no_declarations_def)

lemma given_declarations_socket_of:
  assumes "\<exists>s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    and "D \<in> set given_records"
  shows "\<exists>s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
  using assms declarations_list_socket_member unfolding given_declarations_def by blast

text \<open>
  79, 82 and 83 are entries of the given's readers, 12 a read site of the registrations. 79's socket schema calls 32
  and 37, 12's 7 and 11, 7's 6, 32's 21, 29 and 31, 42's clause 36. 82's clause calls 65, whose clause calls 34, 48, 49, 54, 55 and
  64; 64's calls 63, one of 63's calls 57, whose clause calls 41 and 42. One of 55's clauses calls 50, one of 50's 40
  and 45, one of 39's 35; 45's socket schema calls 10 and 40's 39.
\<close>

lemma given_rooted_declared_sites:
  assumes "d \<in> {6,7,10,11,12,21,29,31,32,34,35,36,37,39,40,41,42,45,47,48,49,54,55,77,79,83}"
  shows "d \<in> system_definitions given_rooted_readers_system"
proof -
  let ?R = "system_definitions given_rooted_readers_system"
  have e: "77 \<in> ?R" "79 \<in> ?R" "82 \<in> ?R" "83 \<in> ?R"
    using given_rooted_entries given_rooted_members(2,3,6,7) by blast+
  have r: "12 \<in> ?R" "47 \<in> ?R" by (rule given_rooted_read_sites(1); simp)+
  have socket: "x \<in> ?R" if "\<exists>s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    "e \<in> ?R" "x \<in> schema_dependencies (decode_finite_schema S)" for e S x
    using that given_socket_reaches by blast
  have sock1: "(79,root_family_socket_schema,1,False,view_identity,root_family_view) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=root_family_producer_record])
      (simp only: list.set insert_iff simp_thms, simp add: root_family_producer_record_def)
  have sock2: "(12,identity_socket_schema,2,False,view_identity,view_identity) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=identity_declarations])
      (simp only: list.set insert_iff simp_thms, simp add: identity_declarations_def)
  have sock3: "(7,comparison_socket_schema,0,False,view_identity,view_identity) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=comparison_declarations])
      (simp only: list.set insert_iff simp_thms, simp add: comparison_declarations_def)
  have sock4: "(32,family_rows_socket_schema,0,False,headed_incidence_view,view_identity) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=family_rows_declarations])
      (simp only: list.set insert_iff simp_thms, simp add: family_rows_declarations_def)
  have sock6: "(45,given_target_socket_schema,2,False,view_identity,view_identity) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=given_target_declarations])
      (simp only: list.set insert_iff simp_thms, simp add: given_target_declarations_def)
  have sock7: "(40,interpretation_socket_schema,0,False,outer_pair_view,inner_right_view) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=interpretation_declarations])
      (simp only: list.set insert_iff simp_thms, simp add: interpretation_declarations_def)
  note sock = sock1 sock2 sock3 sock4 sock6 sock7
  have call: "32 \<in> schema_dependencies (decode_finite_schema root_family_socket_schema)"
    "37 \<in> schema_dependencies (decode_finite_schema root_family_socket_schema)"
    "7 \<in> schema_dependencies (decode_finite_schema identity_socket_schema)"
    "11 \<in> schema_dependencies (decode_finite_schema identity_socket_schema)"
    "6 \<in> schema_dependencies (decode_finite_schema comparison_socket_schema)"
    "21 \<in> schema_dependencies (decode_finite_schema family_rows_socket_schema)"
    "29 \<in> schema_dependencies (decode_finite_schema family_rows_socket_schema)"
    "31 \<in> schema_dependencies (decode_finite_schema family_rows_socket_schema)"
    "10 \<in> schema_dependencies (decode_finite_schema given_target_socket_schema)"
    "39 \<in> schema_dependencies (decode_finite_schema interpretation_socket_schema)"
    by (rule finite_premise_callee; simp add: root_family_socket_schema_def identity_socket_schema_def
      comparison_socket_schema_def family_rows_socket_schema_def 
      given_target_socket_schema_def interpretation_socket_schema_def)+
  have m79: "32 \<in> ?R" "37 \<in> ?R" using given_socket_reaches[OF sock(1) e(2)] call(1,2) by blast+
  have m12: "7 \<in> ?R" "11 \<in> ?R" using given_socket_reaches[OF sock(2) r(1)] call(3,4) by blast+
  have m7: "6 \<in> ?R" using given_socket_reaches[OF sock(3) m12(1)] call(5) by blast
  have m32: "21 \<in> ?R" "29 \<in> ?R" "31 \<in> ?R" using given_socket_reaches[OF sock(4) m79(1)] call(6,7,8) by blast+

  have m82: "65 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF definition_edge_reading_system_formed guard_edge_agreement e(3), of definition_edge_reading_schema])
      (simp_all add: schema_dependencies_def rel_ran_image definition_edge_reading_schema_def)
  have m65: "34 \<in> ?R" "48 \<in> ?R" "49 \<in> ?R" "54 \<in> ?R" "55 \<in> ?R" "64 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF schema_instantiation_system_formed guard_schema_instantiation_agreement m82, of schema_instantiation_schema];
      simp add: schema_dependencies_def rel_ran_image schema_instantiation_schema_def)+
  have m64: "63 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF premise_family_instantiation_system_formed guard_premise_family_agreement m65(6),
        of premise_family_instantiation_schema])
      (simp_all add: schema_dependencies_def rel_ran_image premise_family_instantiation_schema_def)
  have m63: "57 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF premise_rows_system_formed guard_premise_rows_agreement m64, of premise_rows_call_schema])
      (auto simp: premise_rows_clauses_def schema_dependencies_def rel_ran_image premise_rows_call_schema_def)
  have m57: "41 \<in> ?R" "42 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF prospective_instantiation_system_formed guard_prospective_agreement m63,
        of prospective_instantiation_schema];
      simp add: schema_dependencies_def rel_ran_image prospective_instantiation_schema_def)+
  have m55: "50 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF pattern_instantiation_system_formed guard_instantiation_agreement m65(5),
        of instantiation_constant_schema])
      (auto simp: pattern_instantiation_clauses_def schema_dependencies_def rel_ran_image instantiation_constant_schema_def)
  have m50: "40 \<in> ?R" "45 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF quotation_admission_system_formed guard_quotation_agreement m55, of quotation_target_schema];
      auto simp: quotation_admission_clauses_def schema_dependencies_def rel_ran_image quotation_target_schema_def)+
  have m42: "36 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF citation_reading_system_formed guard_reading_agreement m57(2),
        of citation_reading_schema])
      (simp_all add: schema_dependencies_def rel_ran_image citation_reading_schema_def)
  have m45: "10 \<in> ?R" using given_socket_reaches[OF sock(5) m50(2)] call(9) by blast
  have m40: "39 \<in> ?R" using given_socket_reaches[OF sock(6) m50(1)] call(10) by blast
  have m39: "35 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF citation_resolution_system_formed guard_resolution_agreement m40,
        of citation_resolve_local_schema])
      (auto simp: citation_resolution_clauses_def schema_dependencies_def rel_ran_image citation_resolve_local_schema_def)
  show ?thesis using assms e r m79 m12 m7 m32 m65 m57 m50 m42 m45 m40 m39 by auto
qed

text \<open>
  The sites of 32's kept sockets: 72, 81 and 505 are entries of the given's readers; 72's clause calls 71; 77's calls
  76, whose list step calls 75; 122's calls 121, whose list step calls 119; 119's second clause calls 105, whose
  socket schema calls 104. Each socket schema's callees are then reached by @{thm [source] given_socket_reaches}.
\<close>

lemma given_rooted_socket_sites:
  assumes "d \<in> {71,75,81,104,105,119,505}"
  shows "d \<in> system_definitions given_rooted_readers_system"
proof -
  let ?R = "system_definitions given_rooted_readers_system"
  have e: "72 \<in> ?R" "77 \<in> ?R" "81 \<in> ?R" "122 \<in> ?R" "505 \<in> ?R"
    using given_rooted_entries given_rooted_members(1,2,5,9,12) by blast+
  have m72: "71 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF definition_call_admission_system_formed guard_definition_call_agreement e(1),
        of definition_call_admission_schema])
      (simp_all add: schema_dependencies_def rel_ran_image definition_call_admission_schema_def)
  have m77: "76 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF package_closure_admission_system_formed guard_closure_agreement e(2),
        of package_closure_admission_schema])
      (simp_all add: schema_dependencies_def rel_ran_image package_closure_admission_schema_def)
  have m76: "75 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF definition_callee_list_system_formed guard_definition_callee_list_agreement
        m77, of "context_list_step_schema 75 76"])
      (auto simp: context_list_clauses_def schema_dependencies_def rel_ran_image context_list_step_schema_def)
  have m122: "121 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF package_retention_admission_system_formed
        guard_package_retention_agreement e(4), of package_retention_admission_schema])
      (simp_all add: schema_dependencies_def rel_ran_image package_retention_admission_schema_def)
  have m121: "119 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF package_slot_list_system_formed guard_package_slot_list_agreement m122,
        of "context_list_step_schema 119 121"])
      (auto simp: context_list_clauses_def schema_dependencies_def rel_ran_image context_list_step_schema_def)
  have m119: "105 \<in> ?R"
    by (rule given_rooted_clause_reaches[OF package_slot_reading_system_formed guard_package_slot_agreement m121,
        of package_definition_slot_schema])
      (auto simp: package_slot_reading_clauses_def schema_dependencies_def rel_ran_image
        package_definition_slot_schema_def)
  have sock: "(105,schema_slot_row_schema,2,True,view_identity,view_identity) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records
    by (rule declarations_list_socket_member[where D=schema_slot_row_record])
      (simp only: list.set insert_iff simp_thms, simp add: schema_slot_row_record_def)
  have call: "104 \<in> schema_dependencies (decode_finite_schema schema_slot_row_schema)"
    by (rule finite_premise_callee) (simp add: schema_slot_row_schema_def)
  have m105: "104 \<in> ?R" using given_socket_reaches[OF sock m119 call] .
  show ?thesis using assms e m72 m76 m121 m119 m105 by auto
qed

theorem given_declarations_sites:
  "declared_sites given_declarations \<subseteq> system_definitions given_rooted_readers_system"
proof -
  let ?R = "system_definitions given_rooted_readers_system"
  let ?A = "{6,7,10,11,12,21,29,31,32,34,35,36,37,39,40,41,42,45,47,48,49,54,55,77,79,83} :: nat set"
  let ?B = "{71,75,81,104,105,119,505} :: nat set"
  let ?S = "?A \<union> ?B"
  have site: "d \<in> ?R" if "d \<in> ?S" for d
    using that given_rooted_declared_sites[of d] given_rooted_socket_sites[of d] by blast
  have p: "d \<in> ?R" if m: "(d,V,hs) |\<in>| declared_producers given_declarations" for d V hs
  proof -
    obtain D where "D \<in> set given_records" "(d,V,hs) |\<in>| declared_producers D"
      using declarations_list_members(1)[OF m[unfolded given_declarations_records]] by blast
    then have "d \<in> ?S" by (auto simp: given_record_defs)
    then show ?thesis by (rule site)
  qed
  have c: "d \<in> ?R \<and> e \<in> ?R" if m: "(d,e,V,i) |\<in>| declared_consumers given_declarations" for d e V i
  proof -
    obtain D where "D \<in> set given_records" "(d,e,V,i) |\<in>| declared_consumers D"
      using declarations_list_members(2)[OF m[unfolded given_declarations_records]] by blast
    then have "d \<in> ?S \<and> e \<in> ?S" by (auto simp: given_record_defs)
    then show ?thesis using site by blast
  qed
  have s: "e \<in> ?R" if m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations" for e S s keep Vp Vh
  proof -
    obtain D where "D \<in> set given_records" "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
      using m[unfolded given_declarations_records] by (rule declarations_list_sockets)
    then have "e \<in> ?S" by (auto simp: given_record_defs)
    then show ?thesis by (rule site)
  qed
  have dep: "x \<in> ?R" if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    "x \<in> schema_dependencies (decode_finite_schema S)" for e S s keep Vp Vh x
    by (rule given_socket_reaches[OF that(1) s[OF that(1)] that(2)])
  show ?thesis unfolding declared_sites_def using p c s dep by fastforce
qed

section \<open>The carrying to the placed and installed presentations, once for any record\<close>

text \<open>
  A record discharged at the rooted readers, whose sites stand there, is relocated by the placement, on which the
  placement is injective, and discharged at the placed presentation; it is carried by the clause match to the
  presentation the native package reader returns at an installation, an alpha variant of the placed one, and
  discharged there. The correspondence is read back through the placement.
\<close>

definition placed_correspondence ::
    "(nat \<Rightarrow> 'e) \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow> (nat \<Rightarrow> 'i \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
      'e \<Rightarrow> 'i \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "placed_correspondence g D corr = corr \<circ> inv_into (declared_sites D) g"

abbreviation given_placed_program where
  "given_placed_program \<equiv> finite_rename_system given_readers_placement finite_rooted_given_readers"

definition installed_record where
  "installed_record D = declarations_varied given_placed_program given_installed_presentation
    (declarations_relocated given_readers_placement D)"

lemma given_placement_injective_sites:
  assumes sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
  shows "inj_on given_readers_placement (system_definitions (decode_finite_system finite_rooted_given_readers) \<union>
    declared_sites D)"
proof -
  have "system_definitions (decode_finite_system finite_rooted_given_readers) \<union> declared_sites D =
      system_definitions given_rooted_readers_system"
    using sites by (auto simp only: finite_rooted_given_readers_exact)
  then show ?thesis using given_readers_installation(3) by (simp only:)
qed

theorem installed_record_discharged:
  assumes discharged: "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    and sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
  shows "declarations_discharged (positive_meaning (decode_finite_system given_placed_program))
      (declarations_relocated given_readers_placement D) (placed_correspondence given_readers_placement D corr)"
    and "declarations_discharged (positive_meaning (decode_finite_system given_installed_presentation))
      (installed_record D) (placed_correspondence given_readers_placement D corr)"
    and "declarations_discharged (positive_meaning given_readers_program)
      (installed_record D) (placed_correspondence given_readers_placement D corr)"
proof -
  have Pf: "schema_system_formed (decode_finite_system finite_rooted_given_readers)"
    by (simp add: finite_rooted_given_readers_exact)
  have d0: "declarations_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers)) D corr"
    using discharged by (simp add: finite_rooted_given_readers_exact)
  show placed: "declarations_discharged (positive_meaning (decode_finite_system given_placed_program))
      (declarations_relocated given_readers_placement D) (placed_correspondence given_readers_placement D corr)"
    unfolding placed_correspondence_def
    by (rule declarations_relocated_discharged[OF Pf given_placement_injective_sites[OF sites] d0])
  show installed: "declarations_discharged (positive_meaning (decode_finite_system given_installed_presentation))
      (installed_record D) (placed_correspondence given_readers_placement D corr)"
    unfolding installed_record_def by (rule declarations_varied_discharged_variant[OF given_installed_presentation_variant placed])
  show "declarations_discharged (positive_meaning given_readers_program)
      (installed_record D) (placed_correspondence given_readers_placement D corr)"
    using installed by (simp only: given_installed_presentation_exact(3))
qed

text \<open>
  The exchange premise at the installed presentation is derived from the carried discharge
  (@{text finite_declared_commitment_exchanges}), at the placed one from the relocation
  (@{text finite_commitment_exchanges_relocated}); the lift premise at the installed presentation from V3's
  completeness, at the placed one from the relocation of the rooted readers' completeness.
\<close>

theorem installed_record_exchanges:
  assumes discharged: "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    and sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
    and \<kappa>: "finite_witness_construction_formed \<kappa>" and \<kappa>': "finite_witness_construction_formed \<kappa>'"
  shows "finite_registrations_premise_only \<kappa> given_installed_presentation \<Longrightarrow>
      finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment (installed_record D))
        given_installed_presentation"
    and "finite_registrations_premise_only \<kappa>' given_placed_program \<Longrightarrow>
      finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
        (finite_declared_commitment (declarations_relocated given_readers_placement D)) given_placed_program"
proof -
  show "finite_registrations_premise_only \<kappa> given_installed_presentation \<Longrightarrow>
      finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment (installed_record D))
        given_installed_presentation"
    by (rule finite_declared_commitment_exchanges[OF \<kappa> installed_record_discharged(2)[OF discharged sites]])
  have Pf: "schema_system_formed (decode_finite_system finite_rooted_given_readers)"
    by (simp add: finite_rooted_given_readers_exact)
  have d0: "declarations_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers)) D corr"
    using discharged by (simp add: finite_rooted_given_readers_exact)
  show "finite_registrations_premise_only \<kappa>' given_placed_program \<Longrightarrow>
      finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
        (finite_declared_commitment (declarations_relocated given_readers_placement D)) given_placed_program"
    by (rule finite_commitment_exchanges_relocated[OF \<kappa>' Pf given_placement_injective_sites[OF sites] d0])
qed

theorem given_installed_lifts:
  "finite_construction_lifts U (given_installed_construction n) given_installed_presentation"
  "finite_construction_lifts U' (finite_relocated_construction given_readers_placement finite_rooted_given_readers
    (finite_collection_construction given_witness_registrations n)) given_placed_program"
proof -
  show "finite_construction_lifts U (given_installed_construction n) given_installed_presentation"
    by (rule finite_construction_complete_lifts[OF given_installed_construction_complete])
  have formed: "finite_system_formed finite_rooted_given_readers"
    by (simp add: finite_system_formed_correct finite_rooted_given_readers_exact)
  have inj: "inj_on given_readers_placement (system_definitions (decode_finite_system finite_rooted_given_readers))"
    using given_readers_installation(3) by (simp add: finite_rooted_given_readers_exact)
  show "finite_construction_lifts U' (finite_relocated_construction given_readers_placement finite_rooted_given_readers
      (finite_collection_construction given_witness_registrations n)) given_placed_program"
    by (rule finite_construction_lifts_relocated[OF formed inj given_rooted_construction_complete])
qed

text \<open>
  Every socket the carried record holds comes from a socket of the record whose schema is the rooted readers' clause
  at the socket's site, relocated with it and matched to the installed clause at its placement.
\<close>

theorem installed_record_sockets:
  assumes sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
    and member: "(e',T,t,keep,Vp,Vh) |\<in>| declared_sockets (installed_record D)"
  shows "\<exists>e S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<and> e' = given_readers_placement e \<and>
    ((e',c),finite_rename_schema id id given_readers_placement S) |\<in>| finite_system_clauses given_placed_program \<and>
    ((e',c'),T) |\<in>| finite_system_clauses given_installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id given_readers_placement S) T = Some (f,h) \<and> t = h s"
proof -
  obtain S' s c c' f h where src: "(e',S',s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_relocated given_readers_placement D)"
    and placed: "((e',c),S') |\<in>| finite_system_clauses given_placed_program"
    and installed: "((e',c'),T) |\<in>| finite_system_clauses given_installed_presentation"
    and m: "finite_schema_match S' T = Some (f,h)" and t: "t = h s"
    using member unfolding installed_record_def declarations_varied_sockets_member by blast
  obtain e S where eS: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" "e' = given_readers_placement e"
    "S' = finite_rename_schema id id given_readers_placement S"
    using src by (auto simp: declarations_relocated_def)
  show ?thesis using eS placed installed m t by blast
qed

text \<open>
  Conversely no socket is dropped: a socket of the record at a clause of the rooted readers, whose socket
  identifier the clause holds, is carried to the installed clause at its placement that the match finds, the installed
  presentation being an alpha variant of the placed one.
\<close>

theorem installed_record_carries:
  assumes sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    and clause: "((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    and socket: "s \<in> schema_sockets (decode_finite_schema S)"
  shows "\<exists>c' T f h. ((given_readers_placement e,c'),T) |\<in>| finite_system_clauses given_installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id given_readers_placement S) T = Some (f,h) \<and>
    (given_readers_placement e,T,h s,keep,Vp,Vh) |\<in>| declared_sockets (installed_record D)"
proof -
  let ?g = given_readers_placement
  let ?S = "finite_rename_schema id id ?g S"
  have rs: "(?g e,?S,s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_relocated ?g D)"
    using sock by (force simp: declarations_relocated_def)
  have pc: "((?g e,c),?S) |\<in>| finite_system_clauses given_placed_program"
    using clause by (force simp: finite_rename_system_def)
  have sk: "s \<in> schema_sockets (decode_finite_schema ?S)"
    using socket by (simp add: finite_rename_schema_correct renamed_schema_sockets)
  have alpha: "system_alpha_variant (decode_finite_system given_placed_program)
      (decode_finite_system given_installed_presentation)" by (rule given_installed_presentation_variant)
  have Pf: "finite_system_formed given_placed_program" and Nf: "finite_system_formed given_installed_presentation"
    using given_installed_presentation_formed by blast+
  have pcd: "((?g e,c),decode_finite_schema ?S) \<in> system_clauses (decode_finite_system given_placed_program)"
    by (rule iffD1[OF finite_system_clause_decoded pc])
  have defined: "?g e \<in> system_definitions (decode_finite_system given_placed_program)"
    using alpha pcd unfolding system_alpha_variant_def schema_system_formed_def by blast
  obtain k where family: "schema_family_variant k (system_clause_family (decode_finite_system given_placed_program) (?g e))
      (system_clause_family (decode_finite_system given_installed_presentation) (?g e))"
    using alpha defined unfolding system_alpha_variant_def by blast
  have "(c,decode_finite_schema ?S) \<in> system_clause_family (decode_finite_system given_placed_program) (?g e)"
    using pcd by (simp only: system_clause_member)
  then obtain T0 where T0: "(k c,T0) \<in> system_clause_family (decode_finite_system given_installed_presentation) (?g e)"
      "schema_alpha_variant (decode_finite_schema ?S) T0"
    using schema_family_variant_entry[OF family] by blast
  then obtain T where T: "((?g e,k c),T) |\<in>| finite_system_clauses given_installed_presentation"
    "T0 = decode_finite_schema T" by auto
  have "finite_schema_match ?S T \<noteq> None"
    using finite_schema_match_exact(2)[OF finite_system_formed_parts(2)[OF Pf pc] finite_system_formed_parts(2)[OF Nf T(1)]]
      T0(2) T(2) by simp
  then obtain f h where m: "finite_schema_match ?S T = Some (f,h)" by auto
  have "(?g e,T,h s,keep,Vp,Vh) |\<in>| declared_sockets (installed_record D)"
    unfolding installed_record_def declarations_varied_sockets_member using rs pc sk T(1) m by blast
  then show ?thesis using T(1) m by blast
qed

section \<open>The given's record at its installed program\<close>

definition given_installed_declarations where
  "given_installed_declarations = installed_record given_declarations"

definition given_installed_correspondence where
  "given_installed_correspondence = placed_correspondence given_readers_placement given_declarations
    given_declarations_correspondence"

theorem given_installed_declarations_discharged:
  "declarations_discharged (positive_meaning (decode_finite_system given_placed_program))
    (declarations_relocated given_readers_placement given_declarations) given_installed_correspondence"
  "declarations_discharged (positive_meaning (decode_finite_system given_installed_presentation))
    given_installed_declarations given_installed_correspondence"
  "declarations_discharged (positive_meaning given_readers_program) given_installed_declarations
    given_installed_correspondence"
  unfolding given_installed_declarations_def given_installed_correspondence_def
  by (rule installed_record_discharged[OF given_declarations_discharged(2) given_declarations_sites])+

theorem given_installed_declarations_sockets:
  assumes "(e',T,t,keep,Vp,Vh) |\<in>| declared_sockets given_installed_declarations"
  shows "\<exists>e S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations \<and>
    e' = given_readers_placement e \<and> ((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<and>
    ((e',c'),T) |\<in>| finite_system_clauses given_installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id given_readers_placement S) T = Some (f,h) \<and> t = h s"
proof -
  obtain e S s c c' f h where r: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    "e' = given_readers_placement e"
    "((e',c'),T) |\<in>| finite_system_clauses given_installed_presentation"
    "finite_schema_match (finite_rename_schema id id given_readers_placement S) T = Some (f,h)" "t = h s"
    using installed_record_sockets[OF given_declarations_sites assms[unfolded given_installed_declarations_def]]
    by blast
  have "e \<in> system_definitions given_rooted_readers_system"
    using given_declarations_sites declared_sites_members(4)[OF r(1)] by blast
  then obtain c0 where "((e,c0),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    using given_declarations_selected[OF r(1)] by blast
  then show ?thesis using r by blast
qed

theorem given_installed_declarations_carried:
  assumes sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    and socket: "s \<in> schema_sockets (decode_finite_schema S)"
  shows "\<exists>c' T f h. ((given_readers_placement e,c'),T) |\<in>| finite_system_clauses given_installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id given_readers_placement S) T = Some (f,h) \<and>
    (given_readers_placement e,T,h s,keep,Vp,Vh) |\<in>| declared_sockets given_installed_declarations"
proof -
  have "e \<in> system_definitions given_rooted_readers_system"
    using given_declarations_sites declared_sites_members(4)[OF sock] by blast
  then obtain c where "((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    using given_declarations_selected[OF sock] by blast
  then show ?thesis unfolding given_installed_declarations_def by (rule installed_record_carries[OF sock _ socket])
qed

section \<open>Every extension's record at its installed program\<close>

context given_readers_extension
begin

definition extension_installed_record where
  "extension_installed_record D = declarations_varied (finite_rename_system installed_placement Q) installed_presentation
    (declarations_relocated installed_placement D)"

theorem extension_record_discharged:
  assumes discharged: "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    and sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
  shows "declarations_discharged (positive_meaning (decode_finite_system Q)) D corr"
    and "declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system installed_placement Q)))
      (declarations_relocated installed_placement D) (placed_correspondence installed_placement D corr)"
    and "declarations_discharged (positive_meaning (decode_finite_system installed_presentation))
      (extension_installed_record D) (placed_correspondence installed_placement D corr)"
    and "declarations_discharged (positive_meaning installed_program)
      (extension_installed_record D) (placed_correspondence installed_placement D corr)"
proof -
  have Qf: "schema_system_formed (decode_finite_system Q)" using target by (simp add: finite_system_formed_correct)
  have shared: "systems_agree_on given_rooted_readers_system (decode_finite_system Q)
      (system_definitions given_rooted_readers_system \<inter> system_definitions (decode_finite_system Q))"
    by (rule systems_agree_on_subdomain[OF agreement Int_lower1])
  have prods: "d \<in> system_definitions given_rooted_readers_system"
    if "(d,V,hs) |\<in>| declared_producers D" for d V hs
    using subsetD[OF sites declared_sites_members(1)[OF that]] .
  have cons: "e \<in> system_definitions given_rooted_readers_system"
    if "(d,e,V,i) |\<in>| declared_consumers D" for d e V i
    using subsetD[OF sites declared_sites_members(3)[OF that]] .
  have socks: "schema_dependencies (decode_finite_schema S) \<subseteq> system_definitions given_rooted_readers_system"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" for e S s keep Vp Vh
    using subset_trans[OF declared_sites_members(5)[OF that] sites] .
  show atQ: "declarations_discharged (positive_meaning (decode_finite_system Q)) D corr"
    by (rule declarations_shared_discharged[OF given_rooted_readers_formed Qf shared prods cons socks discharged])
  have inside: "system_definitions given_rooted_readers_system \<subseteq> system_definitions (decode_finite_system Q)"
    by (rule whole_agreement_definitions[OF agreement])
  have absorb: "system_definitions (decode_finite_system Q) \<union> declared_sites D = system_definitions (decode_finite_system Q)"
    using sites inside by blast
  have inj: "inj_on installed_placement (system_definitions (decode_finite_system Q) \<union> declared_sites D)"
    unfolding absorb by (rule installation(5))
  show placed: "declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system installed_placement Q)))
      (declarations_relocated installed_placement D) (placed_correspondence installed_placement D corr)"
    unfolding placed_correspondence_def by (rule declarations_relocated_discharged[OF Qf inj atQ])
  show installed: "declarations_discharged (positive_meaning (decode_finite_system installed_presentation))
      (extension_installed_record D) (placed_correspondence installed_placement D corr)"
    unfolding extension_installed_record_def
    by (rule declarations_varied_discharged_variant[OF installed_presentation_variant placed])
  show "declarations_discharged (positive_meaning installed_program)
      (extension_installed_record D) (placed_correspondence installed_placement D corr)"
    using installed by (simp only: installed_presentation_exact(3))
qed

theorem extension_record_exchanges:
  assumes discharged: "declarations_discharged (positive_meaning given_rooted_readers_system) D corr"
    and sites: "declared_sites D \<subseteq> system_definitions given_rooted_readers_system"
    and \<kappa>: "finite_witness_construction_formed \<kappa>"
    and only: "finite_registrations_premise_only \<kappa> installed_presentation"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment (extension_installed_record D))
    installed_presentation"
  by (rule finite_declared_commitment_exchanges[OF \<kappa> extension_record_discharged(3)[OF discharged sites] only])

theorem extension_installed_lifts:
  assumes "finite_construction_complete \<kappa> Q"
  shows "finite_construction_lifts U (installed_construction \<kappa>) installed_presentation"
  by (rule finite_construction_complete_lifts[OF installed_construction_complete[OF assms]])

end

text \<open>The given's record at the asked relation's installed guard and at the first request's installed program.\<close>

theorem asked_installed_declarations_discharged:
  "declarations_discharged (positive_meaning asked_program)
    (asked_extension.extension_installed_record given_declarations)
    (placed_correspondence asked_extension.installed_placement given_declarations given_declarations_correspondence)"
  using asked_extension.extension_record_discharged(3)[OF given_declarations_discharged(2) given_declarations_sites]
    asked_installed_presentation_exact(3) unfolding asked_installed_presentation_def by simp

theorem first_request_installed_declarations_discharged:
  "declarations_discharged (positive_meaning first_request_program)
    (first_request_extension.extension_installed_record given_declarations)
    (placed_correspondence first_request_extension.installed_placement given_declarations
      given_declarations_correspondence)"
  using first_request_extension.extension_record_discharged(3)[OF given_declarations_discharged(2)
    given_declarations_sites] first_request_installed_presentation_exact(3)
  unfolding first_request_installed_presentation_def by simp

end
