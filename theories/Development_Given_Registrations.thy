theory Development_Given_Registrations
  imports Development_Given_Readers Factor_Reader_Witness_Registrations
begin

text \<open>
  The given's four witness registrations (\<open>Factor_Reader_Witness_Registrations\<close>) at the programs they are
  resolved in before the asked program: the given's readers (@{const finite_given_readers}) and the native
  request's program (@{const package_request_system}). Each registration's completeness is discharged from the
  meanings those programs state, none proved again. The construction reads a registration only at a clause of the
  program it resolves (@{thm [source] finite_collection_construction_complete_at}): the given's readers hold 77 and
  392 and neither 525 nor 561, whose clauses stand in the guard's goals program and the request's; the request's
  program holds 77 and 561 and neither 392 nor 525. 525's registration, its listing at 524 over 523, is discharged
  at the asked program, where 523--525 stand.
\<close>

text \<open>A clause of a finite program is a clause of the program it presents, at its decoded schema.\<close>

lemma finite_system_clause_decoded:
  "((d,c),S) |\<in>| finite_system_clauses P \<longleftrightarrow> ((d,c),decode_finite_schema S) \<in> system_clauses (decode_finite_system P)"
  by (auto simp: decode_finite_system_def)

lemma registration_sites:
  "registration_site bound_witness_registration=77"
  "registration_site (additions_witness_registration e l)=e"
  "registration_site merge_witness_registration=561"
  by (simp_all add: bound_witness_registration_def additions_witness_registration_def
    closure_witness_registration_def merge_witness_registration_def)

section \<open>The given's readers\<close>

text \<open>
  The six read sites the registrations' completeness asks, each meaning at the given's readers what its reader's
  system means: 82 and 113 by @{thm [source] given_edge_meaning} and @{thm [source] given_inclusion_meaning}, 5
  and 12 by @{thm [source] given_reader_meaning} at the lineage's agreements, 47 and 76 through the additions'
  system (@{thm [source] use_additions_components}); and the list site 391 over its element 390, the additions'
  own context list (@{text use_additions.listing}).
\<close>

lemma given_readers_meanings:
  "(5,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(12,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
  "(47,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(82,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(113,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
proof -
  have additions: "{47,76}\<subseteq>system_definitions use_additions_system"
    using whole_agreement_definitions[OF complete_data_additions_agreement] complete_data_addition_components(6)
    by blast
  show "(5,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    by (rule given_reader_meaning[OF bag_comparison_system_formed whole_agreement_transitive[OF
      whole_agreement_transitive[OF row_values_bag_agreement row_values_complete_data_agreement]
      complete_data_additions_agreement]]) simp
  show "(12,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    by (rule given_reader_meaning[OF artifact_identity_system_formed whole_agreement_transitive[OF
      whole_agreement_transitive[OF row_values_artifact_agreement row_values_complete_data_agreement]
      complete_data_additions_agreement]]) simp
  show "(47,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    using guard_readers_left[of 47 t] use_additions_components(4)[of t] additions by simp
  show "(76,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    using guard_readers_left[of 76 t] use_additions_components(5)[of t] additions by simp
  show "(82,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    by (rule given_edge_meaning[OF given_entry_members(6)])
  show "(113,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    by (rule given_inclusion_meaning[OF given_entry_members(8)])
qed

lemma given_readers_listing: "context_list_rule_relation (positive_meaning guard_readers_system) 390 391"
proof -
  have e: "(390,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (390,t)\<in>positive_meaning use_additions_system"
    "(391,t)\<in>positive_meaning guard_readers_system \<longleftrightarrow> (391,t)\<in>positive_meaning use_additions_system" for t
    by (rule guard_readers_left, simp)+
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule use_additions.listing.semantics.equation)
qed

subsection \<open>The registrations complete wherever the read sites mean what they mean at the given's readers\<close>

text \<open>
  The one discharge: the registrations' completeness asks the meanings at the read sites 5, 12, 47, 76, 82 and 113
  and, for the additions notion's, the listing at 391 over 390. These are discharged once, at the given's readers,
  from the readers' own systems (@{thm [source] given_readers_meanings}, @{thm [source] given_readers_listing}); a
  program meaning at those sites what the given's readers mean has the registrations complete, none proved again. A
  program agreeing with the given's readers on their common definitions and holding the read sites is one
  (@{text readers_agreement_registrations_complete}, \<open>Development_Rooted_Registrations\<close>).
\<close>

lemma read_meanings_listing:
  assumes read: "\<And>d t. d\<in>{390,391} \<Longrightarrow> (d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  shows "context_list_rule_relation (positive_meaning Q) 390 391"
proof -
  have e: "(390,t)\<in>positive_meaning Q \<longleftrightarrow> (390,t)\<in>positive_meaning guard_readers_system"
    "(391,t)\<in>positive_meaning Q \<longleftrightarrow> (391,t)\<in>positive_meaning guard_readers_system" for t
    by (simp_all only: read insert_iff simp_thms)
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule context_list_rule_relation.equation[OF given_readers_listing])
qed

theorem read_meanings_registrations_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes read: "\<And>d t. d\<in>{5,12,47,76,82,113} \<Longrightarrow>
      (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  shows "finite_registration_complete P n bound_witness_registration"
    and "finite_registration_complete P n merge_witness_registration"
    and "context_list_rule_relation (positive_meaning (decode_finite_system P)) 390 391 \<Longrightarrow>
      finite_registration_complete P n (additions_witness_registration 392 391)"
proof -
  have m: "(5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    "(12,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    "(47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    "(76,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    "(82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    "(113,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    for t
    by (simp_all only: read insert_iff simp_thms given_readers_meanings)
  show "finite_registration_complete P n bound_witness_registration"
    by (rule bound_witness_registration_complete) (simp_all only: m)
  show "finite_registration_complete P n merge_witness_registration"
    by (rule merge_witness_registration_complete) (simp_all only: m)
  show "finite_registration_complete P n (additions_witness_registration 392 391)"
    if listing: "context_list_rule_relation (positive_meaning (decode_finite_system P)) 390 391"
    by (rule additions_witness_registration_complete[where element_site=390]) (simp_all only: m listing)
qed

subsection \<open>The registrations complete there\<close>

theorem given_readers_registrations_complete:
  "finite_registration_complete finite_given_readers n bound_witness_registration"
  "finite_registration_complete finite_given_readers n (additions_witness_registration 392 391)"
  "finite_registration_complete finite_given_readers n merge_witness_registration"
proof -
  have read: "(d,t)\<in>positive_meaning (decode_finite_system finite_given_readers) \<longleftrightarrow>
      (d,t)\<in>positive_meaning guard_readers_system" for d t
    by (simp only: finite_given_readers_exact)
  show "finite_registration_complete finite_given_readers n bound_witness_registration"
    by (rule read_meanings_registrations_complete(1)) (rule read)
  show "finite_registration_complete finite_given_readers n (additions_witness_registration 392 391)"
    by (rule read_meanings_registrations_complete(3)) (rule read, simp only: finite_given_readers_exact given_readers_listing)
  show "finite_registration_complete finite_given_readers n merge_witness_registration"
    by (rule read_meanings_registrations_complete(2)) (rule read)
qed

subsection \<open>The clauses the registrations name\<close>

lemma finite_given_readers_single_clause:
  assumes single: "\<And>c T. ((d,c),T)\<in>system_clauses guard_readers_system \<longleftrightarrow> c=0 \<and> T=X"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_given_readers \<longleftrightarrow> c=0 \<and> finite_schema_of X=S"
proof -
  have formed: "schema_formed X"
    using guard_readers_formed single[of 0 X] unfolding schema_system_formed_def by blast
  have eq: "decode_finite_schema S=X \<longleftrightarrow> finite_schema_of X=S"
    by (metis decode_finite_schema_of[OF formed] decode_finite_schema_injective)
  show ?thesis
    by (simp only: finite_system_clause_decoded finite_given_readers_exact single eq)
qed

text \<open>
  A finite program agreeing with the given's readers on their common definitions holds their clauses at every
  definition both hold.
\<close>

lemma readers_agreement_finite_clauses:
  assumes agree: "systems_agree_on guard_readers_system (decode_finite_system P)
      (system_definitions guard_readers_system\<inter>system_definitions (decode_finite_system P))"
    and sites: "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions (decode_finite_system P)"
  shows "((d,c),S) |\<in>| finite_system_clauses P \<longleftrightarrow> ((d,c),S) |\<in>| finite_system_clauses finite_given_readers"
proof -
  have "((d,c),decode_finite_schema S)\<in>system_clauses (decode_finite_system P) \<longleftrightarrow>
      ((d,c),decode_finite_schema S)\<in>system_clauses guard_readers_system"
    using agree sites unfolding systems_agree_on_def by blast
  then show ?thesis by (simp only: finite_system_clause_decoded finite_given_readers_exact)
qed

text \<open>The given's readers' single clauses at 77 and 392, read from the readers' own systems.\<close>

lemma guard_closure_clause:
  "((77,c),T)\<in>system_clauses guard_readers_system \<longleftrightarrow> c=0 \<and> T=package_closure_admission_schema"
proof -
  have "77\<in>system_definitions package_closure_admission_system" by simp
  then have "((77,c),T)\<in>system_clauses package_closure_admission_system \<longleftrightarrow>
      ((77,c),T)\<in>system_clauses guard_readers_system"
    using whole_agreement_transitive[OF given_reader_agreements(2) additions_guard_agreement]
    unfolding systems_agree_on_def by blast
  then show ?thesis by simp
qed

lemma guard_additions_clause:
  "((392,c),T)\<in>system_clauses guard_readers_system \<longleftrightarrow> c=0 \<and> T=package_additions_schema 391"
proof -
  have "392\<in>system_definitions use_additions_system" by simp
  then have "((392,c),T)\<in>system_clauses use_additions_system \<longleftrightarrow> ((392,c),T)\<in>system_clauses guard_readers_system"
    using additions_guard_agreement unfolding systems_agree_on_def by blast
  then show ?thesis by (simp only: use_additions_families(3))
qed

theorem given_readers_registered_clauses:
  "((77,c),S) |\<in>| finite_system_clauses finite_given_readers \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
  "((392,c),S) |\<in>| finite_system_clauses finite_given_readers \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
  "((525,c),S) |\<notin>| finite_system_clauses finite_given_readers"
  "((561,c),S) |\<notin>| finite_system_clauses finite_given_readers"
proof -
  show "((77,c),S) |\<in>| finite_system_clauses finite_given_readers \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
    by (simp only: finite_given_readers_single_clause[OF guard_closure_clause] finite_registration_matches_def
      bound_witness_registration_def closure_witness_registration_def collection_registration.simps simp_thms)
  show "((392,c),S) |\<in>| finite_system_clauses finite_given_readers \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
    by (simp only: finite_given_readers_single_clause[OF guard_additions_clause] finite_registration_matches_def
      additions_witness_registration_def closure_witness_registration_def collection_registration.simps simp_thms)
  have absent: "((d,c),S) |\<notin>| finite_system_clauses finite_given_readers" if d: "d\<in>{525,561}" for d
  proof
    assume "((d,c),S) |\<in>| finite_system_clauses finite_given_readers"
    then have "((d,c),decode_finite_schema S)\<in>system_clauses guard_readers_system"
      by (simp only: finite_system_clause_decoded finite_given_readers_exact)
    then have "d\<in>system_definitions guard_readers_system"
      using guard_readers_formed unfolding schema_system_formed_def by blast
    then have "d<506" using guard_readers_definitions additions_below audit_below by auto
    then show False using d by simp
  qed
  show "((525,c),S) |\<notin>| finite_system_clauses finite_given_readers" by (rule absent) simp
  show "((561,c),S) |\<notin>| finite_system_clauses finite_given_readers" by (rule absent) simp
qed

subsection \<open>The construction complete and the resolver exact there\<close>

theorem given_readers_construction_complete:
  "finite_construction_complete (finite_collection_construction given_witness_registrations n) finite_given_readers"
proof (rule finite_collection_construction_complete_at)
  fix R c
  assume R: "R \<in> set given_witness_registrations"
    and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses finite_given_readers"
  show "finite_registration_complete finite_given_readers n R"
    using R clause given_readers_registrations_complete given_readers_registered_clauses(3,4) registration_sites
    by (auto simp: given_witness_registrations_def)
qed

text \<open>
  The exact forms at that construction, R5's at no commitment (@{thm [source] finite_complete_resolution_refutation_exact}),
  the construction's formation discharged (@{thm [source] finite_collection_construction_formed}), so that each leaves
  its consumer the resolution's premise alone: the registered forms ask every registration of the list complete at
  the program, which 525's is not asked to be here.
\<close>

lemmas given_readers_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_collection_construction_formed given_readers_construction_complete]

lemmas given_readers_verdict_exact =
  finite_complete_verdict_exact[OF finite_collection_construction_formed given_readers_construction_complete]

lemmas given_readers_demand_exact =
  finite_complete_demand_exact[OF finite_collection_construction_formed given_readers_construction_complete]

subsection \<open>The registrations' code, from the given's readers' own clauses\<close>

text \<open>
  A registration names its clause by @{const finite_schema_of} of its HOL schema, which has no code (the targets'
  artifacts are chosen by a description). Its code is the schema the program itself holds at the clause, read
  through the program's functional clause relation (@{const finite_relation_option}, the index notion's instance
  @{text functional_option_index}). 77's registration reads the given's readers'
  clause at 77; the additions notion's reads their clause at 392, whose list site is 391, with that callee moved to
  the registration's list site (@{const finite_rename_schema}, whose decoding is @{const rename_schema}). Each code
  equation is proved equal to the registration's definition; no schema is written out.
\<close>

lemma package_additions_schema_formed: "schema_formed (package_additions_schema l)"
  by (auto simp: package_additions_schema_def schema_formed_def schema_dependencies_def
    single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_additions_schema_callee:
  "finite_rename_schema id id (\<lambda>d. if d=391 then l else d) (finite_schema_of (package_additions_schema 391))=
    finite_schema_of (package_additions_schema l)"
proof -
  have "rename_schema id id (\<lambda>d. if d=391 then l else d) (package_additions_schema 391)=package_additions_schema l"
    by (simp add: rename_schema_def map_socket_graph_def package_additions_schema_def rename_pattern_identity)
  then have "decode_finite_schema (finite_rename_schema id id (\<lambda>d. if d=391 then l else d)
      (finite_schema_of (package_additions_schema 391)))=decode_finite_schema (finite_schema_of (package_additions_schema l))"
    by (simp only: finite_rename_schema_correct decode_finite_schema_of[OF package_additions_schema_formed])
  then show ?thesis by (simp only: decode_finite_schema_injective)
qed

lemma given_readers_registration_schemas:
  "finite_relation_option (finite_system_clauses finite_given_readers) (77,0)=
    Some (finite_schema_of package_closure_admission_schema)"
  "finite_relation_option (finite_system_clauses finite_given_readers) (392,0)=
    Some (finite_schema_of (package_additions_schema 391))"
proof -
  have functional: "finite_relation_functional (finite_system_clauses finite_given_readers)"
    using finite_given_readers_formed by (simp add: finite_system_formed_def)
  show "finite_relation_option (finite_system_clauses finite_given_readers) (77,0)=
      Some (finite_schema_of package_closure_admission_schema)"
    "finite_relation_option (finite_system_clauses finite_given_readers) (392,0)=
      Some (finite_schema_of (package_additions_schema 391))"
    by (simp_all only: finite_relation_option_correct[OF functional])
      (simp_all add: given_readers_registered_clauses finite_registration_matches_def
        bound_witness_registration_def additions_witness_registration_def closure_witness_registration_def)
qed

lemma given_readers_registrations_code [code]:
  "bound_witness_registration=\<lparr>registration_site=77,
    registration_schema=the (finite_relation_option (finite_system_clauses finite_given_readers) (77,0)),
    registration_variable=2,
    registration_families=Single_Family (closure_witness_family 0 1)\<rparr>"
  "additions_witness_registration e l=\<lparr>registration_site=e,
    registration_schema=finite_rename_schema id id (\<lambda>d. if d=391 then l else d)
      (the (finite_relation_option (finite_system_clauses finite_given_readers) (392,0))),registration_variable=5,
    registration_families=Single_Family (closure_witness_family 1 4)\<rparr>"
  by (simp_all only: given_readers_registration_schemas package_additions_schema_callee option.sel
    bound_witness_registration_def additions_witness_registration_def closure_witness_registration_def)

export_code bound_witness_registration additions_witness_registration finite_given_readers checking SML

section \<open>The native request's program\<close>

text \<open>
  Below 560 the request's program means what the package retention admission means
  (@{thm [source] package_request_lower}), and that is what the given's readers mean there
  (@{thm [source] given_retention_meaning}); the six read sites are the given's readers' and mean there what they
  mean at the given's readers. A finite program presenting it is the one the request at the given relocates.
\<close>

lemma request_given_meaning:
  assumes "d\<in>system_definitions package_retention_admission_system"
  shows "(d,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  using package_request_lower[OF assms, of t] given_retention_meaning[OF assms, of t] by simp

lemma request_readers_meanings:
  "(5,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(12,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
  "(47,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(82,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(113,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
proof -
  have m: "d\<in>system_definitions package_retention_admission_system" if "d\<in>{5,12,47,76,82,113}" for d
    using that by auto
  show "(5,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    "(12,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    "(47,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    "(76,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    "(82,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    "(113,t)\<in>positive_meaning package_request_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    by (simp_all only: request_given_meaning[OF m] given_readers_meanings insert_iff simp_thms)
qed

theorem request_registrations_complete:
  assumes presented: "decode_finite_system P = package_request_system"
  shows "finite_registration_complete P n merge_witness_registration"
    and "finite_registration_complete P n bound_witness_registration"
    and "finite_construction_complete (finite_collection_construction given_witness_registrations n) P"
proof -
  have m: "d\<in>system_definitions package_retention_admission_system" if "d\<in>{5,12,47,76,82,113}" for d
    using that by auto
  show merge: "finite_registration_complete P n merge_witness_registration"
    by (rule read_meanings_registrations_complete(2)) (simp only: presented request_given_meaning[OF m])
  show bound: "finite_registration_complete P n bound_witness_registration"
    by (rule read_meanings_registrations_complete(1)) (simp only: presented request_given_meaning[OF m])
  have below: "system_definitions package_retention_admission_system\<subseteq>{..<390}"
    using whole_agreement_definitions[OF given_retention_complete_agreement] complete_below by blast
  have absent: "((d,c),S) |\<notin>| finite_system_clauses P" if d: "d\<in>{392,525}" for d c S
  proof
    assume "((d,c),S) |\<in>| finite_system_clauses P"
    then have "((d,c),decode_finite_schema S)\<in>system_clauses package_request_system"
      by (simp only: finite_system_clause_decoded presented)
    then have "d\<in>system_definitions package_request_system"
      using package_request_system_formed unfolding schema_system_formed_def by blast
    then have "d\<in>insert 561 (insert 560 (system_definitions package_retention_admission_system))"
      by (simp only: package_request_definitions package_request_list_definitions)
    then show False using d below by auto
  qed
  show "finite_construction_complete (finite_collection_construction given_witness_registrations n) P"
  proof (rule finite_collection_construction_complete_at)
    fix R c
    assume R: "R \<in> set given_witness_registrations"
      and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses P"
    show "finite_registration_complete P n R"
      using R clause merge bound absent[of 392] absent[of 525] registration_sites
      by (auto simp: given_witness_registrations_def)
  qed
qed

end
