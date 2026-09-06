theory Factor_Program_Generation_Causes
  imports Factor_Generation_Programs Factor_Generation_Construction Factor_Base_Programs Factor_Generation_Causes
begin

section \<open>Program payloads retain the existing base and construction accounts\<close>

theorem native_program_base_generation_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and locus: "target_formed l"
  shows "\<exists>C D. \<exists>A :: local_address option artifact_environment. \<exists>u H root.
    program_scope_quoted_at C [] (native_package_environment E pu pr) pu pr P \<and>
    generation_at A u [] (Generation l {||} (Whole_Artifact C) (Whole_Artifact D)) \<and>
    generation_environment_closed A {(u,[])} \<and>
    generation_program_scope (Generation l {||} (Whole_Artifact C) (Whole_Artifact D))
      (native_package_environment E pu pr) pu pr P \<and>
    recorded_base_cause_at A u [] (Generation l {||} (Whole_Artifact C) (Whole_Artifact D)) C \<and>
    certified_base_cause_at A u [] (Generation l {||} (Whole_Artifact C) (Whole_Artifact D)) H root C"
proof -
  obtain C where formed: "exact_formed C"
    and quote: "program_scope_quoted_at C [] (native_package_environment E pu pr) pu pr P"
    using program_scope_quoted_total[OF package] by blast
  obtain D and A :: "local_address option artifact_environment" and u H root where
    gen: "generation_at A u [] (Generation l {||} (Whole_Artifact C) (Whole_Artifact D))"
    and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_base_cause_at A u [] (Generation l {||} (Whole_Artifact C) (Whole_Artifact D)) C"
    and certified: "certified_base_cause_at A u []
      (Generation l {||} (Whole_Artifact C) (Whole_Artifact D)) H root C"
    using every_formed_payload_has_a_certified_base_generation[OF formed locus] by blast
  have scope: "generation_program_scope (Generation l {||} (Whole_Artifact C) (Whole_Artifact D))
    (native_package_environment E pu pr) pu pr P"
    by (rule generation_program_scope_from_payload[OF generation_at_formed[OF gen] _ quote]) simp
  show ?thesis using quote gen closed scope valid certified by blast
qed

theorem constructed_program_generation_total:
  fixes E :: "local_address option artifact_environment"
  assumes quote: "program_scope_quoted_at C q F pu pr P"
    and judged: "construction_judgment_at E xu xr au ar xs B W C"
    and locus: "target_formed l" and predecessors: "\<forall>G\<in>fset V. generation_formed G"
  shows "\<exists>D. \<exists>A :: local_address option artifact_environment. \<exists>u H root.
    generation_at A u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D)) \<and>
    generation_environment_closed A {(u,[])} \<and>
    generation_program_scope (Generation l V (Whole_Artifact C) (Whole_Artifact D)) F pu pr P \<and>
    recorded_construction_cause_at A u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D)) xs B W C \<and>
    certified_recorded_cause_at A u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D)) H root xs B W C"
proof -
  obtain D and A :: "local_address option artifact_environment" and u H root where
    gen: "generation_at A u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D))"
    and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_construction_cause_at A u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D)) xs B W C"
    and certified: "certified_recorded_cause_at A u []
      (Generation l V (Whole_Artifact C) (Whole_Artifact D)) H root xs B W C"
    using native_construction_generation_total[OF judged locus predecessors] by blast
  have scope: "generation_program_scope (Generation l V (Whole_Artifact C) (Whole_Artifact D)) F pu pr P"
    by (rule generation_program_scope_from_payload[OF generation_at_formed[OF gen] _ quote]) simp
  show ?thesis using gen closed scope valid certified by blast
qed

theorem program_payload_does_not_validate_cause:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and locus: "target_formed l"
  shows "\<exists>A :: local_address option artifact_environment. \<exists>u G.
    generation_at A u [] G \<and> generation_environment_closed A {(u,[])} \<and>
    generation_program_scope G (native_package_environment E pu pr) pu pr P \<and>
    \<not>generation_cause_valid_at A u [] G"
proof -
  obtain C where formed: "exact_formed C"
    and quote: "program_scope_quoted_at C [] (native_package_environment E pu pr) pu pr P"
    using program_scope_quoted_total[OF package] by blast
  let ?G="Generation l {||} (Whole_Artifact C) (Whole_Artifact empty_artifact)"
  have gf: "generation_formed ?G" by (rule generation_formed.formed[OF locus]) (use formed in simp_all)
  obtain A :: "local_address option artifact_environment" and u
    where gen: "generation_at A u [] ?G" and closed: "generation_environment_closed A {(u,[])}"
    using closed_generation_presentation_total[OF gf] by blast
  have scope: "generation_program_scope ?G (native_package_environment E pu pr) pu pr P"
    by (rule generation_program_scope_from_payload[OF gf _ quote]) simp
  have invalid: "\<not>generation_cause_valid_at A u [] ?G"
    by (rule empty_cause_is_not_valid) simp
  show ?thesis using gen closed scope invalid by blast
qed

text \<open>
  Every actual program has a complete scope payload and an actual closed base
  generation admitted by an explicit finite policy, with separate retained
  certification. An admitted construction of such a payload likewise produces
  an actual closed generation retaining the original complete construction
  account and certificate. Neither result selects an authority or compels
  adoption. The program admitting or constructing the payload need not equal
  the program carried by it.

  Conversely, every actual program can occur in a formed generation with an
  invalid cause. Recovering the whole program scope from a payload supplies
  its exact identity; validity of the account remains an independent judgment.
\<close>

end
