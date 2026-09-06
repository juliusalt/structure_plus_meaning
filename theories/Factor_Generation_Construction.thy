theory Factor_Generation_Construction
  imports Factor_Certified_Recorded_Cause RRA_Generation_Construction
begin

section \<open>Constructing an actual generation for a recorded account\<close>

theorem recorded_generation_presentation_total:
  fixes F :: "local_address option artifact_environment"
  assumes quote: "judgment_value_quoted_at C r F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and judged: "construction_judgment_at F pu pr au ar xs B W R"
    and locus: "target_formed l" and predecessors: "\<forall>G\<in>fset P. generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u.
    generation_at E u [] (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,r))) \<and>
    generation_environment_closed E {(u,[])} \<and>
    recorded_construction_cause_at E u []
      (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,r))) xs B W R"
proof -
  have built: "source_constructs xs B W R"
    using judged unfolding construction_judgment_at_def factor_constructs_def by blast
  have rf: "exact_formed R" by (rule source_construction_finite(7)[OF built])
  have anchor: "anchor_formed (C,r)" by (rule judgment_value_quoted_anchor[OF quote])
  let ?G = "Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,r))"
  have gf: "generation_formed ?G"
    by (rule generation_formed.formed[OF locus _ _ predecessors]) (use rf anchor in simp_all)
  obtain E :: "local_address option artifact_environment" and u
    where gen: "generation_at E u [] ?G" and closed: "generation_environment_closed E {(u,[])}"
    using closed_generation_presentation_total[OF gf] by blast
  have cause: "generation_cause ?G=Occurrence_Anchor (C,r)" by simp
  have scope: "generation_judgment_scope_at E u [] ?G F pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF gen cause quote])
  have valid: "recorded_construction_cause_at E u [] ?G xs B W R"
    using recorded_construction_cause_with_scope[OF scope] canonical judged by simp
  show ?thesis using gen closed valid by blast
qed

section \<open>Native construction, generation recording, and separate certification\<close>

theorem native_construction_generation_total:
  fixes E :: "local_address option artifact_environment"
  assumes judged: "construction_judgment_at E pu pr au ar xs B W R"
    and locus: "target_formed l" and predecessors: "\<forall>G\<in>fset P. generation_formed G"
  shows "\<exists>F C. \<exists>A :: local_address option artifact_environment. \<exists>u H root.
    judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    generation_at A u [] (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))) \<and>
    generation_environment_closed A {(u,[])} \<and>
    recorded_construction_cause_at A u []
      (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))) xs B W R \<and>
    certified_recorded_cause_at A u []
      (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))) H root xs B W R"
proof -
  obtain F C where quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and kept: "construction_judgment_at F pu pr au ar xs B W R"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using construction_judgment_recordable[OF judged] by blast
  let ?G = "Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))"
  obtain A :: "local_address option artifact_environment" and u
    where gen: "generation_at A u [] ?G" and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_construction_cause_at A u [] ?G xs B W R"
    using recorded_generation_presentation_total[OF quote canonical kept locus predecessors] by blast
  obtain H root where certified: "certified_recorded_cause_at A u [] ?G H root xs B W R"
    using recorded_construction_certification_total[OF valid] by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ C], rule exI[of _ A],
      rule exI[of _ u], rule exI[of _ H], rule exI[of _ root])
    (use quote canonical program gen closed valid certified in blast)
qed

text \<open>
  An existing admitted native construction supplies a complete minimal recorded
  scope. Its exact quotation can be cited by an actual generation with the
  stated locus, predecessor cores, and constructed payload. The generation
  environment is closed by its own grammar, and its proof certificate retains
  the exact recorded scope separately.

  The construction account keeps its input occurrences and semantic dependencies.
  The predecessor field keeps historical membership. No equation identifies
  these boundaries, and this result supplies no continuation or adoption policy.
  Native construction admission remains an explicit premise of the source
  judgment; a single replay does not establish presentation invariance.
\<close>

end
