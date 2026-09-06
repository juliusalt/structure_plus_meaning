theory Factor_Generation_Replay_Causes
  imports Factor_Replay_Scopes Factor_Certified_Recorded_Cause RRA_Generation_Construction
begin

section \<open>The recorded cause is the exact minimal scope of a separate replay\<close>

definition generation_replay_scope ::
  "generation_core \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_replay_scope G R s \<longleftrightarrow> generation_formed G \<and>
    (\<exists>F pu pr au ar root J j.
      replay_scope_quoted_at R s F pu pr au ar root {} \<and> generation_cause G=Whole_Artifact J \<and>
      judgment_value_quoted_at J j (native_judgment_environment F pu pr au ar) pu pr au ar)"

theorem generation_replay_scope_with_record:
  assumes scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
  shows "generation_replay_scope G R s \<longleftrightarrow> generation_formed G \<and>
    (\<exists>J j. generation_cause G=Whole_Artifact J \<and>
      judgment_value_quoted_at J j (native_judgment_environment F pu pr au ar) pu pr au ar)"
proof
  assume "generation_replay_scope G R s"
  then obtain M qu qr bu br other J j where fields: "generation_formed G"
    "replay_scope_quoted_at R s M qu qr bu br other {}" "generation_cause G=Whole_Artifact J"
    "judgment_value_quoted_at J j (native_judgment_environment M qu qr bu br) qu qr bu br"
    unfolding generation_replay_scope_def by blast
  have same: "M=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
    using replay_scope_whole_unique[OF fields(2) scope] by blast
  show "generation_formed G \<and>
    (\<exists>J j. generation_cause G=Whole_Artifact J \<and>
      judgment_value_quoted_at J j (native_judgment_environment F pu pr au ar) pu pr au ar)"
    using fields(1,3,4) same by blast
next
  assume "generation_formed G \<and>
    (\<exists>J j. generation_cause G=Whole_Artifact J \<and>
      judgment_value_quoted_at J j (native_judgment_environment F pu pr au ar) pu pr au ar)"
  then show "generation_replay_scope G R s" using scope unfolding generation_replay_scope_def by blast
qed

theorem generation_replay_same_cause:
  assumes first: "generation_replay_scope G R s"
    and second: "generation_replay_scope H S a"
    and left: "replay_scope_quoted_at R s F pu pr au ar root {}"
    and right: "replay_scope_quoted_at S a M qu qr bu br other {}"
    and cause: "generation_cause G=generation_cause H"
  shows "native_judgment_environment F pu pr au ar=native_judgment_environment M qu qr bu br \<and>
    pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
proof -
  obtain J j where l: "generation_cause G=Whole_Artifact J"
    "judgment_value_quoted_at J j (native_judgment_environment F pu pr au ar) pu pr au ar"
    using first by (simp only: generation_replay_scope_with_record[OF left]; blast)
  obtain K k where r: "generation_cause H=Whole_Artifact K"
    "judgment_value_quoted_at K k (native_judgment_environment M qu qr bu br) qu qr bu br"
    using second by (simp only: generation_replay_scope_with_record[OF right]; blast)
  have same: "K=J" using l(1) r(1) cause by simp
  have read: "judgment_value_quoted_at J k (native_judgment_environment M qu qr bu br) qu qr bu br"
    using r(2) same by simp
  show ?thesis using judgment_value_whole_unique[OF l(2) read] by blast
qed

lemma construction_judgment_minimal_scope:
  assumes package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "construction_judgment_at (native_judgment_environment F pu pr au ar) pu pr au ar xs B W Z
    \<longleftrightarrow>construction_judgment_at F pu pr au ar xs B W Z"
  by (simp only: construction_judgment_with_reads[OF native_judgment_environment_recovers(1,2)[OF package app]]
    construction_judgment_with_reads[OF package app])

theorem generation_replay_construction:
  assumes recorded: "generation_replay_scope G R s"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
    and judged: "construction_judgment_at F pu pr au ar xs B W Z"
    and payload: "generation_payload G=Whole_Artifact Z"
    and gen: "generation_at E gu gr G"
  shows "certified_recorded_cause_at E gu gr G F root xs B W Z"
proof -
  obtain P d t I K where read: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    using judged unfolding construction_judgment_at_def by blast
  let ?M="native_judgment_environment F pu pr au ar"
  obtain J j where cause: "generation_cause G=Whole_Artifact J"
    and quote: "judgment_value_quoted_at J j ?M pu pr au ar"
    using recorded by (simp only: generation_replay_scope_with_record[OF scope]; blast)
  have source: "generation_judgment_scope_at E gu gr G ?M pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF gen cause quote])
  have canonical: "?M=native_judgment_environment ?M pu pr au ar"
    using native_judgment_environment_idempotent[OF read] by simp
  have kept: "native_package_at ?M pu pr P" "native_application_at ?M au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF read] by blast+
  have claim: "construction_claim_presents xs B W Z t" "factor_constructs P d xs B W Z"
    using construction_judgment_with_reads[OF read] judged by blast+
  have replay: "native_replay_at F pu pr au ar root {}" using scope by (simp add: replay_scope_quoted_at_def)
  have certified: "certified_construction_at F pu pr au ar root xs B W Z"
    using claim replay by (simp only: certified_construction_exact_join[OF read])
  have included: "environment_included ?M F" by (rule native_judgment_environment_included)
  show ?thesis unfolding certified_recorded_cause_at_def
    by (rule exI[of _ ?M], rule exI[of _ pu], rule exI[of _ pr], rule exI[of _ au], rule exI[of _ ar],
        rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use source canonical payload kept included certified in blast)
qed

theorem generation_replay_construction_sound:
  assumes "generation_replay_scope G R s" "replay_scope_quoted_at R s F pu pr au ar root {}"
    "construction_judgment_at F pu pr au ar xs B W Z" "generation_payload G=Whole_Artifact Z"
    "generation_at E gu gr G"
  shows "recorded_construction_cause_at E gu gr G xs B W Z"
  by (rule certified_recorded_cause_sound[OF generation_replay_construction[OF assms]])

section \<open>A proof can be retained separately for every proposed history\<close>

theorem generation_replay_scope_total:
  assumes scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
    and payload: "exact_formed Z" and locus: "target_formed l"
    and predecessors: "\<forall>G\<in>fset V. generation_formed G"
  shows "\<exists>H. \<exists>E :: local_address option artifact_environment. \<exists>u.
    generation_replay_scope H R s \<and> generation_locus H=l \<and> generation_predecessors H=V \<and>
    generation_payload H=Whole_Artifact Z \<and>
    generation_at E u [] H \<and> generation_environment_closed E {(u,[])}"
proof -
  obtain P d t I K where read: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    using scope unfolding replay_scope_quoted_at_def native_replay_at_def by blast
  let ?M="native_judgment_environment F pu pr au ar"
  have kept: "native_package_at ?M pu pr P" "native_application_at ?M au ar d t I K" "environment_formed ?M"
    using native_judgment_environment_recovers[OF read] by blast+
  have sites: "(pu,pr)\<in>environment_positions ?M" "(au,ar)\<in>environment_positions ?M"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain J where quote: "judgment_value_quoted_at J [] ?M pu pr au ar"
    using judgment_value_quoted_total[OF kept(3) sites] by blast
  have jf: "exact_formed J" using judgment_value_quoted_formed[OF quote] by blast
  let ?H="Generation l V (Whole_Artifact Z) (Whole_Artifact J)"
  have formed: "generation_formed ?H"
    by (rule generation_formed.formed[OF locus _ _ predecessors]) (use payload jf in simp_all)
  have recorded: "generation_replay_scope ?H R s"
    using formed quote by (simp only: generation_replay_scope_with_record[OF scope]; auto)
  obtain E :: "local_address option artifact_environment" and u where gen:
    "generation_at E u [] ?H" "generation_environment_closed E {(u,[])}"
    using closed_generation_presentation_total[OF formed] by blast
  show ?thesis by (rule exI[of _ ?H], rule exI[of _ E], rule exI[of _ u])
    (use recorded gen in simp)
qed

text \<open>
  The generation's cause contains the complete minimal program-and-call scope.
  The separate replay may retain more material because it also retains proof.
  Equality of those minimal scopes is required exactly; agreement only on the
  decoded construction account or program value would be insufficient.

  Equal recorded causes recover equal complete call scopes even when their
  proofs differ. For an actual construction of the generation's exact payload,
  this join recovers the existing certified recorded-cause relation in every
  outer presentation of that generation. No evidence field is added to its
  identity.

  Any formed locus and finite formed predecessor family can accompany a
  recordable call. The scope relation alone assigns no construction role to
  that call, no relation between its output and the payload, and no historical
  or authority permission. Those conditions belong to their separate joins.
\<close>

end
