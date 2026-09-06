theory Factor_Authority_Independence
  imports Factor_Authority_Programs Factor_Certified_Authority Factor_Generation_Causes Factor_Base_Programs
    RRA_Publication_Construction
begin

section \<open>Actual adoption does not validate the adopted generation's cause\<close>

theorem adoption_can_accept_an_invalid_cause:
  assumes authority: "target_formed A" and purpose: "target_formed p"
  shows "\<exists>E :: bool artifact_environment. \<exists>u r G.
    \<exists>F :: local_address option artifact_environment. \<exists>pu au.
    generation_at E u r G \<and> generation_formed G \<and> \<not>generation_cause_valid_at E u r G \<and>
    native_application_formed F pu [] au [] \<and>
    native_adoption_judgment_at F pu [] au [] A G p"
proof -
  obtain E :: "bool artifact_environment" and u r G where gen:
    "generation_at E u r G" "generation_formed G" "\<not>generation_cause_valid_at E u r G"
    using generation_formation_does_not_validate_its_cause by blast
  obtain F :: "local_address option artifact_environment" and pu au where adopted:
    "native_application_formed F pu [] au []" "native_adoption_judgment_at F pu [] au [] A G p"
    using constant_native_adoption_application[OF authority gen(2) purpose, where b=True] by blast
  show ?thesis using gen adopted by blast
qed

theorem certified_adoption_can_accept_an_invalid_cause:
  assumes authority: "target_formed A" and purpose: "target_formed p"
  shows "\<exists>E :: bool artifact_environment. \<exists>u r G.
    \<exists>F :: local_address option artifact_environment. \<exists>pu au root.
    generation_at E u r G \<and> generation_formed G \<and> \<not>generation_cause_valid_at E u r G \<and>
    certified_adoption_at F pu [] au [] root A G p"
proof -
  obtain E :: "bool artifact_environment" and u r G and F :: "local_address option artifact_environment"
    and pu au where source: "generation_at E u r G" "generation_formed G"
    "\<not>generation_cause_valid_at E u r G" "native_adoption_judgment_at F pu [] au [] A G p"
    using adoption_can_accept_an_invalid_cause[OF authority purpose] by blast
  obtain H root where certificate: "certified_adoption_at H pu [] au [] root A G p"
    using native_adoption_certification_total[OF source(4)] by blast
  show ?thesis using source(1-3) certificate by blast
qed

section \<open>A valid retained certificate does not compel adoption\<close>

theorem certified_cause_can_be_refused:
  assumes authority: "target_formed A" and purpose: "target_formed p"
    and payload: "exact_formed R" and locus: "target_formed l"
  shows "\<exists>C. \<exists>E :: local_address option artifact_environment. \<exists>u H root.
    \<exists>F :: local_address option artifact_environment. \<exists>pu au Q d t I K.
    generation_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_environment_closed E {(u,[])} \<and>
    generation_cause_valid_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) \<and>
    certified_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) H root R \<and>
    native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
    adoption_permission_invariant Q d \<and>
    adoption_value_presents A (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) p t \<and>
    native_application_formed F pu [] au [] \<and>
    \<not>native_adoption_judgment_at F pu [] au [] A
      (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) p"
proof -
  obtain C and E :: "local_address option artifact_environment" and u H root where certified:
    "generation_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C))"
    "generation_environment_closed E {(u,[])}"
    "recorded_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) R"
    "certified_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) H root R"
    using every_formed_payload_has_a_certified_base_generation[OF payload locus] by blast
  let ?G="Generation l {||} (Whole_Artifact R) (Whole_Artifact C)"
  have valid: "generation_cause_valid_at E u [] ?G"
    using certified(3) unfolding generation_cause_valid_at_def by blast
  have formed: "generation_formed ?G" by (rule generation_at_formed[OF certified(1)])
  obtain F :: "local_address option artifact_environment" and pu au Q d t I K where refused:
    "native_package_at F pu [] Q" "native_application_at F au [] d t I K"
    "adoption_permission_invariant Q d" "adoption_value_presents A ?G p t"
    "native_application_formed F pu [] au []" "\<not>native_adoption_judgment_at F pu [] au [] A ?G p"
    using constant_native_adoption_application[OF authority formed purpose, where b=False] by blast
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ E], rule exI[of _ u], rule exI[of _ H],
        rule exI[of _ root], rule exI[of _ F], rule exI[of _ pu], rule exI[of _ au],
        rule exI[of _ Q], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use certified(1,2,4) valid refused in blast)
qed

section \<open>The same exact subject can receive opposite explicit decisions\<close>

theorem exact_subject_does_not_determine_adoption:
  assumes authority: "target_formed A" and core: "generation_formed G" and purpose: "target_formed p"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu au.
    \<exists>F :: local_address option artifact_environment. \<exists>qu bu Q d t I K.
    native_application_formed E pu [] au [] \<and>
    native_adoption_judgment_at E pu [] au [] A G p \<and>
    native_package_at F qu [] Q \<and> native_application_at F bu [] d t I K \<and>
    adoption_permission_invariant Q d \<and> adoption_value_presents A G p t \<and>
    native_application_formed F qu [] bu [] \<and> \<not>native_adoption_judgment_at F qu [] bu [] A G p"
proof -
  obtain E :: "local_address option artifact_environment" and pu au where adopted:
    "native_application_formed E pu [] au []" "native_adoption_judgment_at E pu [] au [] A G p"
    using constant_native_adoption_application[OF authority core purpose, where b=True] by blast
  obtain F :: "local_address option artifact_environment" and qu bu Q d t I K where refused:
    "native_package_at F qu [] Q" "native_application_at F bu [] d t I K"
    "adoption_permission_invariant Q d" "adoption_value_presents A G p t"
    "native_application_formed F qu [] bu []" "\<not>native_adoption_judgment_at F qu [] bu [] A G p"
    using constant_native_adoption_application[OF authority core purpose, where b=False] by blast
  show ?thesis using adopted refused by blast
qed

section \<open>Actual publications and explicit policies vary independently\<close>

lemma singleton_publication_exists:
  assumes formed: "generation_formed G"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>v P.
    publication_environment_closed F v [] P \<and> publication_snapshot P={|G|} \<and>
    snapshot_lookup (publication_snapshot P) (generation_locus G)=Some G"
proof -
  let ?P="\<lparr>publication_snapshot={|G|}, publication_dependencies={||}, publication_evidence={||}\<rparr>"
  have sf: "snapshot_formed {|G|}" using formed by (simp add: snapshot_formed_def selection_formed_def)
  have pf: "publication_formed ?P" using sf by (simp add: publication_formed_def)
  obtain F :: "local_address option artifact_environment" and v where pub: "publication_environment_closed F v [] ?P"
    using closed_publication_presentation_total[OF pf] by blast
  have selected: "snapshot_lookup {|G|} (generation_locus G)=Some G"
    by (rule snapshot_lookup_member[OF sf]) simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ ?P])
    (use pub selected in simp)
qed

theorem currentness_varies_with_publication:
  assumes authority: "target_formed A" and core: "generation_formed G" and purpose: "target_formed p"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu au.
    \<exists>F :: local_address option artifact_environment. \<exists>v P.
    \<exists>H :: local_address option artifact_environment. \<exists>w Q.
    native_adoption_judgment_at E pu [] au [] A G p \<and>
    publication_environment_closed F v [] P \<and> publication_snapshot P={|G|} \<and>
    publication_environment_closed H w [] Q \<and> publication_snapshot Q={||} \<and>
    native_current E pu [] au [] A F v [] (generation_locus G) G p \<and>
    \<not>native_current E pu [] au [] A H w [] (generation_locus G) G p"
proof -
  obtain E :: "local_address option artifact_environment" and pu au where adopted:
    "native_adoption_judgment_at E pu [] au [] A G p"
    using constant_native_adoption_application[OF authority core purpose, where b=True] by blast
  obtain F :: "local_address option artifact_environment" and v P where published:
    "publication_environment_closed F v [] P" "publication_snapshot P={|G|}"
    "snapshot_lookup (publication_snapshot P) (generation_locus G)=Some G"
    using singleton_publication_exists[OF core] by blast
  let ?Q="\<lparr>publication_snapshot={||}, publication_dependencies={||}, publication_evidence={||}\<rparr>"
  have qf: "publication_formed ?Q" by (simp add: publication_formed_def snapshot_formed_def selection_formed_def)
  obtain H :: "local_address option artifact_environment" and w where empty: "publication_environment_closed H w [] ?Q"
    using closed_publication_presentation_total[OF qf] by blast
  have current: "native_current E pu [] au [] A F v [] (generation_locus G) G p"
    using adopted published(3) by (simp add: native_current_with_publication[OF published(1)])
  have absent: "\<not>native_current E pu [] au [] A H w [] (generation_locus G) G p"
    by (simp add: native_current_with_publication[OF empty])
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ au], rule exI[of _ F],
        rule exI[of _ v], rule exI[of _ P], rule exI[of _ H], rule exI[of _ w], rule exI[of _ ?Q])
       (use adopted published(1,2) empty current absent in simp)
qed

theorem currentness_varies_with_policy:
  assumes authority: "target_formed A" and core: "generation_formed G" and purpose: "target_formed p"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>v P.
    \<exists>E :: local_address option artifact_environment. \<exists>pu au.
    \<exists>H :: local_address option artifact_environment. \<exists>qu bu Q d t I K.
    publication_environment_closed F v [] P \<and> publication_snapshot P={|G|} \<and>
    native_application_formed E pu [] au [] \<and>
    native_current E pu [] au [] A F v [] (generation_locus G) G p \<and>
    native_package_at H qu [] Q \<and> native_application_at H bu [] d t I K \<and>
    adoption_permission_invariant Q d \<and> adoption_value_presents A G p t \<and>
    native_application_formed H qu [] bu [] \<and>
    \<not>native_current H qu [] bu [] A F v [] (generation_locus G) G p"
proof -
  obtain F :: "local_address option artifact_environment" and v P where pub:
    "publication_environment_closed F v [] P" "publication_snapshot P={|G|}"
    "snapshot_lookup (publication_snapshot P) (generation_locus G)=Some G"
    using singleton_publication_exists[OF core] by blast
  obtain E :: "local_address option artifact_environment" and pu au
    and H :: "local_address option artifact_environment" and qu bu Q d t I K where decisions:
    "native_application_formed E pu [] au []" "native_adoption_judgment_at E pu [] au [] A G p"
    "native_package_at H qu [] Q" "native_application_at H bu [] d t I K"
    "adoption_permission_invariant Q d" "adoption_value_presents A G p t"
    "native_application_formed H qu [] bu []" "\<not>native_adoption_judgment_at H qu [] bu [] A G p"
    using exact_subject_does_not_determine_adoption[OF authority core purpose] by blast
  have accepted: "native_current E pu [] au [] A F v [] (generation_locus G) G p"
    using pub(3) decisions(2) by (simp add: native_current_with_publication[OF pub(1)])
  have refused: "\<not>native_current H qu [] bu [] A F v [] (generation_locus G) G p"
    using decisions(8) by (simp add: native_current_with_publication[OF pub(1)])
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ P], rule exI[of _ E],
        rule exI[of _ pu], rule exI[of _ au], rule exI[of _ H], rule exI[of _ qu],
        rule exI[of _ bu], rule exI[of _ Q], rule exI[of _ d], rule exI[of _ t],
        rule exI[of _ I], rule exI[of _ K])
       (use pub(1,2) decisions(1,3-7) accepted refused in blast)
qed

theorem certified_currentness_can_accept_an_invalid_cause:
  assumes authority: "target_formed A" and purpose: "target_formed p"
  shows "\<exists>E :: bool artifact_environment. \<exists>u r G.
    \<exists>F :: local_address option artifact_environment. \<exists>v P.
    \<exists>H :: local_address option artifact_environment. \<exists>pu au root.
    generation_at E u r G \<and> \<not>generation_cause_valid_at E u r G \<and>
    publication_environment_closed F v [] P \<and> publication_snapshot P={|G|} \<and>
    certified_current_at H pu [] au [] root A F v [] (generation_locus G) G p"
proof -
  obtain E :: "bool artifact_environment" and u r G and B :: "local_address option artifact_environment"
    and pu au where gen: "generation_at E u r G" "generation_formed G" "\<not>generation_cause_valid_at E u r G"
    and adopted: "native_adoption_judgment_at B pu [] au [] A G p"
    using adoption_can_accept_an_invalid_cause[OF authority purpose] by blast
  obtain F :: "local_address option artifact_environment" and v P where pub:
    "publication_environment_closed F v [] P" "publication_snapshot P={|G|}"
    "snapshot_lookup (publication_snapshot P) (generation_locus G)=Some G"
    using singleton_publication_exists[OF gen(2)] by blast
  have current: "native_current B pu [] au [] A F v [] (generation_locus G) G p"
    using pub(3) adopted by (simp add: native_current_with_publication[OF pub(1)])
  obtain H root where certified:
    "certified_current_at H pu [] au [] root A F v [] (generation_locus G) G p"
    using native_current_certification_total[OF current] by blast
  show ?thesis using gen(1,3) pub(1,2) certified by blast
qed

text \<open>
  These witnesses use actual finite native packages and formed applications.
  Adoption can accept a generation whose recorded cause is invalid. A retained
  adoption certificate can make that same decision. A complete closed
  generation with a retained valid base certificate can be refused by
  an admitted policy at a formed call. Even the identical authority, generation,
  and purpose data receive opposite decisions under the two supplied programs.
  Exact structural equality therefore supplies no program-independent adoption.

  Every formed core also has an actual closed publication selecting it. One
  fixed adoption decision yields currentness in that publication and no
  currentness in an actual empty publication. Holding the publication fixed,
  two formed admitted policy calls give opposite currentness decisions.
  Certified currentness can still select a generation with an invalid cause.

  Cause and certificate theories enter only here, above the raw authority and
  policy layers. These examples do not yet define or certify cross-foundation
  interpretations; their authorization remains a separate transition obligation.
\<close>

end
