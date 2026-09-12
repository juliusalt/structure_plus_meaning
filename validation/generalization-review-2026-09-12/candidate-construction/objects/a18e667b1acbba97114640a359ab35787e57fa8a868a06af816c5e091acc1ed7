theory Factor_Transition_Account_Examples
  imports Factor_Transition_Accounts Factor_Transition_Examples Factor_Construction_Permission_Examples
begin

section \<open>One exact construction proof can accompany different histories\<close>

theorem one_assembly_certificate_different_histories:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and companion: "current_companion C q D r"
    and certified: "current_construction_certificate D r R s xs B W Z"
    and locus: "target_formed m"
  shows "\<exists>H0 H1. \<exists>N0 :: local_address option artifact_environment.
    \<exists>N1 :: local_address option artifact_environment. \<exists>u0 u1.
    predecessor_assembly_certificate C q D r R s H0 xs B W Z \<and>
    predecessor_assembly_certificate C q D r R s H1 xs B W Z \<and>
    generation_predecessors H0={||} \<and> generation_predecessors H1={|G|} \<and>
    generation_cause H0=generation_cause H1 \<and> generation_payload H0=generation_payload H1 \<and>
    generation_locus H0=m \<and> generation_locus H1=m \<and> H0\<noteq>H1 \<and> G\<noteq>H1 \<and>
    generation_at N0 u0 [] H0 \<and> generation_environment_closed N0 {(u0,[])} \<and>
    generation_at N1 u1 [] H1 \<and> generation_environment_closed N1 {(u1,[])}"
proof -
  have empty: "\<forall>J\<in>fset {||}. generation_formed J" by simp
  obtain H0 and N0 :: "local_address option artifact_environment" and u0 where first:
    "predecessor_assembly_certificate C q D r R s H0 xs B W Z"
    "generation_locus H0=m" "generation_predecessors H0={||}" "generation_payload H0=Whole_Artifact Z"
    "generation_at N0 u0 [] H0" "generation_environment_closed N0 {(u0,[])}"
    using predecessor_assembly_candidate_total[OF current companion certified locus empty] by blast
  have gf: "generation_formed G" using current_entry_scope_formed[OF current] by blast
  have hf: "generation_formed H0" using predecessor_assembly_certificate_account[OF first(1)] by blast
  have targets: "target_formed (generation_payload H0)" "target_formed (generation_cause H0)"
    using generation_formed_fields[OF hf] by auto
  let ?H1="Generation m {|G|} (generation_payload H0) (generation_cause H0)"
  have h1f: "generation_formed ?H1" by (rule generation_formed.formed[OF locus targets]) (use gf in simp)
  have recorded: "generation_replay_scope H0 R s"
    using first(1) by (simp add: predecessor_assembly_certificate_def)
  have retained: "generation_replay_scope ?H1 R s"
    using recorded h1f unfolding generation_replay_scope_def by auto
  have payload: "generation_payload ?H1=Whole_Artifact Z" using first(4) by simp
  have second: "predecessor_assembly_certificate C q D r R s ?H1 xs B W Z"
    using current companion certified retained payload unfolding predecessor_assembly_certificate_def by blast
  obtain N1 :: "local_address option artifact_environment" and u1 where gen:
    "generation_at N1 u1 [] ?H1" "generation_environment_closed N1 {(u1,[])}"
    using closed_generation_presentation_total[OF h1f] by blast
  have histories: "fset (generation_predecessors H0)\<noteq>fset (generation_predecessors ?H1)"
    using first(3) by simp
  have different: "H0\<noteq>?H1" using histories by metis
  have edge: "(G,?H1)\<in>predecessor_edges" by (simp add: predecessor_edges_def)
  have strict: "G\<noteq>?H1" using predecessor_size_decreases[OF edge] by (metis less_irrefl)
  show ?thesis
    by (rule exI[of _ H0], rule exI[of _ ?H1], rule exI[of _ N0], rule exI[of _ N1],
        rule exI[of _ u0], rule exI[of _ u1])
       (use first second gen different strict in simp)
qed

section \<open>Complete account material precedes its continuation and acceptance proofs\<close>

theorem universal_current_account_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and successor: "current_entry_scope_quoted_at X r A' m H z E' qu qr Q e"
    and before: "current_snapshot_at C q S" and after: "current_snapshot_at X r U"
    and trans: "transact S T (Applied U)" and history: "G\<in>fset (generation_predecessors H)"
    and assembly: "predecessor_assembly_certificate C q D a R b H xs B0 W Z"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M B K F au R' N' root.
    assembly_support_at M None [] D R N nu nr \<and> successor_material_at B None [] X M None [] \<and>
    continuation_envelope C q K S T U B None [] \<and>
    current_transition_account_at C q F au [] H K X \<and> certified_transition_account C q R' [] H K X \<and>
    replay_scope_quoted_at R' [] N' pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_environment N' pu pr=E \<and>
    native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
proof -
  obtain M B where support: "assembly_support_at M None [] D R N nu nr"
    and body: "successor_material_at B None [] X M None []"
    using predecessor_assembly_support_total[OF assembly successor remainder] by blast
  have bf: "environment_formed B" and site: "(None,[])\<in>environment_positions B"
    using successor_material_at_formed[OF body] by auto
  have sf: "snapshot_formed S" and tf: "transaction_formed T"
    using trans by (auto simp: transact_applied_iff)
  have uf: "snapshot_formed U" by (rule successful_transaction_formed[OF trans])
  obtain t where present: "continuation_value_presents S T U B None [] t"
    using continuation_value_presents_total[OF sf tf uf bf site] by blast
  have formed: "term_formed t" using continuation_value_presents_formed[OF present] by blast
  have ci: "continuation_permission_invariant P d"
    by (rule constant_entry_continuation_invariant[where b=True]) (use every in auto)
  have permitted: "factor_continues P d S T U B None []"
    using ci present every[OF formed] unfolding factor_continues_def by blast
  have companion: "current_companion C q C q" by (rule current_companion_reflexive[OF current])
  obtain L where continued: "predecessor_continuation_certificate C q C q L [] S T U B None []"
    using predecessor_continuation_presentation_total[OF current companion current before permitted present] by blast
  obtain K where envelope: "continuation_envelope C q K S T U B None []"
    using continuation_envelope_total[OF continued] by blast
  have selected: "transition_selection_certificate C q K H X"
    using trans by (simp only: transition_selection_certificate_with_material[OF envelope body successor after])
  have accounted: "transition_account_certificate C q K H X"
    using selected history assembly by (simp only: transition_account_with_material[OF current envelope body support]; blast)
  have kf: "exact_formed K" by (rule continuation_envelope_formed[OF envelope])
  have hf: "generation_formed H" using current_entry_scope_formed[OF successor] by blast
  obtain J ju jr bu br V v tail where old: "current_scope_quoted_at C q J ju jr bu br A V v tail l G p"
    using current_entry_scope_frame[OF current] by blast
  have frame: "current_frame_quoted_at C q J ju jr bu br V v tail"
    using old by (simp add: current_scope_quoted_at_def)
  have fields: "environment_formed J" "(ju,jr)\<in>environment_positions J"
    "(bu,br)\<in>environment_positions J" "environment_formed V" "(v,tail)\<in>environment_positions V"
    using current_frame_quoted_formed[OF frame] by auto
  have target: "target_formed (Whole_Artifact K)" using kf by simp
  obtain w where argument: "amendment_value_presents J ju jr bu br V v tail H (Whole_Artifact K) w"
    using amendment_value_presents_total[OF fields hf target] by blast
  have wf: "term_formed w" using amendment_value_presents_formed[OF argument] by blast
  have accepts: "factor_accepts P d J ju jr bu br V v tail H (Whole_Artifact K)"
    using every[OF wf] by (simp only: factor_acceptance_at_presentation[OF invariant argument])
  obtain F au where allowed: "current_accepts_at C q F au [] H (Whole_Artifact K)"
    and fixed: "native_package_environment F pu pr=E"
    using current_acceptance_application_total[OF current frame invariant argument] accepts by blast
  have transition: "current_transition_account_at C q F au [] H K X"
    using allowed accounted by (simp add: current_transition_account_at_def)
  obtain R' N' root where recorded: "certified_transition_account C q R' [] H K X"
    "replay_scope_quoted_at R' [] N' pu pr au [] root {}" "native_package_environment N' pu pr=E"
    "native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
    using current_transition_account_certification_total[OF current transition] by blast
  show ?thesis using support body envelope transition recorded fixed by blast
qed

section \<open>A fixed native output policy serves every future account presentation\<close>

theorem fixed_current_assembly_for_every_account_presentation:
  assumes formed_output: "exact_formed Z" and authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and> construction_permission_invariant P d \<and>
    (\<forall>xs B W t. source_constructs xs B W Z \<longrightarrow> construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W Z t \<longrightarrow>
      (\<exists>R F au root I K H. \<exists>N :: local_address option artifact_environment. \<exists>u.
        current_construction_certificate C [] R [] xs B W Z \<and>
        replay_scope_quoted_at R [] F pu [] au [] root {} \<and>
        native_package_environment F pu []=E \<and> native_application_at F au [] d t I K \<and>
        predecessor_assembly_certificate C [] C [] R [] H xs B W Z \<and>
        generation_predecessors H={|G|} \<and> generation_locus H=l \<and> G\<noteq>H \<and>
        generation_at N u [] H \<and> generation_environment_closed N {(u,[])}))"
proof -
  obtain E :: "local_address option artifact_environment" and pu P d
    where program: "closed_native_package_at E pu [] P" "d\<in>system_definitions P"
    "construction_permission_invariant P d"
    "\<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow> construction_claim_presents xs B W R t \<longrightarrow>
      schema_call_formed P d t \<and> ((d,t)\<in>positive_meaning P\<longleftrightarrow>R=Z)"
    using construction_output_native_program[OF formed_output] by blast
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P d"
    using current_entry_scope_construction[OF program(1,2) authority locus] by blast
  have companion: "current_companion C [] C []" by (rule current_companion_reflexive[OF current])
  have gf: "generation_formed G" using current_entry_scope_formed[OF current] by blast
  have predecessors: "\<forall>J\<in>fset {|G|}. generation_formed J" using gf by simp
  have every: "\<forall>xs B W t. source_constructs xs B W Z \<longrightarrow> construction_coordinates_formed B W \<longrightarrow>
      construction_claim_presents xs B W Z t \<longrightarrow>
      (\<exists>R F au root I K H. \<exists>N :: local_address option artifact_environment. \<exists>u.
        current_construction_certificate C [] R [] xs B W Z \<and>
        replay_scope_quoted_at R [] F pu [] au [] root {} \<and>
        native_package_environment F pu []=E \<and> native_application_at F au [] d t I K \<and>
        predecessor_assembly_certificate C [] C [] R [] H xs B W Z \<and>
        generation_predecessors H={|G|} \<and> generation_locus H=l \<and> G\<noteq>H \<and>
        generation_at N u [] H \<and> generation_environment_closed N {(u,[])})"
  proof (intro allI impI)
    fix xs B W t assume built: "source_constructs xs B W Z" and coords: "construction_coordinates_formed B W"
      and present: "construction_claim_presents xs B W Z t"
    have truth: "(d,t)\<in>positive_meaning P" using program(4) built coords present by blast
    have allowed: "factor_constructs P d xs B W Z"
      using truth by (simp only: factor_construction_at_presentation[OF built coords program(3) present])
    obtain R F au root I K where certificate: "current_construction_certificate C [] R [] xs B W Z"
      "replay_scope_quoted_at R [] F pu [] au [] root {}" "native_package_environment F pu []=E"
      "native_application_at F au [] d t I K"
      using current_construction_certificate_presentation_total[OF current allowed present] by blast
    obtain H and N :: "local_address option artifact_environment" and u where candidate:
      "predecessor_assembly_certificate C [] C [] R [] H xs B W Z"
      "generation_locus H=l" "generation_predecessors H={|G|}"
      "generation_at N u [] H" "generation_environment_closed N {(u,[])}"
      using predecessor_assembly_candidate_total[OF current companion certificate(1) locus predecessors] by blast
    have edge: "(G,H)\<in>predecessor_edges" using candidate(3) by (simp add: predecessor_edges_def)
    have different: "G\<noteq>H" using predecessor_size_decreases[OF edge] by auto
    show "\<exists>R F au root I K H. \<exists>N :: local_address option artifact_environment. \<exists>u.
        current_construction_certificate C [] R [] xs B W Z \<and>
        replay_scope_quoted_at R [] F pu [] au [] root {} \<and>
        native_package_environment F pu []=E \<and> native_application_at F au [] d t I K \<and>
        predecessor_assembly_certificate C [] C [] R [] H xs B W Z \<and>
        generation_predecessors H={|G|} \<and> generation_locus H=l \<and> G\<noteq>H \<and>
        generation_at N u [] H \<and> generation_environment_closed N {(u,[])}"
      using certificate candidate different by blast
  qed
  show ?thesis using current program(3) every by blast
qed

theorem an_actual_predecessor_assembly_exists:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d R H. \<exists>N :: local_address option artifact_environment. \<exists>u.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    predecessor_assembly_certificate C [] C [] R [] H [] {} empty_source_construction empty_artifact \<and>
    generation_predecessors H={|G|} \<and> G\<noteq>H \<and>
    generation_at N u [] H \<and> generation_environment_closed N {(u,[])}"
proof -
  have built: "source_constructs [] ({} :: (local_address\<times>exact_artifact) set)
      (empty_source_construction :: addressed_construction) empty_artifact"
    by (rule source_constructs_empty) (simp add: construction_sources_formed_def single_valued_def)
  have coords: "construction_coordinates_formed {} empty_source_construction"
    by (simp add: construction_coordinates_formed_def empty_source_construction_def)
  have present: "construction_claim_presents [] {} empty_source_construction empty_artifact
      (construction_claim_term [] {} empty_source_construction empty_artifact)"
    by (rule construction_claim_term_presents[OF built])
  show ?thesis using fixed_current_assembly_for_every_account_presentation[OF empty_artifact_formed authority locus]
    built coords present by blast
qed

section \<open>The earlier unchanged selection is rejected as historical succession\<close>

theorem selected_identity_need_not_have_transition_account:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d F au K R.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    current_transition_selection_at C [] F au [] G K C \<and>
    certified_transition_selection C [] R [] G K C \<and>
    \<not>current_transition_account_at C [] F au [] G K C \<and>
    \<not>certified_transition_account C [] R [] G K C"
proof -
  obtain C G p E pu P d where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P d"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    using fixed_current_selection_accepts_every_formed_material[OF authority locus] by blast
  have package: "native_package_at E pu [] P"
    using current_entry_scope_closed[OF current] by (simp add: closed_native_package_at_def)
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have site: "(pu,[])\<in>environment_positions E"
    using native_package_root_position[OF package] by blast
  obtain F au K R where selected: "current_transition_selection_at C [] F au [] G K C"
    "certified_transition_selection C [] R [] G K C"
    using universal_current_selection_total[OF current invariant _ ef site] every by blast
  have rejected: "\<not>transition_account_certificate C [] K G C"
    by (rule transition_account_unchanged_generation_rejected[OF current])
  show ?thesis using current selected rejected
    unfolding current_transition_account_at_def certified_transition_account_def by blast
qed

text \<open>
  One exact construction certificate and one exact recorded cause can accompany
  two different histories. Both candidates have actual closed generation
  presentations. Their differing predecessor fields change generation identity,
  while the complete construction account remains unchanged.

  A single closed native output policy and actual currentness frame are fixed
  before arbitrary future valid construction accounts are supplied. Every
  complete account presentation has an actual selected call, a closed replay,
  and a fresh candidate whose recorded cause matches that call exactly. The
  empty assembly supplies an explicit instance. This is an assembly witness;
  no adoption of those candidate payloads as programs or full transition
  adequacy is asserted.

  Given an actual candidate frame, matching assembly certificate, historical
  edge, and successful publication transaction, a universal current entry
  constructs the entire account material and both later proofs for every
  remaining formed scope. The supporting material is complete before its
  continuation and acceptance records are constructed.

  The earlier unchanged-selection example has actual continuation and acceptance
  proofs. It fails the historical condition of the stronger account component.
  These examples do not claim that complete dependency, comparison, or interpretation
  admission follows from a permissive ordinary policy.
\<close>

end
