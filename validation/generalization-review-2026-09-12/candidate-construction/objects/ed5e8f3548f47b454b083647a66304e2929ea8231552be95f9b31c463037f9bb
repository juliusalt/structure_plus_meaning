theory Factor_Continuation_Selection_Examples
  imports Factor_Predecessor_Continuation Factor_Amendment_Programs
begin

section \<open>One adoption policy can select distinct entries of the same generation\<close>

theorem current_companion_pair_total:
  assumes closed: "closed_native_package_at E pu pr P"
    and members: "d\<in>system_definitions P" "e\<in>system_definitions P"
    and authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C D G p z. current_entry_scope_quoted_at C [] A l G p E pu pr P d \<and>
    current_entry_scope_quoted_at D [] A l G z E pu pr P e \<and> current_companion C [] D []"
proof -
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have fixed: "native_package_environment E pu pr=E" by (rule native_package_closed_environment_fixed[OF closed])
  have addresses: "octets_formed (snd d)" "octets_formed (snd e)"
    using native_package_definition_anchor[OF package members(1)]
      native_package_definition_anchor[OF package members(2)]
    by (auto simp: anchor_formed_def exact_formed_def)
  obtain p z where purposes: "purpose_entry p d" "purpose_entry z e"
    using purpose_entry_total[OF addresses(1)] purpose_entry_total[OF addresses(2)] by blast
  have pf: "target_formed p" and zf: "target_formed z" using purpose_entry_formed purposes by blast+
  obtain B where payload: "exact_formed B" "program_scope_quoted_at B [] E pu pr P"
    using program_scope_quoted_total[OF package] fixed by auto
  let ?G="Generation l {||} (Whole_Artifact B) (Whole_Artifact empty_artifact)"
  have gf: "generation_formed ?G" by (rule generation_formed.formed) (use locus payload(1) in auto)
  have program: "generation_program_scope ?G E pu pr P"
    by (rule generation_program_scope_from_payload[OF gf _ payload(2)]) simp
  obtain K :: "local_address option artifact_environment" and qu Q h where policy:
    "closed_native_package_at K qu [] Q" "h\<in>system_definitions Q"
    "adoption_permission_invariant Q h"
    "\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q h t \<and> ((h,t)\<in>positive_meaning Q\<longleftrightarrow>True)"
    using constant_adoption_program[of True] by blast
  obtain t x where presentations: "adoption_value_presents A ?G p t" "adoption_value_presents A ?G z x"
    using adoption_value_presents_total[OF authority gf pf]
      adoption_value_presents_total[OF authority gf zf] by blast
  have decisions: "(h,t)\<in>positive_meaning Q" "(h,x)\<in>positive_meaning Q"
    using policy(4)[rule_format, OF presentations(1)] policy(4)[rule_format, OF presentations(2)] by auto
  have first_allowed: "factor_adopts Q h A ?G p" and second_allowed: "factor_adopts Q h A ?G z"
    using policy(3) presentations decisions unfolding factor_adopts_def by blast+
  have policy_package: "native_package_at K qu [] Q" using policy(1) by (simp add: closed_native_package_at_def)
  obtain H au I J where native: "native_package_at H qu [] Q" "native_application_at H au [] h t I J"
    "native_adoption_judgment_at H qu [] au [] A ?G p"
    using native_adoption_application_total[OF policy_package policy(2,3) presentations(1)] first_allowed by blast
  obtain N :: "local_address option artifact_environment" and v V where publication:
    "publication_environment_closed N v [] V"
    "snapshot_lookup (publication_snapshot V) (generation_locus ?G)=Some ?G"
    using singleton_publication_exists[OF gf] by blast
  have current: "native_current H qu [] au [] A N v [] l ?G p"
    using native(3) publication(2) by (simp add: native_current_with_publication[OF publication(1)])
  obtain C where frame: "current_program_scope_quoted_at C [] A l ?G p E pu pr P"
    "current_scope_quoted_at C [] (native_judgment_environment H qu [] au []) qu [] au [] A N v [] l ?G p"
    using current_program_scope_quoted_total[OF current program] by blast
  have entry: "current_entry_scope_quoted_at C [] A l ?G p E pu pr P d"
    using frame(1) purposes(1) members(1) by (simp add: current_entry_scope_quoted_at_def)
  have kept: "native_package_at (native_judgment_environment H qu [] au []) qu [] Q"
    "native_application_at (native_judgment_environment H qu [] au []) au [] h t I J"
    using native_judgment_environment_recovers(1,2)[OF native(1,2)] by blast+
  obtain D where companion: "current_entry_scope_quoted_at D [] A l ?G z E pu pr P e"
    "current_companion C [] D []"
    using current_companion_construction[OF entry frame(2) kept purposes(2) members(2) second_allowed] by blast
  show ?thesis using entry companion by blast
qed

lemma constant_entry_continuation_invariant:
  assumes every: "\<And>t. term_formed t \<Longrightarrow>
    schema_call_formed P d t \<and> ((d,t)\<in>positive_meaning P\<longleftrightarrow>b)"
  shows "continuation_permission_invariant P d"
  using every continuation_value_presents_formed
  unfolding continuation_permission_invariant_def by blast

section \<open>A valid predecessor continuation does not compel amendment\<close>

theorem predecessor_continuation_does_not_authorize_amendment:
  assumes authority: "target_formed A" and locus: "target_formed l"
    and material: "environment_formed B" and site: "(bu,br)\<in>environment_positions B"
  shows "\<exists>C D G p z E pu P d e S R F au root t I K.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and>
    current_entry_scope_quoted_at D [] A l G z E pu [] P e \<and> d\<noteq>e \<and>
    (\<forall>v. term_formed v \<longrightarrow> schema_call_formed P d v \<and> schema_call_formed P e v) \<and>
    current_companion C [] D [] \<and> current_snapshot_at C [] S \<and>
    transact S empty_transaction (Applied S) \<and>
    predecessor_continuation_certificate C [] D [] R [] S empty_transaction S B bu br \<and>
    replay_scope_quoted_at R [] F pu [] au [] root {} \<and>
    native_package_environment F pu []=E \<and> native_application_at F au [] e t I K \<and>
    native_positive_holds F pu [] au [] \<and> \<not>current_continues_at C [] F au [] S empty_transaction S B bu br \<and>
    (\<forall>M a r H c. \<not>current_accepts_at C [] M a r H c)"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site" and E pu P where program:
    "inj g" "closed_native_package_at E pu [] P"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have members: "g False\<in>system_definitions P" "g True\<in>system_definitions P"
    using program(3) by blast+
  have different: "g False\<noteq>g True" using program(1) by (auto dest: injD)
  have interfaces: "\<forall>v. term_formed v \<longrightarrow>
    schema_call_formed P (g False) v \<and> schema_call_formed P (g True) v"
    using program(3)[rule_format, of False] program(3)[rule_format, of True] by blast
  obtain C D G p z where current:
    "current_entry_scope_quoted_at C [] A l G p E pu [] P (g False)"
    "current_entry_scope_quoted_at D [] A l G z E pu [] P (g True)"
    "current_companion C [] D []"
    using current_companion_pair_total[OF program(2) members authority locus] by blast
  obtain S where before: "current_snapshot_at C [] S" "snapshot_formed S"
    using current_entry_snapshot_total[OF current(1)] by blast
  have trans: "transact S empty_transaction (Applied S)"
    by (rule empty_transaction_preserves_snapshot[OF before(2)])
  obtain t where present: "continuation_value_presents S empty_transaction S B bu br t"
    using continuation_value_presents_total[OF before(2) empty_transaction_formed before(2) material site] by blast
  have tf: "term_formed t" using continuation_value_presents_formed[OF present] by blast
  have accepting: "\<And>v. term_formed v \<Longrightarrow>
    schema_call_formed P (g True) v \<and> ((g True,v)\<in>positive_meaning P\<longleftrightarrow>True)"
    using program(3)[rule_format, of True] by blast
  have invariant: "continuation_permission_invariant P (g True)"
    by (rule constant_entry_continuation_invariant[OF accepting])
  have permitted: "factor_continues P (g True) S empty_transaction S B bu br"
    using invariant present accepting[OF tf] unfolding factor_continues_def by blast
  obtain R F au root I K where certificate:
    "predecessor_continuation_certificate C [] D [] R [] S empty_transaction S B bu br"
    "replay_scope_quoted_at R [] F pu [] au [] root {}"
    "native_package_environment F pu []=E" "native_application_at F au [] (g True) t I K"
    using predecessor_continuation_presentation_total[OF current(1,3,2) before(1) permitted present] by blast
  have positive: "native_positive_holds F pu [] au []" by (rule replay_scope_closed_sound[OF certificate(2)])
  have wrong_entry: "\<not>current_continues_at C [] F au [] S empty_transaction S B bu br"
  proof
    assume allowed: "current_continues_at C [] F au [] S empty_transaction S B bu br"
    have "g True=g False"
      by (rule current_continuation_requires_selected_entry[OF current(1) certificate(4) allowed])
    then show False using different by simp
  qed
  have rejects: "\<forall>M a r H c. \<not>current_accepts_at C [] M a r H c"
  proof (intro allI notI)
    fix M a r H c assume accepted: "current_accepts_at C [] M a r H c"
    obtain A' l' G' p' E' pu' pr' Q h x where other:
      "current_entry_scope_quoted_at C [] A' l' G' p' E' pu' pr' Q h"
      "(h,x)\<in>positive_meaning Q"
      using accepted unfolding current_accepts_at_def by blast
    have same: "P=Q \<and> g False=h" using current_entry_scope_unique[OF current(1) other(1)] by blast
    have truth: "(g False,x)\<in>positive_meaning P" using other(2) same by simp
    have formed: "term_formed x" using schema_call_formed_target[OF positive_meaning_formed[OF truth]] by blast
    show False using program(3)[rule_format, of False] formed truth by blast
  qed
  show ?thesis
    by (rule exI[of _ C], rule exI[of _ D], rule exI[of _ G], rule exI[of _ p], rule exI[of _ z],
        rule exI[of _ E], rule exI[of _ pu], rule exI[of _ P], rule exI[of _ "g False"],
        rule exI[of _ "g True"], rule exI[of _ S], rule exI[of _ R], rule exI[of _ F],
        rule exI[of _ au], rule exI[of _ root], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use current different interfaces before(1) trans certificate positive wrong_entry rejects in blast)
qed

text \<open>
  One finite native program contains two distinct entries with opposite
  ordinary meanings. One explicit adoption policy selects both purposes for
  the same generation and publication. The before snapshot is that actual
  publication, and the empty transaction succeeds without changing it.

  The accepting companion entry has a closed recorded continuation proof.
  Both entries admit every formed argument, including every complete future
  amendment argument.
  The same call cannot count at the refusing entry, and that entry refuses
  every amendment argument. Thus predecessor continuation, replay, structural
  success, and currentness together do not compel amendment acceptance.
  This example supplies no new successor or genesis claim; its generated
  core's cause is only a formed target.
\<close>

end
