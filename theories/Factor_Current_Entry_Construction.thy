theory Factor_Current_Entry_Construction
  imports Factor_Current_Entries Factor_Authority_Programs RRA_Publication_Construction
begin

section \<open>Actual currentness frames can select every entry of a closed program\<close>

theorem current_entry_scope_construction:
  assumes closed: "closed_native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p. current_entry_scope_quoted_at C [] A l G p E pu pr P d"
proof -
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have fixed: "native_package_environment E pu pr=E" by (rule native_package_closed_environment_fixed[OF closed])
  obtain R where anchor: "anchor_formed (R,snd d)"
    using native_package_definition_anchor[OF package member] by blast
  have address: "octets_formed (snd d)" using anchor
    by (auto simp: anchor_formed_def exact_formed_def)
  obtain p where entry: "purpose_entry p d" using purpose_entry_total[OF address] by blast
  have purpose: "target_formed p" using purpose_entry_formed[OF entry] by blast
  obtain B where payload: "exact_formed B" "program_scope_quoted_at B [] E pu pr P"
    using program_scope_quoted_total[OF package] fixed by auto
  let ?G="Generation l {||} (Whole_Artifact B) (Whole_Artifact empty_artifact)"
  have core: "generation_formed ?G" by (rule generation_formed.formed) (use locus payload(1) in auto)
  have scope: "generation_program_scope ?G E pu pr P"
    by (rule generation_program_scope_from_payload[OF core _ payload(2)]) simp
  obtain H :: "local_address option artifact_environment" and qu bu where adopted:
    "native_adoption_judgment_at H qu [] bu [] A ?G p"
    using constant_native_adoption_application[OF authority core purpose, where b=True] by blast
  obtain N :: "local_address option artifact_environment" and v Q where publication:
    "publication_environment_closed N v [] Q"
    "snapshot_lookup (publication_snapshot Q) (generation_locus ?G)=Some ?G"
    using singleton_publication_exists[OF core] by blast
  have current: "native_current H qu [] bu [] A N v [] l ?G p"
    using adopted publication(2) by (simp add: native_current_with_publication[OF publication(1)])
  show ?thesis using current_entry_scope_quoted_total[OF current scope entry member] by blast
qed

text \<open>
  An ordinary accepting adoption program and an actual singleton publication
  give a currentness frame for the supplied closed program and selected entry.
  The purpose contains the entry coordinate; the generation payload contains
  the complete program scope. Both are inspected through their complete data
  quotations.

  The generated core's cause is only a formed target. This construction proves
  existence of actual currentness under an explicit policy, not cause validity,
  genesis adequacy, or legitimate succession. No certificate assumption is
  hidden in the construction or imported into raw currentness.
\<close>

end
