theory Factor_Current_Entry_Publications
  imports Factor_Current_Entry_Construction Factor_Current_Companions
begin

section \<open>Currentness for a supplied generation and exact publication\<close>

theorem current_entry_in_publication_total:
  fixes N :: "local_address option artifact_environment"
  assumes program: "generation_program_scope H E pu pr P" and member: "d\<in>system_definitions P"
    and authority: "target_formed A"
    and publication: "publication_environment_closed N v root V"
    and selected: "snapshot_lookup (publication_snapshot V) (generation_locus H)=Some H"
  shows "\<exists>C p J ju bu.
    current_entry_scope_quoted_at C [] A (generation_locus H) H p E pu pr P d \<and>
    current_scope_quoted_at C [] J ju [] bu [] A N v root (generation_locus H) H p \<and>
    current_snapshot_at C [] (publication_snapshot V)"
proof -
  have formed: "generation_formed H" and package: "native_package_at E pu pr P"
    using generation_program_scope_closed[OF program] by (auto simp: closed_native_package_at_def)
  obtain R where anchor: "anchor_formed (R,snd d)"
    using native_package_definition_anchor[OF package member] by blast
  have address: "octets_formed (snd d)" using anchor by (auto simp: anchor_formed_def exact_formed_def)
  obtain p where entry: "purpose_entry p d" using purpose_entry_total[OF address] by blast
  have purpose: "target_formed p" using purpose_entry_formed[OF entry] by blast
  obtain J :: "local_address option artifact_environment" and ju bu where adoption:
    "native_adoption_judgment_at J ju [] bu [] A H p"
    using constant_native_adoption_application[OF authority formed purpose, where b=True] by blast
  have current: "native_current J ju [] bu [] A N v root (generation_locus H) H p"
    using adoption selected by (simp only: native_current_with_publication[OF publication])
  obtain C where frame:
    "current_program_scope_quoted_at C [] A (generation_locus H) H p E pu pr P"
    "current_scope_quoted_at C [] (native_judgment_environment J ju [] bu []) ju [] bu []
      A N v root (generation_locus H) H p"
    using current_program_scope_quoted_total[OF current program] by blast
  have chosen: "current_entry_scope_quoted_at C [] A (generation_locus H) H p E pu pr P d"
    using frame(1) entry member by (simp add: current_entry_scope_quoted_at_def)
  have snapshot: "current_snapshot_at C [] (publication_snapshot V)"
    using frame(2) publication unfolding current_scope_quoted_at_def current_snapshot_at_def by blast
  show ?thesis using chosen frame(2) snapshot by blast
qed

theorem current_entry_publication_total:
  assumes program: "generation_program_scope H E pu pr P" and member: "d\<in>system_definitions P"
    and authority: "target_formed A" and publication: "publication_formed V"
    and selected: "snapshot_lookup (publication_snapshot V) (generation_locus H)=Some H"
  shows "\<exists>C p J ju bu N v.
    current_entry_scope_quoted_at C [] A (generation_locus H) H p E pu pr P d \<and>
    current_scope_quoted_at C [] J ju [] bu [] A N v [] (generation_locus H) H p \<and>
    publication_environment_closed N v [] V \<and> current_snapshot_at C [] (publication_snapshot V)"
proof -
  obtain N :: "local_address option artifact_environment" and v where actual:
    "publication_environment_closed N v [] V"
    using closed_publication_presentation_total[OF publication] by blast
  show ?thesis using actual current_entry_in_publication_total[OF program member authority actual selected] by blast
qed

text \<open>
  The supplied generation already contains its program scope and retains its
  own cause and history. A complete publication selects that generation, and
  an ordinary accepting adoption policy admits the chosen purpose. The
  resulting currentness frame keeps that exact publication environment,
  including its dependency and evidence selections.

  Every formed publication with this selection has such an actual frame.
  This construction does not infer adoption from raw publication or validate
  a cause: it constructs the separate adoption call explicitly. It imposes no
  truth requirement on the entry selected by the new generation.
\<close>

end
