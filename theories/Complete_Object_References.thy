theory Complete_Object_References
  imports Complete_Artifact_References Value_Reference_Identity_Maps
begin

definition complete_empty_artifacts :: "finite_exact_artifact list" where
  "complete_empty_artifacts=[]"

definition complete_object_reference ::
  "finite_exact_artifact \<Rightarrow> finite_exact_artifact list \<Rightarrow> nat \<times> finite_exact_artifact list" where
  "complete_object_reference=value_reference_step"

definition complete_object_references ::
  "finite_exact_artifact list \<Rightarrow> finite_exact_artifact list \<Rightarrow> nat list \<times> finite_exact_artifact list" where
  "complete_object_references=value_reference_sequence"

definition complete_object_table_rows where
  "complete_object_table_rows=map finite_artifact_rows"

theorem complete_object_reference_exact:
  "value_reference_read (snd (complete_object_reference R table))
    (fst (complete_object_reference R table))=Some R"
  by (simp only: complete_object_reference_def value_reference_step_exact)

theorem complete_object_reference_preserves:
  "value_reference_read table i=Some R \<Longrightarrow>
    value_reference_read (snd (complete_object_reference S table)) i=Some R"
  by (simp only: complete_object_reference_def; rule value_reference_step_preserves)

theorem complete_object_reference_rows_exact:
  "map_prod id complete_object_table_rows (complete_object_reference R table)=
    complete_artifact_reference (finite_artifact_rows R) (complete_object_table_rows table)"
  by (simp only: complete_object_reference_def complete_artifact_reference_def complete_object_table_rows_def;
      rule value_reference_step_identity_map[OF finite_artifact_rows_injective])

theorem complete_object_references_exact:
  "map (value_reference_read (snd (complete_object_references values table)))
      (fst (complete_object_references values table))=map Some values"
  by (simp only: complete_object_references_def value_reference_sequence_exact)

text \<open>The native table retains complete artifacts before their existing
  canonical field conversion. The exact identity-map equation establishes
  the same reference indices and complete row table as the earlier row codec.
  Every counted occurrence, malformed value and original whole artifact is
  retained. Converting a table once changes repeated physical work and grants
  no formation, observation, history or admission condition.\<close>

end
