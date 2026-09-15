theory Complete_Artifact_References
  imports Complete_Value_References Factor_Executable_Artifact_Values
begin

definition complete_artifact_reference ::
  "artifact_value_rows \<Rightarrow> artifact_value_rows list \<Rightarrow> nat \<times> artifact_value_rows list" where
  "complete_artifact_reference=value_reference_step"

definition complete_artifact_references ::
  "artifact_value_rows list \<Rightarrow> artifact_value_rows list \<Rightarrow> nat list \<times> artifact_value_rows list" where
  "complete_artifact_references=value_reference_sequence"

theorem complete_artifact_references_exact:
  "map (value_reference_read (snd (complete_artifact_references rows table)))
    (fst (complete_artifact_references rows table))=map Some rows"
  by (simp only: complete_artifact_references_def value_reference_sequence_exact)

theorem complete_artifact_reference_exact:
  "value_reference_read (snd (complete_artifact_reference rows table))
    (fst (complete_artifact_reference rows table))=Some rows"
  by (simp only: complete_artifact_reference_def value_reference_step_exact)

theorem complete_artifact_reference_preserves:
  "value_reference_read table i=Some rows \<Longrightarrow>
    value_reference_read (snd (complete_artifact_reference other table)) i=Some rows"
  by (simp only: complete_artifact_reference_def; rule value_reference_step_preserves)

text \<open>The referenced value is the whole ordered carrier, incidence,
  counted-data list and functional-data list. Counts, empty fields, malformed
  values and distinct complete presentations are all preserved. References
  change physical repetition; they supply no artifact formation or semantic
  admission. The sequence theorem supplies exact recovery of every occurrence.\<close>

end
