theory Complete_Term_References
  imports Complete_Value_References Factor_Executable_Environment_Values
begin

definition complete_empty_terms :: "finite_factor_term list" where
  "complete_empty_terms=[]"

definition complete_term_reference ::
  "finite_factor_term \<Rightarrow> finite_factor_term list \<Rightarrow> nat \<times> finite_factor_term list" where
  "complete_term_reference=value_reference_step"

theorem complete_term_reference_exact:
  "value_reference_read (snd (complete_term_reference t table))
    (fst (complete_term_reference t table))=Some t"
  by (simp only: complete_term_reference_def value_reference_step_exact)

theorem complete_term_reference_preserves:
  "value_reference_read table i=Some t \<Longrightarrow>
    value_reference_read (snd (complete_term_reference u table)) i=Some t"
  by (simp only: complete_term_reference_def; rule value_reference_step_preserves)

text \<open>The existing complete-value reference contract also retains whole
  terms. Payloads, pair structure, complete targets, malformed data, every earlier
  reference and repeated occurrences are preserved. Referencing a term asserts
  neither its formation nor its truth. The renderer can reuse the whole value
  without repeatedly serializing embedded original questions and proof operands.
  Artifact references within that original rendering retain their separate exact
  recovery contract.\<close>

end
