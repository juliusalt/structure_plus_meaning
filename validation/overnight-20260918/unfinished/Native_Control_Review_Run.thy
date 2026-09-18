theory Native_Control_Review_Run
  imports Native_Control_Context_Contract Native_Control_Seed_Subject
begin

declare development_seed_context_def [code] development_seed_roots_def [code]

text \<open>The changed-table control is the existing seed control, on the exact
  exported prefix. It preserves entity terms and changes the name read by equation
  recognition. No unknown refinement proposition is supplied.\<close>

definition context_run_changed :: isabelle_context where
  "context_run_changed=(map (\<lambda>s. if s=STR ''HOL.eq'' then STR ''HOL.eq.moved'' else s)
    (fst development_seed_context),snd development_seed_context)"

definition context_run_questions where
  "context_run_questions=context_input_questions development_seed_context context_run_changed"

value [code] "map (\<lambda>p. (p,context_input_observation p development_seed_context development_seed_context,
  context_input_observation p development_seed_context context_run_changed)) context_input_projections"

text \<open>These are the complete native reports, including every producer cell,
  condition, certificate, comparison, repair, revision and returned admission.\<close>

value [code] "native_steered_development context_run_questions context_run_questions"

text \<open>A bounded view of the same complete operations, for diagnostic review.
  It does not replace the complete preceding reports or their native admission.\<close>

value [code] "(let qs=context_run_questions; run=native_steered_development qs qs in
  (length qs, map (\<lambda>Q. let r=construct_native_development Q in
     (development_comparison r,development_revision r,native_development_admission Q r)) qs,
   fst (snd (snd run)), map_option (map (\<lambda>(m,Q,r,claimed,admitted).
     (m,claimed,admitted))) (snd (snd (snd run)))))"

end
