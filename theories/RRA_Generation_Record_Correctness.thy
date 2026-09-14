theory RRA_Generation_Record_Correctness
  imports RRA_Generation_Record_Assessment RRA_Finite_Generation_Reference_Construction
begin

lemma generation_record_original_result:
  assumes result: "finite_construct_generation_record E l p c rows=Some (F,u,G)"
  shows "generation_record_result_condition f (E,l,p,c,rows) (Some (F,u,G))=(0<f \<and> f<9)"
proof -
  have core: "G=finite_generation_record_core l p c rows"
    and formed: "finite_environment_formed F"
    and native: "finite_check_generation G F u []"
    and preserved: "finite_environment_agrees_on E F (finite_environment_uses E)"
    by (rule finite_construct_generation_record_correct[OF result])+
  have refs: "finite_generation_predecessor_references F u [] l p c=fset_of_list (map fst rows)"
    by (rule finite_construct_generation_record_original_references[OF result])
  have inspected: "generation_record_result_inspect
    (generation_record_result_assessment (E,l,p,c,rows) (Some (F,u,G))) f=(0<f \<and> f<9)"
    using formed native preserved refs
    by (auto simp: generation_record_result_inspect_def generation_record_result_assessment_def
      Let_def core finite_generation_record_core_def; arith)
  show ?thesis using inspected by (simp only: generation_record_result_assessment_exact)
qed

lemma generation_record_original_available:
  "(generation_record_method 0 X\<noteq>None)=generation_record_original_ready X"
proof -
  obtain E l p c rows where input: "X=(E,l,p,c,rows)" by (cases X) auto
  have domain: "(finite_construct_generation_record E l p c rows\<noteq>None)=
    finite_generation_record_ready E l p c rows"
    using finite_construct_generation_record_domain[of E l p c rows]
    by (cases "finite_construct_generation_record E l p c rows") auto
  show ?thesis
    by (simp only: input generation_record_method_original domain
      generation_record_reference_exact[symmetric] generation_record_reference_def case_prod_conv)
qed

theorem generation_record_original_correct:
  assumes facet: "f<9"
  shows "generation_record_condition f (generation_record_method 0) X"
proof -
  have available: "(generation_record_method 0 X\<noteq>None)=generation_record_original_ready X"
    by (rule generation_record_original_available)
  have valid: "generation_record_result_condition f X (generation_record_method 0 X)"
    if ready: "generation_record_original_ready X" and lower: "0<f"
  proof -
    obtain E l p c rows where input: "X=(E,l,p,c,rows)" by (cases X) auto
    obtain F u G where result: "finite_construct_generation_record E l p c rows=Some (F,u,G)"
      using available ready by (simp only: input generation_record_method_original;
        cases "finite_construct_generation_record E l p c rows"; auto)
    show ?thesis
      by (simp only: input generation_record_method_original result
        generation_record_original_result[OF result] lower facet simp_thms)
  qed
  show ?thesis using available valid facet by (auto simp: generation_record_condition_def)
qed

text \<open>
  The original constructor satisfies every independent condition on every
  complete input, including availability and refusal. Exact predecessor
  references are required alongside recovered values and preservation of all
  old material. The finite comparison still computes every actual candidate
  result and reason; its selected test scope is not the premise of this theorem.
\<close>

end
