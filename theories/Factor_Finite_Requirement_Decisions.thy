theory Factor_Finite_Requirement_Decisions
  imports Factor_Finite_Source_Decisions Factor_Finite_Native_Requirements
begin

definition finite_requirement_decision where
  "finite_requirement_decision E u r gs Xs=finite_source_decision
    (finite_admission_requirements_supported gs) (finite_construct_native_requirements gs) E u r Xs"

theorem finite_requirement_decision_exact:
  assumes result: "finite_requirement_decision E u r gs Xs=Some (d,F,v,Q,D,A,T,Ys)"
    and original: "finite_native_source E u r=Some P"
  shows "fset Ys={t\<in>fset Xs. admission_requirements_hold
      (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
    "fimage fst T=A"
    "finite_proofs_sound Q T"
    "t |\<in>| Ys \<Longrightarrow> \<exists>p. ((d,t),p) |\<in>| T"
  by (rule finite_native_source_constructor.finite_source_decision_exact[OF
      native_requirement_source_constructor result[unfolded finite_requirement_decision_def] original])+

corollary finite_requirement_decision_each:
  assumes result: "finite_requirement_decision E u r gs Xs=Some (d,F,v,Q,D,A,T,Ys)"
    and original: "finite_native_source E u r=Some P"
    and admitted: "t |\<in>| Ys" and required: "g\<in>set gs"
  shows "admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
  using admitted required by (simp only: finite_requirement_decision_exact(1)[OF result original]
    mem_Collect_eq admission_requirements_hold_def; blast)

corollary finite_requirement_decision_failed_condition:
  assumes result: "finite_requirement_decision E u r gs Xs=Some (d,F,v,Q,D,A,T,Ys)"
    and original: "finite_native_source E u r=Some P" and required: "g\<in>set gs"
    and failed: "\<not>admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
  shows "t |\<notin>| Ys"
  using finite_requirement_decision_each[OF result original _ required] failed by blast

export_code finite_requirement_decision checking SML

text \<open>
  The original requirement list and actual source meanings determine admission.
  Installation constructs every required occurrence and its shared final guard.
  Native evaluation then computes the admitted original terms and generates
  evidence for every positive result. Failure of any original requirement
  excludes that term. No exceptional supplied satisfaction table is used.

  The same operation serves a problem, proposed change, evidence request or
  criticism only when its complete native subject and original requirements
  have their own exact contracts. The entire workflow still needs those
  concrete instances, coverage criticism, operative transitions, reproducible
  retention and a complete cost account. This mechanism alone does not close
  the six conditions in problems.txt.
\<close>

end
