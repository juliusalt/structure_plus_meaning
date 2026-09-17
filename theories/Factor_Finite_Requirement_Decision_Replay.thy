theory Factor_Finite_Requirement_Decision_Replay
  imports Factor_Finite_Source_Decision_Replay Factor_Finite_Requirement_Decisions
begin

definition finite_requirement_decision_replay where
  "finite_requirement_decision_replay E u r gs Xs=finite_source_decision_replay
    (finite_admission_requirements_supported gs) (finite_construct_native_requirements gs) E u r Xs"

theorem finite_requirement_decision_replay_projection:
  "map_option fst (finite_requirement_decision_replay E u r gs Xs)=finite_requirement_decision E u r gs Xs"
  by (simp only: finite_requirement_decision_replay_def finite_requirement_decision_def
    finite_source_decision_replay_projection)

theorem finite_requirement_decision_replay_terms:
  assumes result: "finite_requirement_decision_replay E u r gs Xs=Some ((d,F,v,Q,D,A,T,Ys),R)"
    and original: "finite_native_source E u r=Some P"
  shows "fset Ys={t\<in>fset Xs. admission_requirements_hold
      (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
    "t |\<in>| Ys \<Longrightarrow> \<exists>p A' M root G au I K B.
      (((d,t),p),Some (A',M,root,G,au,I,K,B)) |\<in>| R"
  by (rule finite_native_source_constructor.finite_source_decision_replay_terms[OF
      native_requirement_source_constructor result[unfolded finite_requirement_decision_replay_def] original])+

corollary finite_requirement_decision_replay_failed_requirement:
  assumes result: "finite_requirement_decision_replay E u r gs Xs=Some ((d,F,v,Q,D,A,T,Ys),R)"
    and original: "finite_native_source E u r=Some P" and required: "g\<in>set gs"
    and failed: "\<not>admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
  shows "t |\<notin>| Ys"
  using required failed by (simp only: finite_requirement_decision_replay_terms(1)[OF result original]
    mem_Collect_eq admission_requirements_hold_def; blast)

end
