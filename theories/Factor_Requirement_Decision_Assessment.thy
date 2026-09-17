theory Factor_Requirement_Decision_Assessment
  imports Factor_Requirement_Decision_Cases
begin

definition requirement_decision_result_condition :: "nat\<Rightarrow>native_requirement_problem\<Rightarrow>
    finite_factor_term fset\<Rightarrow>requirement_decision_result\<Rightarrow>bool" where
  "requirement_decision_result_condition f X expected result=(case X of (E,u,r,gs,Xs) \<Rightarrow>
    (case result of None \<Rightarrow> False | Some (d,F,v,Q,D,A,T,Ys) \<Rightarrow>
      if f=0 then fset Ys\<subseteq>fset expected else if f=1 then fset expected\<subseteq>fset Ys
      else if f=2 then finite_source_preservation_condition E u r (Some (d,F,v))
      else if f=3 then native_package_at (decode_finite_environment F) v [] (decode_finite_system Q) \<and>
        d\<in>system_definitions (decode_finite_system Q) \<and> D=finite_program_term_demand Q Xs
      else if f=4 then finite_program_evaluation_ready Q D \<and>
        fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system Q)}
      else if f=5 then fimage fst T=A \<and> finite_proofs_sound Q T
      else if f=6 then fset Ys={t\<in>fset Xs. (d,t)\<in>fset A} else False))"

definition requirement_decision_result_assessment where
  "requirement_decision_result_assessment X expected result=(case X of (E,u,r,gs,Xs) \<Rightarrow>
    map_option (\<lambda>(d,F,v,Q,D,A,T,Ys). let source=finite_native_source F v [];
      actual=requirement_decision_evaluation_report Q D; inspected=finite_proof_inspection Q T in
      (source,actual,inspected,
        Ys |\<subseteq>| expected,expected |\<subseteq>| Ys,
        finite_source_preservation_observation E u r (Some (d,F,v)),
        source=Some Q \<and> d |\<in>| finite_system_definitions Q \<and> D=finite_program_term_demand Q Xs,
        snd (snd (snd (snd (snd actual))))=Some A,
        fimage fst T=A \<and> finite_inspection_rows_hold inspected,
        Ys=ffilter (\<lambda>t. (d,t) |\<in>| A) Xs)) result)"

definition requirement_decision_result_inspect where
  "requirement_decision_result_inspect report (f::nat)=(case report of None \<Rightarrow> False
    | Some (source,actual,inspected,precise,complete,preserved,native,answers,proofs,terms) \<Rightarrow>
      if f=0 then precise else if f=1 then complete else if f=2 then preserved else if f=3 then native
      else if f=4 then answers else if f=5 then proofs else if f=6 then terms else False)"

theorem requirement_decision_result_assessment_exact:
  "requirement_decision_result_inspect (requirement_decision_result_assessment X expected result) f=
    requirement_decision_result_condition f X expected result"
proof -
  obtain E u r gs Xs where input: "X=(E,u,r,gs,Xs)" by (cases X) auto
  have filtered: "Ys=ffilter test Xs \<longleftrightarrow> fset Ys={t\<in>fset Xs. test t}" for Ys test Xs
    by (simp only: fset_inject[symmetric] ffilter.rep_eq Set.filter_eq)
  show ?thesis
  proof (cases result)
    case None
    then show ?thesis by (simp only: input requirement_decision_result_assessment_def
      requirement_decision_result_inspect_def requirement_decision_result_condition_def
      case_prod_conv option.simps option.case)
  next
    case (Some z)
    obtain d F v Q D A T Ys where shape: "z=(d,F,v,Q,D,A,T,Ys)" by (cases z) auto
    show ?thesis by (simp only: input Some shape requirement_decision_result_assessment_def
      requirement_decision_result_inspect_def requirement_decision_result_condition_def
      requirement_decision_evaluation_report_def case_prod_conv option.simps option.case Let_def
      fst_conv snd_conv less_eq_fset.rep_eq finite_source_preservation_exact
      finite_native_source_correct finite_system_definitions_correct finite_program_evaluation_semantics
      finite_proof_inspection_exact filtered)
  qed
qed

definition requirement_decision_condition where
  "requirement_decision_condition (f::nat) method X=(let reference=requirement_decision_reference X in
    if f=7 then (reference=None \<longrightarrow> method X=None)
    else if f<7 then (reference\<noteq>None \<longrightarrow> (case reference of None \<Rightarrow> False
      | Some (P,expected) \<Rightarrow> requirement_decision_result_condition f X expected (method X))) else False)"

definition requirement_decision_assessment_from where
  "requirement_decision_assessment_from X reference result=(reference\<noteq>None,
    (case reference of None \<Rightarrow> None | Some (P,expected) \<Rightarrow>
      requirement_decision_result_assessment X expected result),result=None)"

definition requirement_decision_inspect where
  "requirement_decision_inspect report (f::nat)=(case report of (ready,body,rejected) \<Rightarrow>
    if f=7 then (\<not>ready \<longrightarrow> rejected) else if f<7 then
      (ready \<longrightarrow> requirement_decision_result_inspect body f) else False)"

theorem requirement_decision_assessment_exact:
  "requirement_decision_inspect (requirement_decision_assessment_from X (requirement_decision_reference X)
    (method X)) f=requirement_decision_condition f method X"
  by (cases "requirement_decision_reference X")
    (auto simp: requirement_decision_assessment_from_def requirement_decision_inspect_def
      requirement_decision_condition_def requirement_decision_result_assessment_exact Let_def split: prod.splits)

end
