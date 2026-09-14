theory Factor_Decision_Replay_Assessment
  imports Factor_Decision_Replay_Cases
begin

definition decision_replay_row_assessment where
  "decision_replay_row_assessment Z row=(case row of (c,result) \<Rightarrow>
    let X=decision_certificate_subject Z c; reference=native_replay_reference X;
      original=(case reference of None \<Rightarrow> None | Some (P,checked) \<Rightarrow> if checked then Some P else None)
    in (X,reference,native_replay_assessment_from X original result))"

definition decision_replay_row_inspect where
  "decision_replay_row_inspect report (f::nat)=(case report of (X,reference,assessment) \<Rightarrow>
    native_replay_inspect assessment f)"

lemma decision_replay_row_exact:
  "decision_replay_row_inspect (decision_replay_row_assessment Z (c,result)) f=
    native_replay_condition f (\<lambda>X. result) (decision_certificate_subject Z c)"
  by (simp only: decision_replay_row_assessment_def Let_def case_prod_conv
    native_replay_original_def[symmetric] decision_replay_row_inspect_def
    native_replay_assessment_def[symmetric]; rule native_replay_assessment_exact)

definition decision_replay_family_condition where
  "decision_replay_family_condition (f::nat) Z R=(if f=0 then
    rel_dom (fset R)=fset (finite_decision_certificates Z) \<and> single_valued (fset R)
    else if f<11 then (\<forall>(c,result)\<in>fset R.
      native_replay_condition (f-1) (\<lambda>X. result) (decision_certificate_subject Z c)) else False)"

definition decision_replay_family_assessment where
  "decision_replay_family_assessment Z R=(finite_decision_certificates Z,
    fimage fst R=finite_decision_certificates Z \<and> finite_relation_functional R,
    finite_inspection_rows (decision_replay_row_assessment Z) R)"

definition decision_replay_family_inspect where
  "decision_replay_family_inspect assessment (f::nat)=(case assessment of (expected,complete,rows) \<Rightarrow>
    if f=0 then complete else if f<11 then fBall rows (\<lambda>(row,report).
      decision_replay_row_inspect report (f-1)) else False)"

theorem decision_replay_family_assessment_exact:
  "decision_replay_family_inspect (decision_replay_family_assessment Z R) f=
    decision_replay_family_condition f Z R"
proof -
  have domain: "fimage fst R=finite_decision_certificates Z \<longleftrightarrow>
    rel_dom (fset R)=fset (finite_decision_certificates Z)"
    by (simp only: fset_inject[symmetric] fimage.rep_eq rel_dom_image)
  have rows: "fBall (finite_inspection_rows (decision_replay_row_assessment Z) R)
      (\<lambda>(row,report). decision_replay_row_inspect report k)=
    (\<forall>(c,result)\<in>fset R. native_replay_condition k (\<lambda>X. result)
      (decision_certificate_subject Z c))" for k
    by (simp only: finite_inspection_rows_def finite_function_graph_all;
      rule ball_cong[OF refl]; rename_tac row; case_tac row;
      simp only: case_prod_conv decision_replay_row_exact)
  show ?thesis by (simp only: decision_replay_family_assessment_def decision_replay_family_inspect_def
    decision_replay_family_condition_def case_prod_conv domain finite_relation_functional_correct rows)
qed

definition decision_replay_condition where
  "decision_replay_condition (f::nat) method X=(if f<8 then
    requirement_decision_condition f (\<lambda>x. map_option fst (method x)) X
    else if f<19 then (requirement_decision_reference X\<noteq>None \<longrightarrow>
      (case method X of None \<Rightarrow> False | Some (Z,R) \<Rightarrow>
        decision_replay_family_condition (f-8) Z R)) else False)"

definition decision_replay_assessment_from where
  "decision_replay_assessment_from X reference result=(
    requirement_decision_assessment_from X reference (map_option fst result),
    map_option (\<lambda>(Z,R). decision_replay_family_assessment Z R) result)"

definition decision_replay_inspect where
  "decision_replay_inspect assessment (f::nat)=(case assessment of (original,family) \<Rightarrow>
    if f<8 then requirement_decision_inspect original f else if f<19 then
      (fst original \<longrightarrow> (case family of None \<Rightarrow> False | Some body \<Rightarrow>
        decision_replay_family_inspect body (f-8))) else False)"

theorem decision_replay_assessment_exact:
  "decision_replay_inspect (decision_replay_assessment_from X (requirement_decision_reference X)
    (method X)) f=decision_replay_condition f method X"
proof -
  have previous: "requirement_decision_inspect (requirement_decision_assessment_from X
      (requirement_decision_reference X) (map_option fst (method X))) f=
    requirement_decision_condition f (\<lambda>x. map_option fst (method x)) X"
    by (rule requirement_decision_assessment_exact)
  have ready: "fst (requirement_decision_assessment_from X reference result)=(reference\<noteq>None)"
    for reference result by (simp only: requirement_decision_assessment_from_def fst_conv)
  show ?thesis
    by (simp only: decision_replay_assessment_from_def decision_replay_inspect_def
        decision_replay_condition_def case_prod_conv previous ready;
      cases "method X";
      auto simp only: decision_replay_family_assessment_exact option.simps option.case
        case_prod_conv split: prod.splits)
qed

export_code decision_replay_assessment_from decision_replay_inspect checking SML

text \<open>
  Every original decision condition remains independently required. Exact
  replay-family domain and functionality are separate from the ten conditions
  for each actual replay. Each row retains its full certificate and result,
  reconstructed source input, actual source/proof reading and complete native
  replay assessment. An unrelated valid replay does not discharge a missing
  required certificate or an original requirement.
\<close>

end
