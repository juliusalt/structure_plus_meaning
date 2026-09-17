theory Factor_Native_History_Reports
  imports Factor_Native_History_Investigation Finite_Assessment_Reports
begin

definition native_history_demand :: "native_history_problem\<Rightarrow>native_history_call fset" where
  "native_history_demand X=snd (snd (snd X))"

definition native_history_base :: "native_history_problem\<Rightarrow>native_history_result" where
  "native_history_base X=(case X of (E,u,r,D) \<Rightarrow> finite_native_program_history E u r D)"

lemma native_history_apply_at:
  "native_history_apply m (native_history_demand X) (native_history_base X)=native_history_method m X"
  by (cases X) (simp add: native_history_demand_def native_history_base_def native_history_method_def)

definition native_history_review_from_original where
  "native_history_review_from_original D original result=(case original of None \<Rightarrow> None
    | Some (P,B) \<Rightarrow> map_option (\<lambda>(Q,A,Hs).
      (finite_program_history_step_review P D A Hs,finite_program_history_witness_review P D Hs)) result)"

lemma native_history_review_from_original_exact:
  "native_history_review_from_original (native_history_demand X) (native_history_original X) result=
    native_history_evidence_review X result"
  by (cases X) (simp only: native_history_review_from_original_def native_history_demand_def
    native_history_evidence_review_def case_prod_conv fst_conv snd_conv)

definition native_history_assessment_from_review where
  "native_history_assessment_from_review original result review=
    ((original\<noteq>None,finite_term_observation_comparison original
      (map_option (\<lambda>(Q,A,Hs). (Q,A)) result),
      (case original of None \<Rightarrow> False | Some (P,B) \<Rightarrow>
        (case result of None \<Rightarrow> False | Some (Q,A,Hs) \<Rightarrow> P=Q)),result=None),
    map_option (\<lambda>(steps,witnesses). iteration_review_holds steps) review=Some True,
    map_option (\<lambda>(steps,witnesses). finite_inference_witness_review_holds witnesses) review=Some True)"

lemma native_history_assessment_from_review_exact:
  "native_history_assessment_from_review (native_history_original X) result
    (native_history_evidence_review X result)=native_history_assessment X result"
  by (simp only: native_history_assessment_from_review_def native_history_assessment_def
    native_history_ready_def native_history_answer_observation_def native_history_program_observation_def Let_def)

definition native_history_context where
  "native_history_context w=map_option (\<lambda>X. (X,native_history_source_report X,
    native_history_original X,native_history_base X)) (native_history_problem w)"

definition native_history_context_cell where
  "native_history_context_cell m C=map_option (\<lambda>(X,reference,original,history).
    let result=native_history_apply m (native_history_demand X) history;
      review=native_history_review_from_original (native_history_demand X) original result
    in (result,native_history_assessment_from_review original result review,review)) C"

lemma native_history_context_cell_at:
  "native_history_context_cell m (Some (X,reference,native_history_original X,native_history_base X))=
    Some (native_history_method m X,native_history_assessment X (native_history_method m X),
      native_history_evidence_review X (native_history_method m X))"
  by (simp only: native_history_context_cell_def option.simps case_prod_conv Let_def native_history_apply_at
    native_history_review_from_original_exact native_history_assessment_from_review_exact)

lemma native_history_context_cell_exact:
  "native_history_context_cell m (native_history_context w)=map_option (\<lambda>X.
    (native_history_method m X,native_history_assessment X (native_history_method m X),
      native_history_evidence_review X (native_history_method m X))) (native_history_problem w)"
proof (cases "native_history_problem w")
  case None
  then show ?thesis by (simp only: native_history_context_def option.simps native_history_context_cell_def)
next
  case (Some X)
  then show ?thesis by (simp only: native_history_context_def option.simps native_history_context_cell_at)
qed

definition native_history_cell_result where
  "native_history_cell_result cell=(case cell of None \<Rightarrow> None | Some (result,A,review) \<Rightarrow> result)"

definition native_history_cell_report where
  "native_history_cell_report cell=map_option (\<lambda>(result,A,review). (A,review)) cell"

definition native_history_cell_inspect where
  "native_history_cell_inspect cell f=native_history_optional_inspect
    (map_option (\<lambda>(result,A,review). A) cell) f"

lemma native_history_cell_report_exact:
  "native_history_cell_report (native_history_context_cell m (native_history_context w))=
    native_history_assess_report m w"
  by (simp add: native_history_cell_report_def native_history_context_cell_exact
    native_history_assess_report_def option.map_comp comp_def Let_def)

lemma native_history_cell_inspect_exact:
  "native_history_cell_inspect (native_history_context_cell m (native_history_context w)) f=
    native_history_optional_inspect (native_history_assess m w) f"
  by (simp add: native_history_cell_inspect_def native_history_context_cell_exact
    native_history_assess_def option.map_comp comp_def)

definition native_history_context_subject where
  "native_history_context_subject C cells=map_option (\<lambda>(X,reference,original,history).
    (X,reference,map (\<lambda>(m,cell). (m,native_history_cell_result cell)) cells)) C"

lemma native_history_context_subject_exact:
  "native_history_context_subject (native_history_context w)
    (map (\<lambda>m. (m,native_history_context_cell m (native_history_context w))) native_history_methods)=
      native_history_report w"
  by (cases "native_history_problem w")
    (simp_all add: native_history_context_subject_def native_history_context_def native_history_context_cell_at
      native_history_cell_result_def native_history_report_def comp_def)

definition native_history_shared_table where
  "native_history_shared_table ws=context_assessment_table native_history_methods ws
    native_history_context native_history_context_cell"

definition native_history_shared_subjects where
  "native_history_shared_subjects table=map (\<lambda>(w,C,cells).
    (w,native_history_context_subject C cells)) table"

definition native_history_shared_assessments where
  "native_history_shared_assessments table=map (\<lambda>(w,C,cells).
    (w,map (\<lambda>(m,cell). (m,native_history_cell_report cell)) cells)) table"

lemma native_history_shared_subjects_exact:
  "native_history_shared_subjects (native_history_shared_table ws)=map (\<lambda>w. (w,native_history_report w)) ws"
  by (simp add: native_history_shared_subjects_def native_history_shared_table_def
    context_assessment_table_def Let_def comp_def native_history_context_subject_exact)

lemma native_history_shared_assessments_exact:
  "native_history_shared_assessments (native_history_shared_table ws)=
    map (\<lambda>w. (w,map (\<lambda>m. (m,native_history_assess_report m w)) native_history_methods)) ws"
  by (simp add: native_history_shared_assessments_def native_history_shared_table_def
    context_assessment_table_def Let_def comp_def native_history_cell_report_exact)

definition native_history_shared_calculation where
  "native_history_shared_calculation ws table=context_assessment_investigation native_history_methods
    [0,1,2,3,4,5] ws table native_history_cell_inspect"

lemma native_history_shared_calculation_exact:
  "native_history_shared_calculation ws (native_history_shared_table ws)=native_history_calculation ws"
  unfolding native_history_shared_calculation_def native_history_shared_table_def
  apply (simp only: context_assessment_investigation_exact native_history_calculation_def
    native_history_methods_def)
  by (rule assessed_subject_investigation_cong) (simp only: native_history_cell_inspect_exact)

definition native_history_report_packet where
  "native_history_report_packet ws selections=(let table=native_history_shared_table ws;
    result=native_history_shared_calculation ws table;
    rows=fst result; relation=fst (snd result)
    in (native_history_shared_subjects table,native_history_shared_assessments table,
      (result,map (investigation_cycle_report native_history_methods [0,1,2,3,4,5] rows relation) selections)))"

theorem native_history_report_packet_exact:
  "native_history_report_packet ws selections=(map (\<lambda>w. (w,native_history_report w)) ws,
    map (\<lambda>w. (w,map (\<lambda>m. (m,native_history_assess_report m w)) native_history_methods)) ws,
    native_history_investigation_report ws selections)"
  by (simp only: native_history_report_packet_def Let_def native_history_shared_subjects_exact
    native_history_shared_assessments_exact native_history_shared_calculation_exact
    native_history_investigation_report_def native_history_methods_def)

text \<open>
  The packet constructs one context per problem, retaining its actual source
  report, original evaluation and base history. Each cell applies the original candidate
  operation and retains one complete evidence review. The same native cells
  supply the subjects, assessments and all comparison and revision fields.
  The projection theorem preserves the entire original report, including list
  order, failed source inputs and every structural reason. No host-supplied
  observation table participates. This equation states semantic reuse and
  does not establish a complete physical cost account or authorize genesis.
\<close>

end
