theory Factor_Native_Derivation_Reports
  imports Factor_Native_Derivation_Investigation Finite_Assessment_Reports
begin

lemma native_derivation_apply_at:
  "native_derivation_apply m X (native_derivation_base X)=native_derivation_method m X"
  by (cases X) (simp add: native_derivation_base_def native_derivation_method_def)

definition native_derivation_assessment_from_review where
  "native_derivation_assessment_from_review original result review=
    ((original\<noteq>None,finite_term_observation_comparison original
      (map_option (\<lambda>(Q,A,Hs). (Q,A)) result),
      (case original of None \<Rightarrow> False | Some (P,B) \<Rightarrow>
        (case result of None \<Rightarrow> False | Some (Q,A,Hs) \<Rightarrow> P=Q)),result=None),
    map_option (\<lambda>(rows,extra,missing). finite_inspection_rows_hold rows) review=Some True,
    map_option (\<lambda>(rows,extra,missing). extra={||} \<and> missing={||}) review=Some True)"

lemma native_derivation_assessment_from_review_exact:
  "native_derivation_assessment_from_review (native_history_original X) result
    (native_derivation_evidence_review X result)=native_derivation_assessment X result"
  by (simp only: native_derivation_assessment_from_review_def native_derivation_assessment_def
    native_history_ready_def native_history_answer_observation_def native_history_program_observation_def Let_def)

definition native_derivation_report where
  "native_derivation_report w=map_option (\<lambda>X. (X,native_history_source_report X,
    map (\<lambda>m. (m,native_derivation_method m X)) native_derivation_methods)) (native_history_problem w)"

definition native_derivation_context where
  "native_derivation_context w=map_option (\<lambda>X. (X,native_history_source_report X,
    native_history_original X,native_derivation_base X,native_derivation_expansion X)) (native_history_problem w)"

definition native_derivation_context_cell where
  "native_derivation_context_cell m C=map_option (\<lambda>(X,reference,original,base,expanded).
    let result=native_derivation_apply_values m X base expanded;
      review=native_derivation_review_from_original original result
    in (result,native_derivation_assessment_from_review original result review,review)) C"

lemma native_derivation_context_cell_at:
  "native_derivation_context_cell m (Some (X,reference,native_history_original X,native_derivation_base X,native_derivation_expansion X))=
    Some (native_derivation_method m X,native_derivation_assessment X (native_derivation_method m X),
      native_derivation_evidence_review X (native_derivation_method m X))"
  by (simp only: native_derivation_context_cell_def option.simps case_prod_conv Let_def native_derivation_apply_values_actual native_derivation_apply_at
    native_derivation_evidence_review_def[symmetric] native_derivation_assessment_from_review_exact)

lemma native_derivation_context_cell_exact:
  "native_derivation_context_cell m (native_derivation_context w)=map_option (\<lambda>X.
    (native_derivation_method m X,native_derivation_assessment X (native_derivation_method m X),
      native_derivation_evidence_review X (native_derivation_method m X))) (native_history_problem w)"
proof (cases "native_history_problem w")
  case None
  then show ?thesis by (simp only: native_derivation_context_def option.simps native_derivation_context_cell_def)
next
  case (Some X)
  then show ?thesis by (simp only: native_derivation_context_def option.simps native_derivation_context_cell_at)
qed

definition native_derivation_cell_result where
  "native_derivation_cell_result cell=(case cell of None \<Rightarrow> None | Some (result,A,review) \<Rightarrow> result)"

definition native_derivation_cell_report where
  "native_derivation_cell_report cell=map_option (\<lambda>(result,A,review). (A,review)) cell"

definition native_derivation_cell_inspect where
  "native_derivation_cell_inspect cell f=native_derivation_optional_inspect
    (map_option (\<lambda>(result,A,review). A) cell) f"

lemma native_derivation_cell_report_exact:
  "native_derivation_cell_report (native_derivation_context_cell m (native_derivation_context w))=
    native_derivation_assess_report m w"
  by (simp add: native_derivation_cell_report_def native_derivation_context_cell_exact
    native_derivation_assess_report_def option.map_comp comp_def Let_def)

lemma native_derivation_cell_inspect_exact:
  "native_derivation_cell_inspect (native_derivation_context_cell m (native_derivation_context w)) f=
    native_derivation_optional_inspect (native_derivation_assess m w) f"
  by (simp add: native_derivation_cell_inspect_def native_derivation_context_cell_exact
    native_derivation_assess_def option.map_comp comp_def)

definition native_derivation_context_subject where
  "native_derivation_context_subject C cells=map_option (\<lambda>(X,reference,original,base,expanded).
    (X,reference,map (\<lambda>(m,cell). (m,native_derivation_cell_result cell)) cells)) C"

lemma native_derivation_context_subject_exact:
  "native_derivation_context_subject (native_derivation_context w)
    (map (\<lambda>m. (m,native_derivation_context_cell m (native_derivation_context w))) native_derivation_methods)=
      native_derivation_report w"
  by (cases "native_history_problem w")
    (simp_all add: native_derivation_context_subject_def native_derivation_context_def native_derivation_context_cell_at
      native_derivation_cell_result_def native_derivation_report_def comp_def)

definition native_derivation_shared_table where
  "native_derivation_shared_table ws=context_assessment_table native_derivation_methods ws
    native_derivation_context native_derivation_context_cell"

definition native_derivation_shared_subjects where
  "native_derivation_shared_subjects table=map (\<lambda>(w,C,cells).
    (w,native_derivation_context_subject C cells)) table"

definition native_derivation_shared_assessments where
  "native_derivation_shared_assessments table=map (\<lambda>(w,C,cells).
    (w,map (\<lambda>(m,cell). (m,native_derivation_cell_report cell)) cells)) table"

lemma native_derivation_shared_subjects_exact:
  "native_derivation_shared_subjects (native_derivation_shared_table ws)=map (\<lambda>w. (w,native_derivation_report w)) ws"
  by (simp add: native_derivation_shared_subjects_def native_derivation_shared_table_def
    context_assessment_table_def Let_def comp_def native_derivation_context_subject_exact)

lemma native_derivation_shared_assessments_exact:
  "native_derivation_shared_assessments (native_derivation_shared_table ws)=
    map (\<lambda>w. (w,map (\<lambda>m. (m,native_derivation_assess_report m w)) native_derivation_methods)) ws"
  by (simp add: native_derivation_shared_assessments_def native_derivation_shared_table_def
    context_assessment_table_def Let_def comp_def native_derivation_cell_report_exact)

definition native_derivation_shared_calculation where
  "native_derivation_shared_calculation ws table=context_assessment_investigation native_derivation_methods
    [0,1,2,3,4,5] ws table native_derivation_cell_inspect"

lemma native_derivation_shared_calculation_exact:
  "native_derivation_shared_calculation ws (native_derivation_shared_table ws)=native_derivation_calculation ws"
  unfolding native_derivation_shared_calculation_def native_derivation_shared_table_def
  apply (simp only: context_assessment_investigation_exact native_derivation_calculation_def
    native_derivation_methods_def)
  by (rule assessed_subject_investigation_cong) (simp only: native_derivation_cell_inspect_exact)

definition native_derivation_report_packet where
  "native_derivation_report_packet ws selections=(let table=native_derivation_shared_table ws;
    result=native_derivation_shared_calculation ws table;
    rows=fst result; relation=fst (snd result)
    in (native_derivation_shared_subjects table,native_derivation_shared_assessments table,
      (result,map (investigation_cycle_report native_derivation_methods [0,1,2,3,4,5] rows relation) selections)))"

theorem native_derivation_report_packet_exact:
  "native_derivation_report_packet ws selections=(map (\<lambda>w. (w,native_derivation_report w)) ws,
    map (\<lambda>w. (w,map (\<lambda>m. (m,native_derivation_assess_report m w)) native_derivation_methods)) ws,
    native_derivation_investigation_report ws selections)"
  by (simp only: native_derivation_report_packet_def Let_def native_derivation_shared_subjects_exact
    native_derivation_shared_assessments_exact native_derivation_shared_calculation_exact
    native_derivation_investigation_report_def native_derivation_methods_def)

export_code native_derivation_report_packet checking SML

text \<open>
  One context retains each original native problem, source report, evaluation
  and base and expanded certificate families. Each cell applies its actual candidate and
  computes one full certificate review. Those same native cells supply the
  subjects, assessments and every comparison and revision field.
  The exact equation preserves the complete original report and all failures.
  This semantic reuse does not establish a complete physical cost account.
\<close>

end
