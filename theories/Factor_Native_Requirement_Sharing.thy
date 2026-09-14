theory Factor_Native_Requirement_Sharing
  imports Factor_Native_Requirement_Investigation Finite_Assessment_Reports
    Factor_Native_Requirement_Report_Assessment
begin

definition native_requirement_shared_context where
  "native_requirement_shared_context w=map_option (\<lambda>X. (X,native_requirement_source_report X))
    (native_requirement_problem w)"

definition native_requirement_shared_cell where
  "native_requirement_shared_cell m context=map_option (\<lambda>(X,source).
    let result=native_requirement_method m X; target=native_requirement_target_report X result in
      (target,native_requirement_assessment_from_reports X source result target)) context"

lemma native_requirement_shared_assessment:
  "map_option snd (native_requirement_shared_cell m (native_requirement_shared_context w))=
    native_requirement_assess m w"
  by (cases "native_requirement_problem w")
    (simp_all add: native_requirement_shared_cell_def native_requirement_shared_context_def
      native_requirement_assess_def native_requirement_assessment_from_reports_exact Let_def)

definition native_requirement_shared_inspect where
  "native_requirement_shared_inspect cell f=native_requirement_optional_inspect (map_option snd cell) f"

definition native_requirement_shared_subject where
  "native_requirement_shared_subject context cells=map_option (\<lambda>(X,source).
    (X,source,map (\<lambda>(m,cell). (m,case cell of None \<Rightarrow> None | Some (target,assessment) \<Rightarrow> target)) cells)) context"

lemma native_requirement_shared_subject_exact:
  "native_requirement_shared_subject (native_requirement_shared_context w)
      (map (\<lambda>m. (m,native_requirement_shared_cell m (native_requirement_shared_context w))) [0,1,2,3,4,5,6,7])=
    native_requirement_report w"
  by (cases "native_requirement_problem w")
    (simp_all add: native_requirement_shared_subject_def native_requirement_shared_context_def
      native_requirement_shared_cell_def native_requirement_report_def Let_def)

lemma native_requirement_shared_comparison:
  "context_assessment_investigation [0,1,2,3,4,5,6,7] [0,1,2,3] ws
    (context_assessment_table [0,1,2,3,4,5,6,7] ws native_requirement_shared_context native_requirement_shared_cell)
      native_requirement_shared_inspect=native_requirement_calculation ws"
  unfolding native_requirement_calculation_def
  apply (simp only: context_assessment_investigation_exact)
  apply (rule assessed_subject_investigation_cong)
  by (simp only: native_requirement_shared_inspect_def native_requirement_shared_assessment)

definition native_requirement_shared_packet where
  "native_requirement_shared_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7] ws native_requirement_shared_context native_requirement_shared_cell;
    result=context_assessment_investigation [0,1,2,3,4,5,6,7] [0,1,2,3] ws table native_requirement_shared_inspect
    in (map (\<lambda>(w,context,cells). (w,native_requirement_shared_subject context cells,
        map (\<lambda>(m,cell). (m,map_option snd cell)) cells)) table,
      result,map (investigation_cycle_report [0,1,2,3,4,5,6,7] [0,1,2,3]
        (fst result) (fst (snd result))) selections))"

theorem native_requirement_shared_packet_subjects:
  "fst (native_requirement_shared_packet ws selections)=map (\<lambda>w.
    (w,native_requirement_report w,map (\<lambda>m. (m,native_requirement_assess m w)) [0,1,2,3,4,5,6,7])) ws"
  by (simp only: native_requirement_shared_packet_def Let_def fst_conv context_assessment_table_def
    map_map comp_def case_prod_conv native_requirement_shared_subject_exact native_requirement_shared_assessment)

theorem native_requirement_shared_packet_investigation:
  "snd (native_requirement_shared_packet ws selections)=native_requirement_investigation_report ws selections"
  by (simp only: native_requirement_shared_packet_def Let_def snd_conv native_requirement_shared_comparison
    native_requirement_investigation_report_def)

text \<open>
  One actual source context and one constructor result per method feed both
  original report forms. The same assessment cells feed the original complete
  comparison and revisions. The generic context equations preserve every
  original field, index, order and repeated position on every supplied scope.
  No condition, failed source or result is omitted.
\<close>

end
