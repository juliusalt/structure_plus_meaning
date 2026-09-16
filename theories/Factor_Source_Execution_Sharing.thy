theory Factor_Source_Execution_Sharing
  imports Factor_Source_Development_Cycle Factor_Steered_Execution_Sharing
    Factor_Workflow_Execution_Sharing
begin

definition source_development_result_fields where
  "source_development_result_fields report=(case
    (source_report_selected report,source_report_installed report,source_report_query report) of
    (Some proposal,Some installed,Some query) \<Rightarrow> Some (proposal,installed,query)
    | _ \<Rightarrow> None)"

theorem constructed_source_development_admission:
  "source_development_admission R (construct_source_development m R)=
    source_development_result_fields (construct_source_development m R)"
  by (auto simp: source_development_admission_def construct_source_development_def
    source_development_result_fields_def steered_development_result_def Let_def
    split: option.splits prod.splits if_splits intro: evaluate_workflow_stage_evidence)

declare source_development_packet_def[code del]

lemma source_development_packet_shared_code [code]:
  "source_development_packet m R=(let report=construct_source_development m R in
    (R,report,source_development_result_fields report))"
  by (simp only: source_development_packet_def Let_def constructed_source_development_admission)

text \<open>The result fields are only a projection of material. They are not
  admission of an arbitrary report. The complete constructor equation establishes
  when that projection equals the original admission, including every refusal.
  It consumes the actual steered original-request admission, selected proposal,
  installation and evaluated query evidence. Arbitrary or mutated reports still
  enter the unchanged source_development_admission operation. No later checker
  may substitute the projection without this constructor premise.\<close>

end
