theory Factor_Constructed_Development_Execution
  imports Factor_Steered_Execution_Sharing Constructed_Assessment_Functions Factor_Development_Report_Identity
begin

definition development_constructed_fields where
  "development_constructed_fields Q report=(case
    (development_generation report,development_observed_conditions report,
      development_scope_review report,development_comparison report,development_revision report) of
    (Some G,Some observations,Some review,Some comparison,Some revision) \<Rightarrow>
      (let ys=development_generated_values Q G; input=development_review_input Q ys observations in
      if development_conditions Q\<noteq>[] \<and> condition_goals (development_scope_criticism Q)\<noteq>[] \<and>
        list_all (\<lambda>x. x\<noteq>None) observations \<and> development_condition_outputs review=[input] \<and>
        fst (fst (snd revision))
      then Some (map (nth ys) (snd (snd (snd comparison)))) else None)
    | _ \<Rightarrow> None)"

lemma constructed_condition_family_evidence:
  "development_condition_family_evidence Q ys
      (map (\<lambda>C. execute_development_condition C (development_problem Q) ys) (development_conditions Q))=
    list_all (\<lambda>x. x\<noteq>None)
      (map (\<lambda>C. execute_development_condition C (development_problem Q) ys) (development_conditions Q))"
  by (simp add: development_condition_family_evidence_def list_all_iff all_set_conv_all_nth
    constructed_option_evidence[OF execute_development_condition_evidence])

theorem constructed_development_admission:
  "native_development_admission Q (construct_native_development Q)=
    development_constructed_fields Q (construct_native_development Q)"
  by (auto simp: native_development_admission_def development_constructed_fields_def
    construct_native_development_def Let_def constructed_condition_family_evidence
    split: option.splits intro: execute_development_condition_evidence)

definition construct_admitted_development where
  "construct_admitted_development Q=(let report=construct_native_development Q
    in (report,development_constructed_fields Q report))"

theorem construct_admitted_development_exact:
  "construct_admitted_development Q=(construct_native_development Q,
    native_development_admission Q (construct_native_development Q))"
  by (simp only: construct_admitted_development_def Let_def constructed_development_admission)

declare development_producer_from_def[code del]

lemma development_producer_from_constructed_code [code]:
  "development_producer_from m Q report decision=(
    if m=1 then (report\<lparr>development_scope_review:=None\<rparr>,decision)
    else if m=2 then (report\<lparr>development_observed_conditions:=map_option
      (map (map_option development_remove_certificates)) (development_observed_conditions report)\<rparr>,decision)
    else if m=3 then (report\<lparr>development_generation:=map_option (\<lambda>(P,D,A,rows). (P,D,A,drop 1 rows))
      (development_generation report)\<rparr>,decision)
    else if m=4 then (report\<lparr>development_compiled_conditions:=None\<rparr>,decision)
    else if m=5 then (report\<lparr>development_comparison:=None\<rparr>,decision)
    else if m=6 then (report\<lparr>development_revision:=None\<rparr>,decision)
    else if m=7 then (let other=Q\<lparr>development_problem:=Finite_Pair (development_problem Q) (development_problem Q)\<rparr>;
      prepared=construct_admitted_development other in prepared)
    else if m=8 then (report,map_option (take 1) decision)
    else if m=9 then (let other=Q\<lparr>development_scope_criticism:=development_formed_condition\<rparr>;
      prepared=construct_admitted_development other in prepared)
    else (report,decision))"
  by (auto simp: development_producer_from_def construct_admitted_development_exact Let_def split: if_splits)

definition constructed_development_admitter where
  "constructed_development_admitter Q report decision=
    exact_cache_read (native_development_admission Q) (map_of [(report,decision)])"

lemma constructed_development_admitter_exact:
  "decision=native_development_admission Q report \<Longrightarrow>
    constructed_development_admitter Q report decision=native_development_admission Q"
  unfolding constructed_development_admitter_def
  by (rule ext; rule exact_cache_read_correct) (auto split: if_splits)

declare native_development_packet_def[code del]
declare development_producer_def[code del]
declare steered_development_result_prepared_code[code del]
declare development_subject_table_prepared_code[code del]
declare development_producer_packet_prepared_code[code del]

lemma native_development_packet_constructed_code [code]:
  "native_development_packet Q=(let (report,decision)=construct_admitted_development Q
    in (Q,report,decision))"
  by (simp only: native_development_packet_def construct_admitted_development_exact Let_def case_prod_conv)

lemma development_producer_constructed_code [code]:
  "development_producer m Q=(let (report,decision)=construct_admitted_development Q
    in development_producer_from m Q report decision)"
  by (simp only: development_producer_def construct_admitted_development_exact Let_def case_prod_conv)

lemma steered_development_result_constructed_code [code]:
  "steered_development_result m Q=(let (original,decision)=construct_admitted_development Q;
    admit=constructed_development_admitter Q original decision;
    actual=development_producer_from m Q original decision; admission=admit (fst actual)
    in (m,Q,fst actual,snd actual,if snd actual=admission then admission else None))"
  by (simp only: construct_admitted_development_exact Let_def case_prod_conv
    constructed_development_admitter_exact[OF refl] steered_development_result_def development_producer_def)

definition constructed_development_context where
  "constructed_development_context Q=(let (original,decision)=construct_admitted_development Q;
    reference=development_reference Q; admit=constructed_development_admitter Q original decision
    in ((Q,original,reference),development_cell_with_decision Q original reference decision admit))"

lemma constructed_development_context_fields:
  "fst (constructed_development_context Q)=(Q,construct_native_development Q,development_reference Q)"
  "snd (constructed_development_context Q) m=development_producer_cell m
    (Q,construct_native_development Q,development_reference Q)"
  by (simp_all add: constructed_development_context_def construct_admitted_development_exact
    constructed_development_admitter_exact[OF refl] development_cell_with_decision_def
    development_producer_cell_def development_producer_assessment_def Let_def)

lemma development_subject_table_constructed_code [code]:
  "development_subject_table qs=constructed_context_assessment_table development_methods [0..<length qs]
    (\<lambda>w. constructed_development_context (qs!w))"
  unfolding development_subject_table_def
  by (rule sym; rule constructed_context_assessment_table_exact)
    (simp_all add: constructed_development_context_fields development_subject_context_def Let_def)

lemma development_producer_packet_constructed_code [code]:
  "development_producer_packet ws selections=(let table=constructed_context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws
      (\<lambda>w. constructed_development_context (development_case_at w));
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws table
      (\<lambda>(actual,assessment). development_producer_inspect assessment)
    in (table,comparison,Parallel.map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4]
      (fst comparison) (fst (snd comparison))) selections))"
proof -
  have table: "constructed_context_assessment_table cs ws
      (\<lambda>w. constructed_development_context (development_case_at w))=
    context_assessment_table cs ws development_producer_context development_producer_cell" for cs
    by (rule constructed_context_assessment_table_exact)
      (simp_all add: constructed_development_context_fields development_producer_context_def Let_def)
  show ?thesis by (simp only: table development_producer_packet_def Parallel.map_def)
qed

text \<open>Known constructor results discharge the original evidence-inspection
  prerequisites by their established universal theorems. The remaining original
  conditions and critical verdict are still computed. The projection itself
  grants no admission to a supplied report: only the constructor equation permits
  this use. The complete original decision is cached with its actual report;
  every unequal report still receives the original independent admission.
  The original question, reference, all producers and every condition are kept.\<close>

end
