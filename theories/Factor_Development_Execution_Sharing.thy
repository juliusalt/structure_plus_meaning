theory Factor_Development_Execution_Sharing
  imports Factor_Development_Subjects Native_Execution_Refinements
begin

definition execute_compiled_development_condition where
  "execute_compiled_development_condition x compiled=(case compiled of None \<Rightarrow> None
    | Some S \<Rightarrow> map_option (Pair S) (evaluate_workflow_stage S x))"

lemma execute_compiled_development_condition_exact:
  "execute_compiled_development_condition x
    (compile_workflow_requirement (development_condition_requirement C ys))=
    execute_development_condition C x ys"
  by (simp only: execute_compiled_development_condition_def execute_development_condition_def)

declare development_condition_evidence_def[code del]

lemma development_condition_evidence_domain_first_code [code]:
  "development_condition_evidence C x ys execution=(case execution of (S,P,D,A,T,zs) \<Rightarrow>
    fimage fst T=A \<and>
    compile_workflow_requirement (development_condition_requirement C ys)=Some S \<and>
    workflow_stage_evidence S x (P,D,A,T,zs))"
  by (cases execution)
    (auto simp: development_condition_evidence_def workflow_stage_evidence_def split: prod.splits)

definition development_revision_from_comparison where
  "development_revision_from_comparison nc nf selected comparison=(case comparison of
    (rows,relation,chosen,adequate) \<Rightarrow>
      investigation_cycle_report [0..<nc] [0..<nf] rows relation selected)"

lemma development_revision_from_comparison_exact:
  "development_revision_from_comparison (length ys) (length observations) selected
    (development_compare ys observations)=development_revise ys observations selected"
  by (simp only: development_revision_from_comparison_def development_revise_def)

definition construct_shared_development where
  "construct_shared_development Q=(let generation=finite_native_generation (development_source Q)
      (development_source_use Q) (development_source_root Q) (development_problem Q) in
    case generation of None \<Rightarrow> \<lparr>development_generation=None,development_compiled_conditions=None,
      development_observed_conditions=None,development_scope_review=None,development_comparison=None,development_revision=None\<rparr>
    | Some G \<Rightarrow> (let ys=development_generated_values Q G;
      compiled=Parallel.map (\<lambda>C. compile_workflow_requirement (development_condition_requirement C ys))
        (development_conditions Q);
      observations=Parallel.map (execute_compiled_development_condition (development_problem Q)) compiled;
      input=development_review_input Q ys observations;
      review=execute_development_condition (development_scope_criticism Q) input [input];
      comparison=development_compare ys observations;
      revision=development_revision_from_comparison (length ys) (length observations)
        (development_selected_facets Q) comparison in
      \<lparr>development_generation=Some G,development_compiled_conditions=Some compiled,
        development_observed_conditions=Some observations,development_scope_review=review,
        development_comparison=Some comparison,development_revision=Some revision\<rparr>))"

theorem construct_shared_development_exact:
  "construct_shared_development Q=construct_native_development Q"
  by (cases "finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)")
    (simp_all add: construct_shared_development_def construct_native_development_def Parallel.map_def
    map_map comp_def execute_compiled_development_condition_exact
    development_revision_from_comparison_exact Let_def)

declare construct_native_development_def[code del]

lemma construct_native_development_shared_code [code]:
  "construct_native_development Q=construct_shared_development Q"
  by (rule construct_shared_development_exact[symmetric])

declare native_development_admission_def[code del]

lemma native_development_admission_shared_code [code]:
  "native_development_admission Q report=(if development_compiled_conditions report=None \<or>
    development_comparison report=None \<or> development_revision report=None then None else
    case development_generation report of None \<Rightarrow> None
    | Some G \<Rightarrow> (case development_observed_conditions report of None \<Rightarrow> None
    | Some observations \<Rightarrow> (case development_scope_review report of None \<Rightarrow> None
    | Some review \<Rightarrow> (let ys=development_generated_values Q G;
      input=development_review_input Q ys observations;
      comparison=development_compare ys observations;
      revision=development_revision_from_comparison (length ys) (length observations)
        (development_selected_facets Q) comparison in
      if development_condition_outputs review=[input] \<and>
        development_generation report=finite_native_generation (development_source Q)
          (development_source_use Q) (development_source_root Q) (development_problem Q) \<and>
        development_conditions Q\<noteq>[] \<and> condition_goals (development_scope_criticism Q)\<noteq>[] \<and>
        development_compiled_conditions report=Some (map (\<lambda>C.
          compile_workflow_requirement (development_condition_requirement C ys)) (development_conditions Q)) \<and>
        development_condition_family_evidence Q ys observations \<and>
        development_condition_evidence (development_scope_criticism Q) input [input] review \<and>
        development_comparison report=Some comparison \<and>
        development_revision report=Some revision \<and> fst (fst (snd revision))
      then Some (map (nth ys) (snd (snd (snd comparison)))) else None))))"
  by (cases "development_generation report";
      cases "development_observed_conditions report"; cases "development_scope_review report")
    (auto simp: native_development_admission_def Let_def development_revision_from_comparison_exact
      split: if_splits)

definition development_cell_with_decision where
  "development_cell_with_decision Q original reference decision admit m=(let
    actual=development_producer_from m Q original decision;
    result=snd actual; values=case_option [] id result; expected=case_option [] id reference
    in (actual,(set values\<subseteq>set expected,set expected\<subseteq>set values,result=reference,
      result=admit (fst actual),fst actual=original)))"

definition development_cell_with_admission where
  "development_cell_with_admission Q original reference admit=
    development_cell_with_decision Q original reference (admit original) admit"

definition prepared_development_cell where
  "prepared_development_cell context=(case context of (Q,original,reference) \<Rightarrow>
    let admit=prepared_computed_function (native_development_admission Q) [original]
    in development_cell_with_admission Q original reference admit)"

theorem prepared_development_cell_exact:
  "prepared_development_cell context m=development_producer_cell m context"
  by (cases "context")
    (simp add: prepared_development_cell_def prepared_computed_function_exact
      development_cell_with_admission_def development_cell_with_decision_def development_producer_cell_def
      development_producer_assessment_def Let_def split: prod.splits)

declare development_subject_table_def[code del]

lemma development_subject_table_prepared_code [code]:
  "development_subject_table qs=prepared_context_assessment_table development_methods [0..<length qs]
    (development_subject_context qs) prepared_development_cell"
  unfolding development_subject_table_def
  by (rule sym; rule prepared_context_assessment_table_exact; rule prepared_development_cell_exact)

declare development_producer_packet_def[code del]

lemma development_producer_packet_prepared_code [code]:
  "development_producer_packet ws selections=(let table=prepared_context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws
      development_producer_context prepared_development_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws table
      (\<lambda>(actual,assessment). development_producer_inspect assessment)
    in (table,comparison,Parallel.map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4]
      (fst comparison) (fst (snd comparison))) selections))"
  by (simp only: development_producer_packet_def
    prepared_context_assessment_table_exact[OF prepared_development_cell_exact] Parallel.map_def)

text \<open>The original complete question determines all prepared computations.
  Compiled conditions and comparison/revision results are shared; independent
  condition executions and initial-selection cycles preserve their ordered maps.
  A computed admission cache contains the actual result on the original report.
  Every changed report uses its exact original admission, with no correctness
  assumption about a producer and no exemption for omitted evidence or criticism.
  Both admission and construction equations apply to arbitrary complete inputs;
  the unchanged subject equations still connect every cell to its original goal.
  Runtime and retained-output measurements are separate from these equations.\<close>

end
