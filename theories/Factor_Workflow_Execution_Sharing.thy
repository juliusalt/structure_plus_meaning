theory Factor_Workflow_Execution_Sharing
  imports Factor_Workflow_Reference Native_Execution_Refinements
begin

declare finite_native_generation_def[code del]

lemma finite_native_generation_source_shared_code [code]:
  "finite_native_generation E u r x=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> let D=finite_program_term_demand P {|x|} in
      map_option (\<lambda>A. (P,D,A,finite_program_generation_rows P
        (finite_native_seed_rows P x A))) (finite_program_evaluation P D))"
  by (auto simp: finite_native_generation_def finite_native_program_evaluation_def
    finite_source_computation_def Let_def option.map_comp comp_def split: option.splits)

declare evaluate_workflow_stage_def[code del]

lemma evaluate_workflow_stage_source_shared_code [code]:
  "evaluate_workflow_stage S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        let D=finite_program_call_closure P
          (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys))) in
        map_option (\<lambda>(A,T). (P,D,A,T,
          filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys))
          (finite_program_proofs P D)))"
  by (auto simp: evaluate_workflow_stage_def workflow_scope_values_def workflow_stage_arguments_def
    workflow_stage_demand_def workflow_stage_requests_def finite_native_program_proofs_def finite_source_computation_def Let_def option.map_comp comp_def
    split: option.splits prod.splits)

declare workflow_stage_reference_def[code del]

lemma workflow_stage_reference_source_shared_code [code]:
  "workflow_stage_reference S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        let D=finite_program_call_closure P
          (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys))) in
        map_option (\<lambda>A. filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys)
          (finite_program_evaluation P D)))"
  by (auto simp: workflow_stage_reference_def workflow_scope_values_def workflow_stage_arguments_def
    workflow_stage_demand_def workflow_stage_requests_def finite_native_program_evaluation_def finite_source_computation_def Let_def option.map_comp comp_def split: option.splits)

declare workflow_stage_evidence_def[code del]

lemma workflow_stage_evidence_source_shared_code [code]:
  "workflow_stage_evidence S input result=(case result of (P,D,A,T,ys) \<Rightarrow>
    (case workflow_scope_result S input of None \<Rightarrow> False | Some scope \<Rightarrow>
      finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P \<and>
      workflow_entry S |\<in>| finite_system_definitions P \<and>
      D=finite_program_call_closure P
        (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair input) scope))) \<and>
      finite_program_evaluation P D=Some A \<and>
      fimage fst T=A \<and> finite_inspection_rows_hold (finite_proof_inspection P T) \<and>
      ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair input y) |\<in>| A) scope))"
  by (auto simp: workflow_stage_evidence_def workflow_scope_values_def workflow_stage_arguments_def
    workflow_stage_demand_def workflow_stage_requests_def finite_native_program_evaluation_def finite_source_computation_def Let_def
    split: option.splits prod.splits)

text \<open>The actual complete scope and source are read once per stage.
  Generation, certificates, the independent reference, and arbitrary submitted
  evidence retain separate operations and their original complete equations.
  In particular the evidence reader still checks the submitted program against
  the actual source, every certificate, all answers and the ordered output.
  No supplied program or constructor assertion replaces those checks.\<close>

end
