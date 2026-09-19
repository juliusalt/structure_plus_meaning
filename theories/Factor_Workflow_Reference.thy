theory Factor_Workflow_Reference
  imports Factor_Workflow_Readiness Factor_Finite_Proof_Inspection
begin

definition workflow_stage_reference :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term list option" where
  "workflow_stage_reference S x=(if workflow_scope_result S x=None then None else
    case finite_native_source (workflow_source S)
      (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
    | Some P \<Rightarrow> (if workflow_entry S |\<notin>| finite_system_definitions P then None else
      let D=workflow_stage_demand P S x in
      map_option (\<lambda>(Q,A). filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
        (workflow_scope_values S x))
        (finite_native_program_evaluation (workflow_source S) (workflow_source_use S)
          (workflow_source_root S) D)))"

lemma workflow_stage_reference_projection:
  "map_option (\<lambda>(P,D,A,T,ys). ys) (evaluate_workflow_stage S x)=workflow_stage_reference S x"
  by (auto simp: evaluate_workflow_stage_def workflow_stage_reference_def
      finite_native_program_proofs_projection[symmetric] option.map_comp comp_def
      map_prod_def split_def Let_def split: option.splits if_splits prod.splits)

theorem workflow_stage_reference_exact:
  assumes reference: "workflow_stage_reference S x=Some ys"
  shows "set ys={y. workflow_stage_relation S x y}"
proof -
  obtain P D A T where result: "evaluate_workflow_stage S x=Some (P,D,A,T,ys)"
    using reference by (auto simp: workflow_stage_reference_projection[symmetric]
      split: option.splits prod.splits)
  show ?thesis by (rule evaluate_workflow_stage_exact(1)[OF result])
qed

fun workflow_reference_paths where
  "workflow_reference_paths [] problem prior=[prior]"
| "workflow_reference_paths (S#Ss) problem prior=(case workflow_stage_reference S
      (workflow_stage_input problem prior) of None \<Rightarrow> []
    | Some ys \<Rightarrow> concat (map (\<lambda>y. workflow_reference_paths Ss problem (prior@[y])) ys))"

theorem workflow_reference_paths_exact:
  "workflow_completed_paths (execute_workflow stages problem prior)=workflow_reference_paths stages problem prior"
  by (induction stages arbitrary: prior)
    (auto simp: Let_def comp_def workflow_stage_reference_projection[symmetric]
      split: option.splits prod.splits)

definition workflow_stage_evidence :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    native_workflow_stage_result \<Rightarrow> bool" where
  "workflow_stage_evidence S input result=(case result of (P,D,A,T,ys) \<Rightarrow>
    workflow_scope_result S input\<noteq>None \<and>
    finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P \<and>
    workflow_entry S |\<in>| finite_system_definitions P \<and>
    D=workflow_stage_demand P S input \<and>
    finite_native_program_evaluation (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A) \<and>
    fimage fst T=A \<and> finite_inspection_rows_hold (finite_proof_inspection P T) \<and>
    ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair input y) |\<in>| A)
      (workflow_scope_values S input))"

lemma evaluate_workflow_stage_evidence:
  "evaluate_workflow_stage S input=Some result \<Longrightarrow> workflow_stage_evidence S input result"
proof -
  assume result: "evaluate_workflow_stage S input=Some result"
  obtain P D A T ys where shape: "result=(P,D,A,T,ys)" by (cases result) auto
  have actual: "evaluate_workflow_stage S input=Some (P,D,A,T,ys)" using result shape by simp
  show ?thesis using evaluate_workflow_stage_fields[OF actual]
    evaluate_workflow_stage_exact(2,3)[OF actual]
    finite_native_program_proofs_evaluation[OF evaluate_workflow_stage_fields(4)[OF actual]]
    by (simp only: shape workflow_stage_evidence_def case_prod_conv finite_proof_inspection_exact; blast)
qed

text \<open>
  The independent complete-answer reference evaluates the original native
  source. It does not consume a candidate's proposed certificates or claimed
  acceptance. The evidence inspection separately checks source identity,
  original demand, all answers, every actual certificate and ordered results.
  Equal completed paths alone cannot replace that inspection.
\<close>

end
