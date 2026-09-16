theory Factor_Workflow_Stage
  imports Factor_Finite_Native_Proof_Construction Factor_Native_Generation_Semantics
begin

datatype workflow_output_scope =
    Workflow_Input
  | Workflow_Values "finite_factor_term list"
  | Workflow_Generated "local_address option definition_site"

record native_workflow_stage =
  workflow_source :: "local_address option finite_artifact_environment"
  workflow_source_use :: "local_address option"
  workflow_source_root :: local_address
  workflow_entry :: "local_address option definition_site"
  workflow_outputs :: workflow_output_scope

definition workflow_scope_result :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term list option" where
  "workflow_scope_result S x=(case workflow_outputs S of Workflow_Input \<Rightarrow> Some [x]
    | Workflow_Values xs \<Rightarrow> Some xs
    | Workflow_Generated entry \<Rightarrow> map_option (\<lambda>(P,D,A,rows).
        finite_generated_outputs entry x rows)
      (finite_native_generation (workflow_source S) (workflow_source_use S) (workflow_source_root S) x))"

definition workflow_scope_values :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term list" where
  "workflow_scope_values S x=case_option [] id (workflow_scope_result S x)"

type_synonym native_workflow_stage_result =
  "local_address option finite_native_system \<times>
    (local_address option definition_site \<times> finite_factor_term) fset \<times>
    (local_address option definition_site \<times> finite_factor_term) fset \<times>
    ((local_address option definition_site \<times> finite_factor_term) \<times>
      (local_address,local_address,local_address) finite_schema_proof) fset \<times>
    finite_factor_term list"

definition workflow_stage_arguments :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term fset" where
  "workflow_stage_arguments S x=fset_of_list
    (map (Finite_Pair x) (workflow_scope_values S x))"

definition evaluate_workflow_stage ::
  "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow> native_workflow_stage_result option" where
  "evaluate_workflow_stage S x=(if workflow_scope_result S x=None then None else
    case finite_native_source (workflow_source S)
      (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
    | Some P \<Rightarrow> (if workflow_entry S |\<notin>| finite_system_definitions P then None else
      let D=finite_program_term_demand P (workflow_stage_arguments S x) in
      map_option (\<lambda>(Q,A,T). (Q,D,A,T,
        filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
          (workflow_scope_values S x)))
        (finite_native_program_proofs (workflow_source S) (workflow_source_use S)
          (workflow_source_root S) D)))"

definition workflow_stage_relation :: "native_workflow_stage \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term \<Rightarrow> bool" where
  "workflow_stage_relation S x y \<longleftrightarrow>
    y\<in>set (workflow_scope_values S x) \<and>
    (\<exists>P. native_package_at (decode_finite_environment (workflow_source S))
      (workflow_source_use S) (workflow_source_root S) (decode_finite_system P) \<and>
      workflow_entry S\<in>system_definitions (decode_finite_system P) \<and>
      (workflow_entry S,Pair_Term (decode_finite_term x) (decode_finite_term y))
        \<in>positive_meaning (decode_finite_system P))"

lemma evaluate_workflow_stage_fields:
  assumes result: "evaluate_workflow_stage S x=Some (P,D,A,T,ys)"
  shows "finite_native_source (workflow_source S) (workflow_source_use S)
      (workflow_source_root S)=Some P"
    "workflow_entry S |\<in>| finite_system_definitions P"
    "D=finite_program_term_demand P (workflow_stage_arguments S x)"
    "finite_native_program_proofs (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A,T)"
    "ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
      (workflow_scope_values S x)"
    "workflow_scope_result S x\<noteq>None"
proof -
  obtain Q where original: "finite_native_source (workflow_source S) (workflow_source_use S)
      (workflow_source_root S)=Some Q"
    and entry: "workflow_entry S |\<in>| finite_system_definitions Q"
    and demand: "D=finite_program_term_demand Q (workflow_stage_arguments S x)"
    and proofs: "finite_native_program_proofs (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A,T)"
    and selected: "ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
      (workflow_scope_values S x)"
    using result by (auto simp: evaluate_workflow_stage_def Let_def
      split: option.splits prod.splits if_splits)
  have actual: "finite_native_source (workflow_source S) (workflow_source_use S)
      (workflow_source_root S)=Some P"
    using proofs by (simp only: finite_native_program_proofs_conditions finite_native_source_correct; blast)
  have same: "Q=P" using original actual by simp
  have ready: "workflow_scope_result S x\<noteq>None"
    using result by (auto simp: evaluate_workflow_stage_def split: if_splits)
  show "finite_native_source (workflow_source S) (workflow_source_use S)
      (workflow_source_root S)=Some P"
    "workflow_entry S |\<in>| finite_system_definitions P"
    "D=finite_program_term_demand P (workflow_stage_arguments S x)"
    "finite_native_program_proofs (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A,T)"
    "ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
      (workflow_scope_values S x)"
    "workflow_scope_result S x\<noteq>None"
    using original entry demand proofs selected ready by (simp_all add: same)
qed

theorem evaluate_workflow_stage_exact:
  assumes result: "evaluate_workflow_stage S x=Some (P,D,A,T,ys)"
  shows "set ys={y. workflow_stage_relation S x y}"
    "fimage fst T=A" "finite_proofs_sound P T"
    "y\<in>set ys \<Longrightarrow> \<exists>p. ((workflow_entry S,Finite_Pair x y),p) |\<in>| T"
proof -
  have source: "finite_native_source (workflow_source S) (workflow_source_use S)
      (workflow_source_root S)=Some P"
    and entry: "workflow_entry S |\<in>| finite_system_definitions P"
    and demand: "D=finite_program_term_demand P (workflow_stage_arguments S x)"
    and proofs: "finite_native_program_proofs (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A,T)"
    and selected: "ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A)
      (workflow_scope_values S x)"
    by (rule evaluate_workflow_stage_fields[OF result])+
  have each: "(workflow_entry S,Finite_Pair x y) |\<in>| A \<longleftrightarrow>
      (workflow_entry S,Pair_Term (decode_finite_term x) (decode_finite_term y))
        \<in>positive_meaning (decode_finite_system P)"
    if member: "y\<in>set (workflow_scope_values S x)" for y
  proof -
    have asked: "(workflow_entry S,Finite_Pair x y) |\<in>| D"
      unfolding demand
      by (rule finite_program_term_demand_root[OF entry])
        (use member in \<open>auto simp: workflow_stage_arguments_def fset_of_list.rep_eq\<close>)
    show ?thesis using finite_native_program_evaluation_call[OF
      finite_native_program_proofs_evaluation[OF proofs] asked] by simp
  qed
  show "set ys={y. workflow_stage_relation S x y}"
    using each source entry
    by (auto simp: selected workflow_stage_relation_def finite_native_source_correct[symmetric]
      finite_system_definitions_correct[symmetric])
  show domain: "fimage fst T=A" and sound: "finite_proofs_sound P T"
    by (rule finite_native_program_proofs_correct[OF proofs])+
  show "y\<in>set ys \<Longrightarrow> \<exists>p. ((workflow_entry S,Finite_Pair x y),p) |\<in>| T"
  proof -
    assume member: "y\<in>set ys"
    have answer: "(workflow_entry S,Finite_Pair x y) |\<in>| A"
      using member by (simp only: selected set_filter; blast)
    show "\<exists>p. ((workflow_entry S,Finite_Pair x y),p) |\<in>| T"
      using answer by (simp only: domain[symmetric] finite_first_projection_member)
  qed
qed

export_code evaluate_workflow_stage checking SML

text \<open>
  A stage reads its actual native source and derives answers and certificates
  for every permitted complete input/output pair. No truth or certificate is
  supplied by the caller. Candidate order and repeated values are retained.
  An unreadable source, absent entry or unavailable finite evaluation prevents
  the stage from returning a result; a successful empty answer is distinct.

  The native source meaning is exact. Whether that source expresses the
  independently required workflow condition and whether the finite candidate
  scope is adequate are separate premises of the whole workflow contract.
\<close>

end
