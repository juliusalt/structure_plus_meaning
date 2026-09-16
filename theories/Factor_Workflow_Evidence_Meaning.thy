theory Factor_Workflow_Evidence_Meaning
  imports Factor_Workflow_Reference
begin

lemma workflow_stage_relation_at_source:
  assumes source: "finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P"
    and entry: "workflow_entry S |\<in>| finite_system_definitions P"
  shows "workflow_stage_relation S x y \<longleftrightarrow> y\<in>set (workflow_scope_values S x) \<and>
    (workflow_entry S,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning (decode_finite_system P)"
  using source entry by (auto simp: workflow_stage_relation_def
    finite_native_source_correct[symmetric] finite_system_definitions_correct[symmetric])

theorem workflow_stage_evidence_exact:
  assumes evidence: "workflow_stage_evidence S x (P,D,A,T,ys)"
  shows "ys=filter (workflow_stage_relation S x) (workflow_scope_values S x)"
proof -
  have source: "finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P"
    and entry: "workflow_entry S |\<in>| finite_system_definitions P"
    and demand: "D=finite_program_term_demand P (workflow_stage_arguments S x)"
    and evaluation: "finite_native_program_evaluation (workflow_source S) (workflow_source_use S)
      (workflow_source_root S) D=Some (P,A)"
    and selected: "ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) (workflow_scope_values S x)"
    using evidence by (auto simp: workflow_stage_evidence_def)
  have each: "(workflow_entry S,Finite_Pair x y) |\<in>| A \<longleftrightarrow> workflow_stage_relation S x y"
    if member: "y\<in>set (workflow_scope_values S x)" for y
  proof -
    have asked: "(workflow_entry S,Finite_Pair x y) |\<in>| D"
      unfolding demand by (rule finite_program_term_demand_root[OF entry])
        (use member in \<open>auto simp: workflow_stage_arguments_def fset_of_list.rep_eq\<close>)
    show ?thesis using finite_native_program_evaluation_call[OF evaluation asked]
      by (simp add: workflow_stage_relation_at_source[OF source entry] member)
  qed
  show ?thesis unfolding selected by (rule filter_cong[OF refl]) (use each in blast)
qed

lemma workflow_stage_evidence_answer:
  assumes evidence: "workflow_stage_evidence S input (P,D,A,T,ys)" and answer: "y\<in>set ys"
  shows "\<exists>N. native_package_at (decode_finite_environment (workflow_source S))
      (workflow_source_use S) (workflow_source_root S) N \<and>
      (workflow_entry S,Pair_Term (decode_finite_term input) (decode_finite_term y))\<in>positive_meaning N"
  using answer by (auto simp: workflow_stage_evidence_exact[OF evidence] workflow_stage_relation_def)

text \<open>Independent evidence inspection recovers the entire original ordered
  answer filter, including repeated results. This fact applies to every inspected
  stage result; it does not assume that a particular producer constructed it.\<close>

end
