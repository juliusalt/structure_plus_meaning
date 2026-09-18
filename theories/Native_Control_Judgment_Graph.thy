theory Native_Control_Judgment_Graph
  imports Native_Control_Judgment_Review Factor_Finite_Program_Proofs
begin

theorem received_judgment_graph_complete:
  assumes result: "judgment_bridge_receive report=Some rows"
    and row: "(i,Some A)\<in>set rows"
    and program: "P=decode_finite_system (judgment_bridge_program (judgment_bridge_candidates!i))"
    and known: "K=decode_finite_call_term ` fset A"
    and graph: "schema_graph_derives P G root d t H"
    and closed: "remaining_obligations (inference_closure (schema_inference_rules P) K) H={}"
  shows "(d,t)\<in>positive_meaning P"
  by (rule schema_graph_development_complete[OF graph _ closed])
    (simp only: program known; rule judgment_bridge_receive_known[OF result row])

definition judgment_bridge_certificates where
  "judgment_bridge_certificates b=finite_program_proofs
    (judgment_bridge_program b) judgment_bridge_demands"

theorem judgment_bridge_certificates_original_truth:
  assumes condition: "judgment_bridge_condition b syntax_judgment_cases"
    and certificates: "judgment_bridge_certificates b=Some (A,T)"
    and scope: "s\<in>set syntax_judgment_cases"
  shows "syntax_judgment_truth s \<longleftrightarrow> (\<exists>p. (judgment_bridge_call s,p) |\<in>| T)"
proof -
  have demand: "judgment_bridge_call s |\<in>| judgment_bridge_demands"
    using scope by (auto simp: judgment_bridge_demands_def fset_of_list_elem)
  show ?thesis
    using finite_program_proofs_complete[OF certificates[unfolded judgment_bridge_certificates_def],
      of "fst (judgment_bridge_call s)" "snd (judgment_bridge_call s)"] demand
      judgment_bridge_program_meaning[OF condition, of s]
    by (simp add: judgment_bridge_call_def)
qed

text \<open>The graph receiver consumes the known-call premise derived from the
  actual evaluated program, and retains the complete graph and residual-closure
  requirements. Certificate construction is the existing native proof operation;
  the theorem does not invent a graph, a package reading or a policy cause.\<close>

end
