theory Factor_Proof_Node_Extension
  imports Factor_Proof_Node_Code Factor_Reference_Packages
begin

section \<open>A local node can refer to the existing environment\<close>

theorem native_proof_node_extension:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and inputs: "graph_node_inputs_at E D N"
    and finite: "finite D" and functional: "single_valued D"
    and targets: "rel_ran D\<subseteq>environment_positions E"
  shows "\<exists>F u I K. environment_formed F \<and> environment_included E F \<and>
    u\<notin>environment_uses E \<and> native_proof_node_at F u [] N D I K \<and>
    (\<forall>v\<in>environment_uses E. \<forall>A. artifact_at F v A \<longleftrightarrow> artifact_at E v A) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have addresses: "\<forall>s n. (s,n)\<in>D \<longrightarrow> octets_formed (snd n)"
  proof (intro allI impI)
    fix s n assume member: "(s,n)\<in>D"
    have position: "n\<in>environment_positions E"
      by (rule subsetD[OF targets rel_ranI[OF member]])
    show "octets_formed (snd n)" by (rule environment_position_address[OF ef position])
  qed
  obtain R L C I K where code: "proof_node_code_for N D R L C I K"
    using proof_node_code_total[OF ef inputs finite functional addresses] by blast
  have reference_scope: "rel_ran C\<subseteq>environment_positions E"
    using proof_node_reference_boundary[OF inputs targets] code
    by (simp add: proof_node_code_for_def)
  let ?u="fresh_use_map (environment_uses E) None (Some [])"
  have fresh: "?u\<notin>environment_uses E"
    using fresh_use_map_outside[OF environment_uses_finite[OF ef], of None "[]"] by blast
  have finite_use: "finite {?u}" by simp
  have disjoint: "{?u}\<inter>environment_uses E={}" using fresh by blast
  have artifacts: "\<forall>v\<in>{?u}. exact_formed ((\<lambda>_. R) v)"
    and profiles: "\<forall>v\<in>{?u}. reference_table_formed ((\<lambda>_. L) v) ((\<lambda>_. C) v)"
    and bounds: "\<forall>v\<in>{?u}. rel_dom ((\<lambda>_. L) v)\<union>rel_dom ((\<lambda>_. C) v)
      \<subseteq>rra_carrier (object_structure ((\<lambda>_. R) v))"
    using code by (auto simp: proof_node_code_for_def)
  have references: "\<forall>v\<in>{?u}. \<forall>d\<in>rel_ran ((\<lambda>_. C) v).
    d\<in>environment_positions E \<or>
    (fst d\<in>{?u} \<and> snd d\<in>rra_carrier (object_structure ((\<lambda>_. R) (fst d))))"
    using reference_scope by blast
  obtain F where installed: "environment_formed F" "environment_included E F"
    "artifact_at F ?u R" "syntax_references F ?u L C"
    "\<forall>v\<in>environment_uses E. \<forall>A. artifact_at F v A \<longleftrightarrow> artifact_at E v A"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using fresh_reference_environment[OF ef finite_use disjoint artifacts profiles bounds references]
    by auto
  have native: "native_proof_node_at F ?u [] N D I K"
    by (rule proof_node_code_recovers[OF code installed(1,3,4)])
  show ?thesis by (rule exI[of _ F], rule exI[of _ ?u], rule exI[of _ I], rule exI[of _ K])
    (use installed fresh native in blast)
qed

text \<open>
  The node form, binding table, and complete discharge relation are retained.
  This instance of the existing code and reference installation contracts
  permits all discharge targets already present in the environment. Whole
  graph construction additionally supports jointly placed fresh targets.
  Neither placement theorem establishes mathematical validity of a node.
\<close>

end
