theory Factor_Finite_Proof_Node_Installation
  imports Factor_Finite_Proof_Nodes Factor_Finite_Block_Installation Factor_Executable_Metadata
begin

definition finite_proof_node_installable where
  "finite_proof_node_installable E N D=(finite_proof_node_ready E N D \<and>
    fimage snd D |\<subseteq>| finite_environment_positions E)"

definition finite_extend_proof_node where
  "finite_extend_proof_node E N D=(if fimage snd D |\<subseteq>| finite_environment_positions E then
    map_option (finite_install_syntax_block E) (finite_compile_proof_node E N D) else None)"

theorem finite_extend_proof_node_domain:
  "(\<exists>F u. finite_extend_proof_node E N D=Some (F,u)) \<longleftrightarrow> finite_proof_node_installable E N D"
  unfolding finite_extend_proof_node_def finite_proof_node_installable_def
  by (cases "fimage snd D |\<subseteq>| finite_environment_positions E";
      cases "finite_compile_proof_node E N D")
    (auto simp: finite_compile_proof_node_domain[symmetric])

theorem finite_extend_proof_node_correct:
  assumes extended: "finite_extend_proof_node E N D=Some (F,u)"
  shows "finite_proof_node_installable E N D"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "\<exists>B. finite_compile_proof_node E N D=Some B \<and>
      ((N,D),finite_block_interior B,finite_block_slots B) |\<in>| finite_proof_node_readings F u []"
proof -
  have available: "finite_proof_node_installable E N D"
    using extended finite_extend_proof_node_domain[of E N D] by blast
  obtain B where compiled: "finite_compile_proof_node E N D=Some B"
    and installed: "finite_install_syntax_block E B=(F,u)"
    using extended by (auto simp: finite_extend_proof_node_def split: if_splits option.splits)
  have ready: "finite_proof_node_ready E N D"
    and code: "proof_node_code_for (decode_finite_graph_node N) (fset D)
      (decode_finite_object (finite_block_artifact B))
      (map_relation_values decode_finite_object (fset (finite_block_literals B)))
      (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
    by (rule finite_compile_proof_node_correct[OF compiled])+
  have ef: "finite_environment_formed E"
    using ready by (simp only: finite_proof_node_ready_exact finite_environment_formed_correct; blast)
  have inputs: "graph_node_inputs_at (decode_finite_environment E) (fset D) (decode_finite_graph_node N)"
    using ready by (simp only: finite_proof_node_ready_exact; blast)
  have targets: "rel_ran (fset D)\<subseteq>environment_positions (decode_finite_environment E)"
    using available by (simp only: finite_proof_node_installable_def less_eq_fset.rep_eq fimage.rep_eq
      finite_environment_positions_correct rel_ran_image; blast)
  have formed: "finite_exact_formed (finite_block_artifact B)"
    and profile: "reference_table_formed
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    and bounds: "rel_dom (fset (finite_block_literals B))\<union>rel_dom (fset (finite_block_callees B))\<subseteq>
      fset (finite_carrier (finite_structure (finite_block_artifact B)))"
    using proof_node_code_properties(1,3,4)[OF code]
    by (simp_all only: finite_exact_formed_correct map_relation_values_domain
      decode_finite_object_selectors decode_finite_structure_fields)
  have references: "rel_ran (fset (finite_block_callees B))\<subseteq>environment_positions (decode_finite_environment E)"
    using proof_node_reference_boundary[OF inputs targets] code
    by (simp only: proof_node_code_for_def; blast)
  have actual: "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "artifact_at (decode_finite_environment F) u (decode_finite_object (finite_block_artifact B))"
    "syntax_references (decode_finite_environment F) u
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    by (rule finite_install_syntax_block_correct[OF ef formed profile bounds references installed])+
  have recovered: "((N,D),finite_block_interior B,finite_block_slots B) |\<in>| finite_proof_node_readings F u []"
    using proof_node_code_recovers[OF code _ actual(4,5)] actual(1)
    by (simp only: finite_environment_formed_correct finite_proof_node_readings_correct)
  show "finite_proof_node_installable E N D" "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "\<exists>B. finite_compile_proof_node E N D=Some B \<and>
      ((N,D),finite_block_interior B,finite_block_slots B) |\<in>| finite_proof_node_readings F u []"
    using available actual compiled recovered by blast+
qed

export_code finite_extend_proof_node finite_proof_node_installable checking SML

text \<open>
  Local installation additionally requires every proof target in the actual
  environment. The compiler can represent future targets; that wider domain
  remains separate. A successful extension recovers the original node form,
  clause, complete binding family, indexed targets, and exact position boundary
  through the existing finite native reader. It preserves every old artifact
  and outgoing binding. Metadata recovery does not establish the inference.
\<close>

end
