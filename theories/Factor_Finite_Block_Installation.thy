theory Factor_Finite_Block_Installation
  imports Factor_Finite_Syntax_Blocks Factor_Finite_Reference_Environments RRA_Finite_Environment_Preservation
begin

definition finite_install_syntax_block :: "local_address option finite_artifact_environment\<Rightarrow>
    local_address option finite_syntax_block\<Rightarrow>local_address option finite_artifact_environment\<times>local_address option" where
  "finite_install_syntax_block E B=(let u=finite_fresh_use_map (finite_environment_uses E) None (Some []) in
    (finite_fresh_reference_sequence E [u] (\<lambda>_. finite_block_artifact B)
      (\<lambda>_. finite_block_literals B) (\<lambda>_. finite_block_callees B),u))"

theorem finite_install_syntax_block_correct:
  assumes ef: "finite_environment_formed E"
    and formed: "finite_exact_formed (finite_block_artifact B)"
    and profile: "reference_table_formed
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    and bounds: "rel_dom (fset (finite_block_literals B))\<union>rel_dom (fset (finite_block_callees B))\<subseteq>
      fset (finite_carrier (finite_structure (finite_block_artifact B)))"
    and targets: "rel_ran (fset (finite_block_callees B))\<subseteq>environment_positions (decode_finite_environment E)"
    and installed: "finite_install_syntax_block E B=(F,u)"
  shows "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "artifact_at (decode_finite_environment F) u (decode_finite_object (finite_block_artifact B))"
    "syntax_references (decode_finite_environment F) u
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
proof -
  have fields: "u=finite_fresh_use_map (finite_environment_uses E) None (Some [])"
    "F=finite_fresh_reference_sequence E [u] (\<lambda>_. finite_block_artifact B)
      (\<lambda>_. finite_block_literals B) (\<lambda>_. finite_block_callees B)"
    using installed by (auto simp: finite_install_syntax_block_def Let_def)
  have fresh: "u\<notin>fset (finite_environment_uses E)"
    using fresh_use_map_outside[of "fset (finite_environment_uses E)" None "[]"]
    by (simp add: fields(1) finite_fresh_use_map_exact)
  have unique: "distinct [u]" by simp
  have separate: "set [u]\<inter>fset (finite_environment_uses E)={}" using fresh by simp
  have artifacts: "\<forall>v\<in>set [u]. finite_exact_formed (finite_block_artifact B)" using formed by simp
  have profiles: "\<forall>v\<in>set [u]. reference_table_formed
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    using profile by simp
  have bounded: "\<forall>v\<in>set [u]. rel_dom (fset (finite_block_literals B))\<union>rel_dom (fset (finite_block_callees B))\<subseteq>
      fset (finite_carrier (finite_structure (finite_block_artifact B)))" using bounds by simp
  have callees: "\<forall>v\<in>set [u]. \<forall>d\<in>rel_ran (fset (finite_block_callees B)).
    d\<in>environment_positions (decode_finite_environment E) \<or>
    (fst d\<in>set [u] \<and> snd d\<in>fset (finite_carrier (finite_structure (finite_block_artifact B))))"
    using targets by blast
  note properties=finite_fresh_reference_sequence_properties[where E=E and us="[u]"
    and R="\<lambda>_. finite_block_artifact B" and L="\<lambda>_. finite_block_literals B" and C="\<lambda>_. finite_block_callees B",
    OF ef unique separate artifacts profiles bounded callees]
  have actual: "finite_environment_formed F \<and>
      environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
      artifact_at (decode_finite_environment F) u (decode_finite_object (finite_block_artifact B)) \<and>
      syntax_references (decode_finite_environment F) u
        (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B)) \<and>
      finite_environment_agrees_on E F (finite_environment_uses E)"
    using properties by (simp only: Let_def fields(2)[symmetric] set_simps finite_environment_agrees_on_correct; blast)
  show "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "artifact_at (decode_finite_environment F) u (decode_finite_object (finite_block_artifact B))"
    "syntax_references (decode_finite_environment F) u
      (map_relation_values decode_finite_object (fset (finite_block_literals B))) (fset (finite_block_callees B))"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    using actual fresh by blast+
qed

text \<open>
  A fresh block uses the original complete reference installation sequence.
  Every literal and callee table is installed unchanged. Its formation and
  recovery prerequisites retain the actual source positions of all callees.
  The preservation conclusion covers every old artifact and outgoing binding.
\<close>

end
