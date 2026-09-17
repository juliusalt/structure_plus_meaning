theory Factor_Finite_Interface_Syntax
  imports Factor_Finite_Pattern_Syntax RRA_Finite_Fresh_Addresses Factor_Interface_Construction
begin

section \<open>The executable interface supplies its actual frame and root\<close>

definition finite_interface_code :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern \<Rightarrow>
    finite_exact_artifact\<times>local_address" where
  "finite_interface_code f p=(let R=finite_pattern_syntax f p in
    case finite_four_addresses (finite_carrier (finite_structure R)) of (b,r,s,t) \<Rightarrow>
      (finite_scope_wrapper R (fimage f (finite_pattern_variables p)) b r s t,r))"

theorem finite_interface_code_properties:
  assumes pattern: "finite_pattern_formed p"
    and addressing: "binder_addressing (pattern_variables (decode_finite_pattern p)) f"
    and result: "finite_interface_code f p=(R,r)"
  shows "finite_exact_formed R"
    "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    "reference_table_formed (pattern_literal_bindings (decode_finite_pattern p)) {}"
    "rel_dom (pattern_literal_bindings (decode_finite_pattern p))\<subseteq>
      rra_carrier (object_structure (decode_finite_object R))"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
      syntax_references E u (pattern_literal_bindings (decode_finite_pattern p)) {} \<longrightarrow>
      (\<exists>I K. scoped_pattern_at E u r (rename_pattern f (decode_finite_pattern p)) I K \<and>
        rra_carrier (object_structure (decode_finite_object R))=I\<union>K)"
proof -
  let ?P="decode_finite_pattern p"
  let ?B="finite_pattern_syntax f p"
  let ?U="finite_carrier (finite_structure ?B)"
  obtain b a s t where headers: "finite_four_addresses ?U=(b,a,s,t)" by (metis surjective_pairing)
  have carrier: "fset ?U=rra_carrier (object_structure (pattern_syntax f ?P))"
    by (simp only: decode_finite_pattern_syntax[symmetric]
      decode_finite_object_selectors decode_finite_structure_fields)
  have positions: "distinct [b,a,s,t]" "{b,a,s,t}\<inter>rra_carrier (object_structure (pattern_syntax f ?P))={}"
    "\<forall>x\<in>{b,a,s,t}. octets_formed x"
    using finite_four_addresses_properties[OF headers] by (simp_all only: carrier)
  have pf: "pattern_formed ?P" using pattern by (simp only: finite_pattern_formed_correct)
  interpret code: interface_syntax_construction ?P f b a s t
    by (rule interface_syntax_construction.intro[OF pf addressing positions])
  have fields: "R=finite_scope_wrapper ?B (fimage f (finite_pattern_variables p)) b a s t" "r=a"
    using result by (auto simp: finite_interface_code_def Let_def headers)
  have actual: "decode_finite_object R=code.framed"
    by (simp only: fields(1) decode_finite_scope_wrapper decode_finite_pattern_syntax
      fimage.rep_eq finite_pattern_variables_correct)
  show "finite_exact_formed R" by (simp only: finite_exact_formed_correct actual; rule code.formed)
  show "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    "reference_table_formed (pattern_literal_bindings ?P) {}"
    "rel_dom (pattern_literal_bindings ?P)\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    using code.counts code.root code.profile code.bounds by (simp_all only: actual fields(2))
  show "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
    syntax_references E u (pattern_literal_bindings ?P) {} \<longrightarrow>
    (\<exists>I K. scoped_pattern_at E u r (rename_pattern f ?P) I K \<and>
      rra_carrier (object_structure (decode_finite_object R))=I\<union>K)"
    using code.recover by (simp only: actual fields(2); blast)
qed

text \<open>
  The complete finite pattern determines its code, binder family, fresh frame
  and root. The same interface-construction contract serves this executable
  result and the original general existence theorem. Recovery uses the actual
  destination artifact and complete literal references, with every original
  pattern occurrence retained.
\<close>

end
