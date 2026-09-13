theory Factor_Finite_Root_Syntax
  imports Factor_Root_Syntax RRA_Finite_Syntax_Construction Factor_Finite_Reference_Forests
begin

section \<open>Executable complete root citation families\<close>

lemma decode_finite_external_occurrence_syntax [simp]:
  "decode_finite_object (finite_external_occurrence_syntax a)=external_occurrence_syntax a"
  using decode_finite_literal_syntax[of "Finite_Anchor (finite_payload_syntax []) a"]
  by (simp only: finite_literal_syntax.simps decode_finite_target.simps
    external_occurrence_syntax_literal[where R="decode_finite_object (finite_payload_syntax [])"])

definition finite_root_family_syntax :: "'u definition_site list\<Rightarrow>finite_exact_artifact" where
  "finite_root_family_syntax ds=finite_family_wrapper
    (finite_syntax_forest (map (\<lambda>d. finite_external_occurrence_syntax (snd d)) ds)) []
    (fset_of_list (zip (family_ports (length ds)) (map (\<lambda>i. syntax_branch i []) [0..<length ds])))"

definition finite_root_family_callees :: "'u definition_site list\<Rightarrow>(local_address\<times>'u definition_site) fset" where
  "finite_root_family_callees ds=finite_syntax_forest_table (map (\<lambda>d. {|([4],d)|}) ds)"

lemma finite_root_family_syntax_correct:
  assumes addresses: "\<forall>d\<in>set ds. octets_formed (snd d)"
  shows "finite_exact_formed (finite_root_family_syntax ds)"
    and "reference_table_formed {} (fset (finite_root_family_callees ds))"
    and "rel_dom (fset (finite_root_family_callees ds))\<subseteq>
      fset (finite_carrier (finite_structure (finite_root_family_syntax ds)))"
    and "rel_ran (fset (finite_root_family_callees ds))=set ds"
    and "\<forall>E u. environment_formed E \<longrightarrow>
      artifact_at E u (decode_finite_object (finite_root_family_syntax ds)) \<longrightarrow>
      syntax_references E u {} (fset (finite_root_family_callees ds)) \<longrightarrow>
      native_root_family_at E u [] (set (zip (family_ports (length ds)) ds))"
proof -
  interpret code: root_family_construction ds by (rule root_family_construction.intro[OF addresses])
  have artifact: "decode_finite_object (finite_root_family_syntax ds)=code.framed"
    by (simp add: finite_root_family_syntax_def fset_of_list.rep_eq map_map comp_def)
  have refs: "fset (finite_root_family_callees ds)=code.callees"
    by (simp add: finite_root_family_callees_def map_map comp_def)
  show "finite_exact_formed (finite_root_family_syntax ds)"
    by (simp only: finite_exact_formed_correct artifact; rule code.formed)
  show "reference_table_formed {} (fset (finite_root_family_callees ds))"
    by (simp only: refs; rule code.reference_table)
  show "rel_dom (fset (finite_root_family_callees ds))\<subseteq>
      fset (finite_carrier (finite_structure (finite_root_family_syntax ds)))"
    using code.reference_bounds by (simp only: refs artifact[symmetric] decode_finite_object_selectors decode_finite_structure_fields)
  show "rel_ran (fset (finite_root_family_callees ds))=set ds"
    by (simp only: refs; rule code.reference_range)
  show "\<forall>E u. environment_formed E \<longrightarrow>
      artifact_at E u (decode_finite_object (finite_root_family_syntax ds)) \<longrightarrow>
      syntax_references E u {} (fset (finite_root_family_callees ds)) \<longrightarrow>
      native_root_family_at E u [] (set (zip (family_ports (length ds)) ds))"
    by (simp only: artifact refs; use code.recovers in blast)
qed

export_code finite_root_family_syntax finite_root_family_callees checking SML

end
