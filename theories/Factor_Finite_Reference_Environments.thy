theory Factor_Finite_Reference_Environments
  imports RRA_Finite_Environment_Construction Factor_Reference_Packages
begin

section \<open>Finite reference installation is the original environment operation\<close>

definition finite_callee_binding_table :: "(local_address\<times>'u definition_site) fset\<Rightarrow>(local_address\<times>'u) fset" where
  "finite_callee_binding_table C=fimage (\<lambda>(k,d). (k,fst d)) C"

lemma finite_callee_binding_table_exact [simp]:
  "fset (finite_callee_binding_table C)=callee_binding_table (fset C)"
  by (simp add: finite_callee_binding_table_def callee_binding_table_def fimage.rep_eq)

definition finite_install_reference_tables :: "local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>
    finite_exact_artifact\<Rightarrow>(local_address\<times>finite_exact_artifact) fset\<Rightarrow>
    (local_address\<times>local_address option definition_site) fset\<Rightarrow>local_address option finite_artifact_environment" where
  "finite_install_reference_tables E u R L C=finite_add_source_bindings
    (finite_graft_environment E u (finite_literal_environment R L)) u (finite_callee_binding_table C)"

lemma decode_finite_install_reference_tables [simp]:
  "decode_finite_environment (finite_install_reference_tables E u R L C)=
    install_reference_tables (decode_finite_environment E) u (decode_finite_object R)
      (map_relation_values decode_finite_object (fset L)) (fset C)"
  by (simp add: finite_install_reference_tables_def install_reference_tables_def)

fun finite_install_reference_sequence :: "local_address option finite_artifact_environment\<Rightarrow>local_address option list\<Rightarrow>
    (local_address option\<Rightarrow>finite_exact_artifact)\<Rightarrow>
    (local_address option\<Rightarrow>(local_address\<times>finite_exact_artifact) fset)\<Rightarrow>
    (local_address option\<Rightarrow>(local_address\<times>local_address option definition_site) fset)\<Rightarrow>
    local_address option finite_artifact_environment" where
  "finite_install_reference_sequence E [] R L C=E"
| "finite_install_reference_sequence E (u#us) R L C=
    finite_install_reference_tables (finite_install_reference_sequence E us R L C) u (R u) (L u) (C u)"

lemma decode_finite_install_reference_sequence [simp]:
  "decode_finite_environment (finite_install_reference_sequence E us R L C)=
    install_reference_sequence (decode_finite_environment E) us (\<lambda>u. decode_finite_object (R u))
      (\<lambda>u. map_relation_values decode_finite_object (fset (L u))) (\<lambda>u. fset (C u))"
  by (induction us) simp_all

definition finite_fresh_reference_sequence where
  "finite_fresh_reference_sequence E us R L C=finite_install_reference_sequence
    (finite_merge_environment E (finite_artifact_family_environment (fset_of_list us) R)) us R L C"

lemma decode_finite_fresh_reference_sequence [simp]:
  "decode_finite_environment (finite_fresh_reference_sequence E us R L C)=
    fresh_reference_sequence (decode_finite_environment E) us (\<lambda>u. decode_finite_object (R u))
      (\<lambda>u. map_relation_values decode_finite_object (fset (L u))) (\<lambda>u. fset (C u))"
  by (simp add: finite_fresh_reference_sequence_def fresh_reference_sequence_def fset_of_list.rep_eq)

theorem finite_fresh_reference_sequence_properties:
  assumes ef: "finite_environment_formed E" and distinct: "distinct us"
    and fresh: "set us\<inter>fset (finite_environment_uses E)={}"
    and formed: "\<forall>u\<in>set us. finite_exact_formed (R u)"
    and profiles: "\<forall>u\<in>set us. reference_table_formed
      (map_relation_values decode_finite_object (fset (L u))) (fset (C u))"
    and bounds: "\<forall>u\<in>set us. rel_dom (fset (L u))\<union>rel_dom (fset (C u))\<subseteq>
      fset (finite_carrier (finite_structure (R u)))"
    and targets: "\<forall>u\<in>set us. \<forall>d\<in>rel_ran (fset (C u)). d\<in>environment_positions (decode_finite_environment E) \<or>
      (fst d\<in>set us \<and> snd d\<in>fset (finite_carrier (finite_structure (R (fst d)))))"
  shows "let F=finite_fresh_reference_sequence E us R L C in
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    (\<forall>u\<in>set us. artifact_at (decode_finite_environment F) u (decode_finite_object (R u)) \<and>
      syntax_references (decode_finite_environment F) u
        (map_relation_values decode_finite_object (fset (L u))) (fset (C u))) \<and>
    (\<forall>u\<in>fset (finite_environment_uses E). \<forall>T.
      artifact_at (decode_finite_environment F) u T \<longleftrightarrow> artifact_at (decode_finite_environment E) u T) \<and>
    (\<forall>u\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) u k v \<longleftrightarrow> binds_slot (decode_finite_environment E) u k v)"
proof -
  have old: "environment_formed (decode_finite_environment E)" using ef by (simp only: finite_environment_formed_correct)
  have separate: "set us\<inter>environment_uses (decode_finite_environment E)={}"
    using fresh by (simp only: finite_environment_uses_correct)
  have artifacts: "\<forall>u\<in>set us. exact_formed (decode_finite_object (R u))"
    using formed by (simp only: finite_exact_formed_correct)
  have slots: "\<forall>u\<in>set us. rel_dom (map_relation_values decode_finite_object (fset (L u)))\<union>rel_dom (fset (C u))\<subseteq>
    rra_carrier (object_structure (decode_finite_object (R u)))"
    using bounds by (simp only: map_relation_values_domain decode_finite_object_selectors decode_finite_structure_fields)
  have callees: "\<forall>u\<in>set us. \<forall>d\<in>rel_ran (fset (C u)). d\<in>environment_positions (decode_finite_environment E) \<or>
    (fst d\<in>set us \<and> snd d\<in>rra_carrier (object_structure (decode_finite_object (R (fst d)))))"
    using targets by (simp only: decode_finite_object_selectors decode_finite_structure_fields)
  show ?thesis using fresh_reference_sequence_properties[OF old distinct separate artifacts profiles slots callees]
    by (simp only: Let_def finite_environment_formed_correct decode_finite_fresh_reference_sequence finite_environment_uses_correct; blast)
qed

export_code finite_install_reference_tables finite_install_reference_sequence finite_fresh_reference_sequence checking SML

text \<open>
  Every code artifact is present before the reference sequence starts. A
  callee may therefore be an original source or any new code block, including
  a recursive peer. Exact decoding connects the executed sequence to the
  original preservation theorem for every artifact and outgoing binding.
\<close>

end
