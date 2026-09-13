theory Factor_Finite_Root_Environments
  imports Factor_Finite_Root_Syntax Factor_Finite_Reference_Environments Factor_Root_Environments
begin

section \<open>Install the actual root selector at a computed fresh use\<close>

definition finite_select_roots :: "local_address option finite_artifact_environment\<Rightarrow>
    local_address option definition_site list\<Rightarrow>
    local_address option finite_artifact_environment\<times>local_address option" where
  "finite_select_roots E ds=(let u=finite_fresh_use_map (finite_environment_uses E) None (Some []);
    R=finite_root_family_syntax ds; C=finite_root_family_callees ds in
    (finite_fresh_reference_sequence E [u] (\<lambda>_. R) (\<lambda>_. {||}) (\<lambda>_. C),u))"

theorem finite_select_roots_correct:
  assumes ef: "finite_environment_formed E"
    and targets: "set ds\<subseteq>environment_positions (decode_finite_environment E)"
    and result: "finite_select_roots E ds=(F,u)"
  shows "finite_environment_formed F"
    and "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    and "u\<notin>fset (finite_environment_uses E)"
    and "native_root_family_at (decode_finite_environment F) u [] (set (zip (family_ports (length ds)) ds))"
    and "rel_ran (set (zip (family_ports (length ds)) ds))=set ds"
    and "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A"
    and "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v"
proof -
  let ?E="decode_finite_environment E"
  let ?R="finite_root_family_syntax ds"
  let ?C="finite_root_family_callees ds"
  have formed: "environment_formed ?E" using ef by (simp only: finite_environment_formed_correct)
  have addresses: "\<forall>d\<in>set ds. octets_formed (snd d)"
    using targets environment_position_address[OF formed] by blast
  have fields: "u=finite_fresh_use_map (finite_environment_uses E) None (Some [])"
    "F=finite_fresh_reference_sequence E [u] (\<lambda>_. ?R) (\<lambda>_. {||}) (\<lambda>_. ?C)"
    using result by (auto simp: finite_select_roots_def Let_def)
  have fresh: "u\<notin>fset (finite_environment_uses E)"
    using fresh_use_map_outside[of "fset (finite_environment_uses E)" None "[]"]
    by (simp add: fields(1) finite_fresh_use_map_exact)
  have profiles: "\<forall>w\<in>set [u]. reference_table_formed
      (map_relation_values decode_finite_object (fset {||})) (fset ?C)"
    using finite_root_family_syntax_correct(2)[OF addresses] by (simp add: map_relation_values_def)
  have bounds: "\<forall>w\<in>set [u]. rel_dom (fset {||})\<union>rel_dom (fset ?C)\<subseteq>
      fset (finite_carrier (finite_structure ?R))"
    using finite_root_family_syntax_correct(3)[OF addresses] by simp
  have callees: "\<forall>w\<in>set [u]. \<forall>d\<in>rel_ran (fset ?C).
    d\<in>environment_positions ?E \<or>
      (fst d\<in>set [u] \<and> snd d\<in>fset (finite_carrier (finite_structure ?R)))"
    using targets by (simp only: finite_root_family_syntax_correct(4)[OF addresses]; blast)
  have installed: "finite_environment_formed F" "environment_included ?E (decode_finite_environment F)"
    "artifact_at (decode_finite_environment F) u (decode_finite_object ?R)"
    "syntax_references (decode_finite_environment F) u {} (fset ?C)"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at ?E w A"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot ?E w k v"
    using finite_fresh_reference_sequence_properties[OF ef, of "[u]" "\<lambda>_. ?R" "\<lambda>_. {||}" "\<lambda>_. ?C"]
      fresh finite_root_family_syntax_correct(1)[OF addresses] profiles bounds callees
    by (simp only: fields(2)[symmetric] Let_def set_simps; auto simp: map_relation_values_def)+
  show "finite_environment_formed F" "environment_included ?E (decode_finite_environment F)"
    "u\<notin>fset (finite_environment_uses E)"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at ?E w A"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot ?E w k v"
    using installed fresh by blast+
  show "native_root_family_at (decode_finite_environment F) u [] (set (zip (family_ports (length ds)) ds))"
    using finite_root_family_syntax_correct(5)[OF addresses] installed(1,3,4)
    by (simp only: finite_environment_formed_correct; blast)
  show "rel_ran (set (zip (family_ports (length ds)) ds))=set ds" by (rule zip_range) simp
qed

export_code finite_select_roots checking SML

end
