theory RRA_Local_Environment_Updates
  imports RRA_Indexed_Environments
begin

definition indexed_artifact_ready where
  "indexed_artifact_ready I u R=(finite_exact_formed R \<and> indexed_environment_artifacts I u={||})"

definition indexed_binding_ready where
  "indexed_binding_ready I u k v=(
    fBex (indexed_environment_artifacts I u) (\<lambda>R. k |\<in>| finite_carrier (finite_structure R)) \<and>
    indexed_environment_artifacts I v\<noteq>{||} \<and> indexed_environment_bindings I u k={||})"

definition indexed_add_artifact where
  "indexed_add_artifact I u R=(if indexed_artifact_ready I u R
    then Some (indexed_insert_artifact I u R) else None)"

definition indexed_add_binding where
  "indexed_add_binding I u k v=(if indexed_binding_ready I u k v
    then Some (indexed_insert_binding I u k v) else None)"

lemma indexed_artifact_ready_exact:
  assumes represented: "indexed_environment_represents I E"
  shows "indexed_artifact_ready I u R \<longleftrightarrow>
    exact_formed (decode_finite_object R) \<and> u\<notin>environment_uses (decode_finite_environment E)"
  using represented
  by (auto simp: indexed_artifact_ready_def indexed_environment_represents_def
    finite_exact_formed_correct environment_uses_def rel_dom_def artifact_at_def
    fset_inject[symmetric])

lemma indexed_binding_ready_exact:
  assumes represented: "indexed_environment_represents I E"
  shows "indexed_binding_ready I u k v \<longleftrightarrow>
    (\<exists>R. artifact_at (decode_finite_environment E) u R \<and> k\<in>rra_carrier (object_structure R)) \<and>
    v\<in>environment_uses (decode_finite_environment E) \<and>
    (\<forall>w. \<not>binds_slot (decode_finite_environment E) u k w)"
  using represented
  by (auto simp: indexed_binding_ready_def indexed_environment_represents_def
    environment_uses_def rel_dom_def binds_slot_def artifact_at_def
    fset_inject[symmetric]; force)

theorem indexed_add_artifact_formed:
  assumes ef: "finite_environment_formed E" and represented: "indexed_environment_represents I E"
    and result: "indexed_add_artifact I u R=Some J"
  shows "finite_environment_formed (finite_add_artifact_use E u R)"
    "indexed_environment_represents J (finite_add_artifact_use E u R)"
proof -
  have ready: "indexed_artifact_ready I u R" and J: "J=indexed_insert_artifact I u R"
    using result by (auto simp: indexed_add_artifact_def split: if_splits)
  have formed: "environment_formed (decode_finite_environment E)"
    using ef by (simp only: finite_environment_formed_correct)
  have rf: "exact_formed (decode_finite_object R)"
    and fresh: "u\<notin>environment_uses (decode_finite_environment E)"
    using ready indexed_artifact_ready_exact[OF represented] by blast+
  show "finite_environment_formed (finite_add_artifact_use E u R)"
    by (simp only: finite_environment_formed_correct decode_finite_add_artifact_use;
      rule added_artifact_formed[OF formed rf fresh])
  show "indexed_environment_represents J (finite_add_artifact_use E u R)"
    by (simp only: J; rule indexed_insert_artifact_exact[OF represented])
qed

theorem indexed_add_binding_formed:
  assumes ef: "finite_environment_formed E" and represented: "indexed_environment_represents I E"
    and result: "indexed_add_binding I u k v=Some J"
  shows "finite_environment_formed (finite_add_source_bindings E u {|(k,v)|})"
    "indexed_environment_represents J (finite_add_source_bindings E u {|(k,v)|})"
proof -
  have ready: "indexed_binding_ready I u k v" and J: "J=indexed_insert_binding I u k v"
    using result by (auto simp: indexed_add_binding_def split: if_splits)
  obtain R where source: "artifact_at (decode_finite_environment E) u R"
    and slot: "k\<in>rra_carrier (object_structure R)"
    and target: "v\<in>environment_uses (decode_finite_environment E)"
    and unbound: "\<forall>w. \<not>binds_slot (decode_finite_environment E) u k w"
    using ready indexed_binding_ready_exact[OF represented] by blast
  have formed: "environment_formed (decode_finite_environment E)"
    using ef by (simp only: finite_environment_formed_correct)
  have added: "environment_formed (add_source_bindings (decode_finite_environment E) u {(k,v)})"
    by (rule add_source_bindings_formed[OF formed source])
      (use slot target unbound in \<open>auto simp: single_valued_def rel_dom_def rel_ran_def\<close>)
  show "finite_environment_formed (finite_add_source_bindings E u {|(k,v)|})"
    using added by (simp only: finite_environment_formed_correct decode_finite_add_source_bindings fset_simps)
  show "indexed_environment_represents J (finite_add_source_bindings E u {|(k,v)|})"
    by (simp only: J; rule indexed_insert_binding_exact[OF represented])
qed

text \<open>
  A new artifact needs its own formation and an actually empty indexed use.
  A new binding needs the actual source occurrence, an existing target, and an
  actually unbound slot. These operations do not recheck the old environment.
  Their exact original-constructor equations and preservation theorems retain
  the established formation premise; no supplied validity field is introduced.
\<close>

end
