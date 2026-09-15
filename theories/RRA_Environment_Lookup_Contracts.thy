theory RRA_Environment_Lookup_Contracts
  imports RRA_Indexed_Environment_Views
begin

definition environment_lookup_represents ::
  "(local_address option\<Rightarrow>finite_exact_artifact fset)\<Rightarrow>
    (local_address option\<Rightarrow>local_address\<Rightarrow>local_address option fset)\<Rightarrow>
      local_address option finite_artifact_environment\<Rightarrow>bool" where
  "environment_lookup_represents artifacts bindings E \<longleftrightarrow>
    (\<forall>u R. R |\<in>| artifacts u \<longleftrightarrow> (u,R) |\<in>| finite_environment_artifacts E) \<and>
    (\<forall>u k v. v |\<in>| bindings u k \<longleftrightarrow> ((u,k),v) |\<in>| finite_environment_bindings E)"

lemma environment_lookup_representation_unique:
  "environment_lookup_represents artifacts bindings E \<Longrightarrow>
    environment_lookup_represents artifacts bindings F \<Longrightarrow> E=F"
proof -
  assume E: "environment_lookup_represents artifacts bindings E"
    and F: "environment_lookup_represents artifacts bindings F"
  have art: "finite_environment_artifacts E=finite_environment_artifacts F"
    using E F by (auto simp: environment_lookup_represents_def intro!: fset_inject[THEN iffD1] set_eqI)
  have bindings: "finite_environment_bindings E=finite_environment_bindings F"
    using E F by (auto simp: environment_lookup_represents_def intro!: fset_inject[THEN iffD1] set_eqI)
  show ?thesis using art bindings by (cases E; cases F) simp
qed

lemma indexed_environment_lookup_contract:
  "environment_lookup_represents (indexed_environment_artifacts I) (indexed_environment_bindings I) E=
    indexed_environment_represents I E"
  by (simp only: environment_lookup_represents_def indexed_environment_represents_def)

lemma finite_environment_index_exists:
  fixes E :: "local_address option finite_artifact_environment"
  shows "\<exists>I::indexed_artifact_environment. indexed_environment_represents I E"
proof -
  obtain A where A: "fset_of_list A=finite_environment_artifacts E" using exists_fset_of_list by blast
  obtain B where B: "fset_of_list B=finite_environment_bindings E" using exists_fset_of_list by blast
  have view: "finite_enumerated_environment A B=E"
    using A B by (cases E) (simp add: finite_enumerated_environment_def)
  show ?thesis using index_environment_rows_exact[of A B] using view by metis
qed

lemma environment_lookup_transfer:
  assumes local: "environment_lookup_represents artifacts bindings E"
    and original: "indexed_environment_represents I E"
  shows "artifacts=indexed_environment_artifacts I" "bindings=indexed_environment_bindings I"
  using local original
  by (auto simp: environment_lookup_represents_def indexed_environment_represents_def
    intro!: ext fset_inject[THEN iffD1] set_eqI)

definition lookup_artifact_ready where
  "lookup_artifact_ready artifacts u R=(finite_exact_formed R \<and> artifacts u={||})"

definition lookup_binding_ready where
  "lookup_binding_ready artifacts bindings u k v=(
    fBex (artifacts u) (\<lambda>R. k |\<in>| finite_carrier (finite_structure R)) \<and>
    artifacts v\<noteq>{||} \<and> bindings u k={||})"

lemma lookup_artifact_ready_exact:
  assumes represented: "environment_lookup_represents artifacts bindings E"
  shows "lookup_artifact_ready artifacts u R \<longleftrightarrow>
    exact_formed (decode_finite_object R) \<and> u\<notin>environment_uses (decode_finite_environment E)"
proof -
  obtain I::indexed_artifact_environment where original: "indexed_environment_represents I E" using finite_environment_index_exists[of E] by blast
  have art: "artifacts=indexed_environment_artifacts I" by (rule environment_lookup_transfer[OF represented original])
  show ?thesis using indexed_artifact_ready_exact[OF original, of u R]
    by (simp only: lookup_artifact_ready_def art indexed_artifact_ready_def)
qed

lemma lookup_binding_ready_exact:
  assumes represented: "environment_lookup_represents artifacts bindings E"
  shows "lookup_binding_ready artifacts bindings u k v \<longleftrightarrow>
    (\<exists>R. artifact_at (decode_finite_environment E) u R \<and> k\<in>rra_carrier (object_structure R)) \<and>
    v\<in>environment_uses (decode_finite_environment E) \<and>
    (\<forall>w. \<not>binds_slot (decode_finite_environment E) u k w)"
proof -
  obtain I::indexed_artifact_environment where original: "indexed_environment_represents I E" using finite_environment_index_exists[of E] by blast
  have art: "artifacts=indexed_environment_artifacts I"
    and binding: "bindings=indexed_environment_bindings I"
    by (rule environment_lookup_transfer[OF represented original])+
  show ?thesis using indexed_binding_ready_exact[OF original, of u k v]
    by (simp only: lookup_binding_ready_def art binding indexed_binding_ready_def)
qed

theorem lookup_added_artifact_formed:
  assumes represented: "environment_lookup_represents artifacts bindings E"
    and formed: "finite_environment_formed E" and ready: "lookup_artifact_ready artifacts u R"
  shows "finite_environment_formed (finite_add_artifact_use E u R)"
proof -
  obtain I::indexed_artifact_environment where original: "indexed_environment_represents I E" using finite_environment_index_exists[of E] by blast
  have art: "artifacts=indexed_environment_artifacts I" by (rule environment_lookup_transfer[OF represented original])
  have added: "indexed_add_artifact I u R=Some (indexed_insert_artifact I u R)"
    using ready by (simp add: lookup_artifact_ready_def art indexed_add_artifact_def indexed_artifact_ready_def)
  show ?thesis by (rule indexed_add_artifact_formed[OF formed original added])
qed

theorem lookup_added_binding_formed:
  assumes represented: "environment_lookup_represents artifacts bindings E"
    and formed: "finite_environment_formed E" and ready: "lookup_binding_ready artifacts bindings u k v"
  shows "finite_environment_formed (finite_add_source_bindings E u {|(k,v)|})"
proof -
  obtain I::indexed_artifact_environment where original: "indexed_environment_represents I E" using finite_environment_index_exists[of E] by blast
  have art: "artifacts=indexed_environment_artifacts I"
    and binding: "bindings=indexed_environment_bindings I"
    by (rule environment_lookup_transfer[OF represented original])+
  have added: "indexed_add_binding I u k v=Some (indexed_insert_binding I u k v)"
    using ready by (simp add: lookup_binding_ready_def art binding indexed_add_binding_def indexed_binding_ready_def)
  show ?thesis by (rule indexed_add_binding_formed[OF formed original added])
qed

text \<open>
  The complete original relations determine the required lookup functions.
  Every finite environment has a reference index, used only as a proof witness.
  Local guards and formation preservation transfer through that complete
  relation contract. The new implementation need not construct that witness
  or scan a whole view. Its original formation argument is reused once here.
\<close>

end
