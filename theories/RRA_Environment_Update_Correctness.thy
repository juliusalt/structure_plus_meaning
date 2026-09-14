theory RRA_Environment_Update_Correctness
  imports RRA_Environment_Update_Methods
begin

lemma environment_store_load_raw:
  "map_option raw_environment_store (load_environment_store A B)=
    (if finite_environment_formed (finite_enumerated_environment A B) then Some (index_environment_rows A B) else None)"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma environment_store_add_artifact_raw:
  "map_option raw_environment_store (environment_store_add_artifact I u R)=
    indexed_add_artifact (raw_environment_store I) u R"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma environment_store_add_binding_raw:
  "map_option raw_environment_store (environment_store_add_binding I u k v)=
    indexed_add_binding (raw_environment_store I) u k v"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma stored_environment_update_raw:
  "map_option raw_environment_store (stored_environment_update I op)=
    (if environment_update_guard 1 (raw_environment_store I) op then
      Some (indexed_environment_update (raw_environment_store I) op) else None)"
  by (cases op) (auto simp: environment_store_add_artifact_raw environment_store_add_binding_raw
    indexed_add_artifact_def indexed_add_binding_def indexed_artifact_ready_def indexed_binding_ready_def)

lemma environment_update_guard_full:
  fixes I :: indexed_artifact_environment and E :: "local_address option finite_artifact_environment"
  assumes represented: "indexed_environment_represents I E"
  shows "environment_update_guard 1 I op=finite_environment_update_ready E op"
proof -
  have shaped: "environment_update_guard 1 I op=(case op of Install_Artifact u R \<Rightarrow> indexed_artifact_ready I u R
    | Install_Binding u k v \<Rightarrow> indexed_binding_ready I u k v)"
    by (cases op) (auto simp: indexed_artifact_ready_def indexed_binding_ready_def)
  show ?thesis
    unfolding shaped finite_environment_update_ready_exact
    by (cases op) (simp_all add: indexed_artifact_ready_exact[OF represented]
      indexed_binding_ready_exact[OF represented])
qed

lemma indexed_environment_update_represents:
  "indexed_environment_represents I E \<Longrightarrow>
    indexed_environment_represents (indexed_environment_update I op) (finite_environment_update_body E op)"
  by (cases op) (auto intro: indexed_insert_artifact_exact indexed_insert_binding_exact)

lemma indexed_environment_update_view:
  "indexed_environment_represents I E \<Longrightarrow>
    indexed_environment_view (indexed_environment_update I op)=finite_environment_update_body E op"
  by (rule indexed_environment_view_representation; rule indexed_environment_update_represents)

lemma environment_update_raw_option_exact:
  "environment_update_option 1 (A,B,op)=(let E=finite_enumerated_environment A B in
    if finite_environment_formed E \<and> finite_environment_update_ready E op
      then Some (finite_environment_update_body E op) else None)"
  by (simp add: environment_update_option_def Let_def
    environment_update_guard_full[OF index_environment_rows_exact, unfolded One_nat_def]
    indexed_environment_update_view[OF index_environment_rows_exact])

lemma environment_update_stored_option_exact:
  "environment_update_option 0 (A,B,op)=environment_update_option 1 (A,B,op)"
proof (cases "load_environment_store A B")
  case None
  have unformed: "\<not>finite_environment_formed (finite_enumerated_environment A B)"
    using environment_store_load_raw[of A B] by (simp add: None split: if_splits)
  show ?thesis by (simp add: environment_update_option_def None unformed Let_def)
next
  case (Some I)
  have formed: "finite_environment_formed (finite_enumerated_environment A B)"
    and raw: "raw_environment_store I=index_environment_rows A B"
    using environment_store_load_raw[of A B] Some by (auto split: if_splits)
  have projected: "map_option (\<lambda>J. indexed_environment_view (raw_environment_store J)) (stored_environment_update I op)=
    map_option indexed_environment_view (map_option raw_environment_store (stored_environment_update I op))"
    by (simp only: option.map_comp comp_def)
  show ?thesis
    by (simp only: environment_update_option_def case_prod_conv Some option.case
      projected stored_environment_update_raw raw;
      simp add: formed Let_def)
qed

theorem environment_update_correct_methods:
  assumes method: "m\<in>{0,1}"
  shows "environment_update_method m X=environment_update_reference X"
  using method by (cases X)
    (auto simp: environment_update_method_def environment_update_reference_def
      environment_update_stored_option_exact[unfolded One_nat_def] environment_update_raw_option_exact[unfolded One_nat_def]
      finite_optional_image_exact Let_def intro!: fset_inject[THEN iffD1] set_eqI)

text \<open>
  Both complete implementations equal the independently specified guarded
  constructor on every original input. The abstract API's raw projection is
  proved through its lifting contract, and the complete recovered environment
  follows from the original representation equation. The native case comparison
  checks actual results and exposes omitted guards; it is not the premise of
  this all-input equality.
\<close>

end
