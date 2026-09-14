theory RRA_Formed_Environment_Stores
  imports RRA_Local_Environment_Updates Optional_Result_Invariants "HOL-Library.Code_Target_Nat"
begin

definition indexed_environment_valid :: "indexed_artifact_environment \<Rightarrow> bool" where
  "indexed_environment_valid I \<longleftrightarrow>
    (\<exists>E. finite_environment_formed E \<and> indexed_environment_represents I E)"

lemma indexed_loaded_environment_valid:
  "finite_environment_formed (finite_enumerated_environment A B) \<Longrightarrow>
    indexed_environment_valid (index_environment_rows A B)"
  using index_environment_rows_exact[of A B] by (auto simp: indexed_environment_valid_def)

lemma indexed_empty_environment_valid:
  "indexed_environment_valid (index_environment_rows [] [])"
  by (rule indexed_loaded_environment_valid)
    (simp add: finite_environment_formed_def finite_enumerated_environment_def finite_relation_functional_def)

lemma indexed_add_artifact_valid:
  "indexed_environment_valid I \<Longrightarrow> indexed_add_artifact I u R=Some J \<Longrightarrow> indexed_environment_valid J"
  using indexed_add_artifact_formed by (fastforce simp: indexed_environment_valid_def)

lemma indexed_add_binding_valid:
  "indexed_environment_valid I \<Longrightarrow> indexed_add_binding I u k v=Some J \<Longrightarrow> indexed_environment_valid J"
  using indexed_add_binding_formed by (fastforce simp: indexed_environment_valid_def)

typedef formed_environment_store = "{I. indexed_environment_valid I}"
  morphisms raw_environment_store Formed_Environment_Store
  using indexed_empty_environment_valid by blast

setup_lifting type_definition_formed_environment_store

lift_definition empty_environment_store :: formed_environment_store
  is "index_environment_rows [] []" by (rule indexed_empty_environment_valid)

lift_definition (code_dt) load_environment_store ::
  "(local_address option\<times>finite_exact_artifact) list \<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list \<Rightarrow> formed_environment_store option"
  is "\<lambda>A B. if finite_environment_formed (finite_enumerated_environment A B)
    then Some (index_environment_rows A B) else None"
  by (auto intro: indexed_loaded_environment_valid)

lift_definition (code_dt) environment_store_add_artifact ::
  "formed_environment_store \<Rightarrow> local_address option \<Rightarrow> finite_exact_artifact \<Rightarrow> formed_environment_store option"
  is indexed_add_artifact
  by (auto intro: optional_result_invariant indexed_add_artifact_valid)

lift_definition (code_dt) environment_store_add_binding ::
  "formed_environment_store \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> formed_environment_store option"
  is indexed_add_binding
  by (auto intro: optional_result_invariant indexed_add_binding_valid)

lift_definition environment_store_artifacts ::
  "formed_environment_store \<Rightarrow> local_address option \<Rightarrow> finite_exact_artifact fset"
  is indexed_environment_artifacts .

lift_definition environment_store_bindings ::
  "formed_environment_store \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> local_address option fset"
  is indexed_environment_bindings .

theorem environment_store_formed:
  "\<exists>E. finite_environment_formed E \<and> indexed_environment_represents (raw_environment_store S) E"
  using raw_environment_store[of S] by (simp add: indexed_environment_valid_def)

export_code empty_environment_store load_environment_store environment_store_add_artifact
  environment_store_add_binding environment_store_artifacts environment_store_bindings checking SML

text \<open>
  Every value of the exposed store type represents a formed original finite
  environment. Loading checks its complete original rows once. Later insertions
  construct a new value only after their local actual prerequisites hold.
  Callers supply artifacts and uses, never a validity flag. Formation does not
  certify a generation cause, policy, transition, allocation method, or genesis.
\<close>

end
