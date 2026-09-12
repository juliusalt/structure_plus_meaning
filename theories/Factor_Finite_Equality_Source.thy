theory Factor_Finite_Equality_Source
  imports Factor_Native_Equality Factor_Finite_Artifact_Enumeration Factor_Executable_Systems
begin

section \<open>A finite presentation of the existing complete equality source\<close>

definition finite_equality_artifact :: finite_exact_artifact where
  "finite_equality_artifact=finite_enumerated_artifact (map (\<lambda>n. [n]) [0..<26])
    (map (\<lambda>(r,s,t). ([r],[s],[t]))
      [(0,16,15),(15,15,1),(1,17,2),(1,18,6),(17,17,18),
       (2,19,3),(2,20,5),(19,19,20),(3,4,4),(5,5,4),
       (6,7,8),(8,21,9),(8,22,11),(8,23,14),(21,21,22),(22,22,23),
       (9,10,10),(11,24,12),(11,25,13),(24,24,25),(12,12,10),(13,13,10)]) [] []"

theorem finite_equality_artifact_correct:
  "decode_finite_object finite_equality_artifact=equality_artifact"
  by (auto simp: finite_equality_artifact_def equality_artifact_def finite_enumerated_artifact_def
    decode_finite_object_def decode_finite_structure_def decode_finite_basis_def empty_basis_def
    fset_of_list.rep_eq fun_eq_iff)

definition finite_equality_environment :: "local_address option finite_artifact_environment" where
  "finite_equality_environment=finite_enumerated_environment [(None,finite_equality_artifact)] []"

lemma finite_equality_environment_correct:
  "decode_finite_environment finite_equality_environment=equality_environment"
  by (simp add: finite_equality_environment_def finite_equality_artifact_correct equality_environment_def
    literal_environment_def map_relation_values_def)

lemma finite_equality_environment_formed:
  "finite_environment_formed finite_equality_environment"
  by (simp only: finite_environment_formed_correct finite_equality_environment_correct equality_environment_formed)

definition finite_equality_schema ::
  "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "finite_equality_schema=\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable [10]) (Finite_Variable [10]),
    finite_schema_premises={||},finite_schema_materials={||}\<rparr>"

lemma finite_equality_schema_correct:
  "decode_finite_schema finite_equality_schema=native_equality_schema"
  by (simp add: finite_equality_schema_def native_equality_schema_def decode_finite_schema_def map_relation_values_def)

text \<open>
  The finite rows recover exactly the original equality artifact, environment,
  and schema. They introduce no replacement meaning for the original program.
\<close>

end
