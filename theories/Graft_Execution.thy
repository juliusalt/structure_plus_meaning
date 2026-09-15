theory Graft_Execution
  imports RRA_Graft_Investigation Factor_Executable_Artifact_Values
begin

setup \<open>Finite_Observation_Contracts.export @{term graft_investigation}\<close>

export_code graft_packet graft_indices graft_inspect graft_view_formed use_word_length
  finite_artifact_rows finite_environment_artifacts finite_environment_bindings
  fset set nat_of_integer integer_of_nat
  in SML module_name Graft_Execution file_prefix graft

end
