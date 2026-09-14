theory Use_Allocation_Execution
  imports RRA_Use_Allocation_Investigation
begin

setup \<open>Finite_Observation_Contracts.export @{term use_allocation_investigation}\<close>

export_code use_allocation_packet use_allocation_indices use_allocation_inspect use_word_length
  fset set nat_of_integer integer_of_nat
  in SML module_name Use_Allocation_Execution file_prefix use_allocation

end
