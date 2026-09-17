theory Factor_Ordered_Generation_Checking
  imports RRA_Generation_Child_Row_Images Factor_Ordered_Target_Equality
begin

section \<open>Generations are checked as values\<close>

declare finite_check_generation_word_rows_code[code del] lookup_check_generation_word_rows_code[code del]
  finite_generation_record_ready_structural_code[code del] lookup_generation_record_ready_structural_code[code del]

declare finite_check_generation.simps[code] lookup_check_generation.simps[code]
  finite_generation_record_ready_def[code] lookup_generation_record_ready_def[code]

text \<open>
  A generation check compares the locus, payload and cause it reads with the
  supplied ones, and matches predecessors, by value equality. Target equality
  compares canonical artifact fields and stops at the first difference; the
  predecessor bijection of a node compares its few actual predecessors. Encoding
  every compared target and predecessor subtree as a complete word at every node
  was the dominant replay cost, so the original equations are the executable ones
  for every export again. Every result is the original check.
\<close>

end
