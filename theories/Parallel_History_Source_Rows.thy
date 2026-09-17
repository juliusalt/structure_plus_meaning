theory Parallel_History_Source_Rows
  imports "HOL-Library.Parallel" Digit_History_Presentation
begin

section \<open>Independent history source cases are evaluated in parallel\<close>

declare digit_history_source_cases_def[code del]

lemma digit_history_source_cases_parallel_code [code]:
  "digit_history_source_cases ws=Parallel.map (\<lambda>w.
    (w,required_history_case (digit_history_source_index w),bounded_history_case w)) ws"
  by (simp only: digit_history_source_cases_def Parallel.map_def)

declare digit_history_source_rows_def[code del]

lemma digit_history_source_rows_parallel_code [code]:
  "digit_history_source_rows ws=Parallel.map (\<lambda>(w,old,original). (w,old,original,digit_history_chain_length w,
    digit_history_source_equal (digit_history_case w) original)) (digit_history_source_cases ws)"
  by (simp only: digit_history_source_rows_def Parallel.map_def)

text \<open>Each original bounded case, its digit case and their source equality depend
  only on their own scope index. Isabelle's exact parallel map equation retains
  the scope order, repeated indices and every complete case and source row.\<close>

end
