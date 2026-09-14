theory Finite_Evaluation_Caches
  imports Finite_Assessment_Reports Exact_Cache_Readings
begin

definition finite_evaluation_cache where
  "finite_evaluation_cache evaluate inputs=map (\<lambda>x. (x,evaluate x)) (remdups inputs)"

definition finite_cached_evaluation where
  "finite_cached_evaluation evaluate cache x=exact_cache_read evaluate (map_of cache) x"

theorem finite_evaluation_cache_lookup:
  "map_of (finite_evaluation_cache evaluate inputs) x=(if x\<in>set inputs then Some (evaluate x) else None)"
  by (simp only: finite_evaluation_cache_def mapped_function_lookup set_remdups)

theorem finite_cached_evaluation_exact:
  "finite_cached_evaluation evaluate (finite_evaluation_cache evaluate inputs) x=evaluate x"
  unfolding finite_cached_evaluation_def
  by (rule exact_cache_read_correct) (auto simp: finite_evaluation_cache_lookup split: if_splits)

theorem finite_evaluation_cache_inputs:
  "map fst (finite_evaluation_cache evaluate inputs)=remdups inputs"
  by (simp add: finite_evaluation_cache_def comp_def)

corollary finite_evaluation_cache_distinct:
  "distinct (map fst (finite_evaluation_cache evaluate inputs))"
  by (simp only: finite_evaluation_cache_inputs distinct_remdups)

corollary finite_evaluation_cache_size:
  "length (finite_evaluation_cache evaluate inputs)\<le>length inputs"
  by (simp add: finite_evaluation_cache_def length_remdups_leq)

text \<open>
  Each complete input value occurs once in the constructed evaluation table.
  A lookup at any input, including an input absent from the table, returns the
  original operation's exact complete value. The theorem requires a table
  constructed by that operation; arbitrary supplied rows receive no such
  contract. Equality of complete inputs supplies sharing without ordered proof
  values, descriptions, digests or separately supplied truth.

  The row-count bound counts the represented evaluations. It does not bound
  equality, lookup, allocation, reader work or the complete physical cost.
\<close>

end
