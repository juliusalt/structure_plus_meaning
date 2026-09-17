theory Parallel_Inspection_Caches
 imports Parallel_Computed_Preparation Finite_Evaluation_Relations Finite_Evaluation_Caches
begin

definition parallel_inspection_rows where
 "parallel_inspection_rows inspect inputs=(let prepared=finite_computed_function inspect inputs in
   finite_inspection_rows prepared inputs)"

lemma parallel_inspection_rows_exact:
 "parallel_inspection_rows inspect inputs=finite_inspection_rows inspect inputs"
 by (simp only: parallel_inspection_rows_def finite_computed_function_exact Let_def)

definition parallel_evaluation_cache where
 "parallel_evaluation_cache evaluate inputs=Parallel.map (\<lambda>x. (x,evaluate x)) (remdups inputs)"

lemma parallel_evaluation_cache_exact:
 "parallel_evaluation_cache evaluate inputs=finite_evaluation_cache evaluate inputs"
 by (simp only: parallel_evaluation_cache_def Parallel.map_def finite_evaluation_cache_def)

text \<open>Actual complete input keys determine independent original computations.
 The computed function retains the original operation on every key, including
 misses. The original finite inspection map still supplies every returned row;
 only the preparation runs in parallel. The list-cache equation keeps the exact
 original distinct-key order. No returned value, condition or refusal is supplied.\<close>
end
