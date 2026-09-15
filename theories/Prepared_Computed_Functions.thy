theory Prepared_Computed_Functions
  imports Memoized_Function_Sequences
begin

definition prepared_computed_function where
  "prepared_computed_function evaluate keys=(let cache=snd (computed_sequence evaluate [] keys)
    in exact_cache_read evaluate (map_of cache))"

theorem prepared_computed_function_exact:
  "prepared_computed_function evaluate keys=evaluate"
proof (rule ext)
  fix x
  have exact: "computation_cache_exact evaluate (snd (computed_sequence evaluate [] keys))"
    using computed_sequence_exact[OF computation_cache_empty, of evaluate keys] by blast
  show "prepared_computed_function evaluate keys x=evaluate x"
    unfolding prepared_computed_function_def Let_def
    by (rule exact_cache_read_correct; rule computation_cache_lookup[OF exact]; assumption)
qed

text \<open>Every cache value comes from the actual computation. Repeated
  keys reuse that complete value, and an unprepared key executes the original
  function. The resulting function is equal on its entire domain, independent
  of the chosen preparation keys or their order.\<close>

end
