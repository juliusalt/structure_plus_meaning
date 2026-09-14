theory Finite_Evaluation_Relations
  imports Exact_Cache_Readings Finite_Inspection_Rows Finite_Functional_Enumeration
begin

definition finite_relation_cached_evaluation where
  "finite_relation_cached_evaluation evaluate rows x=exact_cache_read evaluate (finite_relation_option rows) x"

theorem finite_relation_cached_evaluation_exact:
  "finite_relation_cached_evaluation evaluate (finite_inspection_rows evaluate inputs) x=evaluate x"
  unfolding finite_relation_cached_evaluation_def
proof (rule exact_cache_read_correct)
  fix y assume found: "finite_relation_option (finite_inspection_rows evaluate inputs) x=Some y"
  have member: "(x,y) |\<in>| finite_inspection_rows evaluate inputs"
    by (rule finite_relation_option_member[OF found])
  show "y=evaluate x" using member by (simp only: finite_inspection_row_exact; blast)
qed

text \<open>
  The existing complete inspection rows also serve finite-set query families.
  Exact relation lookup preserves every entire input and computed value.
  Missing lookups invoke the actual operation, so the equality holds outside
  the prepared query family too. No order on queried proof values is required.
\<close>

end
