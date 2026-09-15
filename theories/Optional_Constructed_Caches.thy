theory Optional_Constructed_Caches
  imports Exact_Cache_Readings
begin

definition optional_constructed_cache where
  "optional_constructed_cache key value sources=concat (map (\<lambda>entry.
    case entry of None \<Rightarrow> [] | Some x \<Rightarrow> [(key x,value x)]) sources)"

lemma optional_constructed_cache_lookup:
  assumes found: "map_of (optional_constructed_cache key value sources) k=Some y"
  shows "\<exists>x. Some x\<in>set sources \<and> k=key x \<and> y=value x"
  using map_of_SomeD[OF found]
  by (auto simp: optional_constructed_cache_def split: option.splits)

theorem optional_constructed_cache_exact:
  assumes entries: "\<And>x. Some x\<in>set sources \<Longrightarrow> value x=evaluate (key x)"
  shows "exact_cache_read evaluate (map_of (optional_constructed_cache key value sources)) k=evaluate k"
proof (rule exact_cache_read_correct)
  fix y
  assume found: "map_of (optional_constructed_cache key value sources) k=Some y"
  from optional_constructed_cache_lookup[OF found]
  obtain x where source: "Some x\<in>set sources" and key_eq: "k=key x" and value_eq: "y=value x"
    by blast
  show "y=evaluate k" by (simp only: key_eq value_eq entries[OF source])
qed

text \<open>Only actual optional constructor results enter this cache. Its
  lookup theorem retains the constructor membership and the complete value
  equation for every hit. Misses execute the supplied original operation.\<close>

end
