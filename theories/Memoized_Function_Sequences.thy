theory Memoized_Function_Sequences
  imports Exact_Cache_Readings
begin

definition computation_cache_exact where
  "computation_cache_exact evaluate cache \<longleftrightarrow>
    (\<forall>(x,y)\<in>set cache. y=evaluate x)"

lemma computation_cache_empty [simp]:
  "computation_cache_exact evaluate []"
  by (simp add: computation_cache_exact_def)

lemma computation_cache_lookup:
  assumes exact: "computation_cache_exact evaluate cache"
    and found: "map_of cache x=Some y"
  shows "y=evaluate x"
  using map_of_SomeD[OF found] exact by (auto simp: computation_cache_exact_def)

definition computed_cache_step where
  "computed_cache_step evaluate cache x=(case map_of cache x of
    Some y \<Rightarrow> (y,cache)
    | None \<Rightarrow> let y=evaluate x in (y,(x,y)#cache))"

lemma computed_cache_step_exact:
  "computation_cache_exact evaluate cache \<Longrightarrow>
    fst (computed_cache_step evaluate cache x)=evaluate x"
  by (auto simp: computed_cache_step_def Let_def
      dest: computation_cache_lookup split: option.splits)

lemma computed_cache_step_preserves:
  "computation_cache_exact evaluate cache \<Longrightarrow>
    computation_cache_exact evaluate (snd (computed_cache_step evaluate cache x))"
  by (auto simp: computed_cache_step_def computation_cache_exact_def Let_def split: option.splits)

fun computed_sequence where
  "computed_sequence evaluate cache []=([],cache)"
| "computed_sequence evaluate cache (x#xs)=(let (y,next_cache)=computed_cache_step evaluate cache x;
      (ys,last_cache)=computed_sequence evaluate next_cache xs in (y#ys,last_cache))"

theorem computed_sequence_exact:
  assumes "computation_cache_exact evaluate cache"
  shows "fst (computed_sequence evaluate cache xs)=map evaluate xs \<and>
    computation_cache_exact evaluate (snd (computed_sequence evaluate cache xs))"
  using assms
proof (induction xs arbitrary: cache)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y next_cache where step: "computed_cache_step evaluate cache x=(y,next_cache)"
    by (cases "computed_cache_step evaluate cache x") auto
  have current: "y=evaluate x"
    using computed_cache_step_exact[OF Cons.prems, of x] by (simp only: step fst_conv)
  have kept: "computation_cache_exact evaluate next_cache"
    using computed_cache_step_preserves[OF Cons.prems, of x] by (simp only: step snd_conv)
  have tail: "fst (computed_sequence evaluate next_cache xs)=map evaluate xs \<and>
      computation_cache_exact evaluate (snd (computed_sequence evaluate next_cache xs))"
    by (rule Cons.IH[OF kept])
  show ?case using tail by (simp add: step current case_prod_unfold Let_def)
qed

corollary computed_sequence_empty_exact:
  "fst (computed_sequence evaluate [] xs)=map evaluate xs"
  using computed_sequence_exact[OF computation_cache_empty, of evaluate xs] by blast

text \<open>A cache entry is justified by its actual evaluation. Each step
  either reads an exact earlier entry or evaluates and retains the entire
  result. The sequence preserves every ordered result and repeated occurrence.
  Arbitrary supplied caches require the stated invariant; the empty cache
  needs no supplied premise. Physical time and key-comparison cost remain
  separate from this complete computation equation.\<close>

end
