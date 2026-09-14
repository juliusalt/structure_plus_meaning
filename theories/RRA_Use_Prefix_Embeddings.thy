theory RRA_Use_Prefix_Embeddings
  imports RRA_Fresh_Uses
begin

fun prefix_use_map :: "local_address\<Rightarrow>local_address option\<Rightarrow>
    local_address option\<Rightarrow>local_address option" where
  "prefix_use_map prefix u None=u"
| "prefix_use_map prefix u (Some a)=Some (prefix@a)"

definition prefix_avoids_uses where
  "prefix_avoids_uses U u prefix \<longleftrightarrow> (\<forall>a. Some (prefix@a)\<notin>insert u U)"

theorem prefix_use_map_outside:
  "prefix_avoids_uses U u prefix \<Longrightarrow> prefix_use_map prefix u (Some a)\<notin>insert u U"
  by (simp add: prefix_avoids_uses_def)

theorem prefix_use_map_injective:
  assumes fresh: "prefix_avoids_uses U u prefix"
  shows "inj (prefix_use_map prefix u)"
proof (rule injI)
  fix x y
  assume equal: "prefix_use_map prefix u x=prefix_use_map prefix u y"
  show "x=y" using fresh equal
    by (cases x; cases y) (auto simp: prefix_avoids_uses_def)
qed

lemma original_fresh_use_prefix:
  "fresh_use_map U u=prefix_use_map (fresh_use_prefix U u) u"
  by (rule ext) (rename_tac x; case_tac x; simp)

lemma original_prefix_avoids_uses:
  "finite U \<Longrightarrow> prefix_avoids_uses U u (fresh_use_prefix U u)"
  using fresh_use_map_outside by (auto simp: prefix_avoids_uses_def)

text \<open>
  A fresh prefix preserves the supplied boundary at the absent input, embeds
  every present input injectively, and avoids the entire old use set and boundary.
  The original zero-prefix allocator instantiates this common contract. The
  contract does not prescribe one nominal prefix or a byte bound on use words.
\<close>

end
