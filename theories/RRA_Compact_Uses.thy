theory RRA_Compact_Uses
  imports RRA_Use_Prefix_Embeddings
begin

fun use_word_head :: "local_address option\<Rightarrow>nat" where
  "use_word_head None=0"
| "use_word_head (Some [])=0"
| "use_word_head (Some (a#word))=a"

definition compact_use_head where
  "compact_use_head U u=Suc (Max (use_word_head ` insert u U))"

definition compact_use_prefix where
  "compact_use_prefix U u=[compact_use_head U u]"

definition compact_use_map where
  "compact_use_map U u=prefix_use_map (compact_use_prefix U u) u"

theorem compact_use_prefix_avoids:
  assumes finite: "finite U"
  shows "prefix_avoids_uses U u (compact_use_prefix U u)"
proof (unfold prefix_avoids_uses_def compact_use_prefix_def, intro allI notI)
  fix word
  assume member: "Some ([compact_use_head U u]@word)\<in>insert u U"
  have heads_finite: "finite (use_word_head ` insert u U)" using finite by simp
  have head_member: "use_word_head (Some ([compact_use_head U u]@word))\<in>
      use_word_head ` insert u U"
    by (rule imageI[OF member])
  have bound: "use_word_head (Some ([compact_use_head U u]@word))\<le>
      Max (use_word_head ` insert u U)"
    by (rule Max_ge[OF heads_finite head_member])
  show False using bound by (simp add: compact_use_head_def)
qed

theorem compact_use_map_injective:
  "finite U \<Longrightarrow> inj (compact_use_map U u)"
  by (simp only: compact_use_map_def; rule prefix_use_map_injective; rule compact_use_prefix_avoids)

theorem compact_use_map_outside:
  "finite U \<Longrightarrow> compact_use_map U u (Some word)\<notin>insert u U"
  by (simp only: compact_use_map_def; rule prefix_use_map_outside; rule compact_use_prefix_avoids)

lemma compact_use_map_boundary [simp]: "compact_use_map U u None=u"
  by (simp add: compact_use_map_def)

lemma compact_use_word_length:
  "use_word_length (compact_use_map U u (Some word))=Suc (length word)"
  by (simp add: compact_use_map_def compact_use_prefix_def)

text \<open>
  The next head is computed from every actual old use and the actual boundary.
  The prefix has one natural coordinate, while the original suffix is unchanged.
  This bounds word-coordinate growth. Computing the initial bound, natural
  number bit cost, cached allocation-state maintenance, graft preservation and
  the complete physical cost require their own further accounts.
\<close>

end
