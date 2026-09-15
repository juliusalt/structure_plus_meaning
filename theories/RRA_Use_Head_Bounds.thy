theory RRA_Use_Head_Bounds
  imports RRA_Finite_Compact_Uses
begin

lemma compact_use_head_greater:
  assumes finite: "finite U" and member: "v\<in>insert u U"
  shows "use_word_head v<compact_use_head U u"
proof -
  have "use_word_head v\<le>Max (use_word_head ` insert u U)"
    by (rule Max_ge) (use finite member in auto)
  then show ?thesis by (simp add: compact_use_head_def)
qed

lemma finite_compact_use_head_exact:
  "finite_compact_use_head U u=compact_use_head (fset U) u"
  by (simp add: finite_compact_use_head_def compact_use_head_def fMax.F.rep_eq fimage.rep_eq)

lemma finite_compact_use_head_greater:
  "v |\<in>| finsert u U \<Longrightarrow> use_word_head v<finite_compact_use_head U u"
  by (simp only: finite_compact_use_head_exact; rule compact_use_head_greater) simp_all

lemma use_head_bound_prefix_avoids:
  "(\<forall>v\<in>insert u U. use_word_head v<n) \<Longrightarrow> prefix_avoids_uses U u [n]"
  by (auto simp: prefix_avoids_uses_def)

end
