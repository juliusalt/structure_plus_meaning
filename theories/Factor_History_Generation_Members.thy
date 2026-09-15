theory Factor_History_Generation_Members
  imports Factor_Digit_History_States
begin

lemma required_history_member_generation:
  assumes valid: "finite_required_history_valid q"
    and member: "(d,G)\<in>set (required_history_members q)"
  shows "finite_check_generation G (required_history_material q) (fst d) (snd d)"
  using valid member unfolding finite_required_history_valid_def by blast

lemma required_history_member_generations:
  assumes valid: "finite_required_history_valid q"
    and members: "list_all (\<lambda>row. row\<in>set (required_history_members q)) rows"
  shows "list_all (\<lambda>(d,G). finite_check_generation G (required_history_material q) (fst d) (snd d)) rows"
  using members required_history_member_generation[OF valid]
  by (auto simp: list_all_iff)

theorem digit_history_indexed_generations:
  assumes valid: "digit_required_history_valid q"
    and members: "indexed_history_members (digit_history_index q) rows"
  shows "list_all (\<lambda>(d,G). finite_check_generation G
    (snd (digit_allocated_view (digit_history_material q))) (fst d) (snd d)) rows"
proof -
  have original: "finite_required_history_valid (digit_history_original_state q)"
    and cache: "history_member_index_exact (digit_history_index q) (digit_history_ledger q)"
    using valid by (simp only: digit_required_history_valid_def; blast)+
  have old_members: "list_all (\<lambda>row. row\<in>set (required_history_members (digit_history_original_state q))) rows"
    using members by (simp only: indexed_history_members_exact[OF cache]
      digit_history_original_state_def finite_history_with_components)
  show ?thesis using required_history_member_generations[OF original old_members]
    by (simp only: digit_history_original_state_def finite_history_with_components)
qed

text \<open>
  The exact index and original closed-state invariant establish each complete
  requested generation reading at its original site. The entire requested row
  remains the membership subject. Readable material outside the ledger does
  not acquire this premise, and invariant validity is not historical reachability.
\<close>

end
