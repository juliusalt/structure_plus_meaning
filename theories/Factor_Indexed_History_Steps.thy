theory Factor_Indexed_History_Steps
  imports Factor_Indexed_History_Members Factor_Required_History_Transitions
begin

definition indexed_required_history_step where
  "indexed_required_history_step (q::indexed_required_history_state) l rows E pu pr au ar root R=(
    if indexed_history_members (snd q) rows then
      map_option (\<lambda>(A,u,G). (finite_required_history_append (fst q) A u G,
        history_member_insert (snd q) u [] G))
        (finite_required_history_attempt (fst q) l rows E pu pr au ar root R) else None)"

theorem indexed_required_history_step_projection:
  assumes cache: "history_member_index_exact (snd q) (required_history_members (fst q))"
  shows "map_option fst (indexed_required_history_step q l rows E pu pr au ar root R)=
    finite_required_history_step (fst q) l rows E pu pr au ar root R"
  by (simp add: indexed_required_history_step_def finite_required_history_step_factored
    indexed_history_members_exact[OF cache] option.map_comp comp_def case_prod_unfold)

theorem indexed_required_history_step_valid:
  assumes previous: "indexed_required_history_valid q"
    and result: "indexed_required_history_step q l rows E pu pr au ar root R=Some following"
  shows "indexed_required_history_valid following"
proof -
  have valid: "finite_required_history_valid (fst q)"
    and cache: "history_member_index_exact (snd q) (required_history_members (fst q))"
    using previous by (auto simp: indexed_required_history_valid_def)
  have old_step: "finite_required_history_step (fst q) l rows E pu pr au ar root R=Some (fst following)"
    using indexed_required_history_step_projection[OF cache, of l rows E pu pr au ar root R] result by simp
  have next_valid: "finite_required_history_valid (fst following)"
    by (rule finite_required_history_step_valid[OF valid old_step])
  obtain A u G where following: "following=(finite_required_history_append (fst q) A u G,
    history_member_insert (snd q) u [] G)"
    using result by (auto simp: indexed_required_history_step_def split: if_splits option.splits)
  have next_cache: "history_member_index_exact (snd following) (required_history_members (fst following))"
    using history_member_insert_exact[OF cache, of u "[]" G]
    by (simp add: following finite_required_history_append_def)
  show ?thesis using next_valid next_cache by (simp add: indexed_required_history_valid_def)
qed

typedef indexed_required_history = "{q. indexed_required_history_valid q}"
  morphisms raw_indexed_required_history Indexed_Required_History
  using finite_required_histories_nonempty indexed_required_history_initial by blast

setup_lifting type_definition_indexed_required_history

lift_definition (code_dt) index_required_history :: "required_history\<Rightarrow>indexed_required_history"
  is "\<lambda>q. (raw_required_history q,history_members_index (required_history_members (raw_required_history q)))"
  by (simp add: indexed_required_history_initial required_history_valid)

lift_definition (code_dt) indexed_history_step ::
  "indexed_required_history \<Rightarrow> finite_exact_target \<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option definition_site \<Rightarrow>
    finite_exact_artifact \<Rightarrow> indexed_required_history option"
  is indexed_required_history_step
  by (auto intro: optional_result_invariant indexed_required_history_step_valid)

lemma indexed_required_history_valid:
  "indexed_required_history_valid (raw_indexed_required_history q)"
  using raw_indexed_required_history[of q] by simp

lemma index_required_history_raw:
  "raw_indexed_required_history (index_required_history q)=
    (raw_required_history q,history_members_index (required_history_members (raw_required_history q)))"
  by transfer simp

lemma indexed_history_step_raw:
  "map_option raw_indexed_required_history (indexed_history_step q l rows E pu pr au ar root R)=
    indexed_required_history_step (raw_indexed_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

export_code index_required_history indexed_history_step raw_indexed_required_history history_member_view checking SML

text \<open>
  Initialization indexes an existing valid history once. Every successful step
  checks only requested predecessor buckets and inserts only the newly admitted
  member into the same index. Original replay, policy, allocation and material
  operations retain their existing implementation and cost. The invariant
  enforces membership fidelity and complete original history validity; it does
  not identify arbitrary invariant states with reachable authorized histories.
\<close>

end
