theory Factor_Indexed_History_Projection
  imports Factor_Indexed_History_Steps
begin

instantiation indexed_required_history :: equal
begin

definition "HOL.equal q p \<longleftrightarrow>
  HOL.equal (raw_indexed_required_history q) (raw_indexed_required_history p)"

instance
  by standard (simp add: equal_indexed_required_history_def equal raw_indexed_required_history_inject)

end

declare equal_indexed_required_history_def [code]

lift_definition (code_dt) indexed_history_original :: "indexed_required_history\<Rightarrow>required_history"
  is fst
  by (simp add: indexed_required_history_valid_def)

lemma indexed_history_original_raw:
  "raw_required_history (indexed_history_original q)=fst (raw_indexed_required_history q)"
  by transfer simp

type_synonym history_index_result =
  "finite_required_history_state\<times>(local_address option definition_site\<times>finite_generation) fset"

definition history_index_state_view :: "indexed_required_history_state\<Rightarrow>history_index_result" where
  "history_index_state_view q=(fst q,history_member_view (snd q))"

definition indexed_history_view where
  "indexed_history_view q=history_index_state_view (raw_indexed_required_history q)"

definition history_index_original_result :: "finite_required_history_state\<Rightarrow>history_index_result" where
  "history_index_original_result q=(q,fset_of_list (required_history_members q))"

lemma history_index_state_view_valid:
  "indexed_required_history_valid q \<Longrightarrow>
    history_index_state_view q=history_index_original_result (fst q)"
  by (simp add: indexed_required_history_valid_def history_index_state_view_def
    history_index_original_result_def history_member_view_exact)

theorem indexed_required_history_step_view:
  assumes valid: "indexed_required_history_valid q"
  shows "map_option history_index_state_view (indexed_required_history_step q l rows E pu pr au ar root R)=
    map_option history_index_original_result (finite_required_history_step (fst q) l rows E pu pr au ar root R)"
proof -
  have cache: "history_member_index_exact (snd q) (required_history_members (fst q))"
    using valid by (simp add: indexed_required_history_valid_def)
  have projection: "map_option fst (indexed_required_history_step q l rows E pu pr au ar root R)=
    finite_required_history_step (fst q) l rows E pu pr au ar root R"
    by (rule indexed_required_history_step_projection[OF cache])
  show ?thesis
  proof (cases "indexed_required_history_step q l rows E pu pr au ar root R")
    case None
    then show ?thesis using projection by simp
  next
    case (Some following)
    have following_valid: "indexed_required_history_valid following"
      by (rule indexed_required_history_step_valid[OF valid Some])
    have original: "finite_required_history_step (fst q) l rows E pu pr au ar root R=Some (fst following)"
      using projection Some by simp
    show ?thesis by (simp only: Some original option.map history_index_state_view_valid[OF following_valid])
  qed
qed

theorem indexed_history_step_view:
  "map_option indexed_history_view (indexed_history_step q l rows E pu pr au ar root R)=
    map_option history_index_original_result
      (finite_required_history_step (fst (raw_indexed_required_history q)) l rows E pu pr au ar root R)"
proof -
  have "map_option history_index_state_view
      (map_option raw_indexed_required_history (indexed_history_step q l rows E pu pr au ar root R))=
    map_option history_index_original_result
      (finite_required_history_step (fst (raw_indexed_required_history q)) l rows E pu pr au ar root R)"
    by (simp only: indexed_history_step_raw
      indexed_required_history_step_view[OF indexed_required_history_valid])
  then show ?thesis by (simp add: option.map_comp comp_def indexed_history_view_def[abs_def])
qed

export_code indexed_history_original indexed_history_view history_index_state_view history_index_original_result checking SML

text \<open>
  The complete observation retains every original state field and the exact
  decoded membership relation. Both come from the actual output. Equality of
  only the original state would miss a stale cache; the additional relation
  is independently determined by the original ordered ledger.
\<close>

end
