theory Factor_Required_History_Projection
  imports Factor_Required_History_Construction
begin

instantiation required_history :: equal
begin

definition "HOL.equal q p \<longleftrightarrow> HOL.equal (raw_required_history q) (raw_required_history p)"

instance
  by standard (simp add: equal_required_history_def equal raw_required_history_inject)

end

declare equal_required_history_def [code]

lemma prepare_required_history_raw:
  "map_option raw_required_history (prepare_required_history S su sr gs)=
    finite_prepare_required_history S su sr gs"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma required_history_step_raw:
  "map_option raw_required_history (required_history_step q l rows E pu pr au ar root R)=
    finite_required_history_step (raw_required_history q) l rows E pu pr au ar root R"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma finite_required_history_member_subset:
  assumes "finite_required_history_valid q" "set rows\<subseteq>set (required_history_members q)"
  shows "finite_required_history_valid (q\<lparr>required_history_members:=rows\<rparr>)"
  using assms by (auto simp: finite_required_history_valid_def; blast)

text \<open>
  Projection retains every field of the original checked operation. The subset
  lemma concerns the stated invariant: retaining material does not by itself
  place every generation in the admission ledger. Reachability through the
  preparation and step API is a separate property.
\<close>

end
