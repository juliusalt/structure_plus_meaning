theory Factor_History_Index_References
  imports Factor_Indexed_History_Projection Factor_Required_History_Methods
begin

type_synonym history_index_subject = "indexed_required_history\<times>required_history_input"
type_synonym history_index_result_row =
  "required_history_certificate option\<times>history_index_result option option"

fun history_index_original_subject where
  "history_index_original_subject (q,input)=(indexed_history_original q,input)"

fun history_index_apply where
  "history_index_apply (q,History_Step l rows E pu pr au ar root R)=
    indexed_history_step q l rows E pu pr au ar root R"

definition history_index_reference where
  "history_index_reference X=map_option history_index_original_result
    (required_history_reference_option (history_index_original_subject X))"

definition history_index_transition where
  "history_index_transition X following \<longleftrightarrow>
    required_history_transition (history_index_original_subject X) (fst following) \<and>
    snd following=fset_of_list (required_history_members (fst following))"

theorem history_index_reference_exact:
  "history_index_reference X=Some following \<longleftrightarrow> history_index_transition X following"
  by (cases following) (auto simp: history_index_reference_def history_index_transition_def
    history_index_original_result_def required_history_reference_exact split: option.splits)

lemma history_index_apply_exact:
  "map_option indexed_history_view (history_index_apply X)=history_index_reference X"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  show ?thesis by (cases input) (simp add: shape history_index_reference_def
    indexed_history_step_view indexed_history_original_raw)
qed

fun history_index_unguarded where
  "history_index_unguarded (q,History_Step l rows E pu pr au ar root R)=(
    let previous=raw_indexed_required_history q in
    map_option (\<lambda>(A,u,G). (finite_required_history_append (fst previous) A u G,
      history_member_insert (snd previous) u [] G))
      (finite_required_history_attempt (fst previous) l rows E pu pr au ar root R))"

definition history_index_prepare where
  "history_index_prepare X=(X,history_index_reference X,
    map_option raw_indexed_required_history (history_index_apply X),history_index_unguarded X)"

definition history_index_family_prepare where
  "history_index_family_prepare subjects=fimage (\<lambda>(key,input).
    (key,map_option history_index_prepare input)) subjects"

definition history_index_family_reference where
  "history_index_family_reference subjects=fimage (\<lambda>(key,input).
    (key,map_option history_index_reference input)) subjects"

definition history_index_prepared_reference where
  "history_index_prepared_reference prepared=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>(X,reference,typed,unguarded). reference) input)) prepared"

lemma history_index_prepared_reference_exact:
  "history_index_prepared_reference (history_index_family_prepare subjects)=history_index_family_reference subjects"
  by (simp add: history_index_prepared_reference_def history_index_family_prepare_def
    history_index_family_reference_def history_index_prepare_def fimage_fimage option.map_comp
    comp_def case_prod_unfold)

text \<open>
  The original required-history transition determines every result field and
  the exact membership relation independently of the store. Actual typed and
  unguarded operations are computed once per complete input and shared by the
  subsequent candidate comparisons. Their preparation equations retain the
  original subjects; no observations or validity flags are supplied.
\<close>

end
