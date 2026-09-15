theory Factor_History_Index_Methods
  imports Factor_History_Index_References
begin

definition history_index_only_new where
  "history_index_only_new (following::indexed_required_history_state)=(
    case required_history_members (fst following) of [] \<Rightarrow> following | row#rest \<Rightarrow>
      ((fst following)\<lparr>required_history_members:=[row]\<rparr>,history_members_index [row]))"

definition history_index_wrong_site where
  "history_index_wrong_site (following::indexed_required_history_state)=(
    case required_history_members (fst following) of [] \<Rightarrow> following | (site,G)#rest \<Rightarrow>
      (fst following,history_member_insert (snd following) None [] G))"

definition history_index_prepared_method where
  "history_index_prepared_method (m::nat) prepared=(case prepared of
    (X,reference,typed,unguarded) \<Rightarrow> let previous=raw_indexed_required_history (fst X) in
    if m=0 then map_option history_index_state_view typed
    else if m=1 then reference else
    map_option history_index_state_view (
      if m=2 then map_option (\<lambda>following. (fst following,snd previous)) typed
      else if m=3 then map_option (\<lambda>following. (fst following,Empty_Store)) typed
      else if m=4 then map_option history_index_only_new typed
      else if m=5 then map_option (\<lambda>following.
        ((fst following)\<lparr>required_history_members:=required_history_members (fst previous)\<rparr>,snd following)) typed
      else if m=6 then map_option (\<lambda>following.
        ((fst following)\<lparr>required_history_members:=rev (required_history_members (fst following))\<rparr>,snd following)) typed
      else if m=7 then unguarded
      else if m=8 then map_option history_index_wrong_site typed
      else if m=9 then map_option (\<lambda>following.
        ((fst following)\<lparr>required_history_goals:=[]\<rparr>,snd following)) typed
      else if m=10 then Some previous else None))"

lemma history_index_prepared_correct:
  assumes "m\<in>{0,1}"
  shows "history_index_prepared_method m (history_index_prepare X)=history_index_reference X"
  using assms history_index_apply_exact[of X]
  by (auto simp: history_index_prepared_method_def history_index_prepare_def Let_def
    option.map_comp comp_def indexed_history_view_def[abs_def])

definition history_index_prepared_family_method where
  "history_index_prepared_family_method (m::nat) prepared=(
    if m=12 then {||} else if m=13 then fimage (\<lambda>(key,input).
      (key,Some (case input of None \<Rightarrow> None | Some P \<Rightarrow> history_index_prepared_method 0 P))) prepared
    else fimage (\<lambda>(key,input). (key,map_option (history_index_prepared_method m) input)) prepared)"

definition history_index_family_method where
  "history_index_family_method m subjects=
    history_index_prepared_family_method m (history_index_family_prepare subjects)"

theorem history_index_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> history_index_family_method m subjects=history_index_family_reference subjects"
  by (auto simp: history_index_family_method_def history_index_prepared_family_method_def
    history_index_family_prepare_def history_index_family_reference_def
    fimage_fimage option.map_comp comp_def case_prod_unfold history_index_prepared_correct)

definition history_index_inspect ::
  "(history_index_result_row fset\<times>history_index_result_row fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "history_index_inspect=finite_reader_inspect"

definition history_index_family_condition where
  "history_index_family_condition f method subjects=relation_reader_condition
    (\<lambda>row. row |\<in>| history_index_family_reference subjects) f (method subjects)"

definition history_index_context where
  "history_index_context subjects=(let prepared=history_index_family_prepare subjects in
    (subjects,prepared,history_index_prepared_reference prepared))"

definition history_index_assessment where
  "history_index_assessment m context=(case context of (subjects,prepared,reference) \<Rightarrow>
    (history_index_prepared_family_method m prepared,reference))"

lemma history_index_assessment_exact:
  "history_index_inspect (history_index_assessment m (history_index_context subjects)) f=
    history_index_family_condition f (history_index_family_method m) subjects"
  by (simp only: history_index_inspect_def history_index_assessment_def history_index_context_def
    Let_def case_prod_conv history_index_prepared_reference_exact history_index_family_method_def
    history_index_family_condition_def finite_reader_inspect_exact[OF refl])

text \<open>
  Whole comparisons distinguish a stale or empty cache, loss of prior members,
  an omitted new ledger entry, reordered ledger presentation, a bypassed
  membership gate, an unsupported cached site, altered original requirements,
  refusal, a no-op, a deleted family and conflated unavailable preparation.
  Cache equality concerns every decoded member; original list order remains
  a separate field. The typed method and original reference have complete
  all-input equations, independently of the finite case scope.
\<close>

end
