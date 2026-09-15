theory Factor_Digit_History_Methods
  imports Factor_Digit_History_References Factor_Native_Graph_Cases
begin

definition digit_history_only_new where
  "digit_history_only_new (q::digit_required_history_state)=(case digit_history_ledger q of [] \<Rightarrow> q
    | row#rest \<Rightarrow> q\<lparr>digit_history_ledger:=[row],digit_history_index:=history_members_index [row]\<rparr>)"

definition digit_history_wrong_cache where
  "digit_history_wrong_cache (q::digit_required_history_state)=(case digit_history_ledger q of [] \<Rightarrow> q
    | (site,G)#rest \<Rightarrow> q\<lparr>digit_history_index:=history_member_insert (digit_history_index q) None [] G\<rparr>)"

definition digit_history_reserve_state where
  "digit_history_reserve_state (q::digit_required_history_state)=(case digit_history_ledger q of [] \<Rightarrow> None
    | ((u,r),G)#rest \<Rightarrow> if r=[] then
      (case finite_singleton_option (digit_allocated_artifacts (digit_history_material q) u) of None \<Rightarrow> None
      | Some R \<Rightarrow> map_option (\<lambda>A. q\<lparr>digit_history_material:=A\<rparr>)
          (digit_allocated_graft (digit_history_material q) u [(None,R)] [])) else None)"

definition digit_history_without_old_material :: "digit_history_subject\<Rightarrow>digit_history_result option\<Rightarrow>
    digit_history_result option" where
  "digit_history_without_old_material X result=(case digit_history_ledger (raw_digit_required_history (fst X)) of
    [] \<Rightarrow> result | (site,G)#rest \<Rightarrow> map_option (\<lambda>(n,q,I).
      (n,q\<lparr>required_history_material:=native_graph_remove_use (fst site) (required_history_material q)\<rparr>,I)) result)"

definition digit_history_prepared_method where
  "digit_history_prepared_method (m::nat) prepared=(case prepared of
    (X,reference,typed,legacy,unguarded,no_policy,no_replay) \<Rightarrow>
    let previous=raw_digit_required_history (fst X);
      changed=(if m=3 then map_option (\<lambda>q. q\<lparr>digit_history_index:=digit_history_index previous\<rparr>) typed
        else if m=4 then map_option (\<lambda>q. q\<lparr>digit_history_index:=Empty_Store\<rparr>) typed
        else if m=5 then map_option (\<lambda>q. q\<lparr>digit_history_ledger:=digit_history_ledger previous\<rparr>) typed
        else if m=6 then map_option digit_history_only_new typed
        else if m=7 then unguarded else if m=8 then no_policy else if m=9 then no_replay
        else if m=10 then map_option (\<lambda>q. q\<lparr>digit_history_header:=
          (digit_history_header q)\<lparr>history_header_goals:=[]\<rparr>\<rparr>) typed
        else if m=15 then map_option (\<lambda>q. q\<lparr>digit_history_ledger:=rev (digit_history_ledger q)\<rparr>) typed
        else if m=16 then map_option digit_history_wrong_cache typed
        else if m=18 then Option.bind typed digit_history_reserve_state else typed)
    in if m=1 then reference else if m=2 then legacy else if m=11 then None
      else if m=12 then Some (digit_history_state_view previous)
      else if m=17 then digit_history_without_old_material X (map_option digit_history_state_view typed)
      else map_option digit_history_state_view changed)"

lemma digit_history_prepared_correct:
  assumes "m\<in>{0,1}"
  shows "digit_history_prepared_method m (digit_history_prepare X)=digit_history_reference_option X"
  using assms digit_history_apply_exact[of X]
  by (auto simp: digit_history_prepared_method_def digit_history_prepare_def Let_def
    option.map_comp comp_def digit_history_view_def[abs_def])

definition digit_history_family_prepare where
  "digit_history_family_prepare subjects=fimage (\<lambda>(key,input).
    (key,map_option digit_history_prepare input)) subjects"

definition digit_history_prepared_reference where
  "digit_history_prepared_reference prepared=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>(X,reference,typed,legacy,unguarded,no_policy,no_replay). reference) input)) prepared"

lemma digit_history_prepared_reference_exact:
  "digit_history_prepared_reference (digit_history_family_prepare subjects)=digit_history_family_reference subjects"
  by (simp add: digit_history_prepared_reference_def digit_history_family_prepare_def digit_history_family_reference_def
    digit_history_prepare_def fimage_fimage option.map_comp comp_def case_prod_unfold)

definition digit_history_prepared_family_method where
  "digit_history_prepared_family_method (m::nat) prepared=(if m=13 then {||}
    else if m=14 then fimage (\<lambda>(key,input). (key,Some (case input of None \<Rightarrow> None
      | Some P \<Rightarrow> digit_history_prepared_method 0 P))) prepared
    else fimage (\<lambda>(key,input). (key,map_option (digit_history_prepared_method m) input)) prepared)"

definition digit_history_family_method where
  "digit_history_family_method m subjects=digit_history_prepared_family_method m (digit_history_family_prepare subjects)"

lemma digit_history_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> digit_history_family_method m subjects=digit_history_family_reference subjects"
  by (auto simp: digit_history_family_method_def digit_history_prepared_family_method_def digit_history_family_prepare_def
    digit_history_family_reference_def fimage_fimage option.map_comp comp_def case_prod_unfold digit_history_prepared_correct)

definition digit_history_context where
  "digit_history_context subjects=(let prepared=digit_history_family_prepare subjects in
    (subjects,prepared,digit_history_prepared_reference prepared))"

definition digit_history_assessment where
  "digit_history_assessment m context=(case context of (subjects,prepared,reference) \<Rightarrow>
    (digit_history_prepared_family_method m prepared,reference))"

definition digit_history_inspect :: "(digit_history_result_row fset\<times>digit_history_result_row fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "digit_history_inspect=finite_reader_inspect"

theorem digit_history_assessment_exact:
  "digit_history_inspect (digit_history_assessment m (digit_history_context subjects)) f=
    digit_history_family_condition f (digit_history_family_method m) subjects"
  by (simp only: digit_history_inspect_def digit_history_assessment_def digit_history_context_def Let_def case_prod_conv
    digit_history_prepared_reference_exact digit_history_family_method_def digit_history_family_condition_def
    finite_reader_inspect_exact[OF refl])

text \<open>
  Every candidate returns a complete actual value. Controls expose stale or
  missing caches, lost or reordered ledger rows, omitted membership, policy or
  replay checks, altered requirements, refusal, a no-op, lost old material and
  a further actual prefix reservation. The legacy original allocator remains
  separate from the bounded operation. Whole families also expose deletion and
  conflated unavailable preparation. Every original field and cache member is
  retained in the result comparison.
\<close>

end
