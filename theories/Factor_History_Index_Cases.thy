theory Factor_History_Index_Cases
  imports Factor_History_Index_Methods Factor_Required_History_Cases
begin

lemma index_required_history_original [simp]:
  "indexed_history_original (index_required_history q)=q"
  by (metis indexed_history_original_raw index_required_history_raw fst_conv raw_required_history_inject)

definition history_index_source_case where
  "history_index_source_case w=fimage (\<lambda>(key,input).
    (key,map_option (\<lambda>(q,request). (index_required_history q,request)) input)) (required_history_case w)"

definition history_index_original_family where
  "history_index_original_family subjects=fimage (\<lambda>(key,input).
    (key,map_option history_index_original_subject input)) subjects"

lemma history_index_source_case_original:
  "history_index_original_family (history_index_source_case w)=required_history_case w"
  by (simp add: history_index_original_family_def history_index_source_case_def fimage_fimage
    option.map_comp option.map_id[unfolded id_def] comp_def case_prod_unfold history_index_original_subject.simps)

fun history_index_next_request where
  "history_index_next_request q (History_Step l rows E pu pr au ar root R)=
    History_Step l (required_history_members (fst (raw_indexed_required_history q))) E pu pr au ar root R"

fun history_index_chain where
  "history_index_chain 0 X=Some X"
| "history_index_chain (Suc n) X=(case history_index_chain n X of None \<Rightarrow> None
    | Some (q,request) \<Rightarrow> map_option (\<lambda>following.
      (following,history_index_next_request following request)) (history_index_apply (q,request)))"

definition history_index_case where
  "history_index_case (w::nat)=(if w<12 then history_index_source_case w else
    fimage (\<lambda>(key,input). (key,case input of None \<Rightarrow> None
      | Some X \<Rightarrow> history_index_chain (w-11) X)) (history_index_source_case 0))"

lemma history_index_case_previous:
  "w<12 \<Longrightarrow> history_index_original_family (history_index_case w)=required_history_case w"
  by (simp add: history_index_case_def history_index_source_case_original)

definition history_index_source_scope :: "nat list\<Rightarrow>nat list" where
  "history_index_source_scope ws=filter (\<lambda>w. w<12) ws"

definition history_index_previous_cases where
  "history_index_previous_cases ws=map (\<lambda>w. (w,required_history_case w)) (history_index_source_scope ws)"

definition history_index_source_equal ::
  "(required_history_certificate option\<times>history_index_subject option) fset\<Rightarrow>
    (required_history_certificate option\<times>required_history_subject option) fset\<Rightarrow>bool" where
  "history_index_source_equal subjects previous \<longleftrightarrow> history_index_original_family subjects=previous"

definition history_index_indices :: "nat list" where "history_index_indices=[0..<16]"

text \<open>
  The original twelve complete certificate families are reused directly and
  recovered by a proved all-input equation. Four further cases run one through
  four actual indexed steps from the prepared original source. Every subsequent
  request uses the members of the actual preceding output. The inherited
  empty-ledger fixture still distinguishes retained material from admission;
  it is not claimed reachable through preparation and insertion alone.
\<close>

end
