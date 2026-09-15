theory Factor_Digit_History_States
  imports Factor_History_State_Components Factor_Indexed_History_Members RRA_Digit_Environment_Availability
begin

record digit_required_history_state =
  digit_history_header :: finite_required_history_header
  digit_history_material :: digit_allocated_environment
  digit_history_ledger :: "(local_address option definition_site\<times>finite_generation) list"
  digit_history_index :: history_member_index

definition digit_history_original_state :: "digit_required_history_state\<Rightarrow>finite_required_history_state" where
  "digit_history_original_state q=finite_history_with (digit_history_header q)
    (snd (digit_allocated_view (digit_history_material q))) (digit_history_ledger q)"

definition digit_required_history_valid where
  "digit_required_history_valid q \<longleftrightarrow>
    finite_required_history_valid (digit_history_original_state q) \<and>
    history_member_index_exact (digit_history_index q) (digit_history_ledger q)"

definition digit_history_load_state :: "finite_required_history_state\<Rightarrow>digit_required_history_state option" where
  "digit_history_load_state q=map_option (\<lambda>material.
    \<lparr>digit_history_header=finite_history_header q,digit_history_material=material,
      digit_history_ledger=required_history_members q,
      digit_history_index=history_members_index (required_history_members q)\<rparr>)
    (load_digit_environment (required_history_material q))"

theorem digit_history_load_state_domain:
  "digit_history_load_state q\<noteq>None \<longleftrightarrow> finite_environment_formed (required_history_material q)"
  by (simp only: digit_history_load_state_def map_option_is_None load_digit_environment_domain)

theorem digit_history_load_state_properties:
  assumes result: "digit_history_load_state q=Some following"
  shows "digit_history_original_state following=q"
    "history_member_index_exact (digit_history_index following) (digit_history_ledger following)"
    "fst (digit_allocated_view (digit_history_material following))=
      finite_compact_use_head (finite_environment_uses (required_history_material q)) None"
proof -
  obtain material where loaded: "load_digit_environment (required_history_material q)=Some material"
    and following: "following=\<lparr>digit_history_header=finite_history_header q,digit_history_material=material,
      digit_history_ledger=required_history_members q,
      digit_history_index=history_members_index (required_history_members q)\<rparr>"
    using result by (auto simp: digit_history_load_state_def split: option.splits)
  have view: "digit_allocated_view material=
    (finite_compact_use_head (finite_environment_uses (required_history_material q)) None,required_history_material q)"
    using load_digit_environment_exact[of "required_history_material q"] loaded
    by (auto split: if_splits)
  show "digit_history_original_state following=q"
    by (simp add: following digit_history_original_state_def view finite_history_components_recover)
  show "history_member_index_exact (digit_history_index following) (digit_history_ledger following)"
    by (simp add: following history_members_index_exact)
  show "fst (digit_allocated_view (digit_history_material following))=
      finite_compact_use_head (finite_environment_uses (required_history_material q)) None"
    by (simp add: following view)
qed

theorem digit_history_load_state_valid:
  "finite_required_history_valid q \<Longrightarrow> digit_history_load_state q=Some following \<Longrightarrow>
    digit_required_history_valid following"
  by (simp add: digit_required_history_valid_def digit_history_load_state_properties)

lemma digit_required_histories_nonempty:
  "\<exists>q. digit_required_history_valid q"
proof -
  obtain q where valid: "finite_required_history_valid q" using finite_required_histories_nonempty by blast
  have formed: "finite_environment_formed (required_history_material q)"
    using valid by (auto simp: finite_required_history_valid_def)
  obtain following where loaded: "digit_history_load_state q=Some following"
    using formed digit_history_load_state_domain[of q] by (cases "digit_history_load_state q") auto
  show ?thesis using digit_history_load_state_valid[OF valid loaded] by blast
qed

typedef digit_required_history = "{q. digit_required_history_valid q}"
  morphisms raw_digit_required_history Digit_Required_History
  using digit_required_histories_nonempty by blast

setup_lifting type_definition_digit_required_history

lift_definition (code_dt) load_digit_required_history :: "required_history\<Rightarrow>digit_required_history option"
  is "\<lambda>q. digit_history_load_state (raw_required_history q)"
  by (auto intro: optional_result_invariant digit_history_load_state_valid required_history_valid)

lemma digit_required_history_valid:
  "digit_required_history_valid (raw_digit_required_history q)"
  using raw_digit_required_history[of q] by simp

lemma load_digit_required_history_raw:
  "map_option raw_digit_required_history (load_digit_required_history q)=
    digit_history_load_state (raw_required_history q)"
  by transfer (simp add: option.map_id[unfolded id_def])

instantiation digit_required_history :: equal
begin

definition "HOL.equal q p \<longleftrightarrow> HOL.equal (raw_digit_required_history q) (raw_digit_required_history p)"

instance by standard (simp add: equal_digit_required_history_def equal raw_digit_required_history_inject)

end

declare equal_digit_required_history_def [code]

type_synonym digit_history_result = "nat\<times>finite_required_history_state\<times>
  (local_address option definition_site\<times>finite_generation) fset"

definition digit_history_state_view :: "digit_required_history_state\<Rightarrow>digit_history_result" where
  "digit_history_state_view q=(fst (digit_allocated_view (digit_history_material q)),
    digit_history_original_state q,history_member_view (digit_history_index q))"

definition digit_history_view where
  "digit_history_view q=digit_history_state_view (raw_digit_required_history q)"

export_code load_digit_required_history digit_history_view checking SML

text \<open>
  The state stores one fixed header, one actual persistent digit material,
  the complete ordered ledger and its exact membership cache. The full original
  history is a derived view. Loading preserves every original field and computes
  the initial material bound once. The closed type carries original validity
  and cache fidelity; it does not identify those conditions with reachability
  or confer authority on external actions.
\<close>

end
