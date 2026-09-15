theory History_Input_Transitions
  imports Factor_Digit_History_References Optional_Transition_Sequences
begin

type_synonym 'a history_subject_input = "'a\<times>required_history_input"
type_synonym bounded_history_subject = "(nat\<times>finite_required_history_state) history_subject_input"

fun history_request_members where
  "history_request_members (History_Step l rows E pu pr au ar root R) members=
    History_Step l members E pu pr au ar root R"

definition history_subject_map where
  "history_subject_map project X=(project (fst X),snd X)"

definition history_next_input :: "('a history_subject_input\<Rightarrow>'a option)\<Rightarrow>
    ('a\<Rightarrow>(local_address option definition_site\<times>finite_generation) list)\<Rightarrow>
    'a history_subject_input\<Rightarrow>'a history_subject_input option" where
  "history_next_input step read_members X=map_option
    (\<lambda>following. (following,history_request_members (snd X) (read_members following))) (step X)"

lemma history_next_input_projection:
  assumes each: "\<And>X. map_option project (step X)=original_step (history_subject_map project X)"
    and members: "\<And>q. original_members (project q)=read_members q"
  shows "map_option (history_subject_map project) (history_next_input step read_members X)=
    history_next_input original_step original_members (history_subject_map project X)"
  unfolding history_next_input_def
  by (simp only: each[symmetric]; simp add: option.map_comp comp_def history_subject_map_def members)

definition history_following_input :: "('a history_subject_input\<Rightarrow>'a option)\<Rightarrow>
    ('a\<Rightarrow>(local_address option definition_site\<times>finite_generation) list)\<Rightarrow>
    'a history_subject_input option\<Rightarrow>'a history_subject_input option" where
  "history_following_input step read_members input=Option.bind input (history_next_input step read_members)"

lemma history_following_input_projection:
  assumes each: "\<And>X. map_option project (step X)=original_step (history_subject_map project X)"
    and members: "\<And>q. original_members (project q)=read_members q"
  shows "map_option (history_subject_map project) (history_following_input step read_members input)=
    history_following_input original_step original_members (map_option (history_subject_map project) input)"
  unfolding history_following_input_def
  by (rule optional_bind_projection[where project="history_subject_map project"])
    (rule refl, rule history_next_input_projection[where project=project and step=step
      and original_step=original_step and read_members=read_members and original_members=original_members,
      OF each members])

definition history_input_chain where
  "history_input_chain step read_members n input=(history_following_input step read_members ^^ n) input"

theorem history_input_chain_projection:
  assumes each: "\<And>X. map_option project (step X)=original_step (history_subject_map project X)"
    and members: "\<And>q. original_members (project q)=read_members q"
  shows "map_option (history_subject_map project) (history_input_chain step read_members n input)=
    history_input_chain original_step original_members n (map_option (history_subject_map project) input)"
  unfolding history_input_chain_def
  by (rule function_iteration_projection; rule history_following_input_projection[where project=project and step=step
    and original_step=original_step and read_members=read_members and original_members=original_members,
    OF each members])

fun bounded_history_apply where
  "bounded_history_apply (state,History_Step l rows E pu pr au ar root R)=
    bounded_required_history_step state l rows E pu pr au ar root R"

definition digit_history_base where
  "digit_history_base q=digit_history_base_view (raw_digit_required_history q)"

lemma digit_history_apply_base:
  "map_option digit_history_base (digit_history_apply X)=
    bounded_history_apply (history_subject_map digit_history_base X)"
proof -
  obtain q input where shape: "X=(q,input)" by (cases X) auto
  have cache: "history_member_index_exact (digit_history_index (raw_digit_required_history q))
    (digit_history_ledger (raw_digit_required_history q))"
    using digit_required_history_valid[of q] by (simp only: digit_required_history_valid_def; blast)
  show ?thesis using digit_required_history_step_projection[OF cache]
    by (cases input) (simp only: shape digit_history_apply.simps history_subject_map_def fst_conv snd_conv
      bounded_history_apply.simps digit_history_base_def[abs_def] option.map_comp comp_def
      digit_history_step_raw[symmetric])
qed

lemma digit_history_members_base:
  "required_history_members (snd (digit_history_base q))=digit_history_ledger (raw_digit_required_history q)"
  by (simp only: digit_history_base_def digit_history_base_components digit_history_original_components)

definition digit_history_initial_subject :: "required_history_subject\<Rightarrow>digit_history_subject option" where
  "digit_history_initial_subject X=map_option (\<lambda>q. (q,snd X)) (load_digit_required_history (fst X))"

definition bounded_history_initial_subject :: "required_history_subject\<Rightarrow>bounded_history_subject option" where
  "bounded_history_initial_subject X=map_option (\<lambda>q. (q,snd X)) (bounded_history_load (raw_required_history (fst X)))"

lemma digit_history_initial_subject_projection:
  "map_option (history_subject_map digit_history_base) (digit_history_initial_subject X)=
    bounded_history_initial_subject X"
proof -
  have loaded: "map_option digit_history_base (load_digit_required_history (fst X))=
    bounded_history_load (raw_required_history (fst X))"
    using digit_history_load_base_projection[of "raw_required_history (fst X)"]
    by (simp only: load_digit_required_history_raw[symmetric] option.map_comp comp_def digit_history_base_def[abs_def])
  show ?thesis unfolding digit_history_initial_subject_def bounded_history_initial_subject_def
    by (simp only: loaded[symmetric]; simp add: option.map_comp comp_def history_subject_map_def)
qed

text \<open>
  Every subsequent request uses the actual returned state and its complete
  ordered ledger. Exact state projection and the original ledger-reading
  equation compose through optional bind and arbitrary iteration. Initial
  loading retains the entire original request and material bound.
\<close>

end
