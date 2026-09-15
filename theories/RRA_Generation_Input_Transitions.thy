theory RRA_Generation_Input_Transitions
  imports RRA_Digit_Generation_References RRA_Digit_Environment_Loading
begin

type_synonym 'a generation_record_input =
  "'a option\<times>finite_exact_target\<times>finite_exact_target\<times>finite_exact_target\<times>
    (local_address option definition_site\<times>finite_generation) list"
type_synonym bounded_generation_subject =
  "(nat\<times>local_address option finite_artifact_environment) generation_record_input"

definition generation_input_map :: "('a\<Rightarrow>'b)\<Rightarrow>'a generation_record_input\<Rightarrow>'b generation_record_input" where
  "generation_input_map project X=(case X of (input,l,p,c,rows) \<Rightarrow> (map_option project input,l,p,c,rows))"

definition generation_following_input ::
  "('a\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>finite_exact_target\<Rightarrow>
      (local_address option definition_site\<times>finite_generation) list\<Rightarrow>
      ('a\<times>local_address option\<times>finite_generation) option)\<Rightarrow>
    'a generation_record_input\<Rightarrow>'a generation_record_input" where
  "generation_following_input construct X=(case X of (input,l,p,c,rows) \<Rightarrow>
    case input of None \<Rightarrow> X | Some q \<Rightarrow>
      case construct q l p c rows of None \<Rightarrow> (None,l,p,c,rows)
      | Some (following,u,G) \<Rightarrow> (Some following,l,p,c,[((u,[]),G)]))"

theorem generation_following_input_projection:
  assumes each: "\<And>q l p c rows. map_option (\<lambda>(following,u,G). (project following,u,G))
    (construct q l p c rows)=original (project q) l p c rows"
  shows "generation_input_map project (generation_following_input construct X)=
    generation_following_input original (generation_input_map project X)"
proof -
  obtain input l p c rows where shape: "X=(input,l,p,c,rows)" by (cases X) auto
  show ?thesis
  proof (cases input)
    case None then show ?thesis by (simp add: shape generation_input_map_def generation_following_input_def)
  next
    case (Some q)
    show ?thesis
    proof (cases "construct q l p c rows")
      case None
      have original: "original (project q) l p c rows=None" using each[of q l p c rows] None by simp
      show ?thesis by (simp add: shape Some None original generation_input_map_def generation_following_input_def)
    next
      case (Some result)
      obtain following u G where result: "result=(following,u,G)" by (cases result) auto
      have original: "original (project q) l p c rows=Some (project following,u,G)"
        using each[of q l p c rows] Some by (simp add: result)
      show ?thesis by (simp add: shape \<open>input=Some q\<close> Some result original
        generation_input_map_def generation_following_input_def)
    qed
  qed
qed

theorem generation_input_iteration_projection:
  assumes each: "\<And>q l p c rows. map_option (\<lambda>(following,u,G). (project following,u,G))
    (construct q l p c rows)=original (project q) l p c rows"
  shows "generation_input_map project ((generation_following_input construct ^^ n) X)=
    (generation_following_input original ^^ n) (generation_input_map project X)"
  by (rule function_iteration_projection)
    (rule generation_following_input_projection[where project=project and construct=construct and original=original]; rule each)

definition digit_initial_generation_input :: "generation_record_problem\<Rightarrow>digit_generation_subject" where
  "digit_initial_generation_input X=(case X of (E,l,p,c,rows) \<Rightarrow> (load_digit_environment E,l,p,c,rows))"

definition bounded_initial_generation_input :: "generation_record_problem\<Rightarrow>bounded_generation_subject" where
  "bounded_initial_generation_input X=(case X of (E,l,p,c,rows) \<Rightarrow>
    (if finite_environment_formed E then Some (finite_compact_use_head (finite_environment_uses E) None,E) else None,l,p,c,rows))"

theorem initial_generation_input_projection:
  "generation_input_map digit_allocated_view (digit_initial_generation_input X)=bounded_initial_generation_input X"
  by (simp add: generation_input_map_def digit_initial_generation_input_def bounded_initial_generation_input_def
    load_digit_environment_exact split: prod.splits)

definition digit_generation_chain where
  "digit_generation_chain n X=(generation_following_input digit_construct_generation ^^ n) X"

definition bounded_generation_chain where
  "bounded_generation_chain n X=(generation_following_input finite_construct_bounded_generation ^^ n) X"

theorem digit_generation_chain_projection:
  "generation_input_map digit_allocated_view (digit_generation_chain n X)=
    bounded_generation_chain n (generation_input_map digit_allocated_view X)"
  unfolding digit_generation_chain_def bounded_generation_chain_def
  by (rule generation_input_iteration_projection) (rule digit_construct_generation_projection)

definition digit_generation_reserve where
  "digit_generation_reserve q=digit_allocated_graft q None [(None,finite_payload_syntax [31])] []"

definition bounded_generation_reserve where
  "bounded_generation_reserve state=finite_bounded_graft_reference state None
    (finite_enumerated_environment [(None,finite_payload_syntax [31])] [])"

lemma digit_generation_reserve_projection:
  "map_option digit_allocated_view (digit_generation_reserve q)=bounded_generation_reserve (digit_allocated_view q)"
  by (simp only: digit_generation_reserve_def bounded_generation_reserve_def digit_graft_reference_exact)

definition generation_reserve_input :: "('a\<Rightarrow>'a option)\<Rightarrow>'a generation_record_input\<Rightarrow>'a generation_record_input" where
  "generation_reserve_input reserve X=(case X of (input,l,p,c,rows) \<Rightarrow>
    (Option.bind input reserve,l,p,c,rows))"

lemma generation_reserve_input_projection:
  assumes each: "\<And>q. map_option project (reserve q)=original (project q)"
  shows "generation_input_map project (generation_reserve_input reserve X)=
    generation_reserve_input original (generation_input_map project X)"
proof -
  have projected: "map_option project (Option.bind input reserve)=
    Option.bind (map_option project input) original" for input
    by (rule optional_bind_projection[where project=project
      and following=reserve and original_following=original]) (rule refl, rule each)
  show ?thesis by (simp only: generation_input_map_def generation_reserve_input_def case_prod_unfold fst_conv snd_conv projected)
qed

definition digit_generation_reservations where
  "digit_generation_reservations n X=(generation_reserve_input digit_generation_reserve ^^ n) X"

definition bounded_generation_reservations where
  "bounded_generation_reservations n X=(generation_reserve_input bounded_generation_reserve ^^ n) X"

theorem digit_generation_reservations_projection:
  "generation_input_map digit_allocated_view (digit_generation_reservations n X)=
    bounded_generation_reservations n (generation_input_map digit_allocated_view X)"
  unfolding digit_generation_reservations_def bounded_generation_reservations_def
  by (rule function_iteration_projection)
    (rule generation_reserve_input_projection[where project=digit_allocated_view
      and reserve=digit_generation_reserve and original=bounded_generation_reserve]; rule digit_generation_reserve_projection)

text \<open>
  A successful construction supplies the actual next predecessor site and
  generation. Failure leaves subsequent preparation unavailable. Complete
  optional constructor projection composes through every generated next input
  and arbitrary finite iteration. Boundary-only reservations advance the actual
  state through the same proved graft operation and have a separate projection.
\<close>

end
