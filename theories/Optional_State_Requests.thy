theory Optional_State_Requests
  imports Optional_Transition_Sequences
begin

definition optional_request_map where
  "optional_request_map project X=(map_option project (fst X),snd X)"

lemma optional_request_map_unavailable:
  "optional_request_map project (None,request)=(None,request)"
  by (simp only: optional_request_map_def fst_conv snd_conv option.map)

definition optional_request_follow where
  "optional_request_follow step revise X=(case Option.bind (fst X) (\<lambda>q. step q (snd X)) of
    None \<Rightarrow> (None,snd X)
  | Some (following,result) \<Rightarrow> (Some following,revise (snd X) result))"

theorem optional_request_follow_projection:
  assumes each: "\<And>q request. map_option (\<lambda>(following,result). (project following,result))
    (step q request)=original (project q) request"
  shows "optional_request_map project (optional_request_follow step revise X)=
    optional_request_follow original revise (optional_request_map project X)"
proof -
  have projected: "map_option (\<lambda>(following,result). (project following,result))
      (Option.bind (fst X) (\<lambda>q. step q (snd X)))=
    Option.bind (map_option project (fst X)) (\<lambda>q. original q (snd X))"
    by (rule optional_bind_projection[where project=project
      and following="\<lambda>q. step q (snd X)" and original_following="\<lambda>q. original q (snd X)"])
      (rule refl, rule each)
  show ?thesis
    by (cases "Option.bind (fst X) (\<lambda>q. step q (snd X))")
      (simp_all add: optional_request_map_def optional_request_follow_def projected[symmetric]
        split: prod.splits)
qed

theorem optional_request_iteration_projection:
  assumes each: "\<And>q request. map_option (\<lambda>(following,result). (project following,result))
    (step q request)=original (project q) request"
  shows "optional_request_map project ((optional_request_follow step revise ^^ n) X)=
    (optional_request_follow original revise ^^ n) (optional_request_map project X)"
  by (rule function_iteration_projection)
    (rule optional_request_follow_projection[where project=project and step=step and original=original]; rule each)

text \<open>
  The next request is derived from the actual complete returned value. A failed
  step makes the next state unavailable while preserving the failed request.
  Optional projection and arbitrary iteration follow from the existing bind
  and iteration contracts for every state and request representation.
\<close>

end
