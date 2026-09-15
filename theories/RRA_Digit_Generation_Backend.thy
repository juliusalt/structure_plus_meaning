theory RRA_Digit_Generation_Backend
  imports RRA_Generation_Record_Backends RRA_Digit_Generation_Construction
begin

lemma digit_generation_backend_result:
  assumes result: "digit_construct_generation q l p c rows=Some (following,u,G)"
  shows "finite_construct_bounded_generation
      (fst (digit_allocated_view q),snd (digit_allocated_view q)) l p c rows=
    Some ((fst (digit_allocated_view following),snd (digit_allocated_view following)),u,G)"
  using digit_construct_generation_projection[of q l p c rows]
  by (simp add: result)

lemma digit_construct_generation_domain:
  "digit_construct_generation q l p c rows\<noteq>None \<longleftrightarrow>
    finite_generation_record_ready (snd (digit_allocated_view q)) l p c rows"
proof -
  have available: "finite_construct_bounded_generation (digit_allocated_view q) l p c rows\<noteq>None \<longleftrightarrow>
    finite_generation_record_ready (snd (digit_allocated_view q)) l p c rows"
    using finite_construct_bounded_generation_domain[of
      "fst (digit_allocated_view q)" "snd (digit_allocated_view q)" l p c rows]
    by (simp only: prod.collapse digit_graft_view_bound simp_thms)
  show ?thesis using available
    by (simp only: digit_construct_generation_projection[symmetric] map_option_is_None)
qed

interpretation digit_generation_backend: generation_record_backend
    "\<lambda>q. snd (digit_allocated_view q)" digit_construct_generation
proof (unfold_locales)
  show "digit_construct_generation q l p c rows\<noteq>None \<longleftrightarrow>
    finite_generation_record_ready (snd (digit_allocated_view q)) l p c rows" for q l p c rows
    by (rule digit_construct_generation_domain)
  show "digit_construct_generation q l p c rows=Some (following,u,G) \<Longrightarrow>
    G=finite_generation_record_core l p c rows" for q l p c rows following u G
    by (rule finite_construct_bounded_generation_correct(3)[OF digit_generation_backend_result])
  show "digit_construct_generation q l p c rows=Some (following,u,G) \<Longrightarrow>
    finite_check_generation G (snd (digit_allocated_view following)) u []" for q l p c rows following u G
    by (rule finite_construct_bounded_generation_correct(7)[OF digit_generation_backend_result])
  show "digit_construct_generation q l p c rows=Some (following,u,G) \<Longrightarrow>
    finite_environment_agrees_on (snd (digit_allocated_view q)) (snd (digit_allocated_view following))
      (finite_environment_uses (snd (digit_allocated_view q)))" for q l p c rows following u G
    by (rule finite_construct_bounded_generation_correct(6)[OF digit_generation_backend_result])
  show "digit_construct_generation q l p c rows=Some (following,u,G) \<Longrightarrow>
    finite_generation_predecessor_references (snd (digit_allocated_view following)) u [] l p c=
      fset_of_list (map fst rows)" for q l p c rows following u G
    by (rule finite_construct_bounded_generation_correct(8)[OF digit_generation_backend_result])
qed

text \<open>
  The digit constructor supplies each backend premise through its established
  complete optional projection. The closed state supplies the bound needed by
  the bounded reference. Original formation and inclusion follow from the
  generic backend contract; neither is an extra representation assumption.
\<close>

end
