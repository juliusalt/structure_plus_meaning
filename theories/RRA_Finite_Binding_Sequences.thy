theory RRA_Finite_Binding_Sequences
  imports Optional_Transition_Sequences RRA_Digit_Allocation_References
begin

lemma finite_source_bindings_empty [simp]:
  "finite_add_source_bindings E u {||}=E"
  by (simp add: finite_add_source_bindings_def)

lemma finite_source_bindings_composition:
  "finite_add_source_bindings (finite_add_source_bindings E u D) u F=
    finite_add_source_bindings E u (D |\<union>| F)"
  by (simp add: finite_add_source_bindings_def fimage_funion funion_assoc)

lemma finite_binding_ready_after_disjoint:
  "k\<notin>fset (fimage fst D) \<Longrightarrow>
    finite_environment_update_ready (finite_add_source_bindings E u D) (Install_Binding u k v)=
      finite_environment_update_ready E (Install_Binding u k v)"
  by (auto simp: finite_add_source_bindings_def finite_environment_update_ready.simps
    Bex_def fimage.rep_eq split_paired_Ex intro: rev_image_eqI)

definition finite_source_binding_step where
  "finite_source_binding_step u state row=finite_allocation_reference state
    (Add_Allocated_Binding u (fst row) (snd row))"

theorem finite_source_binding_sequence:
  assumes distinct: "distinct (map fst rows)"
    and ready: "list_all (\<lambda>(k,v). finite_environment_update_ready E (Install_Binding u k v)) rows"
  shows "optional_transition_sequence (finite_source_binding_step u) rows (n,E)=
    Some (n,finite_add_source_bindings E u (fset_of_list rows))"
  using distinct ready
proof (induction rows arbitrary: E)
  case Nil then show ?case by simp
next
  case (Cons row rows)
  obtain k v where row: "row=(k,v)" by (cases row) auto
  let ?F="finite_add_source_bindings E u {|(k,v)|}"
  have head: "finite_environment_update_ready E (Install_Binding u k v)"
    and tail: "list_all (\<lambda>(j,w). finite_environment_update_ready E (Install_Binding u j w)) rows"
    using Cons.prems(2) by (simp_all add: row)
  have unique: "distinct (map fst rows)" and absent: "k\<notin>fst ` set rows"
    using Cons.prems(1) by (simp_all add: row)
  have each: "finite_environment_update_ready ?F (Install_Binding u j w)=
      finite_environment_update_ready E (Install_Binding u j w)" if "(j,w)\<in>set rows" for j w
    by (rule finite_binding_ready_after_disjoint) (use absent that in \<open>auto intro: rev_image_eqI\<close>)
  have next_ready: "list_all (\<lambda>(j,w). finite_environment_update_ready ?F (Install_Binding u j w)) rows"
  proof (simp only: list_all_iff; intro ballI)
    fix z assume in_rows: "z\<in>set rows"
    obtain j w where pair: "z=(j,w)" by (cases z) auto
    have member: "(j,w)\<in>set rows" using in_rows pair by simp
    have original: "finite_environment_update_ready E (Install_Binding u j w)"
      using bspec[OF tail[unfolded list_all_iff] in_rows]
      by (simp only: pair case_prod_conv)
    show "(case z of (j,w) \<Rightarrow> finite_environment_update_ready ?F (Install_Binding u j w))"
      by (simp only: pair case_prod_conv each[OF member]; rule original)
  qed
  have continuation: "optional_transition_sequence (finite_source_binding_step u) rows (n,?F)=
    Some (n,finite_add_source_bindings ?F u (fset_of_list rows))"
    by (rule Cons.IH[OF unique next_ready])
  have first: "finite_source_binding_step u (n,E) (k,v)=Some (n,?F)"
    by (simp only: finite_source_binding_step_def fst_conv snd_conv finite_allocation_reference_def
      case_prod_conv Let_def allocated_environment_update_at.simps head if_True
      allocated_environment_next_head.simps finite_environment_update_body.simps)
  show ?case by (simp only: row optional_transition_sequence.simps first option.case continuation
    finite_source_bindings_composition; simp)
qed

definition digit_source_binding_step where
  "digit_source_binding_step u q row=digit_allocated_add_binding q u (fst row) (snd row)"

lemma digit_source_binding_step_projection:
  "map_option digit_allocated_view (digit_source_binding_step u q row)=
    finite_source_binding_step u (digit_allocated_view q) row"
  using digit_allocation_typed_exact[of q "Add_Allocated_Binding u (fst row) (snd row)"]
  by (simp only: digit_source_binding_step_def finite_source_binding_step_def digit_allocated_update.simps)

theorem digit_source_binding_sequence_projection:
  "map_option digit_allocated_view (optional_transition_sequence (digit_source_binding_step u) rows q)=
    optional_transition_sequence (finite_source_binding_step u) rows (digit_allocated_view q)"
  by (rule optional_transition_sequence_projection) (rule digit_source_binding_step_projection)

text \<open>
  A sequence of distinct initially ready source bindings equals the complete
  original batch extension and leaves the allocation head unchanged. Every
  digit step preserves this optional sequence exactly. Repeated keys, missing
  targets and already occupied slots retain their actual rejection behavior.
\<close>

end
