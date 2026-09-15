theory RRA_Digit_Generation_Construction
  imports RRA_Digit_Generation_Installation
begin

context finite_bounded_generation_construction
begin

abbreviation selected_frame where "selected_frame\<equiv>generation_selected_frame l p c anchors"
abbreviation allocated_frame where "allocated_frame\<equiv>finite_add_artifact_use E (Some [n]) selected_frame"
abbreviation bound_predecessors where
  "bound_predecessors\<equiv>finite_fresh_generation_predecessor_environment E (Some [n]) l p c as v"
abbreviation literal_import where
  "literal_import\<equiv>finite_literal_environment selected_frame (finite_generation_record_literals l p c)"

lemma selected_frame_formed:
  "finite_exact_formed selected_frame"
  by (simp only: finite_exact_formed_correct generation_selected_frame_def
    finite_generation_record_frame_exact; rule bounded.installed.literals.source_formed)

lemma selected_frame_allocation:
  "finite_allocation_reference (n,E) (Allocate_Artifact selected_frame)=Some (Suc n,allocated_frame)"
proof -
  have absent: "\<not>fBex (finite_environment_artifacts E) (\<lambda>(u,R). u=Some [n])"
    using bounded.fresh by (auto simp: finite_environment_uses_def Bex_def fimage.rep_eq intro: rev_image_eqI)
  show ?thesis by (simp only: finite_allocation_reference_def case_prod_conv Let_def
    allocated_environment_update_at.simps finite_environment_update_ready.simps
    selected_frame_formed absent simp_thms if_True allocated_environment_next_head.simps
    finite_environment_update_body.simps)
qed

lemma predecessor_binding_rows_distinct:
  "distinct (map fst (generation_predecessor_binding_rows anchors))"
  using generation_predecessor_slots_injective
  by (auto simp: generation_predecessor_binding_rows_def map_map comp_def distinct_map inj_on_def inj_def)

lemma predecessor_binding_initial_ready:
  assumes index: "i<length anchors"
  shows "finite_environment_update_ready allocated_frame
    (Install_Binding (Some [n]) (generation_predecessor_slot i) (v i))"
proof -
  have source: "artifact_at (decode_finite_environment allocated_frame) (Some [n])
    (decode_finite_object selected_frame)" by simp
  have inside: "generation_predecessor_slot i\<in>rra_carrier (object_structure (decode_finite_object selected_frame))"
    using native.frame.predecessor_slots_inside[of i] index
    by (simp only: generation_selected_frame_def finite_generation_record_frame_exact
      bounded.installed.frame_same length_map)
  have chosen: "artifact_at (decode_finite_environment E) (v i) (fst (decoded_anchors!i))"
    using selected_anchors index by auto
  have present: "artifact_at (decode_finite_environment allocated_frame) (v i) (fst (decoded_anchors!i))"
    using chosen by simp
  have target: "v i\<in>environment_uses (decode_finite_environment allocated_frame)"
    using present by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  have unbound: "\<not>binds_slot (decode_finite_environment allocated_frame) (Some [n]) (generation_predecessor_slot i) w" for w
    by (simp only: decode_finite_add_artifact_use added_artifact_bindings;
      rule bounded.installed.original_unbound)
  show ?thesis using source inside target unbound
    by (simp only: finite_environment_update_ready_exact original_environment_update_ready.simps; blast)
qed

lemma predecessor_binding_rows_ready:
  "list_all (\<lambda>(k,w). finite_environment_update_ready allocated_frame (Install_Binding (Some [n]) k w))
    (generation_predecessor_binding_rows anchors)"
proof -
  have all: "\<forall>i\<in>set [0..<length anchors]. finite_environment_update_ready allocated_frame
    (Install_Binding (Some [n]) (generation_predecessor_slot i) (v i))"
    using predecessor_binding_initial_ready by auto
  show ?thesis using all by (auto simp only: generation_predecessor_binding_rows_def list_all_iff set_map image_iff case_prod_conv)
qed

lemma predecessor_binding_sequence:
  "optional_transition_sequence (finite_source_binding_step (Some [n]))
    (generation_predecessor_binding_rows anchors) (Suc n,allocated_frame)=Some (Suc n,bound_predecessors)"
  using finite_source_binding_sequence[OF predecessor_binding_rows_distinct predecessor_binding_rows_ready,
    where n="Suc n"]
  by (simp only: finite_fresh_generation_predecessor_environment_def generation_selected_frame_def
    generation_predecessor_binding_rows_def fset_of_list_map length_map)

lemma generation_literal_graft_ready:
  "finite_graft_prerequisites (prefix_use_map [Suc n] (Some [n])) bound_predecessors (Some [n]) literal_import"
proof -
  have old: "finite_environment_formed bound_predecessors"
    by (simp only: finite_environment_formed_correct finite_fresh_generation_predecessor_exact;
      rule bounded.installed.predecessor_formed)
  have imported: "finite_environment_formed literal_import"
    by (simp only: finite_environment_formed_correct decode_finite_literal_environment
      generation_selected_frame_def finite_generation_record_frame_exact finite_generation_record_literals_exact;
      rule bounded.installed.literals.literal_formed)
  have shared: "finite_shared_graft_artifact bound_predecessors (Some [n]) literal_import"
    by (auto simp: finite_shared_graft_artifact_def finite_fresh_generation_predecessor_environment_def
      finite_add_source_bindings_def finite_add_artifact_use_def finite_literal_environment_def
      generation_selected_frame_def Bex_def)
  have compatible: "finite_boundary_bindings_compatible (prefix_use_map [Suc n] (Some [n]))
    bound_predecessors (Some [n]) literal_import"
    by (simp only: finite_boundary_bindings_compatible_exact finite_fresh_generation_predecessor_exact
      decode_finite_literal_environment generation_selected_frame_def finite_generation_record_frame_exact
      finite_generation_record_literals_exact; rule bounded.installed.embedded.boundary_compatible)
  show ?thesis by (simp only: finite_graft_prerequisites_def old imported shared compatible simp_thms)
qed

lemma generation_literal_graft:
  "finite_bounded_graft_reference (Suc n,bound_predecessors) (Some [n]) literal_import=
    Some (Suc (Suc n),finite_bounded_generation_environment n E l p c as v)"
  by (simp only: finite_bounded_graft_reference_def fst_conv snd_conv Let_def
    generation_literal_graft_ready[unfolded generation_selected_frame_def] if_True finite_bounded_generation_environment_def
    finite_embedded_generation_record_environment_def generation_selected_frame_def)

theorem complete_generation_installation:
  "finite_generation_installation (n,E) l p c anchors=
    Some (Suc (Suc n),finite_bounded_generation_environment n E l p c as v)"
  by (simp add: finite_generation_installation_def generation_literal_rows_exact
    selected_frame_allocation predecessor_binding_sequence generation_literal_graft)

end

theorem finite_generation_steps_bounded:
  assumes bound: "finite_environment_head_bound n E"
  shows "finite_construct_generation_steps (n,E) l p c rows=finite_construct_bounded_generation (n,E) l p c rows"
proof (cases "finite_generation_record_ready E l p c rows")
  case False then show ?thesis by (simp add: finite_construct_generation_steps_def finite_construct_bounded_generation_def)
next
  case True
  obtain anchors where queried: "keyed_option_map (finite_anchor_artifact E) (map fst rows)=Some anchors"
    using finite_generation_record_anchors_available[OF True] by (cases "keyed_option_map (finite_anchor_artifact E) (map fst rows)") auto
  interpret construction: finite_bounded_generation_construction E l p c rows anchors n
    by (unfold_locales) (rule True, rule queried, rule bound)
  show ?thesis by (simp add: finite_construct_generation_steps_def finite_construct_bounded_generation_def
    True bound queried construction.complete_generation_installation finite_bounded_generation_body_def)
qed

theorem digit_construct_generation_projection:
  "map_option (\<lambda>(following,u,G). (digit_allocated_view following,u,G)) (digit_construct_generation q l p c rows)=
    finite_construct_bounded_generation (digit_allocated_view q) l p c rows"
proof -
  have bound: "finite_environment_head_bound (fst (digit_allocated_view q)) (snd (digit_allocated_view q))"
    by (rule digit_graft_view_bound)
  show ?thesis using finite_generation_steps_bounded[OF bound, where l=l and p=p and c=c and rows=rows]
    by (simp only: digit_construct_generation_steps_projection prod.collapse)
qed

text \<open>
  Original readiness and the actual bound discharge every allocation, binding
  and graft guard through the general frame and literal contracts. The entire
  optional digit result therefore equals the independently established bounded
  generation constructor, including refusal, all old material, exact original
  predecessor references and the updated allocation head.
\<close>

end
