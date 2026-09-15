theory RRA_Digit_Generation_Installation
  imports RRA_Bounded_Generation_Construction RRA_Finite_Binding_Sequences
    RRA_Literal_Environment_Rows RRA_Digit_Generation_Readings RRA_Cached_Graft_References
begin

definition generation_literal_rows where
  "generation_literal_rows l p c=[
    (syntax_branch 0 [4],finite_target_artifact l),
    (syntax_branch 2 [4],finite_target_artifact p),
    (syntax_branch 3 [4],finite_target_artifact c)]"

lemma generation_literal_rows_exact:
  "fset_of_list (generation_literal_rows l p c)=finite_generation_record_literals l p c"
  by (simp add: generation_literal_rows_def finite_generation_record_literals_def)

definition generation_predecessor_binding_rows where
  "generation_predecessor_binding_rows anchors=map (\<lambda>i.
    (generation_predecessor_slot i,fst (fst (anchors!i)))) [0..<length anchors]"

definition generation_selected_frame where
  "generation_selected_frame l p c anchors=finite_generation_record_frame l p c
    (map (\<lambda>(d,R). (R,snd d)) anchors)"

definition digit_generation_installation where
  "digit_generation_installation q l p c anchors=(let u=digit_allocated_next_use q;
    R=generation_selected_frame l p c anchors; literals=generation_literal_rows l p c in
    Option.bind (digit_allocated_allocate q R) (\<lambda>frame.
      Option.bind (optional_transition_sequence (digit_source_binding_step u)
        (generation_predecessor_binding_rows anchors) frame) (\<lambda>predecessors.
        digit_allocated_graft predecessors u (finite_literal_artifact_rows R literals)
          (finite_literal_binding_rows literals))))"

definition finite_generation_installation where
  "finite_generation_installation state l p c anchors=(let u=Some [fst state];
    R=generation_selected_frame l p c anchors; literals=generation_literal_rows l p c in
    Option.bind (finite_allocation_reference state (Allocate_Artifact R)) (\<lambda>frame.
      Option.bind (optional_transition_sequence (finite_source_binding_step u)
        (generation_predecessor_binding_rows anchors) frame) (\<lambda>predecessors.
        finite_bounded_graft_reference predecessors u (finite_literal_environment R (fset_of_list literals)))))"

lemma digit_allocated_next_use_view:
  "digit_allocated_next_use q=Some [fst (digit_allocated_view q)]"
  by transfer (simp add: bounded_environment_next_use_def encoded_bounded_view_def)

theorem digit_generation_installation_projection:
  "map_option digit_allocated_view (digit_generation_installation q l p c anchors)=
    finite_generation_installation (digit_allocated_view q) l p c anchors"
  unfolding digit_generation_installation_def finite_generation_installation_def
    Let_def digit_allocated_next_use_view
proof (rule optional_bind_projection)
  show "map_option digit_allocated_view (digit_allocated_allocate q (generation_selected_frame l p c anchors))=
    finite_allocation_reference (digit_allocated_view q) (Allocate_Artifact (generation_selected_frame l p c anchors))"
    using digit_allocation_typed_exact[of q "Allocate_Artifact (generation_selected_frame l p c anchors)"]
    by (simp only: digit_allocated_update.simps)
next
  fix frame
  show "map_option digit_allocated_view
      (Option.bind (optional_transition_sequence
        (digit_source_binding_step (Some [fst (digit_allocated_view q)]))
        (generation_predecessor_binding_rows anchors) frame)
        (\<lambda>predecessors. digit_allocated_graft predecessors (Some [fst (digit_allocated_view q)])
          (finite_literal_artifact_rows (generation_selected_frame l p c anchors) (generation_literal_rows l p c))
          (finite_literal_binding_rows (generation_literal_rows l p c))))=
    Option.bind (optional_transition_sequence
      (finite_source_binding_step (Some [fst (digit_allocated_view q)]))
      (generation_predecessor_binding_rows anchors) (digit_allocated_view frame))
      (\<lambda>predecessors. finite_bounded_graft_reference predecessors (Some [fst (digit_allocated_view q)])
        (finite_literal_environment (generation_selected_frame l p c anchors)
          (fset_of_list (generation_literal_rows l p c))))"
    by (rule optional_bind_projection[OF digit_source_binding_sequence_projection])
      (simp only: digit_graft_reference_exact finite_literal_rows_environment)
qed

definition digit_construct_generation where
  "digit_construct_generation q l p c rows=(if digit_generation_ready q l p c rows then
    Option.bind (keyed_option_map (digit_generation_anchor q) (map fst rows)) (\<lambda>anchors.
      map_option (\<lambda>following. (following,digit_allocated_next_use q,finite_generation_record_core l p c rows))
        (digit_generation_installation q l p c anchors)) else None)"

definition finite_construct_generation_steps where
  "finite_construct_generation_steps state l p c rows=(if finite_generation_record_ready (snd state) l p c rows then
    Option.bind (keyed_option_map (finite_anchor_artifact (snd state)) (map fst rows)) (\<lambda>anchors.
      map_option (\<lambda>following. (following,Some [fst state],finite_generation_record_core l p c rows))
        (finite_generation_installation state l p c anchors)) else None)"

theorem digit_construct_generation_steps_projection:
  "map_option (\<lambda>(following,u,G). (digit_allocated_view following,u,G))
      (digit_construct_generation q l p c rows)=
    finite_construct_generation_steps (digit_allocated_view q) l p c rows"
  by (simp add: digit_construct_generation_def finite_construct_generation_steps_def
    digit_generation_readiness_exact digit_generation_anchor_exact[abs_def] digit_allocated_next_use_view
    map_option_bind bind_map_option option.map_comp comp_def case_prod_unfold
    digit_generation_installation_projection[symmetric])

export_code digit_construct_generation finite_construct_generation_steps checking SML

text \<open>
  Actual point readers select anchors, the stored head allocates the frame,
  guarded point updates attach the predecessors and a cached graft installs
  all three literal targets. Whole optional projection preserves every state,
  result use and generation core. This operation equation alone does not yet
  establish that all stages succeed whenever original readiness holds; that
  obligation is the bridge to the bounded complete constructor.
\<close>

end
