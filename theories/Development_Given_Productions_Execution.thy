theory Development_Given_Productions_Execution
  imports Development_Given_Productions Development_Given_Modes_Execution Factor_Committed_Traces
    Native_Execution_Refinements
begin

text \<open>
  77/1 and 77/2 (#779's calls, with O4's fixtures and 77's least bound handed in beside
  @{const given_witness_registrations}) over the given's rooted readers, under the narrowed commitment of the given's
  record (@{const given_declarations}) and of the record declaring 12's input production at 37.0/2
  (@{const given_input_declarations}), with the frame of the producing socket (@{const lookup_frames}), at the moded
  selection with @{const given_modes} and at R5's default (I3 of correction (13), DECISIONS.md, task 495's entry).
  Each run: the verdict, the diagnoses' kinds and the states the committed search visits. Beside them the trace of
  every goal at 12 the moded search meets: its position, the focus, and the conditions of the framed socket test at
  37.0/2 the production is met under.
\<close>

declare [[code abort: finite_object_of union_class]]

section \<open>The runs\<close>

definition productions_selection :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat,nat) finite_witness_construction \<Rightarrow> (nat,nat,nat,nat) resolution_commitment \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection" where
  "productions_selection moded D \<kappa> K = (if moded
    then finite_moded_select \<kappa> K (resolution_declarations.truncate D) given_modes finite_rooted_given_readers
    else finite_committed_select \<kappa> K finite_rooted_given_readers)"

definition productions_call :: "nat \<Rightarrow> local_address option definition_site list option \<times> finite_factor_term" where
  "productions_call k = (if k = 1
    then (Some (snd (modes_fixture_install modes_fixture_one [0])), modes_77_call modes_fixture_one [0])
    else (Some (snd (modes_fixture_install modes_fixture_two [1,0])), modes_77_call modes_fixture_two [1]))"

definition productions_search :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool option \<times> nat list" where
  "productions_search moded D \<Phi> k n = (let (bound,t) = productions_call k; \<kappa> = modes_construction bound n;
    K = finite_narrowed_commitment finite_rooted_given_readers n D \<Phi>; sel = productions_selection moded D \<kappa> K;
    R = finite_committed_search_by sel \<kappa> K finite_rooted_given_readers n None {||} (finite_initial_state 77 t) in
    (finite_resolution_verdict (finite_outcome_result finite_rooted_given_readers 77 t R),
     sorted_list_of_fset (fimage modes_diagnosis_kind (resolution_diagnoses R))))"

definition productions_states :: "bool \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
    (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "productions_states moded D \<Phi> k n = (let (bound,t) = productions_call k; \<kappa> = modes_construction bound n;
    K = finite_narrowed_commitment finite_rooted_given_readers n D \<Phi> in
    committed_resolution_states (productions_selection moded D \<kappa> K) \<kappa> K finite_rooted_given_readers 77 t n)"

section \<open>The goals at 12 and the framed socket test at 37.0/2\<close>

text \<open>
  At a goal at 12 whose position's parent is 37's node, the conditions R5f1's step reads before the production is met
  (@{const finite_socket_productions} at the frame {3} of @{const lookup_frames}): the goal committed, the socket's
  declared test (@{const finite_socket_declared_framed}), the frame found at the socket, 37's children framed
  (@{const finite_children_framed}), 37's node unshared, the socket's pair, the kept test or input and output apart;
  and for 37's premises at sockets 0 (26) and 1 (5): the original goal pending, nothing pending under it, its
  instantiated pattern ground.
\<close>

definition production_socket_probe :: "(nat,nat,nat,nat) produced_declarations \<Rightarrow> (nat,nat,nat) resolution_frames \<Rightarrow>
    (nat,nat,nat,nat) resolution_commitment \<Rightarrow> nat list option \<Rightarrow> (nat,nat,nat,nat) resolution_state \<Rightarrow>
    (nat,nat,nat,nat) resolution_goal \<Rightarrow> (nat list \<times> nat list \<times> bool list) fset" where
  "production_socket_probe D \<Phi> K F st g = (case g of Resolution_Call_Goal q r e p \<Rightarrow>
      if e = 12 then (let E = resolution_declarations.truncate D; ch = Some {|3|};
          ys = (case resolution_view_pattern view_identity p of Some (x,y) \<Rightarrow> finite_pattern_variables y | None \<Rightarrow> {||});
          nds = ffilter (\<lambda>nd. resolution_node_position nd = butlast q \<and> resolution_node_site nd = 37)
            (resolution_nodes st) in
        fimage (\<lambda>nd. (q, (case F of None \<Rightarrow> [] | Some f \<Rightarrow> 1 # f),
          [finite_goal_committing K F st g,
           finite_socket_declared_framed E \<Phi> view_identity lookup_view ch F st q ys g,
           finite_frame_at \<Phi> view_identity lookup_view (resolution_node_site nd) (resolution_node_schema nd) (last q) ch
             \<noteq> None,
           finite_children_framed {|3|} st nd (last q),
           finite_premise_only_unshared nd,
           finite_socket_pair view_identity q (resolution_node_schema nd),
           finite_socket_kept_framed E \<Phi> view_identity lookup_view ch F st q ys g,
           finite_input_output_apart lookup_view nd] @
          map (\<lambda>s'. fBex (resolution_pending st) (\<lambda>h. resolution_goal_position h = butlast q @ [s'])) [0,1] @
          map (\<lambda>s'. resolution_pending_under st (butlast q @ [s']) = {||}) [0,1] @
          map (\<lambda>s'. fBex (finite_schema_premises (resolution_node_schema nd)) (\<lambda>(s'',e',p'). s'' = s' \<and>
            finite_pattern_variables (finite_pattern_substitute (finite_node_binding nd) p') = {||})) [0,1])) nds)
        else {||}
    | Resolution_Material_Goal q r M \<Rightarrow> {||})"

text \<open>The trace of 12's production: the committed search's trace (@{const committed_trace}) at @{const production_socket_probe}.\<close>

abbreviation production_trace ::
    "((nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection) \<Rightarrow>
      (nat,nat,nat,nat) finite_witness_construction \<Rightarrow> (nat,nat,nat,nat) resolution_commitment \<Rightarrow>
      (nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat,nat) produced_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> nat \<Rightarrow> nat list option \<Rightarrow> nat list fset \<Rightarrow>
      (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat list \<times> nat list \<times> bool list) fset" where
  "production_trace sel \<kappa> K P D \<Phi> \<equiv> committed_trace (production_socket_probe D \<Phi> K) sel \<kappa> K P"

definition productions_trace :: "(nat,nat,nat,nat) produced_declarations \<Rightarrow> (nat,nat,nat) resolution_frames \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat list \<times> bool list) list" where
  "productions_trace D \<Phi> k n = (let (bound,t) = productions_call k; \<kappa> = modes_construction bound n;
    K = finite_narrowed_commitment finite_rooted_given_readers n D \<Phi> in
    sorted_list_of_fset (production_trace (productions_selection True D \<kappa> K) \<kappa> K finite_rooted_given_readers D \<Phi> n
      None {||} (finite_initial_state 77 t)))"

text \<open>
  The rows. At 200, 77/1 and 77/2 are unresolved, cut at the bound, with the same verdict and diagnoses with and
  without the production. Since correction (15)'s open siblings (OS2, task 855) the production is met at 77/1: 220
  states against 614 before, 12's committed sub-search a produced check. The trace names it: 12(x4,x3) at 2.0.1.2 is
  taken under 37 at 2.0.1 with its input ground and its output free, and every condition of the framed test the
  production reads holds there but the kept test, the socket being free: 37's children framed
  (@{const finite_children_framed}, the fourth of the list) among them, 26 at 2.0.1.0 and 5 at 2.0.1.1 having their
  goals taken, their instantiated patterns ground and goals pending under them, none holding a variable 37's binding
  gives at 12's premise or at the frame {3}. 77/2 at 200 is cut before 37 (201 states, as before). Task 815's figures
  at 400 predate the narrowed test (correction (15)'s census: 830 and 430 states, the production met).
\<close>

lemma given_productions_controls:
  "productions_search True given_input_declarations lookup_frames 1 200 = (None, [0,2]) \<and>
   productions_search True given_declarations lookup_frames 1 200 = (None, [0,2]) \<and>
   productions_states True given_input_declarations lookup_frames 1 200 = 220 \<and>
   productions_search True given_input_declarations lookup_frames 2 200 = (None, [0]) \<and>
   productions_search True given_declarations lookup_frames 2 200 = (None, [0]) \<and>
   productions_states True given_input_declarations lookup_frames 2 200 = 201 \<and>
   productions_states True given_declarations lookup_frames 2 200 = 201 \<and>
   set (productions_trace given_input_declarations lookup_frames 1 200) =
    {([2,0,1,2],[1,2,0,1],[True,True,True,True,True,True,False,True,False,False,False,False,True,True]),
     ([2,0,1,2],[1,2,0,1,2],[False,False,True,True,True,True,False,True,False,False,False,False,True,True])}"
  by eval

end
