theory Factor_Check_Controls
  imports Factor_Resolution_Checks Development_Given_Modes_Execution
begin

text \<open>
  The check form against the committed form at a bag check (K2 of correction (14), task 495's entry): 7, the
  four-field comparison, at the largest artifact of 77/2's environment (#794's draft builds it so) with itself and
  with its fields reversed, and at a pair with one entry changed, over the given's rooted readers and the given's
  record under the narrowed commitment at the moded selection with @{const given_modes}, through the route forms'
  constants. Each row: the verdict and the states at the check form (@{const moded_check_resolution}, the search
  started at the root's own focus) and at the committed form at @{term None} (@{const moded_committed_resolution}),
  O1's count; R4's verdict beside the refuted pair.
\<close>

section \<open>The artifacts of 77/2's environment\<close>

definition check_control_artifacts :: "finite_factor_term list" where
  "check_control_artifacts = (case finite_environment_value (fst (modes_fixture_install modes_fixture_two [1,0])) of
      Finite_Pair rs bs \<Rightarrow> (case finite_data_list_read rs of
        Some xs \<Rightarrow> map (\<lambda>r. case r of Finite_Pair u a \<Rightarrow> a | _ \<Rightarrow> r) xs | None \<Rightarrow> [])
    | _ \<Rightarrow> [])"

definition check_control_fields :: "finite_factor_term \<Rightarrow> finite_factor_term list list" where
  "check_control_fields t = (case t of Finite_Pair a (Finite_Pair e (Finite_Pair b f)) \<Rightarrow>
      map (\<lambda>x. case finite_data_list_read x of Some ys \<Rightarrow> ys | None \<Rightarrow> []) [a,e,b,f]
    | _ \<Rightarrow> [])"

definition check_control_rebuilt :: "finite_factor_term list list \<Rightarrow> finite_factor_term" where
  "check_control_rebuilt fs = (case map finite_data_list fs of [a,e,b,f] \<Rightarrow>
      Finite_Pair a (Finite_Pair e (Finite_Pair b f)) | _ \<Rightarrow> Finite_Payload [])"

definition check_control_sized :: "nat list \<Rightarrow> finite_factor_term" where
  "check_control_sized ns = (case filter (\<lambda>a. map length (check_control_fields a) = ns) check_control_artifacts of
      a # as \<Rightarrow> a | [] \<Rightarrow> Finite_Payload [])"

definition check_control_reversed :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "check_control_reversed t = check_control_rebuilt (map rev (check_control_fields t))"

definition check_control_changed :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "check_control_changed t = check_control_rebuilt (case check_control_fields t of
      (x # xs) # fs \<Rightarrow> (Finite_Payload [255,255] # xs) # fs | fs \<Rightarrow> fs)"

section \<open>The two forms\<close>

definition check_control_row :: "finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option \<times> nat \<times> bool option \<times> nat" where
  "check_control_row t n = (let \<kappa> = no_witness_construction; P = finite_rooted_given_readers;
      K = finite_narrowed_commitment P n given_declarations {||};
      Dm = resolution_declarations.truncate given_declarations;
      sel = finite_moded_select \<kappa> K Dm given_modes P in
    (finite_resolution_verdict (moded_check_resolution \<kappa> P n given_declarations {||} Dm given_modes 7 t n),
     committed_search_states sel \<kappa> K P n (Some []) {||} (finite_initial_state 7 t),
     finite_resolution_verdict (moded_committed_resolution \<kappa> P n given_declarations {||} Dm given_modes 7 t n),
     committed_resolution_states sel \<kappa> K P 7 t n))"

definition check_control_r4 :: "finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option" where
  "check_control_r4 t n = finite_resolution_verdict
    (finite_program_resolution no_witness_construction finite_rooted_given_readers 7 t n)"

section \<open>The rows\<close>

text \<open>
  The environment holds four artifacts, their fields of (1,0,0,0), (9,6,0,2), (27,23,0,1) and (18,14,0,1) entries. At
  the largest, (27,23,0,1), with itself the check form resolves in 649 states against 1,655 at the committed form at
  @{term None}: below the ground root every join keeps its first found state, so 5's dead "later" walks at 6.1/0 go
  (#794's prototype: 695 against 1,701). With its fields reversed the largest's evaluation exceeds the probe's bound
  beside the first row; at (9,6,0,2) reversed the check form resolves in 284 states against 309, each entry walked to
  its displaced position, the certificate's own size. A pair with one carrier entry changed is refuted by both forms
  in 12 states, as R4 refutes it; unresolved never refutes and never admits. The bound is 2000, never reached.
\<close>

lemma check_controls:
  "check_control_row (Finite_Pair (check_control_sized [27,23,0,1]) (check_control_sized [27,23,0,1])) 2000 =
      (Some True, 649, Some True, 1655) \<and>
    check_control_row (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_reversed (check_control_sized [9,6,0,2]))) 2000 = (Some True, 284, Some True, 309) \<and>
    check_control_row (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_changed (check_control_sized [9,6,0,2]))) 2000 = (Some False, 12, Some False, 12) \<and>
    check_control_r4 (Finite_Pair (check_control_sized [9,6,0,2])
      (check_control_changed (check_control_sized [9,6,0,2]))) 2000 = Some False"
  by eval

end
