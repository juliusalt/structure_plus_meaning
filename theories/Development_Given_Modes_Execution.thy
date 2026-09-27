theory Development_Given_Modes_Execution
  imports Development_Given_Execution_Fixtures Native_Execution_Refinements
begin

text \<open>
  The given's modes at #779's calls (O4 of correction (12) of "Committed choice, for refusals", DECISIONS.md, task
  495's entry), in a thin theory no library theory imports: 77 at one definition (77/1) and at two (77/2), with 77's
  least bound handed in beside the given's registrations, and 113 at three rows (113/7) with no construction, over the
  given's rooted readers and the given's record under the narrowed commitment, as
  @{text Development_Given_Declarations_Execution} calls it. Each call at the moded selection with
  @{const given_modes} and at R5's default (@{const finite_committed_select}): the verdict, the diagnoses' kinds and
  the states the committed search visits (@{const committed_resolution_states}).
\<close>

declare [[code abort: finite_object_of union_class]]

section \<open>The two selections\<close>

abbreviation modes_commitment :: "nat \<Rightarrow> (nat,nat,nat,nat) resolution_commitment" where
  "modes_commitment n \<equiv> finite_narrowed_commitment finite_rooted_given_readers n given_declarations {||}"

definition modes_selection :: "bool \<Rightarrow> (nat,nat,nat,nat) finite_witness_construction \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection" where
  "modes_selection moded \<kappa> n = (if moded then finite_moded_select \<kappa> (modes_commitment n)
      (resolution_declarations.truncate given_declarations) given_modes finite_rooted_given_readers
    else finite_committed_select \<kappa> (modes_commitment n) finite_rooted_given_readers)"


definition modes_run :: "bool \<Rightarrow> local_address option definition_site list option \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow>
    nat \<Rightarrow> bool option \<times> nat list \<times> nat" where
  "modes_run moded bound d t n = (let \<kappa> = modes_construction bound n; sel = modes_selection moded \<kappa> n;
    R = finite_committed_search_by sel \<kappa> (modes_commitment n) finite_rooted_given_readers n None {||}
      (finite_initial_state d t) in
    (finite_resolution_verdict (finite_outcome_result finite_rooted_given_readers d t R),
     sorted_list_of_fset (fimage modes_diagnosis_kind (resolution_diagnoses R)),
     committed_resolution_states sel \<kappa> (modes_commitment n) finite_rooted_given_readers d t n))"

definition modes_77_1 :: "bool \<Rightarrow> nat \<Rightarrow> bool option \<times> nat list \<times> nat" where
  "modes_77_1 moded n = modes_run moded (Some (snd (modes_fixture_install modes_fixture_one [0]))) 77
    (modes_77_call modes_fixture_one [0]) n"

definition modes_77_2 :: "bool \<Rightarrow> nat \<Rightarrow> bool option \<times> nat list \<times> nat" where
  "modes_77_2 moded n = modes_run moded (Some (snd (modes_fixture_install modes_fixture_two [1,0]))) 77
    (modes_77_call modes_fixture_two [1]) n"

definition modes_113_7 :: "bool \<Rightarrow> nat \<Rightarrow> bool option \<times> nat list \<times> nat" where
  "modes_113_7 moded n = modes_run moded None 113 (modes_113_call 3) n"

text \<open>
  Each row: the verdict (resolved: @{term "Some True"}; unresolved: @{term None}), the kinds of the diagnoses the
  search left (0 a cut at the bound, 2 a witnessed failure) and the states it visited. 113/7 at 230, R3's least bound,
  is resolved at both selections, in 413 states at the moded selection against 514 at R5's default: 5 at the whole
  view binds 6.1/1's output in the bag checks. 77/1 and 77/2 are unresolved at both: the order alone does not resolve
  77 (correction (12), "The prediction, checked"), the next costs being the production at 37.0/2 (correction (13))
  and 11's premise-only target (RD1). At 200 the moded search visits more states at 77/1 (614 against 280): past
  5's binding at 37.0/1 it reaches 12's committed sub-search, whose least presentation is (13)'s cost.
\<close>

lemma given_modes_controls:
  "modes_113_7 True 230 = (Some True, [], 413) \<and> modes_113_7 False 230 = (Some True, [0], 514) \<and>
   modes_77_1 True 200 = (None, [0,2], 614) \<and> modes_77_1 False 200 = (None, [0,2], 280) \<and>
   modes_77_2 True 200 = (None, [0], 201) \<and>
   modes_77_2 True 300 = (None, [0,2], 326)"
  by eval

end
