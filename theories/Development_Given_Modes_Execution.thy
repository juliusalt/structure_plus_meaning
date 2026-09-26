theory Development_Given_Modes_Execution
  imports Development_Given_Modes Development_Given_Carried_Declarations Factor_Reader_Witness_Registrations
    Factor_Narrowed_Commitments Factor_Finite_Closed_Installation Native_Execution_Refinements
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

section \<open>#779's fixtures\<close>

definition modes_fixture_artifact :: "nat \<Rightarrow> finite_exact_artifact" where
  "modes_fixture_artifact k = \<lparr>finite_structure = \<lparr>finite_carrier = fset_of_list (map (\<lambda>i. [i]) [1..<Suc k]),
    finite_incidence = {||}\<rparr>, finite_data = \<lparr>finite_bag = {#}, finite_bindings = {||}\<rparr>\<rparr>"

definition modes_fixture_environment :: "nat \<Rightarrow> nat \<Rightarrow> local_address option finite_artifact_environment" where
  "modes_fixture_environment m k = \<lparr>finite_environment_artifacts =
      fset_of_list (map (\<lambda>j. (Some [j], modes_fixture_artifact k)) [1..<Suc m]),
    finite_environment_bindings = {||}\<rparr>"

definition modes_fixture_fact :: "(nat,nat,nat) finite_factor_schema" where
  "modes_fixture_fact = \<lparr>finite_schema_conclusion=Finite_Pattern_Payload [], finite_schema_premises={||},
    finite_schema_materials={||}\<rparr>"

definition modes_fixture_one :: "(nat,nat,nat,nat) finite_schema_system" where
  "modes_fixture_one = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),modes_fixture_fact)|}\<rparr>"

definition modes_fixture_two :: "(nat,nat,nat,nat) finite_schema_system" where
  "modes_fixture_two = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),modes_fixture_fact),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Variable 0,
        finite_schema_premises={|(0,(0,Finite_Variable 0))|}, finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition modes_fixture_install :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat list \<Rightarrow>
    local_address option finite_artifact_environment \<times> local_address option definition_site list" where
  "modes_fixture_install prog ds = (case finite_extend_mapped_native (fst empty_package_selection)
      empty_installation_program prog (\<lambda>_. (None,[])) of
    Some (K,v) \<Rightarrow> (K, map (finite_program_coordinates (fst empty_package_selection) {||}
      (finite_system_definitions prog) (\<lambda>_. (None,[]))) ds)
  | None \<Rightarrow> (finite_empty_environment, []))"

text \<open>77's call at an installed package and its root sites, and the sites 77's least bound holds.\<close>

definition modes_77_call :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat list \<Rightarrow> finite_factor_term" where
  "modes_77_call prog ds = (case modes_fixture_install prog ds of (E,rs) \<Rightarrow>
    Finite_Pair (finite_environment_value E) (finite_data_list (map finite_site_data rs)))"

definition modes_113_call :: "nat \<Rightarrow> finite_factor_term" where
  "modes_113_call m = Finite_Pair (finite_environment_value (modes_fixture_environment m 1))
    (finite_environment_value (modes_fixture_environment m 1))"

definition modes_construction ::
    "local_address option definition_site list option \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) finite_witness_construction" where
  "modes_construction bound n = (case bound of None \<Rightarrow> no_witness_construction
    | Some ds \<Rightarrow> (let \<kappa> = finite_collection_construction given_witness_registrations n in
        \<kappa>\<lparr>witness_value := (\<lambda>P d S B a. if d=77 \<and> a=2 then Some (finite_data_list (map finite_site_data ds))
          else witness_value \<kappa> P d S B a)\<rparr>))"

section \<open>The two selections\<close>

abbreviation modes_commitment :: "nat \<Rightarrow> (nat,nat,nat,nat) resolution_commitment" where
  "modes_commitment n \<equiv> finite_narrowed_commitment finite_rooted_given_readers n given_declarations {||}"

definition modes_selection :: "bool \<Rightarrow> (nat,nat,nat,nat) finite_witness_construction \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat,nat) resolution_state \<Rightarrow> (nat,nat,nat,nat) resolution_selection" where
  "modes_selection moded \<kappa> n = (if moded then finite_moded_select \<kappa> (modes_commitment n)
      (resolution_declarations.truncate given_declarations) given_modes finite_rooted_given_readers
    else finite_committed_select \<kappa> (modes_commitment n) finite_rooted_given_readers)"

fun modes_diagnosis_kind :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> nat" where
  "modes_diagnosis_kind (Resolution_Cut G) = 0"
| "modes_diagnosis_kind (Resolution_Stuck G) = 1"
| "modes_diagnosis_kind (Resolution_Witnessed B g) = 2"
| "modes_diagnosis_kind (Resolution_Refused C) = 3"
| "modes_diagnosis_kind (Resolution_Unconstructed d S a G) = 4"

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
  is resolved at both selections, in 493 states at the moded selection against 649 at R5's default: 5 at the whole
  view binds 6.1/1's output in the bag checks. 77/1 and 77/2 are unresolved at both: the order alone does not resolve
  77 (correction (12), "The prediction, checked"), the next costs being the production at 37.0/2 (correction (13))
  and 11's premise-only target (RD1). At 200 the moded search visits more states at 77/1 (614 against 295): past
  5's binding at 37.0/1 it reaches 12's committed sub-search, whose least presentation is (13)'s cost.
\<close>

lemma given_modes_controls:
  "modes_113_7 True 230 = (Some True, [], 493) \<and> modes_113_7 False 230 = (Some True, [0], 649) \<and>
   modes_77_1 True 200 = (None, [0,2], 614) \<and> modes_77_1 False 200 = (None, [0,2], 295) \<and>
   modes_77_2 True 200 = (None, [0], 201) \<and> modes_77_2 False 200 = (None, [0], 201) \<and>
   modes_77_2 True 300 = (None, [0,2], 326)"
  by eval

end
