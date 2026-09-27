theory Development_Given_Execution_Fixtures
  imports Development_Given_Modes Development_Given_Carried_Declarations Factor_Reader_Witness_Registrations
    Factor_Narrowed_Commitments Factor_Finite_Closed_Installation
begin

text \<open>
  The fixtures the given's execution theories share, in a theory that evaluates nothing, so that each execution
  theory imports it and none imports another: #779's calls (77 at one definition and at two, with 77's least bound
  handed in beside the given's registrations; 113 at three rows), the construction each call runs with, the calls of
  77/1 and 77/2 by number, and the kind of a diagnosis. @{text Development_Given_Modes_Execution},
  @{text Development_Given_Productions_Execution} and @{text Development_Given_Checks_Execution} evaluate them.
\<close>

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

text \<open>77/1 and 77/2 by number: the least bound and the call.\<close>

definition productions_call :: "nat \<Rightarrow> local_address option definition_site list option \<times> finite_factor_term" where
  "productions_call k = (if k = 1
    then (Some (snd (modes_fixture_install modes_fixture_one [0])), modes_77_call modes_fixture_one [0])
    else (Some (snd (modes_fixture_install modes_fixture_two [1,0])), modes_77_call modes_fixture_two [1]))"

text \<open>The kind of a diagnosis: 0 a cut at the bound, 1 a stuck state, 2 a witnessed failure, 3 a refusal, 4 an unconstructed witness.\<close>

fun modes_diagnosis_kind :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> nat" where
  "modes_diagnosis_kind (Resolution_Cut G) = 0"
| "modes_diagnosis_kind (Resolution_Stuck G) = 1"
| "modes_diagnosis_kind (Resolution_Witnessed B g) = 2"
| "modes_diagnosis_kind (Resolution_Refused C) = 3"
| "modes_diagnosis_kind (Resolution_Unconstructed d S a G) = 4"

end
