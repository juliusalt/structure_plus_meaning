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

section \<open>55's pair clause at depth 1 to 3 (#896's fixture)\<close>

text \<open>
  A pattern quoted in an environment (@{const finite_pattern_syntax} at the binder coordinates of \<open>{x0,x1}\<close>, at use
  @{term None}) and a call of 55 at its root, as #827's: the scope x0,x1, x0 bound to [7] and x1 to [8], an instance,
  the used variables x1,x0, the interior (every position of the quoted pattern) and no external slot. At depth 1 the
  pattern is (x0,x1), at depth 2 ((x0,x1),x0), at depth 3 (((x0,x1),x0),x1). The instance: 0 the true one, 1 its last
  leaf changed, 2 its first leaf changed ([7] and [8] exchanged). #896's and correction (16)'s calls.
\<close>

definition c55_binder :: "nat \<Rightarrow> local_address" where
  "c55_binder = finite_binder_coordinates {|0,1|}"

definition c55_payloads :: "local_address list \<Rightarrow> finite_factor_term" where
  "c55_payloads A = finite_data_list (map Finite_Payload A)"

definition c55_interior :: "nat \<Rightarrow> local_address list" where
  "c55_interior k = (if k = 1 then [[3],[1],[2],[],[0]] else [[3],[2,3],[1],[2],[2,0],[],[2,2],[0],[2,1]])"

definition c896_pattern :: "nat \<Rightarrow> nat finite_term_pattern" where
  "c896_pattern k = (if k = 1 then Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)
    else if k = 2 then Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 0)
    else Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Variable 0)) (Finite_Variable 1))"

fun c896_fill :: "(nat \<Rightarrow> finite_factor_term) \<Rightarrow> nat finite_term_pattern \<Rightarrow> finite_factor_term" where
  "c896_fill f (Finite_Variable a) = f a"
| "c896_fill f (Finite_Pattern_Pair p q) = Finite_Pair (c896_fill f p) (c896_fill f q)"
| "c896_fill f (Finite_Pattern_Target t) = Finite_Target t"
| "c896_fill f (Finite_Pattern_Payload v) = Finite_Payload v"

fun c896_flip_first :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "c896_flip_first (Finite_Pair a b) = Finite_Pair (c896_flip_first a) b"
| "c896_flip_first (Finite_Payload v) = Finite_Payload (if v = [7] then [8] else [7])"
| "c896_flip_first (Finite_Target t) = Finite_Target t"

fun c896_flip_last :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "c896_flip_last (Finite_Pair a b) = Finite_Pair a (c896_flip_last b)"
| "c896_flip_last (Finite_Payload v) = Finite_Payload (if v = [7] then [8] else [7])"
| "c896_flip_last (Finite_Target t) = Finite_Target t"

definition c896_interior :: "nat \<Rightarrow> local_address list" where
  "c896_interior k = (if k \<le> 2 then c55_interior k
    else [[3],[2,3],[1],[2],[2,0],[],[2,2],[0],[2,1],[2,2,3],[2,2,2],[2,2,0],[2,2,1]])"

definition c896_environment :: "nat \<Rightarrow> local_address option finite_artifact_environment" where
  "c896_environment k = finite_enumerated_environment [(None,finite_pattern_syntax c55_binder (c896_pattern k))] []"

text \<open>55's call at depth k with instance t and used variables ws, stated once; #896's and #827's calls its instances.\<close>

definition c55_call :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> nat list \<Rightarrow> finite_factor_term" where
  "c55_call k t ws = Finite_Pair (Finite_Pair (finite_environment_value (c896_environment k)) (finite_use_data None))
    (Finite_Pair (Finite_Payload [])
      (Finite_Pair (Finite_Pair (c55_payloads [c55_binder 0,c55_binder 1])
          (finite_data_list [Finite_Pair (Finite_Payload (c55_binder 0)) (Finite_Payload [7]),
            Finite_Pair (Finite_Payload (c55_binder 1)) (Finite_Payload [8])]))
        (Finite_Pair t (Finite_Pair (c55_payloads (map c55_binder ws))
          (Finite_Pair (c55_payloads (c896_interior k)) (c55_payloads []))))))"

definition c896_term :: "nat \<Rightarrow> nat \<Rightarrow> finite_factor_term" where
  "c896_term k v = (let i = c896_fill (\<lambda>a. Finite_Payload (if a = 0 then [7] else [8])) (c896_pattern k);
     t = (if v = 1 then c896_flip_last i else if v = 2 then c896_flip_first i else i) in c55_call k t [1,0])"

fun modes_diagnosis_kind :: "('a,'s,'d,'c) resolution_diagnosis \<Rightarrow> nat" where
  "modes_diagnosis_kind (Resolution_Cut G) = 0"
| "modes_diagnosis_kind (Resolution_Stuck G) = 1"
| "modes_diagnosis_kind (Resolution_Witnessed B g) = 2"
| "modes_diagnosis_kind (Resolution_Refused C) = 3"
| "modes_diagnosis_kind (Resolution_Unconstructed d S a G) = 4"

end
