theory Development_Given_Declarations_Execution
  imports Development_Given_Declarations Native_Execution_Refinements
begin

text \<open>
  The control of the given's declarations (\<open>Development_Given_Declarations\<close>), by evaluation over the given's
  rooted readers under the committed resolution, in a thin theory that no library theory imports. The artifact has
  five atoms, so its enumerations, the presentations 10 and 45 read it through, number 120.

  500 reads every target leaf of a term through 45, whose output there nothing else holds: the declared producer
  45 is committed, 10 inside it, and 10's material socket keeps one enumeration; the call is resolved. At 10 itself,
  called with an output, a presentation that is not the canonical one (the atoms listed in reverse) is resolved,
  and a list missing one atom is refuted: no presentation is lost to the commitment and a refusal is a refutation.

  The given's readers hold no call whose derivation reaches 6's output at a consumer the form of the commitments
  fits with a free output: wherever 49 reads 6's output, the clause's head holds it too, so a ground call fixes it.
\<close>

definition given_control_artifact :: finite_exact_artifact where
  "given_control_artifact = \<lparr>finite_structure = \<lparr>finite_carrier = {|[1],[2],[3],[4],[5]|}, finite_incidence = {||}\<rparr>,
    finite_data = \<lparr>finite_bag = {#}, finite_bindings = {||}\<rparr>\<rparr>"

definition given_control_rows :: "local_address list \<Rightarrow> finite_factor_term" where
  "given_control_rows A = Finite_Pair (finite_data_list (map Finite_Payload A))
    (Finite_Pair (finite_data_list []) (Finite_Pair (finite_data_list []) (finite_data_list [])))"

abbreviation given_control_resolution :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "given_control_resolution d t \<equiv> finite_resolution_verdict (finite_committed_resolution no_witness_construction
    (finite_declared_commitment given_declarations) finite_rooted_given_readers d t 40)"

lemma given_declarations_control:
  "given_control_resolution 500 (Finite_Target (Finite_Whole given_control_artifact)) = Some True \<and>
   given_control_resolution 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[5],[4],[3],[2],[1]])) = Some True \<and>
   given_control_resolution 10 (Finite_Pair (Finite_Target (Finite_Whole given_control_artifact))
    (given_control_rows [[1],[2],[3],[4]])) = Some False"
  by eval

end
