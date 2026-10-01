theory Factor_Extension_Registration_Controls
  imports Factor_Extension_Registrations Development_Given_Execution_Fixtures
begin

text \<open>
  AX2b's control (task 934), imported by no theory, one lemma by one evaluation. A small program is installed
  (@{const modes_fixture_install}): definition 0 a fact, 1 calling 0, 2 calling 1 and 0. The bound's registration
  (@{const extension_bound_registration}), its value its family's collection
  (@{text extension_bound_registration_value}), is collected at 960's clause bindings through the given's readers,
  its environment the installed environment and its roots one definition. What the evaluation shows is the state of
  W2's queries over readers with material observations. The base query (the roots selected by 5) answers the one
  root. The step query (82 at the environment) is not answered: 82's derivation holds material goals at 10, which
  W2's query search, run with no witness construction, leaves open, as R4 leaves the ground edge call open. So the
  collection gives nothing: the bound stays unresolved, never refuted, until W2's queries run with the given's
  construction.
\<close>

definition extension_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "extension_control_program = \<lparr>finite_system_interfaces={|(0,Finite_Variable 0),(1,Finite_Variable 0),(2,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),modes_fixture_fact),
      ((1,0),\<lparr>finite_schema_conclusion=Finite_Variable 0,
        finite_schema_premises={|(0,(0,Finite_Variable 0))|}, finite_schema_materials={||}\<rparr>),
      ((2,0),\<lparr>finite_schema_conclusion=Finite_Variable 0,
        finite_schema_premises={|(0,(1,Finite_Variable 0)),(1,(0,Finite_Variable 0))|}, finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition extension_control_bindings :: "nat \<Rightarrow> (nat\<times>finite_factor_term) fset" where
  "extension_control_bindings root = (case modes_fixture_install extension_control_program [0,1,2] of (E,rs) \<Rightarrow>
    {|(0,finite_environment_value E),(2,finite_data_list [finite_site_data (rs!root)])|})"

definition extension_control_edge :: finite_factor_term where
  "extension_control_edge = (case modes_fixture_install extension_control_program [0,1,2] of (E,rs) \<Rightarrow>
    Finite_Pair (finite_environment_value E) (Finite_Pair (finite_site_data (rs!1)) (finite_site_data (rs!0))))"

lemma extension_registration_controls:
  "let n=80 in
    map_option length (finite_query_answers finite_given_readers n (witness_selection_query (2::nat) (Finite_Variable 0) 0)
      (extension_control_bindings 2) [])=Some 1 \<and>
    finite_resolution_unresolved (finite_program_resolution no_witness_construction finite_given_readers 82
      extension_control_edge n) \<and>
    finite_family_collected finite_given_readers n (closure_witness_family 0 2) (extension_control_bindings 2)=None \<and>
    finite_family_collected finite_given_readers n (closure_witness_family 0 2) (extension_control_bindings 0)=None"
  by eval

end
