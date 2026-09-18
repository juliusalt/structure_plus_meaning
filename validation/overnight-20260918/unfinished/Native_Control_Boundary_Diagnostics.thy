theory Native_Control_Boundary_Diagnostics
  imports Development_Policy
begin

text \<open>Execute the existing seed's malformed-equation subject under the present
  structural assessment, native demand membership, and compiled policy. These
  commands observe the current contracts; they add no claim of proof acceptance,
  condition satisfaction for another subject, or admission of a development choice.\<close>

value [code] "isabelle_malformed_entities ([], [Isabelle_Code_Equation (Isabelle_Bound 0)])"
value [code] "isabelle_demand_acceptance [Isabelle_Code_Equation (Isabelle_Bound 0)]
  [Isabelle_Code_Equation (Isabelle_Bound 0)]"
value [code] "isabelle_demand_acceptance [] [Isabelle_Code_Equation (Isabelle_Bound 0)]"
value [code] "(let e=Isabelle_Code_Equation (Isabelle_Bound 0) in
  case development_policy_source [e] of None \<Rightarrow> None
  | Some (d,F,u) \<Rightarrow> map_option (\<lambda>(P,A). (d,isabelle_entity_data e) |\<in>| A)
      (finite_native_program_evaluation F u [] (fset_of_list [(d,isabelle_entity_data e)])))"

end
