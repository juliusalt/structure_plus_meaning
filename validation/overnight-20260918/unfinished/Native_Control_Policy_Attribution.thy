theory Native_Control_Policy_Attribution
 imports "Native_Control_Foundation_20260918_0052.Development_Policy"
begin

text \<open>Attribute the previous optional result using the constructor and evaluator's
  actual readiness predicates. Complete demands use every definition of the read
  program on the same original term; readiness is checked, not assumed.\<close>

value [code] "(let e=Isabelle_Code_Equation (Isabelle_Bound 0) in
  map_option (\<lambda>(d,F,u). map_option (\<lambda>P.
      (finite_system_formed P,
       finite_admission_requirements_supported [Existing_Admission d] P,
       finite_construct_source_requirements F u [] [Existing_Admission d] = None))
    (finite_native_source F u [])) (isabelle_acceptance_source [e]))"

value [code] "(let e=Isabelle_Code_Equation (Isabelle_Bound 0) in
  map_option (\<lambda>(d,F,u). map_option (\<lambda>P.
    (let D=fset_of_list [(d,isabelle_entity_data e)];
         full=fimage (\<lambda>c. (c,isabelle_entity_data e)) (finite_system_definitions P) in
     (finite_system_formed P,
      finite_program_head_covered P D, finite_program_demand_closed P D,
      finite_program_head_covered P full, finite_program_demand_closed P full,
      map_option (\<lambda>A. (d,isabelle_entity_data e) |\<in>| A) (finite_program_evaluation P full))))
    (finite_native_source F u [])) (development_policy_source [e]))"

value [code] "(let e=Isabelle_Code_Equation (Isabelle_Bound 0) in
  map_option (\<lambda>(d,F,u). map_option (\<lambda>P.
    (let full=fimage (\<lambda>c. (c,isabelle_entity_data e)) (finite_system_definitions P) in
      map_option (\<lambda>A. (d,isabelle_entity_data e) |\<in>| A) (finite_program_evaluation P full)))
    (finite_native_source F u [])) (development_policy_source []))"

end
