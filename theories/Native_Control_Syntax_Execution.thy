theory Native_Control_Syntax_Execution
  imports Native_Control_Syntax_Candidate
begin

text \<open>This is an isolated candidate execution context. The equations below
  preserve complete constructor values for all inputs. Executing this context
  does not select the candidate under development policy or change production.\<close>

declare finite_syntax_join_def[code del]

lemma finite_syntax_join_enumerated_code [code]:
  "finite_syntax_join f g U I R S=finite_syntax_join_enumerated f g U I R S"
  by (rule finite_syntax_join_enumerated_exact[symmetric])

declare finite_attach_structure_def[code del]

lemma finite_attach_structure_enumerated_code [code]:
  "finite_attach_structure R H=\<lparr>finite_structure=\<lparr>
    finite_carrier=enumerated_union (finite_carrier (finite_structure R)) (finite_carrier H),
    finite_incidence=enumerated_union (finite_incidence (finite_structure R)) (finite_incidence H)\<rparr>,
    finite_data=finite_data R\<rparr>"
  by (simp only: enumerated_union_exact finite_attach_structure_def)

export_code profile_terms profile_input_formed finite_ground_program profile_program_formed
  profile_source_reading profile_agreement profile_context profile_coordinates
  profile_rename_old profile_rename_target profile_extension_ready profile_compile
  profile_install profile_select finite_ground_source profile_compile_term
  profile_pattern_term profile_compiled_forest profile_artifact_size integer_of_nat
  context_execution_membership context_execution_membership_summary
  in Eval module_name Native_Control_Syntax_Execution file_prefix "native_control_syntax_execution"

end
