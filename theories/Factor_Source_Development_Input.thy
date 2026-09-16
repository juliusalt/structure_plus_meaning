theory Factor_Source_Development_Input
  imports Factor_Source_Development_Subjects
begin

definition source_development_material_input where
  "source_development_material_input (source::local_address finite_term_pattern) atoms edges counts functions=
    \<lparr>finite_material_source=source,finite_material_atoms=atoms,finite_material_edges=edges,
      finite_material_counts=counts,finite_material_functions=functions\<rparr>"

definition source_development_schema_input where
  "source_development_schema_input conclusion premises materials=
    (\<lparr>finite_schema_conclusion=conclusion,finite_schema_premises=fset_of_list premises,
      finite_schema_materials=fset_of_list materials\<rparr> ::
      (local_address,local_address,local_address option definition_site) finite_factor_schema)"

definition source_development_program_input where
  "source_development_program_input interfaces clauses=
    (\<lparr>finite_system_interfaces=fset_of_list interfaces,finite_system_clauses=fset_of_list clauses\<rparr>
      ::local_address option finite_native_system)"

definition source_development_request_input where
  "source_development_request_input E u r targets input outputs=
    \<lparr>source_development_environment=E,source_development_use=u,source_development_root=r,
      source_development_targets=targets,source_development_input=input,source_development_outputs=outputs\<rparr>"

text \<open>These constructors retain every original field. Encoding neither checks
  nor supplies source compatibility, candidate satisfaction or admission.
  Malformed mathematical subjects remain available to their actual native
  checks; malformed host encodings are a separate transport failure.\<close>

end
