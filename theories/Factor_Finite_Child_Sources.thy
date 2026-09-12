theory Factor_Finite_Child_Sources
  imports Factor_Finite_Inference_Sources
begin

section \<open>The new package retains all original source artifacts and bindings\<close>

definition finite_child_artifact :: "octets\<Rightarrow>finite_exact_artifact" where
  "finite_child_artifact p=finite_literal_definition_artifact p
    (map (\<lambda>n. [n]) [24,25,26,27,28,29,30])
    (map (\<lambda>(r,s,x). ([r],[s],[x]))
      [(14,24,25),(25,26,28),(25,27,5),(26,26,27),(28,28,29),(28,29,30)])
    [([30],[1])]"

definition finite_child_sources :: "octets\<Rightarrow>local_address option finite_artifact_environment" where
  "finite_child_sources p=(let E=finite_literal_sources p in
    E\<lparr>finite_environment_artifacts:=finsert (Some [2],finite_child_artifact p) (finite_environment_artifacts E),
      finite_environment_bindings:=finsert ((Some [2],[29]),Some [2]) (finite_environment_bindings E)\<rparr>)"

definition finite_child_schema :: "octets\<Rightarrow>local_address option finite_native_schema" where
  "finite_child_schema p=\<lparr>finite_schema_conclusion=Finite_Pattern_Payload p,
    finite_schema_premises={|([24],(Some [2],[1]),Finite_Pattern_Payload p)|},finite_schema_materials={||}\<rparr>"

definition finite_child_program :: "octets\<Rightarrow>local_address option finite_native_system" where
  "finite_child_program p=\<lparr>finite_system_interfaces={|((Some [2],[1]),Finite_Pattern_Payload p)|},
    finite_system_clauses={|(((Some [2],[1]),[7]),finite_child_schema p)|}\<rparr>"

section \<open>The parent discharges the actual premise to one separate assertion\<close>

definition finite_child_parent :: finite_exact_artifact where
  "finite_child_parent=finite_inference_node_artifact [7]
    (map (\<lambda>n. [n]) [8,9,10,11,12,13,14,15,16,17])
    (map (\<lambda>(r,s,x). ([r],[s],[x]))
      [(2,8,9),(9,10,12),(9,11,13),(10,10,11),(12,12,14),(12,14,15),(13,13,16),(13,16,17)])
    [([15],[24]),([17],[])]"

definition finite_child_assertion :: finite_exact_artifact where
  "finite_child_assertion=finite_enumerated_artifact [[]] [] [] []"

definition finite_child_extension :: "octets\<Rightarrow>local_address option finite_artifact_environment" where
  "finite_child_extension p=(let E=finite_child_sources p in
    E\<lparr>finite_environment_artifacts:=finsert (Some [],finite_child_parent)
        (finsert (Some [1],finite_child_assertion) (finite_environment_artifacts E)),
      finite_environment_bindings:=finsert ((Some [],[6]),Some [2])
        (finsert ((Some [],[14]),Some [2])
          (finsert ((Some [],[16]),Some [1]) (finite_environment_bindings E)))\<rparr>)"

definition finite_child_parent_interior :: "local_address list" where
  "finite_child_parent_interior=finite_literal_node_interior @ map (\<lambda>n. [n]) [8,9,10,11,12,13,15,17]"

definition finite_child_parent_slots :: "local_address list" where
  "finite_child_parent_slots=[[6],[14],[16]]"

definition finite_child_discharges ::
  "(local_address option definition_site\<times>local_address option definition_site) list" where
  "finite_child_discharges=[((Some [2],[24]),(Some [1],[]))]"

text \<open>
  The original literal package, counted background and outgoing binding remain
  unchanged at their original uses. A separate package at use Some [2] has a
  literal identity clause with one ordinary premise. The parent and assertion
  are further separate artifacts. Every complete native source and support
  check remains a proof obligation in the following source-check theory.
\<close>

end
