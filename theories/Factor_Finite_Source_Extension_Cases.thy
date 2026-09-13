theory Factor_Finite_Source_Extension_Cases
  imports Factor_Finite_Source_Extensions Factor_Finite_Native_Controls
begin

section \<open>Each extended source is read again from its actual artifacts\<close>

definition finite_source_extension_seed :: "nat \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option\<times>local_address) option" where
  "finite_source_extension_seed i=(let empty=\<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>;
    E=finite_guard_source False in
    if i=8 then Some (finite_guard_source True,None,[0])
    else if i=9 then Some (case finite_select_roots empty [] of (F,u) \<Rightarrow> (F,u,[]))
    else if i=10 then Some (empty,None,[0])
    else if i=11 then Some (E\<lparr>finite_environment_artifacts:=finsert
      (Some [255],finite_payload_syntax [256]) (finite_environment_artifacts E)\<rparr>,None,[0])
    else map_option (\<lambda>(F,u). (F,u,[])) (finite_extend_mapped_native E (finite_nat_guard_source_model False)
      (finite_native_control_candidate i) native_guard_source_coordinate))"

definition finite_source_extension_candidate :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option finite_native_system \<Rightarrow> nat \<Rightarrow> local_address option finite_native_system" where
  "finite_source_extension_candidate E P i=(let
    d=(finite_fresh_use_map (finite_environment_uses E) None (Some []),[]);
    absent=(finite_fresh_use_map (finite_environment_uses E) None (Some [1]),[]);
    ds=sorted_list_of_fset (finite_system_definitions P);
    R=fset_of_list (zip (family_ports (length ds)) ds);
    S=finite_rename_schema (\<lambda>_. []) id id (finite_requirement_guard_schema R);
    clause=(if i=4 then finite_control_rule (Finite_Variable []) {|([],absent,Finite_Variable [])|}
      else if i=5 then finite_control_rule (Finite_Pattern_Payload [256]) {||} else S)
    in if i=0 then P
      else if i=2 then P\<lparr>finite_system_interfaces:=fimage (\<lambda>(e,p). (e,Finite_Pattern_Payload [254]))
        (finite_system_interfaces P)\<rparr>
      else if i=3 then P\<lparr>finite_system_clauses:={||}\<rparr>
      else finite_add_view_definition P d (Finite_Variable []) {|([],clause)|})"

definition finite_source_extension_case where
  "finite_source_extension_case E pu pr P i=(let Q=finite_source_extension_candidate E P i in
    (i,Q,finite_system_formed Q,finite_source_extension_context E pu pr Q,
      map_option (\<lambda>(N,F,u).
        (N,fimage (\<lambda>d. (d,finite_program_coordinates E (finite_system_definitions N) (finite_system_definitions Q) id d))
          (finite_system_definitions Q),F,u,finite_native_package_readings F pu pr,finite_native_package_readings F u []))
        (finite_extend_source_native E pu pr Q)))"

definition finite_source_extension_cases where
  "finite_source_extension_cases i=map_option (\<lambda>(E,pu,pr). (let source=finite_native_source E pu pr;
      P=(case source of None \<Rightarrow> \<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr> | Some N \<Rightarrow> N)
    in (E,pu,pr,source,map (finite_source_extension_case E pu pr P) [0,1,2,3,4,5]))) (finite_source_extension_seed i)"

lemma finite_source_extension_case_subject:
  "fst (snd (finite_source_extension_case E pu pr P i))=finite_source_extension_candidate E P i"
  by (simp add: finite_source_extension_case_def Let_def)

export_code finite_source_extension_cases checking SML

text \<open>
  The first eight sources are actual constructed packages, including empty
  added clause families, unseeded and seeded cycles, whole and anchored literal
  targets, and both complete material operands. Further sources have a different
  original clause, an empty package, no package, or an unused malformed artifact.

  Every readable source supplies its complete program directly to candidate
  construction. The six proposals retain it, add a complete conjunction, change
  interfaces, remove clauses, cite an absent callee, or add malformed syntax.
  Empty source fields remain empty: changing or removing no rows is not a
  mismatch. Unreadable sources use a displayed empty proposal and still execute
  the source check; the placeholder cannot establish a source premise.

  Each extension independently recovers its source again. Reports retain all
  proposed program fields, recovered original fields, calculated coordinate
  rows, and complete returned environments and package readings. No assumed
  program model is supplied to the source-checking extension operation.
\<close>

end
