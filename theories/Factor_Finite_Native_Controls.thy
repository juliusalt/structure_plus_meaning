theory Factor_Finite_Native_Controls
  imports Factor_Finite_Guard_Source_Extensions Factor_Finite_Native_Observations Factor_Finite_System_Unions
    Factor_Finite_Requirement_Installation
begin

section \<open>Complete construction subjects exercise empty families, cycles and every schema field\<close>

definition finite_control_rule :: "'a finite_term_pattern\<Rightarrow>('s\<times>'d\<times>'a finite_term_pattern) fset\<Rightarrow>
    ('a,'s,'d) finite_factor_schema" where
  "finite_control_rule p C=\<lparr>finite_schema_conclusion=p,finite_schema_premises=C,finite_schema_materials={||}\<rparr>"

definition finite_control_material :: "bool\<Rightarrow>(nat,nat,nat) finite_factor_schema" where
  "finite_control_material good=\<lparr>finite_schema_conclusion=Finite_Variable 0,finite_schema_premises={||},
    finite_schema_materials={|(0,\<lparr>finite_material_source=Finite_Pattern_Target (Finite_Whole finite_empty_artifact),
      finite_material_atoms=Finite_Pattern_Payload (if good then [] else [1]),
      finite_material_edges=Finite_Pattern_Payload [],finite_material_counts=Finite_Pattern_Payload [],
      finite_material_functions=Finite_Pattern_Payload []\<rparr>)|}\<rparr>"

definition finite_native_control_group :: "nat\<Rightarrow>(nat,nat,nat,nat) finite_schema_system" where
  "finite_native_control_group i=(let
      empty=\<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr>;
      one=\<lparr>finite_system_interfaces={|(1,Finite_Variable 0)|},finite_system_clauses={||}\<rparr>;
      peer=\<lparr>finite_system_interfaces={|(1,Finite_Variable 0),(2,Finite_Variable 0)|},
        finite_system_clauses={|((1,0),finite_requirement_guard_schema {|(0,2)|}),
          ((2,0),finite_requirement_guard_schema {|(0,1)|})|}\<rparr>;
      literal=finite_payload_syntax [42]
    in if i=0 then empty else if i=1 then one else
      if i=2 then one\<lparr>finite_system_clauses:={|((1,0),finite_requirement_guard_schema {|(0,1)|})|}\<rparr> else
      if i=3 then peer else
      if i=4 then peer\<lparr>finite_system_clauses:=finsert ((2,1),finite_control_rule (Finite_Pattern_Payload []) {||})
        (finite_system_clauses peer)\<rparr> else
      if i=5 then one\<lparr>finite_system_clauses:=
        {|((1,0),finite_control_rule (Finite_Pattern_Target (Finite_Whole literal)) {||}),
          ((1,1),finite_control_rule (Finite_Pattern_Target (Finite_Anchor literal [])) {||})|}\<rparr> else
      if i=6 \<or> i=7 then one\<lparr>finite_system_clauses:={|((1,0),finite_control_material (i=6))|}\<rparr> else
      if i=11 then one\<lparr>finite_system_clauses:={|((1,0),finite_requirement_guard_schema {|(0,2)|})|}\<rparr> else
      if i=12 then one\<lparr>finite_system_clauses:=
        {|((1,0),finite_control_rule (Finite_Variable 0) {||}),((1,0),finite_control_rule (Finite_Pattern_Payload []) {||})|}\<rparr> else
      one\<lparr>finite_system_clauses:=
        {|((1,0),finite_control_rule (Finite_Pattern_Payload []) {||}),((1,1),finite_control_rule (Finite_Pattern_Payload [256]) {||})|}\<rparr>)"

definition finite_native_control_candidate where
  "finite_native_control_candidate i=(let P=finite_nat_guard_source_model False in
    if i=8 then P\<lparr>finite_system_interfaces:={|(0,Finite_Pattern_Payload [])|}\<rparr> else
    if i=9 then finite_nat_guard_source_model True else
    if i=10 then \<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr> else
    finite_system_union P (finite_native_control_group i))"

definition finite_native_control_report where
  "finite_native_control_report i=(let E=finite_guard_source False; P=finite_nat_guard_source_model False;
    Q=finite_native_control_candidate i; h=finite_program_coordinates E (finite_system_definitions P)
      (finite_system_definitions Q) native_guard_source_coordinate in
    (Q,finite_system_formed Q,finite_system_agrees_on P Q (finite_system_definitions P),
      map_option (\<lambda>(F,u). (fimage (\<lambda>d. (d,h d)) (finite_system_definitions Q),
        finite_native_package_observation F None [0] (finite_guard_source_program False) (finite_guard_source_program True) u))
        (finite_extend_mapped_native E P Q native_guard_source_coordinate)))"

lemma finite_native_control_subject:
  "fst (finite_native_control_report i)=finite_native_control_candidate i"
  by (simp add: finite_native_control_report_def Let_def)

theorem finite_native_control_profile:
  assumes formed: "finite_system_formed (finite_native_control_candidate i)"
    and agreement: "finite_system_agrees_on (finite_nat_guard_source_model False) (finite_native_control_candidate i) {|0|}"
  shows "finite_mapped_native_extension (finite_guard_source False) (finite_nat_guard_source_model False)
    (finite_native_control_candidate i) None [0] (decode_finite_system (finite_guard_source_program False)) native_guard_source_coordinate"
  by (rule finite_guard_source_extension_profile[OF formed])
    (use agreement in \<open>simp only: finite_system_agrees_on_correct; simp\<close>)

export_code finite_native_control_report checking SML

text \<open>
  Every index supplies its complete program fields. The formation and
  preservation conditions are computed from those actual fields. The source
  model has an independently proved whole-program correspondence to its
  native artifact. Valid prerequisites instantiate the same universal
  constructor contract used by the requirement cases.

  The subjects include no new definitions, an empty clause family, an
  unsupported self cycle, mutually recursive peers, a seeded peer cycle,
  whole and anchored literal targets, and complete material operands.
  Separate inputs change or omit old fields, cite an absent definition,
  repeat a clause key with different values, or contain a malformed clause.
\<close>

end
