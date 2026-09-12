theory Factor_Requirement_Source_Readings
  imports Retained_Clause_Execution
begin

section \<open>Both executed artifacts use the same complete variable frame\<close>

abbreviation finite_requirement_frame where
  "finite_requirement_frame b \<equiv> if b then finite_guard_artifact else finite_variable_artifact"

lemma finite_requirement_frame_records:
  assumes formed: "finite_object_formed (finite_requirement_frame b)"
  shows "finite_record_at (finite_requirement_frame b) [1] [[17],[18]] [[2],[6]]"
  "finite_record_at (finite_requirement_frame b) [2] [[19],[20]] [[3],[5]]"
  "finite_record_at (finite_requirement_frame b) [8] [[21],[22],[23]] [[9],[11],[14]]"
  by (simp only: finite_record_at_def formed; cases b; simp_all only: if_True if_False; code_simp)+

lemma finite_requirement_frame_families:
  assumes formed: "finite_object_formed (finite_requirement_frame b)"
  shows "finite_family_at (finite_requirement_frame b) [0] {|([16],[15])|}"
  "finite_family_at (finite_requirement_frame b) [6] {|([7],[8])|}"
  "finite_binder_scope_at (finite_requirement_frame b) [3] {|[4]|}"
  "finite_binder_scope_at (finite_requirement_frame b) [9] {|[10]|}"
  by (simp only: finite_binder_scope_at_def finite_family_at_def formed; cases b; simp_all only: if_True if_False; code_simp)+

lemma finite_requirement_frame_citations:
  assumes formed: "finite_exact_formed (finite_requirement_frame b)"
  shows "finite_citation_at (finite_requirement_frame b) [5] (Local [4]) {|[5]|}"
  "finite_citation_at (finite_requirement_frame b) [11] (Local [10]) {|[11]|}"
  "finite_citation_at (finite_requirement_frame b) [15] (Local [1]) {|[15]|}"
  by (simp only: finite_citation_at_def formed; cases b; simp_all only: if_True if_False; code_simp)+

lemma finite_requirement_frame_carrier:
  "[1] |\<in>| finite_carrier (finite_structure (finite_requirement_frame b))"
  by (cases b; simp_all only: if_True if_False; code_simp)

locale requirement_source_frame =
  fixes E :: "'u artifact_environment" and u :: 'u and b :: bool
  assumes formed: "environment_formed E"
    and artifact: "artifact_at E u (decode_finite_object (finite_requirement_frame b))"
begin

lemma finite_exact: "finite_exact_formed (finite_requirement_frame b)"
  using formed artifact by (simp add: finite_exact_formed_correct environment_formed_def)

lemma finite_object: "finite_object_formed (finite_requirement_frame b)"
  using finite_exact by (simp add: finite_exact_formed_def)

lemma interface:
  "scoped_pattern_at E u [2] (Pattern_Variable [4]) {[2],[19],[20],[3],[4],[5]} {}"
proof -
  let ?A="decode_finite_object (finite_requirement_frame b)"
  have rec: "record_at ?A [2] [[19],[20]] [[3],[5]]"
    using finite_requirement_frame_records(2)[OF finite_object] by (simp only: finite_record_at_correct)
  have scope: "binder_scope_at ?A [3] {[4]}"
    using finite_requirement_frame_families(3)[OF finite_object] by (simp add: finite_binder_scope_at_correct)
  have cite: "citation_at ?A [5] (Local [4]) {[5]}"
    using finite_requirement_frame_citations(1)[OF finite_exact] by (simp add: finite_citation_at_correct)
  have quote: "pattern_quoted_at E u {[4]} [5] (Pattern_Variable [4]) {[5]} {}"
    by (rule pattern_quoted_at.variable[OF formed artifact cite]) auto
  show ?thesis unfolding scoped_pattern_at_def
    by (rule conjI[OF formed], rule exI[of _ ?A], rule exI[of _ "[[19],[20]]"],
      rule exI[of _ "[3]"], rule exI[of _ "[5]"], rule exI[of _ "{[4]}"], rule exI[of _ "{[5]}"])
      (use artifact rec scope quote in auto)
qed

lemma schema:
  assumes conclusion: "schema_conclusion S=Pattern_Variable [10]"
    and variables: "schema_variables S={[10]}" and material: "schema_material_premises S={}"
    and calls: "prospective_family_at E u {[10]} [14] (schema_premises S)"
  shows "native_schema_at E u [8] S"
proof -
  let ?A="decode_finite_object (finite_requirement_frame b)"
  have rec: "record_at ?A [8] [[21],[22],[23]] [[9],[11],[14]]"
    using finite_requirement_frame_records(3)[OF finite_object] by (simp only: finite_record_at_correct)
  have scope: "binder_scope_at ?A [9] {[10]}"
    using finite_requirement_frame_families(4)[OF finite_object] by (simp add: finite_binder_scope_at_correct)
  have cite: "citation_at ?A [11] (Local [10]) {[11]}"
    using finite_requirement_frame_citations(2)[OF finite_exact] by (simp add: finite_citation_at_correct)
  have quote: "pattern_quoted_at E u {[10]} [11] (Pattern_Variable [10]) {[11]} {}"
    by (rule pattern_quoted_at.variable[OF formed artifact cite]) auto
  show ?thesis unfolding native_schema_at_def
    by (rule conjI[OF formed], rule exI[of _ ?A], rule exI[of _ "[[21],[22],[23]]"],
      rule exI[of _ "[9]"], rule exI[of _ "[11]"], rule exI[of _ "[14]"],
      rule exI[of _ "{[10]}"], rule exI[of _ "{[11]}"], rule exI[of _ "{}"])
      (use artifact rec scope quote calls conclusion variables material in
        \<open>auto simp: native_premise_family_calls_only\<close>)
qed

lemma raw_definition:
  assumes schema: "native_schema_at E u [8] S"
  shows "native_definition_at E u [1] (Pattern_Variable [4]) {([7],S)}"
proof -
  let ?A="decode_finite_object (finite_requirement_frame b)"
  have rec: "record_at ?A [1] [[17],[18]] [[2],[6]]"
    using finite_requirement_frame_records(1)[OF finite_object] by (simp only: finite_record_at_correct)
  have family: "family_at ?A [6] {([7],[8])}"
    using finite_requirement_frame_families(2)[OF finite_object] by (simp add: finite_family_at_correct)
  have clauses: "native_schema_family_at E u [6] {([7],S)}"
    unfolding native_schema_family_at_def
    by (rule conjI[OF formed], rule exI[of _ ?A], rule exI[of _ "{([7],[8])}"])
      (use artifact family schema in \<open>auto simp: single_valued_def rel_dom_def\<close>)
  show ?thesis unfolding native_definition_at_def
    by (rule conjI[OF formed], rule exI[of _ ?A], rule exI[of _ "[[17],[18]]"],
      rule exI[of _ "[2]"], rule exI[of _ "[6]"],
      rule exI[of _ "{[2],[19],[20],[3],[4],[5]}"], rule exI[of _ "{}"])
      (use artifact rec interface clauses in auto)
qed

lemma roots: "native_root_family_at E u [0] {([16],(u,[1]))}"
proof -
  let ?A="decode_finite_object (finite_requirement_frame b)"
  have family: "family_at ?A [0] {([16],[15])}"
    using finite_requirement_frame_families(1)[OF finite_object] by (simp add: finite_family_at_correct)
  have cite: "citation_at ?A [15] (Local [1]) {[15]}"
    using finite_requirement_frame_citations(3)[OF finite_exact] by (simp add: finite_citation_at_correct)
  have af: "exact_formed ?A" using formed artifact by (simp add: environment_formed_def)
  have carrier: "[1]\<in>rra_carrier (object_structure ?A)"
    using finite_requirement_frame_carrier[where b=b] by (simp add: decode_finite_object_def decode_finite_structure_def)
  have location: "citation_location E u (Local [1]) u [1]"
    using artifact af carrier by (auto simp: anchor_formed_def)
  have loc: "located_at E u [15] u [1]" using artifact cite location unfolding located_at_def by blast
  show ?thesis unfolding native_root_family_at_def
    by (rule conjI[OF formed], rule exI[of _ ?A], rule exI[of _ "{([16],[15])}"])
      (use artifact family loc in \<open>auto simp: single_valued_def rel_dom_def\<close>)
qed

end

lemma finite_guard_environments_formed:
  "finite_environment_formed (finite_guard_source b)"
  "finite_environment_formed (finite_guard_environment b)"
  by (cases b; simp_all only: if_True if_False; code_simp)+

lemma finite_variable_source_frame:
  "requirement_source_frame (decode_finite_environment (finite_guard_source True)) None False"
  by (rule requirement_source_frame.intro)
    (use finite_guard_environments_formed(1)[where b=True] in
      \<open>auto simp: finite_environment_formed_correct finite_guard_source_def artifact_at_def map_relation_values_def\<close>)

lemma finite_guard_frame:
  "requirement_source_frame (decode_finite_environment (finite_guard_environment b)) (Some [1]) True"
  by (rule requirement_source_frame.intro)
    (use finite_guard_environments_formed(2)[where b=b] in
      \<open>auto simp: finite_environment_formed_correct finite_guard_environment_def artifact_at_def map_relation_values_def\<close>)

lemma finite_variable_premise_check: "finite_family_at finite_variable_artifact [14] {||}"
  by code_simp

lemma finite_variable_source_schema:
  "native_schema_at (decode_finite_environment (finite_guard_source True)) None [8]
    (decode_finite_schema finite_variable_schema)"
proof -
  interpret frame: requirement_source_frame "decode_finite_environment (finite_guard_source True)" None False
    by (rule finite_variable_source_frame)
  have family: "family_at (decode_finite_object finite_variable_artifact) [14] {}"
    using finite_variable_premise_check by (simp add: finite_family_at_correct)
  have body: "prospective_family_at (decode_finite_environment (finite_guard_source True)) None {[10]} [14] {}"
    unfolding prospective_family_at_def
    by (rule conjI[OF frame.formed], rule exI[of _ "decode_finite_object finite_variable_artifact"], rule exI[of _ "{}"])
      (use frame.artifact family in \<open>auto simp: single_valued_def rel_dom_def\<close>)
  show ?thesis by (rule frame.schema)
    (use body in \<open>auto simp: finite_variable_schema_def finite_equality_schema_def decode_finite_schema_def
      schema_variables_def rel_ran_def map_relation_values_def\<close>)
qed

lemma finite_guard_premise_checks:
  "finite_record_at finite_guard_artifact [27] [[28],[29]] [[30],[31]]"
  "finite_family_at finite_guard_artifact [14] {|([26],[27])|}"
  "finite_citation_at finite_guard_artifact [31] (Local [10]) {|[31]|}"
  "finite_citation_at finite_guard_artifact [30] (External [32] [1]) {|[30],[33]|}"
proof -
  have exact: "finite_exact_formed finite_guard_artifact"
    using requirement_source_frame.finite_exact[OF finite_guard_frame[where b=False]] by simp
  have formed: "finite_object_formed finite_guard_artifact" using exact by (simp add: finite_exact_formed_def)
  show "finite_record_at finite_guard_artifact [27] [[28],[29]] [[30],[31]]"
    by (simp only: finite_record_at_def formed; code_simp)
  show "finite_family_at finite_guard_artifact [14] {|([26],[27])|}"
    by (simp only: finite_family_at_def formed; code_simp)
  show "finite_citation_at finite_guard_artifact [31] (Local [10]) {|[31]|}"
    by (simp only: finite_citation_at_def exact; code_simp)
  show "finite_citation_at finite_guard_artifact [30] (External [32] [1]) {|[30],[33]|}"
    by (simp only: finite_citation_at_def exact; code_simp)
qed

lemma finite_guard_source_carrier:
  "[1] |\<in>| finite_carrier (finite_structure (if b then finite_variable_artifact else finite_equality_artifact))"
  by (cases b; simp_all only: if_True if_False; code_simp)

lemma finite_guard_prospective:
  "prospective_call_at (decode_finite_environment (finite_guard_environment b)) (Some [1]) {[10]} [27]
    (None,[1]) (Pattern_Variable [10]) {[27],[28],[29],[30],[33],[31]} {[32]}"
proof -
  interpret frame: requirement_source_frame "decode_finite_environment (finite_guard_environment b)" "Some [1]" True
    by (rule finite_guard_frame)
  let ?E="decode_finite_environment (finite_guard_environment b)"
  let ?A="decode_finite_object finite_guard_artifact"
  have rec: "record_at ?A [27] [[28],[29]] [[30],[31]]"
    using finite_guard_premise_checks(1) by (simp only: finite_record_at_correct)
  have variable: "citation_at ?A [31] (Local [10]) {[31]}"
    using finite_guard_premise_checks(3) by (simp add: finite_citation_at_correct)
  have art: "artifact_at ?E (Some [1]) ?A" using frame.artifact by simp
  have quote: "pattern_quoted_at ?E (Some [1]) {[10]} [31] (Pattern_Variable [10]) {[31]} {}"
    by (rule pattern_quoted_at.variable[OF frame.formed art variable]) auto
  let ?cite="External [32] [1]"
  have citation: "citation_at ?A [30] ?cite {[30],[33]}"
    using finite_guard_premise_checks(4) by (simp add: finite_citation_at_correct)
  let ?source="decode_finite_object (if b then finite_variable_artifact else finite_equality_artifact)"
  have source: "artifact_at ?E None ?source"
    by (simp add: finite_guard_environment_def artifact_at_def map_relation_values_def)
  have exact: "exact_formed ?source" using frame.formed source by (simp add: environment_formed_def)
  have carrier: "[1]\<in>rra_carrier (object_structure ?source)"
    using finite_guard_source_carrier[where b=b] by simp
  have binding: "binds_slot ?E (Some [1]) [32] None"
    by (simp add: finite_guard_environment_def binds_slot_def)
  have loc: "citation_location ?E (Some [1]) ?cite None [1]"
    using source exact carrier binding by (auto simp: anchor_formed_def)
  have slots: "citation_slots ?cite={[32]}" by simp
  show ?thesis unfolding prospective_call_at_def
    by (rule conjI[OF frame.formed], rule exI[of _ ?A], rule exI[of _ "[[28],[29]]"],
      rule exI[of _ "[30]"], rule exI[of _ "[31]"], rule exI[of _ ?cite],
      rule exI[of _ "{[30],[33]}"], rule exI[of _ "{[31]}"], rule exI[of _ "{}"])
      (use art rec citation loc quote slots in \<open>simp add: insert_commute\<close>)
qed

lemma finite_guard_native_schema:
  "native_schema_at (decode_finite_environment (finite_guard_environment b)) (Some [1]) [8]
    (decode_finite_schema finite_guard_schema)"
proof -
  interpret frame: requirement_source_frame "decode_finite_environment (finite_guard_environment b)" "Some [1]" True
    by (rule finite_guard_frame)
  have family: "family_at (decode_finite_object finite_guard_artifact) [14] {([26],[27])}"
    using finite_guard_premise_checks(2) by (simp add: finite_family_at_correct)
  have body: "prospective_family_at (decode_finite_environment (finite_guard_environment b)) (Some [1]) {[10]} [14]
      {([26],(None,[1]),Pattern_Variable [10])}"
    unfolding prospective_family_at_def
    by (rule conjI[OF frame.formed], rule exI[of _ "decode_finite_object finite_guard_artifact"],
      rule exI[of _ "{([26],[27])}"])
      (use frame.artifact family finite_guard_prospective[where b=b] in \<open>auto simp: single_valued_def rel_dom_def\<close>)
  show ?thesis by (rule frame.schema)
    (use body in \<open>auto simp: finite_guard_schema_def finite_variable_schema_def finite_equality_schema_def
      decode_finite_schema_def schema_variables_def rel_ran_def map_relation_values_def\<close>)
qed

lemma finite_source_definition:
  "native_definition_at (decode_finite_environment (finite_guard_source b)) None [1]
    (Pattern_Variable [4]) {([7],decode_finite_schema (if b then finite_variable_schema else finite_equality_schema))}"
proof (cases b)
  case False
  have same: "decode_finite_environment (finite_guard_source False)=equality_environment"
    by (simp add: finite_guard_source_def finite_equality_environment_def[symmetric] finite_equality_environment_correct)
  show ?thesis using equality_definition_at by (simp only: False if_False same finite_equality_schema_correct; simp)
next
  case True
  show ?thesis using requirement_source_frame.raw_definition[OF finite_variable_source_frame finite_variable_source_schema]
    by (simp only: True if_True)
qed

lemma finite_guard_raw_definition:
  "native_definition_at (decode_finite_environment (finite_guard_environment b)) (Some [1]) [1]
    (Pattern_Variable [4]) {([7],decode_finite_schema finite_guard_schema)}"
  by (rule requirement_source_frame.raw_definition[OF finite_guard_frame finite_guard_native_schema])

lemma finite_guard_source_roots:
  "native_root_family_at (decode_finite_environment (finite_guard_source b)) None [0] {([16],(None,[1]))}"
proof (cases b)
  case False
  show ?thesis using equality_root_family
    by (simp only: False; simp add: finite_guard_source_def finite_equality_environment_def[symmetric]
      finite_equality_environment_correct)
next
  case True
  show ?thesis using requirement_source_frame.roots[OF finite_variable_source_frame] by (simp only: True)
qed

lemma finite_guard_roots:
  "native_root_family_at (decode_finite_environment (finite_guard_environment b)) (Some [1]) [0]
    {([16],(Some [1],[1]))}"
  by (rule requirement_source_frame.roots[OF finite_guard_frame])

text \<open>
  The two executed artifacts share one concrete frame. Its complete interface,
  schema, definition, and roots are recovered once with arbitrary surrounding
  environment and use. The variable and guarded instances supply their actual
  premise families. The unchanged equality instance reuses its original proof.
\<close>

end
