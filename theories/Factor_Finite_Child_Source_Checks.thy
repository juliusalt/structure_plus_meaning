theory Factor_Finite_Child_Source_Checks
  imports Factor_Finite_Child_Sources Factor_Closed_Native_Definitions
begin

section \<open>Complete concrete source and node checks\<close>

lemma finite_child_environment_checks:
  "finite_environment_formed (finite_child_sources [])"
  "finite_environment_formed (finite_child_extension [])"
  by code_simp+

lemma finite_child_environments_formed:
  "environment_formed (decode_finite_environment (finite_child_sources []))"
  "environment_formed (decode_finite_environment (finite_child_extension []))"
  using finite_child_environment_checks by (simp_all only: finite_environment_formed_correct)

lemma finite_child_artifact_at:
  "artifact_at (decode_finite_environment (finite_child_sources p)) (Some [2]) (decode_finite_object (finite_child_artifact p))"
  by (simp add: finite_child_sources_def Let_def)

lemma finite_child_record_checks:
  "finite_record_at (finite_child_artifact []) [1] [[17],[18]] [[2],[6]]"
  "finite_record_at (finite_child_artifact []) [2] [[19],[20]] [[3],[5]]"
  "finite_record_at (finite_child_artifact []) [8] [[21],[22],[23]] [[3],[5],[14]]"
  "finite_record_at (finite_child_artifact []) [25] [[26],[27]] [[28],[5]]"
  by code_simp+

lemma finite_child_family_checks:
  "finite_family_at (finite_child_artifact []) [6] {|([7],[8])|}"
  "finite_family_at (finite_child_artifact []) [14] {|([24],[25])|}"
  by code_simp+

lemma finite_child_binder_check:
  "finite_binder_scope_at (finite_child_artifact []) [3] {||}"
  by code_simp

lemma finite_child_binder:
  "binder_scope_at (decode_finite_object (finite_child_artifact [])) [3] {}"
  using finite_child_binder_check by (simp add: finite_binder_scope_at_correct)

lemma finite_child_payload_check:
  "finite_payload_leaf_at (finite_child_artifact []) [5] []"
  by code_simp

lemma finite_child_pattern:
  "pattern_quoted_at (decode_finite_environment (finite_child_sources [])) (Some [2]) {} [5]
    (Pattern_Payload []) {[5]} {}"
proof -
  have leaf: "payload_leaf_at (decode_finite_object (finite_child_artifact [])) [5] []"
    using finite_child_payload_check by (simp only: finite_payload_leaf_at_correct)
  have quoted_term: "term_quoted_at (decode_finite_environment (finite_child_sources [])) (Some [2]) [5]
      (Payload_Term []) {[5]} {}"
    by (rule term_quoted_at.payload[OF finite_child_environments_formed(1) finite_child_artifact_at leaf])
  show ?thesis by (rule pattern_quoted_at.payload[OF quoted_term]) simp
qed

lemma finite_child_location_checks:
  "((Some [2],[1]),{|[28],[30]|},{|[29]|}) |\<in>|
    finite_location_readings (finite_child_sources []) (Some [2]) (finite_child_artifact []) [28]"
  "((Some [2],[1]),{|[15]|},{||}) |\<in>|
    finite_location_readings (finite_child_sources []) (Some [2]) (finite_child_artifact []) [15]"
  by code_simp+

lemma finite_child_prospective:
  "prospective_call_at (decode_finite_environment (finite_child_sources [])) (Some [2]) {} [25]
    (Some [2],[1]) (Pattern_Payload []) {[25],[26],[27],[28],[30],[5]} {[29]}"
proof -
  let ?E="decode_finite_environment (finite_child_sources [])"
  let ?R="decode_finite_object (finite_child_artifact [])"
  have rec: "record_at ?R [25] [[26],[27]] [[28],[5]]"
    using finite_child_record_checks(4) by (simp only: finite_record_at_correct)
  obtain cite where citation: "citation_at ?R [28] cite {[28],[30]}"
    and loc: "citation_location ?E (Some [2]) cite (Some [2]) [1]"
    and encoded_slots: "{|[29]|}=finite_citation_slots cite"
    using finite_child_location_checks(1) by (auto simp: finite_location_readings_member)
  have slots: "citation_slots cite={[29]}"
    using arg_cong[OF encoded_slots, of fset] by (simp add: finite_citation_slots_correct)
  show ?thesis unfolding prospective_call_at_def
    apply (rule conjI[OF finite_child_environments_formed(1)])
    apply (rule exI[of _ ?R], rule exI[of _ "[[26],[27]]"], rule exI[of _ "[28]"])
    apply (rule exI[of _ "[5]"], rule exI[of _ cite], rule exI[of _ "{[28],[30]}"])
    apply (rule exI[of _ "{[5]}"], rule exI[of _ "{}"])
    using finite_child_artifact_at rec citation loc finite_child_pattern slots
    by (simp add: insert_commute)
qed

lemma finite_child_prospective_check:
  "(((Some [2],[1]),Finite_Pattern_Payload []),{|[25],[26],[27],[28],[30],[5]|},{|[29]|}) |\<in>|
    finite_prospective_call_readings (finite_child_sources []) (Some [2]) {||} [25]"
  using finite_child_prospective by (simp add: finite_prospective_call_readings_correct)

lemma finite_child_parent_components:
  "finite_record_at finite_child_parent [] [[3],[4],[5]] [[0],[1],[2]]"
  "((Some [2],[7]),{|[0],[7]|},{|[6]|}) |\<in>|
    finite_site_citation_readings (finite_child_extension []) (Some []) [0]"
  "({||},{|[1]|},{||}) |\<in>|
    finite_binding_table_readings (finite_child_extension []) (Some []) [1]"
  "(fset_of_list finite_child_discharges,{|[2],[8],[9],[10],[11],[12],[13],[15],[17]|},{|[14],[16]|}) |\<in>|
    finite_discharge_table_readings (finite_child_extension []) (Some []) [2]"
  by code_simp+

lemma finite_child_native_parent:
  "native_proof_node_at (decode_finite_environment (finite_child_extension [])) (Some []) []
    (Schema_Inference (Some [2],[7]) {||}) (set finite_child_discharges)
    (set finite_child_parent_interior) (set finite_child_parent_slots)"
proof -
  let ?E="decode_finite_environment (finite_child_extension [])"
  let ?R="decode_finite_object finite_child_parent"
  let ?C="{[0],[7]} :: local_address set"
  let ?B="{[1]} :: local_address set"
  let ?J="{[2],[8],[9],[10],[11],[12],[13],[15],[17]} :: local_address set"
  have art: "artifact_at ?E (Some []) ?R"
    by (simp add: finite_child_extension_def Let_def)
  have rec: "record_at ?R [] [[3],[4],[5]] [[0],[1],[2]]"
    using finite_child_parent_components(1) by (simp only: finite_record_at_correct)
  have citation: "site_citation_at ?E (Some []) [0] (Some [2],[7]) ?C {[6]}"
    using finite_child_parent_components(2) by (simp add: finite_site_citation_readings_correct)
  have bindings: "native_binding_table_at ?E (Some []) [1] {} ?B {}"
    using finite_child_parent_components(3)
    by (simp add: finite_binding_table_readings_correct decode_finite_term_bindings_def map_relation_values_def)
  have discharges: "native_discharge_table_at ?E (Some []) [2] (set finite_child_discharges) ?J {[14],[16]}"
    using finite_child_parent_components(4)
    by (simp add: finite_discharge_table_readings_correct fset_of_list.rep_eq)
  have physical:
    "insert [] (set [[3],[4],[5]]) \<inter> (?C \<union> ?B \<union> ?J)={}"
    "?C \<inter> ?B={}" "?C \<inter> ?J={}" "?B \<inter> ?J={}"
    "insert [] (set [[3],[4],[5]] \<union> ?C \<union> ?B \<union> ?J) \<inter> ({[6]} \<union> {} \<union> {[14],[16]})={}"
    by simp_all
  have assembled: "native_proof_node_at ?E (Some []) []
    (Schema_Inference (Some [2],[7]) {||}) (set finite_child_discharges)
    (insert [] (set [[3],[4],[5]] \<union> ?C \<union> ?B \<union> ?J)) ({[6]} \<union> {} \<union> {[14],[16]})"
    by (rule native_proof_node_at.inference[OF finite_child_environments_formed(2) art rec citation _ discharges physical])
      (use bindings in simp)
  show ?thesis using assembled
    by (simp add: finite_child_parent_interior_def finite_literal_node_interior_def
      finite_child_parent_slots_def insert_commute)
qed

lemma finite_child_parent_check:
  "((Finite_Inference (Some [2],[7]) {||},fset_of_list finite_child_discharges),
      fset_of_list finite_child_parent_interior,fset_of_list finite_child_parent_slots) |\<in>|
    finite_proof_node_readings (finite_child_extension []) (Some []) []"
  using finite_child_native_parent
  by (simp add: finite_proof_node_readings_correct decode_finite_binding_set_def fset_of_list.rep_eq)

lemma finite_child_assertion_record:
  "finite_record_at finite_child_assertion [] [] []"
  by code_simp

lemma finite_child_native_assertion:
  "native_proof_node_at (decode_finite_environment (finite_child_extension [])) (Some [1]) [] Schema_Assertion {} {[]} {}"
proof -
  have art: "artifact_at (decode_finite_environment (finite_child_extension [])) (Some [1])
      (decode_finite_object finite_child_assertion)"
    by (simp add: finite_child_extension_def Let_def)
  have rec: "record_at (decode_finite_object finite_child_assertion) [] [] []"
    using finite_child_assertion_record by (simp only: finite_record_at_correct)
  show ?thesis by (rule native_proof_node_at.assertion[OF finite_child_environments_formed(2) art rec])
qed

lemma finite_child_assertion_check:
  "((Finite_Assertion,{||}),{|[]|},{||}) |\<in>|
    finite_proof_node_readings (finite_child_extension []) (Some [1]) []"
  using finite_child_native_assertion by (simp add: finite_proof_node_readings_correct)

section \<open>The package uses the existing complete native composition boundary\<close>

lemma finite_child_native_schema:
  "native_schema_at (decode_finite_environment (finite_child_sources [])) (Some [2]) [8]
    (decode_finite_schema (finite_child_schema []))"
proof -
  let ?E="decode_finite_environment (finite_child_sources [])"
  let ?R="decode_finite_object (finite_child_artifact [])"
  let ?Q="{([24],(Some [2],[1]),Pattern_Payload [])}"
  have rec: "record_at ?R [8] [[21],[22],[23]] [[3],[5],[14]]"
    using finite_child_record_checks(3) by (simp only: finite_record_at_correct)
  have family: "family_at ?R [14] {([24],[25])}"
    using finite_child_family_checks(2) by (simp only: finite_family_at_correct) simp
  have premise_family: "prospective_family_at ?E (Some [2]) {} [14] ?Q"
    unfolding prospective_family_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R], rule exI[of _ "{([24],[25])}"])
      (use family finite_child_artifact_at finite_child_prospective in \<open>auto simp: single_valued_def rel_dom_def\<close>)
  show ?thesis unfolding native_schema_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R],
      rule exI[of _ "[[21],[22],[23]]"], rule exI[of _ "[3]"], rule exI[of _ "[5]"],
      rule exI[of _ "[14]"], rule exI[of _ "{}"], rule exI[of _ "{[5]}"], rule exI[of _ "{}"])
      (use finite_child_artifact_at rec finite_child_binder finite_child_pattern premise_family in
        \<open>simp add: finite_child_schema_def decode_finite_schema_def map_relation_values_def
          schema_variables_def native_premise_family_calls_only\<close>)
qed

lemma finite_child_native_definition:
  "native_definition_at (decode_finite_environment (finite_child_sources [])) (Some [2]) [1]
    (Pattern_Payload []) {([7],decode_finite_schema (finite_child_schema []))}"
proof -
  let ?E="decode_finite_environment (finite_child_sources [])"
  let ?R="decode_finite_object (finite_child_artifact [])"
  have rec: "record_at ?R [1] [[17],[18]] [[2],[6]]" "record_at ?R [2] [[19],[20]] [[3],[5]]"
    using finite_child_record_checks(1,2) by (simp_all only: finite_record_at_correct)
  have scope: "scoped_pattern_at ?E (Some [2]) [2] (Pattern_Payload []) {[2],[19],[20],[3],[5]} {}"
    unfolding scoped_pattern_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R],
      rule exI[of _ "[[19],[20]]"], rule exI[of _ "[3]"], rule exI[of _ "[5]"],
      rule exI[of _ "{}"], rule exI[of _ "{[5]}"])
      (use finite_child_artifact_at rec(2) finite_child_binder finite_child_pattern in auto)
  have family: "family_at ?R [6] {([7],[8])}"
    using finite_child_family_checks(1) by (simp only: finite_family_at_correct) simp
  have clauses: "native_schema_family_at ?E (Some [2]) [6] {([7],decode_finite_schema (finite_child_schema []))}"
    unfolding native_schema_family_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R], rule exI[of _ "{([7],[8])}"])
      (use finite_child_artifact_at family finite_child_native_schema in \<open>auto simp: single_valued_def rel_dom_def\<close>)
  show ?thesis unfolding native_definition_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R],
      rule exI[of _ "[[17],[18]]"], rule exI[of _ "[2]"], rule exI[of _ "[6]"],
      rule exI[of _ "{[2],[19],[20],[3],[5]}"], rule exI[of _ "{}"])
      (use finite_child_artifact_at rec(1) scope clauses in auto)
qed

lemma finite_child_root_family_check:
  "finite_family_at (finite_child_artifact []) [0] {|([16],[15])|}"
  by code_simp

lemma finite_child_roots:
  "native_root_family_at (decode_finite_environment (finite_child_sources [])) (Some [2]) [0]
    {([16],Some [2],[1])}"
proof -
  let ?E="decode_finite_environment (finite_child_sources [])"
  let ?R="decode_finite_object (finite_child_artifact [])"
  have family: "family_at ?R [0] {([16],[15])}"
    using finite_child_root_family_check by (simp add: finite_family_at_correct)
  obtain cite where citation: "citation_at ?R [15] cite {[15]}"
    and loc: "citation_location ?E (Some [2]) cite (Some [2]) [1]"
    using finite_child_location_checks(2) by (auto simp: finite_location_readings_member)
  have located: "located_at ?E (Some [2]) [15] (Some [2]) [1]"
    unfolding located_at_def
    by (rule exI[of _ ?R], rule exI[of _ cite], rule exI[of _ "{[15]}"])
      (use finite_child_artifact_at citation loc in simp)
  show ?thesis unfolding native_root_family_at_def
    by (rule conjI[OF finite_child_environments_formed(1)], rule exI[of _ ?R], rule exI[of _ "{([16],[15])}"])
      (use finite_child_artifact_at family located in \<open>auto simp: single_valued_def rel_dom_def\<close>)
qed

lemma finite_child_root_check:
  "{|([16],Some [2],[1])|} |\<in>| finite_native_root_family_readings (finite_child_sources []) (Some [2]) [0]"
  using finite_child_roots by (simp add: finite_native_root_family_readings_correct)

lemma finite_child_native_package:
  "native_package_at (decode_finite_environment (finite_child_sources [])) (Some [2]) [0]
    (decode_finite_system (finite_child_program []))"
proof -
  let ?E="decode_finite_environment (finite_child_sources [])"
  let ?S="decode_finite_schema (finite_child_schema [])"
  let ?G="{((Some [2],[1]),Pattern_Payload [],{([7],?S)})}"
  have formed: "native_package_formed ?E {(Some [2],[1])}" and graph: "native_definition_graph ?E {(Some [2],[1])}=?G"
    using native_closed_definition_graph[OF finite_child_environments_formed(1), where G="?G"] finite_child_native_definition
    by (auto simp: rel_dom_def schema_dependencies_def finite_child_schema_def
      decode_finite_schema_def map_relation_values_def rel_ran_def)
  have program: "native_program ?E {(Some [2],[1])}=decode_finite_system (finite_child_program [])"
    unfolding native_program_def graph
    by (auto simp: finite_child_program_def decode_finite_system_def map_relation_values_def)
  have roots: "native_root_family_at ?E (Some [2]) [0] {([16],Some [2],[1])}"
    using finite_child_root_check by (simp only: finite_native_root_family_readings_correct) simp
  show ?thesis unfolding native_package_at_def
    by (rule exI[of _ "{([16],Some [2],[1])}"])
      (use roots formed program in \<open>auto simp: rel_ran_def\<close>)
qed

end
