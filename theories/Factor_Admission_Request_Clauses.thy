theory Factor_Admission_Request_Clauses
  imports Factor_Admission_Request_Boundary Factor_Pattern_Determination
    Factor_Admitted_Context Factor_Recursive_Groups
begin

section \<open>Native request checks retain the actual fixed source domain\<close>

definition admission_source_data :: "nat set \<Rightarrow> factor_term" where
  "admission_source_data D=data_list_term (map admission_counter (sorted_list_of_set D))"

lemma admission_source_data_formed [simp]: "term_formed (admission_source_data D)"
  by (simp add: admission_source_data_def data_list_term_formed octets_formed_def)

lemma admission_source_data_closed [simp]: "self_contained_term (admission_source_data D)"
  by (simp add: admission_source_data_def data_list_term_self_contained)

lemma admission_source_data_member:
  assumes finite: "finite D"
  shows "selected_data_member t (admission_source_data D) \<longleftrightarrow>
    (\<exists>d\<in>D. t=admission_counter d)"
  using finite by (auto simp: admission_source_data_def selected_data_member_exact data_list_term_injective)

definition admission_supported_site_schema :: "nat set \<Rightarrow> (nat,nat,nat) factor_schema" where
  "admission_supported_site_schema D=data_rule data_x
    {(0,5,Pattern_Pair data_x (Pattern_Pair (exact_term_pattern (admission_source_data D)) data_y))}"

definition admission_supported_leaf_schema :: "(nat,nat,nat) factor_schema" where
  "admission_supported_leaf_schema=data_rule
    (Pattern_Pair (Pattern_Payload [0]) data_x) {(0,362,data_x)}"

definition admission_supported_pair_schema :: "(nat,nat,nat) factor_schema" where
  "admission_supported_pair_schema=data_rule
    (Pattern_Pair (Pattern_Payload [1]) (Pattern_Pair data_x data_y))
    {(0,363,data_x),(1,363,data_y)}"

definition admission_supported_list_schema :: "(nat,nat,nat) factor_schema" where
  "admission_supported_list_schema=data_rule
    (Pattern_Pair (Pattern_Payload [2]) data_x) {(0,363,data_x)}"

definition admission_supported_goal_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "admission_supported_goal_clauses={(0,admission_supported_leaf_schema),
    (1,admission_supported_pair_schema),(2,admission_supported_list_schema)}"

definition admission_fresh_counter_schema :: "nat set \<Rightarrow> (nat,nat,nat) factor_schema" where
  "admission_fresh_counter_schema D=data_rule data_x
    {(0,340,data_y),(1,46,collection_join_pattern
      (exact_term_pattern (admission_counter (admission_source_floor D))) data_y data_x)}"

definition admission_request_family :: "nat set \<Rightarrow> nat \<Rightarrow>
    (nat\<times>(nat,nat,nat) factor_schema) set" where
  "admission_request_family D d=(if d=362 then {(0,admission_supported_site_schema D)}
    else if d=363 then admission_supported_goal_clauses
    else if d=364 then list_profile_clauses 363 364
    else if d=365 then {(0,admission_fresh_counter_schema D)}
    else if d=366 then {(0,admitted_pair_schema 364 365)}
    else if d=367 then {(0,admitted_context_schema 366 361)} else {})"

definition admission_request_definition_group :: "nat set \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "admission_request_definition_group D=\<lparr>
    system_interfaces={(d,data_x) |d. d\<in>{362,363,364,365,366,367}},
    system_clauses={((d,c),S). d\<in>{362,363,364,365,366,367} \<and>
      (c,S)\<in>admission_request_family D d}\<rparr>"

lemma admission_request_group_definitions [simp]:
  "system_definitions (admission_request_definition_group D)={362,363,364,365,366,367}"
  by (auto simp: admission_request_definition_group_def system_definitions_def rel_dom_def)

lemma admission_request_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces (admission_request_definition_group D) \<longleftrightarrow>
    d\<in>{362,363,364,365,366,367} \<and> p=data_x"
  by (auto simp: admission_request_definition_group_def)

lemmas admission_request_schema_defs=admission_supported_site_schema_def
  admission_supported_leaf_schema_def admission_supported_pair_schema_def admission_supported_list_schema_def
  admission_fresh_counter_schema_def

lemma admission_request_group_formed_over:
  "schema_system_formed_over {5,46,340,361} (admission_request_definition_group D)"
  by (rule schema_system_formed_over_families
    [where D="{362,363,364,365,366,367}" and p="\<lambda>_. data_x" and C="admission_request_family D"])
    (auto simp: admission_request_definition_group_def admission_request_family_def
      admission_supported_goal_clauses_def admission_request_schema_defs list_profile_clauses_def
      data_list_nil_schema_def list_step_schema_def schema_formed_def schema_dependencies_def
      admitted_pair_schema_def admitted_context_schema_def single_valued_def rel_ran_def octets_formed_def)

interpretation admission_request_group:
  positive_definition_group admission_sequence_system "admission_request_definition_group D"
proof (rule positive_definition_group.intro)
  show "schema_system_formed admission_sequence_system" by simp
  have support: "{5,46,340,361}\<subseteq>system_definitions admission_sequence_system" by auto
  show "schema_system_formed_over (system_definitions admission_sequence_system)
      (admission_request_definition_group D)"
    by (rule schema_system_formed_over_mono[OF admission_request_group_formed_over support])
  show "system_definitions admission_sequence_system\<inter>
    system_definitions (admission_request_definition_group D)={}"
    by auto
qed

definition admission_request_system :: "nat set \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "admission_request_system D=system_union admission_sequence_system (admission_request_definition_group D)"

lemma admission_request_system_formed [simp]: "schema_system_formed (admission_request_system D)"
  using admission_request_group.formed by (simp only: admission_request_system_def)

lemma admission_request_definitions [simp]:
  "system_definitions (admission_request_system D)=
    system_definitions admission_sequence_system\<union>{362,363,364,365,366,367}"
  by (simp add: admission_request_system_def)

lemma admission_request_call:
  "schema_call_formed (admission_request_system D) d t \<longleftrightarrow>
    d\<in>system_definitions (admission_request_system D) \<and> term_formed t"
  unfolding admission_request_system_def
  by (rule admission_request_group.variable_calls[OF admission_sequence_call admission_request_group_interfaces])

lemma admission_request_clauses:
  assumes "d\<in>{362,363,364,365,366,367}"
  shows "((d,c),S)\<in>system_clauses (admission_request_system D) \<longleftrightarrow>
    (c,S)\<in>admission_request_family D d"
proof -
  have inside: "d\<in>system_definitions (admission_request_definition_group D)"
    using assms by simp
  have absent: "((d,c),S)\<notin>system_clauses admission_sequence_system"
    by (rule admission_request_group.no_old_clause[OF inside])
  show ?thesis using absent assms
    by (auto simp: admission_request_system_def admission_request_definition_group_def)
qed

lemma admission_request_old_meaning:
  assumes "d\<in>system_definitions admission_sequence_system"
  shows "(d,t)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    (d,t)\<in>positive_meaning admission_sequence_system"
  using admission_request_group.old_meaning[OF assms, where t=t and D=D]
  by (simp only: admission_request_system_def)

text \<open>
  The actual source domain supplies the complete supported-site term and its
  exact allocation floor. Ordinary native membership checks every requested
  leaf. Recursive goal admission preserves pair and collection structure, and
  the existing complete list recognizer checks the whole requirement family.

  The existing pair constructor combines support with allocation. The existing
  admitted-context constructor then requires that same request before the
  native sequence output can be admitted, including for an empty goal family.
  The caller cannot supply a different source list inside the request.
\<close>

end
