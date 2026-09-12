theory Factor_Admission_Sequence_Clauses
  imports Factor_Admission_Sequences Factor_Admission_Plan_Exact
begin

section \<open>Native planning retains the complete ordered requirement family\<close>

definition admission_sequence_nil_schema :: "(nat,nat,nat) factor_schema" where
  "admission_sequence_nil_schema=data_rule
    (admission_plan_pattern (Pattern_Payload []) data_x (Pattern_Payload []) data_x (Pattern_Payload []))
    {(0,340,data_x)}"

definition admission_sequence_step_schema :: "(nat,nat,nat) factor_schema" where
  "admission_sequence_step_schema=data_rule
    (admission_plan_pattern (Pattern_Pair data_x data_y) data_z
      (Pattern_Pair data_w (Pattern_Variable 4)) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,341,admission_plan_pattern data_x data_z data_w (Pattern_Variable 7) (Pattern_Variable 8)),
     (1,361,admission_plan_pattern data_y (Pattern_Variable 7)
       (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 9)),
     (2,46,collection_join_pattern (Pattern_Variable 8) (Pattern_Variable 9) (Pattern_Variable 6))}"

definition admission_sequence_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "admission_sequence_clauses={(0,admission_sequence_nil_schema),(1,admission_sequence_step_schema)}"

definition admission_sequence_system :: "(nat,nat,nat,nat) schema_system" where
  "admission_sequence_system=add_view_definition admission_plan_system 361 data_x admission_sequence_clauses"

lemmas admission_sequence_schema_defs=admission_sequence_nil_schema_def admission_sequence_step_schema_def

lemma admission_sequence_system_formed [simp]: "schema_system_formed admission_sequence_system"
  unfolding admission_sequence_system_def
  by (rule add_recursive_definition_formed[OF admission_plan_formed])
    (auto simp: admission_sequence_clauses_def admission_sequence_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_ran_def octets_formed_def)

lemma admission_sequence_definitions [simp]:
  "system_definitions admission_sequence_system=insert 361 (system_definitions admission_plan_system)"
  by (simp add: admission_sequence_system_def)

lemma admission_sequence_call:
  "schema_call_formed admission_sequence_system d t \<longleftrightarrow>
    d\<in>system_definitions admission_sequence_system \<and> term_formed t"
  using added_variable_calls[OF admission_plan_formed
    admission_sequence_system_formed[unfolded admission_sequence_system_def] admission_plan_call]
  by (simp only: admission_sequence_system_def[symmetric])

lemma admission_sequence_old_meaning:
  assumes "d\<in>system_definitions admission_plan_system"
  shows "(d,t)\<in>positive_meaning admission_sequence_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning admission_plan_system"
  using added_definition_preserves_old(2)[OF admission_plan_formed
    admission_sequence_system_formed[unfolded admission_sequence_system_def], of d t] assms
  by (auto simp: admission_sequence_system_def)

lemma admission_sequence_entry_clauses [simp]:
  "((361,c),S)\<in>system_clauses admission_sequence_system \<longleftrightarrow>
    (c,S)\<in>admission_sequence_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses admission_plan_system \<Longrightarrow>
    d\<in>system_definitions admission_plan_system" for d c S
    using admission_plan_formed unfolding schema_system_formed_def by blast
  have absent: "((361,c),S)\<notin>system_clauses admission_plan_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: admission_sequence_system_def)
qed

lemma admission_sequence_components:
  "(340,z)\<in>positive_meaning admission_sequence_system \<longleftrightarrow> (\<exists>n. z=admission_counter n)"
  "(341,z)\<in>positive_meaning admission_sequence_system \<longleftrightarrow> admission_plan_result z"
  "(46,z)\<in>positive_meaning admission_sequence_system \<longleftrightarrow>
    (46,z)\<in>positive_meaning data_append_system"
  using admission_sequence_old_meaning[of 340 z] admission_sequence_old_meaning[of 341 z]
    admission_sequence_old_meaning[of 46 z]
  by (auto simp: admission_plan_counter_exact admission_plan_exact admission_plan_append_meaning)

definition admission_sequence_result :: "factor_term \<Rightarrow> bool" where
  "admission_sequence_result z \<longleftrightarrow>
    (\<exists>gs n ds k cs. admission_sequence gs n=(ds,k,cs) \<and>
      z=admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"

text \<open>
  The step invokes the existing native planner on the actual next goal and
  recurses on the complete remaining family at its returned counter. The
  original native append operation combines their instructions. The output
  retains every result entry in the same order as the submitted requirements.
  No candidate plan or table of successful predicates is supplied as input.
\<close>

end
