theory Factor_Prefixed_Observation_Clauses
  imports Factor_Paired_Context_Results
begin

section \<open>Every observation retains its value's prefix and source key\<close>

definition prefixed_observation_row_schema :: "bool\<Rightarrow>(nat,nat,nat) factor_schema" where
  "prefixed_observation_row_schema first=data_rule
    (context_relation_pattern data_x
      (Pattern_Pair (Pattern_Pair data_x data_y)
        (Pattern_Pair data_z (Pattern_Pair data_w (Pattern_Variable 4))))
      (Pattern_Pair data_y (Pattern_Pair data_z (if first then data_w else Pattern_Variable 4)))) {}"

definition prefixed_observation_clauses :: "nat\<Rightarrow>(nat\<times>(nat,nat,nat) factor_schema) set" where
  "prefixed_observation_clauses d=(if d=354 then {(0,prefixed_observation_row_schema True)}
    else if d=355 then {(0,prefixed_observation_row_schema False)}
    else if d=356 then related_list_clauses 354 356
    else if d=357 then related_list_clauses 355 357
    else if d=358 then {(0,paired_context_results_schema 356 357)} else {})"

definition prefixed_observation_program :: "(nat,nat,nat,nat) schema_system" where
  "prefixed_observation_program=\<lparr>
    system_interfaces={(354,data_x),(355,data_x),(356,data_x),(357,data_x),(358,data_x)},
    system_clauses={((354,0),prefixed_observation_row_schema True),
      ((355,0),prefixed_observation_row_schema False),
      ((356,0),related_list_nil_schema),((356,1),related_list_step_schema 354 356),
      ((357,0),related_list_nil_schema),((357,1),related_list_step_schema 355 357),
      ((358,0),paired_context_results_schema 356 357)}\<rparr>"

lemma prefixed_observation_definitions [simp]:
  "system_definitions prefixed_observation_program={354,355,356,357,358}"
  by (auto simp: prefixed_observation_program_def system_definitions_def rel_dom_def)

lemma prefixed_observation_interfaces [simp]:
  "(d,p)\<in>system_interfaces prefixed_observation_program \<longleftrightarrow>
    d\<in>{354,355,356,357,358} \<and> p=data_x"
  by (auto simp: prefixed_observation_program_def)

lemma prefixed_observation_clause [simp]:
  "((d,c),S)\<in>system_clauses prefixed_observation_program \<longleftrightarrow>
    d\<in>{354,355,356,357,358} \<and> (c,S)\<in>prefixed_observation_clauses d"
  by (auto simp: prefixed_observation_program_def prefixed_observation_clauses_def related_list_clauses_def)

lemmas prefixed_observation_schema_defs=prefixed_observation_row_schema_def
  paired_context_results_schema_def related_list_nil_schema_def related_list_step_schema_def

lemma prefixed_observation_formed [simp]: "schema_system_formed prefixed_observation_program"
  by (simp only: schema_system_formed_def prefixed_observation_definitions)
    (auto simp: prefixed_observation_program_def prefixed_observation_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma prefixed_observation_call:
  "schema_call_formed prefixed_observation_program d t \<longleftrightarrow>
    d\<in>{354,355,356,357,358} \<and> term_formed t"
  by (auto simp: schema_call_formed_def)

text \<open>
  A repeated context variable checks the owner of every source key. Each
  projection keeps the local key and the entire prefix around the selected
  value. Both values remain in its source pattern, so even the unselected
  component must be formed. The sequence lifts and shared-context pairing
  use their existing general clauses; this program has no external callees.
\<close>

end
