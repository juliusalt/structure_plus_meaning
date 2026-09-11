theory Factor_Binding_Observation_Clauses
  imports Factor_Related_Lists
begin

section \<open>One owning use relates each paired row to its two observations\<close>

definition binding_observation_row_schema :: "bool\<Rightarrow>(nat,nat,nat) factor_schema" where
  "binding_observation_row_schema first=data_rule
    (context_relation_pattern data_x
      (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
      (Pattern_Pair data_y (if first then data_z else data_w))) {}"

abbreviation binding_observation_argument where
  "binding_observation_argument u bs xs ys \<equiv> Pair_Term u (Pair_Term bs (Pair_Term xs ys))"

abbreviation binding_observation_pattern where
  "binding_observation_pattern u bs xs ys \<equiv> Pattern_Pair u (Pattern_Pair bs (Pattern_Pair xs ys))"

definition binding_observation_pair_schema :: "(nat,nat,nat) factor_schema" where
  "binding_observation_pair_schema=data_rule
    (binding_observation_pattern data_x data_y data_z data_w)
    {(0,345,context_relation_pattern data_x data_y data_z),
     (1,346,context_relation_pattern data_x data_y data_w)}"

definition binding_observation_clauses :: "nat\<Rightarrow>(nat\<times>(nat,nat,nat) factor_schema) set" where
  "binding_observation_clauses d=(if d=343 then {(0,binding_observation_row_schema True)}
    else if d=344 then {(0,binding_observation_row_schema False)}
    else if d=345 then related_list_clauses 343 345
    else if d=346 then related_list_clauses 344 346
    else if d=347 then {(0,binding_observation_pair_schema)} else {})"

definition binding_observation_program :: "(nat,nat,nat,nat) schema_system" where
  "binding_observation_program=\<lparr>
    system_interfaces={(343,data_x),(344,data_x),(345,data_x),(346,data_x),(347,data_x)},
    system_clauses={((343,0),binding_observation_row_schema True),
      ((344,0),binding_observation_row_schema False),
      ((345,0),related_list_nil_schema),((345,1),related_list_step_schema 343 345),
      ((346,0),related_list_nil_schema),((346,1),related_list_step_schema 344 346),
      ((347,0),binding_observation_pair_schema)}\<rparr>"

lemma binding_observation_definitions [simp]:
  "system_definitions binding_observation_program={343,344,345,346,347}"
  by (auto simp: binding_observation_program_def system_definitions_def rel_dom_def)

lemma binding_observation_interfaces [simp]:
  "(d,p)\<in>system_interfaces binding_observation_program \<longleftrightarrow>
    d\<in>{343,344,345,346,347} \<and> p=data_x"
  by (auto simp: binding_observation_program_def)

lemma binding_observation_clause [simp]:
  "((d,c),S)\<in>system_clauses binding_observation_program \<longleftrightarrow>
    d\<in>{343,344,345,346,347} \<and> (c,S)\<in>binding_observation_clauses d"
  by (auto simp: binding_observation_program_def binding_observation_clauses_def related_list_clauses_def)

lemmas binding_observation_schema_defs=binding_observation_row_schema_def
  binding_observation_pair_schema_def related_list_nil_schema_def related_list_step_schema_def

lemma binding_observation_program_formed [simp]: "schema_system_formed binding_observation_program"
  by (simp only: schema_system_formed_def binding_observation_definitions)
    (auto simp: binding_observation_program_def binding_observation_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma binding_observation_call:
  "schema_call_formed binding_observation_program d t \<longleftrightarrow>
    d\<in>{343,344,345,346,347} \<and> term_formed t"
  by (auto simp: schema_call_formed_def)

text \<open>
  The two scalar clauses retain one key and select one value from its pair.
  Their repeated context variable checks the owning use of every input row.
  The existing related-list clauses lift each operation over the same complete
  input sequence. The final ordinary clause keeps both results together.
  This five-definition program has seven ordinary clauses and no external callees.
\<close>

end
