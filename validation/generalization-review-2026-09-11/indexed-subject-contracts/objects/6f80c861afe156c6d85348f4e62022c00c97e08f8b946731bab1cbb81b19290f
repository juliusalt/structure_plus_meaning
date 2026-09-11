theory Factor_Term_Sequence_Clauses
  imports Factor_List_Folds Factor_Recursive_Groups
begin

section \<open>Pairing and counting specialize the existing fold\<close>

definition term_pair_step_schema :: "(nat,nat,nat) factor_schema" where
  "term_pair_step_schema=data_rule
    (collection_join_pattern data_x data_y (Pattern_Pair data_x data_y)) {}"

definition term_count_step_schema :: "(nat,nat,nat) factor_schema" where
  "term_count_step_schema=data_rule
    (collection_join_pattern data_x data_y (Pattern_Pair (Pattern_Payload []) data_y)) {}"

definition term_index_schema :: "(nat,nat,nat) factor_schema" where
  "term_index_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,233,collection_join_pattern (Pattern_Payload []) data_x data_x),
     (1,233,collection_join_pattern (Pattern_Pair data_z data_w) (Pattern_Variable 4) data_x),
     (2,235,collection_join_pattern (Pattern_Payload []) (Pattern_Variable 4) data_y)}"

definition term_sequence_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "term_sequence_clause_family d=
    (if d=232 then {(0,term_pair_step_schema)}
    else if d=233 then list_fold_clauses 232 233
    else if d=234 then {(0,term_count_step_schema)}
    else if d=235 then list_fold_clauses 234 235
    else if d=236 then {(0,term_index_schema)}
    else {})"

definition term_sequence_system :: "(nat,nat,nat,nat) schema_system" where
  "term_sequence_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{232,233,234,235,236}},
    system_clauses={((d,c),S). d\<in>{232,233,234,235,236} \<and> (c,S)\<in>term_sequence_clause_family d}\<rparr>"

lemmas term_sequence_schema_defs = term_pair_step_schema_def term_count_step_schema_def term_index_schema_def
  list_fold_clauses_def list_fold_nil_schema_def list_fold_step_schema_def

lemma term_sequence_definitions [simp]:
  "system_definitions term_sequence_system={232,233,234,235,236}"
  by (auto simp: term_sequence_system_def system_definitions_def rel_dom_def)

lemma term_sequence_clause [simp]:
  "((d,c),S)\<in>system_clauses term_sequence_system \<longleftrightarrow>
    d\<in>{232,233,234,235,236} \<and> (c,S)\<in>term_sequence_clause_family d"
  by (auto simp: term_sequence_system_def)

lemma term_sequence_system_formed [simp]: "schema_system_formed term_sequence_system"
proof -
  have finite: "finite (term_sequence_clause_family d)" for d
    by (simp add: term_sequence_clause_family_def list_fold_clauses_def)
  have functional: "single_valued (term_sequence_clause_family d)" for d
    by (auto simp: term_sequence_clause_family_def list_fold_clauses_def single_valued_def split: if_splits)
  have schemas: "schema_formed S \<and> schema_dependencies S\<subseteq>{232,233,234,235,236}"
    if "(c,S)\<in>term_sequence_clause_family d" for c S d
    using that by (auto simp: term_sequence_clause_family_def term_sequence_schema_defs
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def
      octets_formed_def split: if_splits)
  have over: "schema_system_formed_over {} term_sequence_system"
    by (rule schema_system_formed_over_families[where D="{232,233,234,235,236}"
        and p="\<lambda>_. Pattern_Variable 0" and C=term_sequence_clause_family])
      (use finite functional schemas in \<open>auto simp: term_sequence_system_def\<close>)+
  show ?thesis using over by simp
qed

lemma term_sequence_external_dependencies:
  "system_external_dependencies term_sequence_system={}"
  using system_external_dependencies_boundary[of "{}" term_sequence_system] by auto

lemma term_sequence_call:
  "schema_call_formed term_sequence_system d t \<longleftrightarrow>
    d\<in>system_definitions term_sequence_system \<and> term_formed t"
  by (simp only: schema_call_formed_def term_sequence_system_formed term_sequence_definitions)
    (auto simp: term_sequence_system_def)

interpretation term_pair_fold: list_fold_profile term_sequence_system 232 233
  by (unfold_locales)
    (auto simp: term_sequence_clause_family_def term_sequence_call)

interpretation term_count_fold: list_fold_profile term_sequence_system 234 235
  by (unfold_locales)
    (auto simp: term_sequence_clause_family_def term_sequence_call)

text \<open>
  Five definitions contain seven ordinary clauses. Pairing retains a formed
  head and seed. Counting replaces each formed head by the empty payload.
  Both traversals are instances of the existing relational fold, with its
  complete list boundary and separate recursive and step sockets.

  Position selection checks the complete input, reconstructs it from a prefix
  and a selected head with its tail, and counts that identical prefix. The
  suffix and prefix are local witnesses, not additional fields of the source.
  The closed program has no external callees or material premises.
\<close>

end
