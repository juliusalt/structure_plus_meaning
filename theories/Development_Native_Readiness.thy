theory Development_Native_Readiness
  imports Factor_Bag_Difference Development_Problems
begin

section \<open>Readiness is a native definition\<close>

text \<open>
  The owner's direction of 2026-09-19 makes native definitions normative: a notion of the development is a
  Factor program over native structure, its meaning is its positive meaning, and Isabelle verifies its
  contract. Readiness is the first notion of the loop defined so. Its argument carries the whole subject:
  the problems, each with the list of its decompositions (a decomposition is the list of its premise
  problems), the answered problems and the open ones. The status of a problem is therefore structure of
  the argument, not an absence the program would have to establish by telling octets apart: the program
  compares problems only for equality, through variables that occur twice, and states no payload but the
  empty payload that ends every data list.

  Settlement is a least closure, which positive meaning is: every premise of a list is settled when the
  problem is answered and one of its decompositions has every premise settled. A problem is ready when it
  is open and every premise of every one of its decompositions is settled.
\<close>

abbreviation readiness_context :: "nat term_pattern" where
  "readiness_context \<equiv> Pattern_Pair data_x data_y"

definition settled_nil_schema :: "(nat,nat,nat) factor_schema" where
  "settled_nil_schema=data_rule (Pattern_Pair readiness_context (Pattern_Payload [])) {}"

definition settled_step_schema :: "(nat,nat,nat) factor_schema" where
  "settled_step_schema=data_rule
    (Pattern_Pair readiness_context (Pattern_Pair data_z data_w))
    {(0,5,Pattern_Pair (Pattern_Pair data_z (Pattern_Variable 4)) (Pattern_Pair data_x (Pattern_Variable 5))),
     (1,5,Pattern_Pair data_z (Pattern_Pair data_y (Pattern_Variable 6))),
     (2,5,Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8))),
     (3,200,Pattern_Pair readiness_context (Pattern_Variable 7)),
     (4,200,Pattern_Pair readiness_context data_w)}"

definition settled_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "settled_clauses={(0,settled_nil_schema),(1,settled_step_schema)}"

definition native_settled_system :: "(nat,nat,nat,nat) schema_system" where
  "native_settled_system=add_view_definition bag_comparison_system 200 data_x settled_clauses"

lemmas settled_schema_defs=settled_nil_schema_def settled_step_schema_def

lemma native_settled_system_formed [simp]: "schema_system_formed native_settled_system"
  unfolding native_settled_system_def
  by (rule add_recursive_definition_formed[OF bag_comparison_system_formed])
    (auto simp: settled_clauses_def settled_schema_defs schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma native_settled_definitions [simp]:
  "system_definitions native_settled_system=insert 200 (system_definitions bag_comparison_system)"
  by (simp add: native_settled_system_def)

lemma native_settled_call:
  "schema_call_formed native_settled_system d t \<longleftrightarrow>
    d\<in>system_definitions native_settled_system \<and> term_formed t"
proof -
  have prior: "schema_call_formed bag_comparison_system d t \<longleftrightarrow>
      d\<in>system_definitions bag_comparison_system \<and> term_formed t" for d t
    by (simp add: bag_comparison_call)
  show ?thesis using added_variable_calls[OF bag_comparison_system_formed
    native_settled_system_formed[unfolded native_settled_system_def] prior]
    by (simp only: native_settled_system_def[symmetric])
qed

lemma native_settled_old_meaning:
  assumes "d\<in>system_definitions bag_comparison_system"
  shows "(d,t)\<in>positive_meaning native_settled_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using added_definition_preserves_old(2)[OF bag_comparison_system_formed
    native_settled_system_formed[unfolded native_settled_system_def], of d t] assms
  by (auto simp: native_settled_system_def)

lemma native_settled_clause [simp]:
  "((200,c),S)\<in>system_clauses native_settled_system \<longleftrightarrow> (c,S)\<in>settled_clauses"
proof -
  have owned: "((200,c),S)\<in>system_clauses bag_comparison_system \<Longrightarrow>
    200\<in>system_definitions bag_comparison_system"
    using bag_comparison_system_formed unfolding schema_system_formed_def by blast
  have absent: "((200,c),S)\<notin>system_clauses bag_comparison_system" using owned by auto
  show ?thesis using absent by (simp add: native_settled_system_def)
qed

section \<open>Every decomposition of a problem, and readiness\<close>

definition native_decompositions_system :: "(nat,nat,nat,nat) schema_system" where
  "native_decompositions_system=add_view_definition native_settled_system 201 data_x (context_list_clauses 200 201)"

lemma native_decompositions_system_formed [simp]: "schema_system_formed native_decompositions_system"
  unfolding native_decompositions_system_def
  by (rule add_recursive_definition_formed[OF native_settled_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma native_decompositions_definitions [simp]:
  "system_definitions native_decompositions_system=insert 201 (system_definitions native_settled_system)"
  by (simp add: native_decompositions_system_def)

lemma native_decompositions_call:
  "schema_call_formed native_decompositions_system d t \<longleftrightarrow>
    d\<in>system_definitions native_decompositions_system \<and> term_formed t"
proof -
  have prior: "schema_call_formed native_settled_system d t \<longleftrightarrow>
      d\<in>system_definitions native_settled_system \<and> term_formed t" for d t
    by (rule native_settled_call)
  show ?thesis using added_variable_calls[OF native_settled_system_formed
    native_decompositions_system_formed[unfolded native_decompositions_system_def] prior]
    by (simp only: native_decompositions_system_def[symmetric])
qed

lemma native_decompositions_old_meaning:
  assumes "d\<in>system_definitions native_settled_system"
  shows "(d,t)\<in>positive_meaning native_decompositions_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_settled_system"
  using added_definition_preserves_old(2)[OF native_settled_system_formed
    native_decompositions_system_formed[unfolded native_decompositions_system_def], of d t] assms
  by (auto simp: native_decompositions_system_def)

lemma native_decompositions_clause [simp]:
  "((201,c),S)\<in>system_clauses native_decompositions_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 200 201"
proof -
  have owned: "((201,c),S)\<in>system_clauses native_settled_system \<Longrightarrow>
    201\<in>system_definitions native_settled_system"
    using native_settled_system_formed unfolding schema_system_formed_def by blast
  have absent: "((201,c),S)\<notin>system_clauses native_settled_system" using owned by auto
  show ?thesis using absent by (simp add: native_decompositions_system_def)
qed

interpretation native_decompositions: context_list_profile native_decompositions_system 200 201
  by (rule context_list_profile.intro) (auto simp: native_decompositions_call)

definition ready_schema :: "(nat,nat,nat) factor_schema" where
  "ready_schema=data_rule (Pattern_Pair (Pattern_Pair readiness_context data_z) data_w)
    {(0,5,Pattern_Pair data_w (Pattern_Pair data_z (Pattern_Variable 4))),
     (1,5,Pattern_Pair (Pattern_Pair data_w (Pattern_Variable 5)) (Pattern_Pair data_x (Pattern_Variable 6))),
     (2,201,Pattern_Pair readiness_context (Pattern_Variable 5))}"

definition native_readiness_system :: "(nat,nat,nat,nat) schema_system" where
  "native_readiness_system=add_view_definition native_decompositions_system 202 data_x {(0,ready_schema)}"

interpretation native_readiness_view: positive_view native_decompositions_system 202 data_x "{(0,ready_schema)}"
  by (rule positive_view.intro)
    (auto simp: ready_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def
      rel_ran_def octets_formed_def)

lemma native_readiness_system_formed [simp]: "schema_system_formed native_readiness_system"
  unfolding native_readiness_system_def by (rule native_readiness_view.formed)

lemma native_readiness_definitions [simp]:
  "system_definitions native_readiness_system=insert 202 (system_definitions native_decompositions_system)"
  by (simp add: native_readiness_system_def)

lemma native_readiness_old_meaning:
  assumes "d\<in>system_definitions native_decompositions_system"
  shows "(d,t)\<in>positive_meaning native_readiness_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_decompositions_system"
  using native_readiness_view.old_meaning[OF assms] by (simp add: native_readiness_system_def)

section \<open>The contract of native settlement\<close>

text \<open>
  The subject is a table: each key with the list of its decompositions, a decomposition being the list of
  its premise keys, and the list of answered keys. A key is settled when it is answered and one of its
  decompositions has every premise settled; this least closure is stated here once, and native settlement
  computes exactly it.
\<close>

type_synonym readiness_table = "(factor_term\<times>factor_term list list) list"

definition readiness_entry :: "factor_term\<times>factor_term list list \<Rightarrow> factor_term" where
  "readiness_entry e=Pair_Term (fst e) (data_list_term (map data_list_term (snd e)))"

definition readiness_table_term :: "readiness_table \<Rightarrow> factor_term" where
  "readiness_table_term T=data_list_term (map readiness_entry T)"

definition readiness_table_data :: "readiness_table \<Rightarrow> factor_term list \<Rightarrow> bool" where
  "readiness_table_data T A \<longleftrightarrow> data_elements A \<and>
    (\<forall>e\<in>set T. term_formed (fst e) \<and> self_contained_term (fst e) \<and> (\<forall>h\<in>set (snd e). data_elements h))"

inductive_set table_settled :: "readiness_table \<Rightarrow> factor_term list \<Rightarrow> factor_term set" for T A where
  settle: "k\<in>set A \<Longrightarrow> (k,hs)\<in>set T \<Longrightarrow> h\<in>set hs \<Longrightarrow> \<forall>x\<in>set h. x\<in>table_settled T A \<Longrightarrow>
    k\<in>table_settled T A"

lemma readiness_entries_data:
  assumes "readiness_table_data T A"
  shows "data_elements (map readiness_entry T)"
  using assms by (auto simp: readiness_table_data_def readiness_entry_def data_list_term_formed
    data_list_term_self_contained)

lemma readiness_decompositions_data:
  assumes "readiness_table_data T A" "e\<in>set T"
  shows "data_elements (map data_list_term (snd e))"
  using assms by (auto simp: readiness_table_data_def data_list_term_formed data_list_term_self_contained)

lemma readiness_entry_injective:
  "readiness_entry e=readiness_entry e' \<longleftrightarrow> e=e'"
  by (cases e; cases e') (auto simp: readiness_entry_def data_list_term_injective inj_map_eq_map
    inj_def)

abbreviation readiness_context_term :: "readiness_table \<Rightarrow> factor_term list \<Rightarrow> factor_term" where
  "readiness_context_term T A \<equiv> Pair_Term (readiness_table_term T) (data_list_term A)"

lemma native_settled_selection:
  "(5,t)\<in>positive_meaning native_settled_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  by (rule native_settled_old_meaning) (simp add: bag_comparison_definitions)

theorem native_settled_sound:
  assumes holds: "(200,t)\<in>positive_meaning native_settled_system"
    and shaped: "t=Pair_Term (readiness_context_term T A) z"
  shows "\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)"
proof -
  have "\<forall>z. t=Pair_Term (readiness_context_term T A) z \<longrightarrow>
      (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A))"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=200 \<longrightarrow> (\<forall>z.
      t=Pair_Term (readiness_context_term T A) z \<longrightarrow>
      (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)))", THEN mp], simp_all only: simp_thms)
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses native_settled_system"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning native_settled_system \<and>
        (e=200 \<longrightarrow> (\<forall>z. evaluate_pattern f p=Pair_Term (readiness_context_term T A) z \<longrightarrow>
          (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A))))"
    show "d=200 \<longrightarrow> (\<forall>z. evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_context_term T A) z \<longrightarrow>
      (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)))"
    proof (intro impI allI)
      fix z assume defined: "d=200"
        and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_context_term T A) z"
      have cases: "S=settled_nil_schema \<or> S=settled_step_schema"
        using clause defined by (auto simp: settled_clauses_def)
      then show "\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)"
      proof
        assume "S=settled_nil_schema"
        then have "z=data_list_term []" using shape by (simp add: settled_nil_schema_def)
        then show ?thesis by (intro exI[of _ "[]"]) simp
      next
        assume schema: "S=settled_step_schema"
        have context_fields: "f 0=readiness_table_term T" "f 1=data_list_term A" and z: "z=Pair_Term (f 2) (f 3)"
          using shape schema by (simp_all add: settled_step_schema_def)
        have entry: "(5,Pair_Term (Pair_Term (f 2) (f 4)) (Pair_Term (f 0) (f 5)))\<in>positive_meaning bag_comparison_system"
          using support[rule_format, of 0 5] schema native_settled_selection by (auto simp: settled_step_schema_def)
        obtain x pre post where entry_shape: "Pair_Term (Pair_Term (f 2) (f 4)) (Pair_Term (f 0) (f 5))=
            Pair_Term x (Pair_Term (data_list_term (pre@x#post)) (data_list_term (pre@post)))"
          using data_selection_sound[OF entry] by blast
        have "map readiness_entry T=pre@x#post" and x: "x=Pair_Term (f 2) (f 4)"
          using entry_shape context_fields by (simp_all add: readiness_table_term_def data_list_term_injective)
        then obtain e where e: "e\<in>set T" and ex: "readiness_entry e=Pair_Term (f 2) (f 4)"
          by (metis in_set_conv_decomp list.set_intros(1) set_append Un_iff imageE list.set_map)
        have key: "f 2=fst e" and decompositions: "f 4=data_list_term (map data_list_term (snd e))"
          using ex by (simp_all add: readiness_entry_def)
        have answered: "(5,Pair_Term (f 2) (Pair_Term (f 1) (f 6)))\<in>positive_meaning bag_comparison_system"
          using support[rule_format, of 1 5] schema native_settled_selection by (auto simp: settled_step_schema_def)
        obtain y apre apost where answered_shape: "Pair_Term (f 2) (Pair_Term (f 1) (f 6))=
            Pair_Term y (Pair_Term (data_list_term (apre@y#apost)) (data_list_term (apre@apost)))"
          using data_selection_sound[OF answered] by blast
        have in_answered: "f 2\<in>set A"
          using answered_shape context_fields by (auto simp: data_list_term_injective)
        have chosen: "(5,Pair_Term (f 7) (Pair_Term (f 4) (f 8)))\<in>positive_meaning bag_comparison_system"
          using support[rule_format, of 2 5] schema native_settled_selection by (auto simp: settled_step_schema_def)
        obtain w hpre hpost where chosen_shape: "Pair_Term (f 7) (Pair_Term (f 4) (f 8))=
            Pair_Term w (Pair_Term (data_list_term (hpre@w#hpost)) (data_list_term (hpre@hpost)))"
          using data_selection_sound[OF chosen] by blast
        have "f 7\<in>set (map data_list_term (snd e))"
          using chosen_shape decompositions by (auto simp: data_list_term_injective)
        then obtain h where h: "h\<in>set (snd e)" and fh: "f 7=data_list_term h" by auto
        have below: "\<forall>z. Pair_Term (Pair_Term (f 0) (f 1)) (f 7)=Pair_Term (readiness_context_term T A) z \<longrightarrow>
            (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A))"
          using support[rule_format, of 3 200] schema by (auto simp: settled_step_schema_def)
        obtain hs' where "f 7=data_list_term hs'" "\<forall>x\<in>set hs'. x\<in>table_settled T A"
          using below context_fields by auto
        then have settled_premises: "\<forall>x\<in>set h. x\<in>table_settled T A" using fh by (simp add: data_list_term_injective)
        have first: "f 2\<in>table_settled T A"
          using table_settled.settle[OF in_answered _ h settled_premises] e key by (cases e) auto
        have rest: "\<forall>z. Pair_Term (Pair_Term (f 0) (f 1)) (f 3)=Pair_Term (readiness_context_term T A) z \<longrightarrow>
            (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A))"
          using support[rule_format, of 4 200] schema by (auto simp: settled_step_schema_def)
        obtain zs where "f 3=data_list_term zs" "\<forall>x\<in>set zs. x\<in>table_settled T A"
          using rest context_fields by auto
        then show ?thesis using z first by (intro exI[of _ "f 2#zs"]) simp
      qed
    qed
  qed
  then show ?thesis using shaped by blast
qed

lemma native_settled_nil:
  assumes data: "readiness_table_data T A"
  shows "(200,Pair_Term (readiness_context_term T A) (data_list_term []))\<in>positive_meaning native_settled_system"
proof -
  let ?f="(!) [readiness_table_term T,data_list_term A]"
  have clause: "((200,0),settled_nil_schema)\<in>system_clauses native_settled_system"
    by (simp add: settled_clauses_def)
  have formed: "term_formed (readiness_table_term T)" "term_formed (data_list_term A)"
    using readiness_entries_data[OF data] data
    by (simp_all add: readiness_table_term_def data_list_term_formed readiness_table_data_def)
  have variables: "schema_variables settled_nil_schema={0,1}"
    by (auto simp: settled_nil_schema_def schema_variables_def)
  have result: "(200,evaluate_pattern ?f (schema_conclusion settled_nil_schema))\<in>positive_meaning native_settled_system"
    by (rule ordinary_positive_valuation_step[OF clause])
      (use formed variables in \<open>auto simp: settled_nil_schema_def native_settled_call octets_formed_def\<close>)
  then show ?thesis by (simp add: settled_nil_schema_def)
qed

theorem native_settled_complete:
  assumes data: "readiness_table_data T A" and settled: "k\<in>table_settled T A"
    and rest: "(200,Pair_Term (readiness_context_term T A) (data_list_term zs))\<in>positive_meaning native_settled_system"
  shows "(200,Pair_Term (readiness_context_term T A) (data_list_term (k#zs)))\<in>positive_meaning native_settled_system"
  using settled rest
proof (induction arbitrary: zs rule: table_settled.induct)
  case (settle k hs h zs)
  have settled_list: "(200,Pair_Term (readiness_context_term T A) (data_list_term h))\<in>positive_meaning native_settled_system"
  proof -
    have "\<forall>ys. set ys\<subseteq>set h \<longrightarrow>
        (200,Pair_Term (readiness_context_term T A) (data_list_term ys))\<in>positive_meaning native_settled_system"
    proof (intro allI impI)
      fix ys assume "set ys\<subseteq>set h"
      then show "(200,Pair_Term (readiness_context_term T A) (data_list_term ys))\<in>positive_meaning native_settled_system"
      proof (induction ys)
        case Nil
        show ?case by (rule native_settled_nil[OF data])
      next
        case (Cons y ys)
        then show ?case using settle.IH by auto
      qed
    qed
    then show ?thesis by blast
  qed
  obtain epre epost where entries: "map readiness_entry T=epre@readiness_entry (k,hs)#epost"
    using settle.hyps(2) by (metis in_set_conv_decomp map_append list.simps(9))
  obtain apre apost where answers: "A=apre@k#apost"
    using settle.hyps(1) by (metis in_set_conv_decomp)
  obtain hpre hpost where choices: "map data_list_term hs=hpre@data_list_term h#hpost"
    using settle.hyps(3) by (metis in_set_conv_decomp map_append list.simps(9))
  let ?f="(!) [readiness_table_term T,data_list_term A,k,data_list_term zs,
    data_list_term (map data_list_term hs),data_list_term (epre@epost),data_list_term (apre@apost),
    data_list_term h,data_list_term (hpre@hpost)]"
  have clause: "((200,1),settled_step_schema)\<in>system_clauses native_settled_system"
    by (simp add: settled_clauses_def)
  have entries_data: "data_elements (map readiness_entry T)" by (rule readiness_entries_data[OF data])
  have answers_data: "data_elements A" using data by (simp add: readiness_table_data_def)
  have choices_data: "data_elements (map data_list_term hs)"
    using readiness_decompositions_data[OF data settle.hyps(2)] by simp
  have key_data: "term_formed k \<and> self_contained_term k" using answers_data settle.hyps(1) by blast
  have zs_formed: "term_formed (data_list_term zs)"
    using positive_meaning_formed[OF settle.prems] by (auto simp: schema_call_formed_def pattern_accepts_def)
  have entry_call: "(5,Pair_Term (Pair_Term k (data_list_term (map data_list_term hs)))
      (Pair_Term (readiness_table_term T) (data_list_term (epre@epost))))\<in>positive_meaning native_settled_system"
    using data_selection_complete[of epre "readiness_entry (k,hs)" epost] entries entries_data
    by (simp add: native_settled_selection readiness_table_term_def readiness_entry_def)
  have answer_call: "(5,Pair_Term k (Pair_Term (data_list_term A) (data_list_term (apre@apost))))\<in>positive_meaning native_settled_system"
    using data_selection_complete[of apre k apost] answers answers_data by (simp add: native_settled_selection)
  have choice_call: "(5,Pair_Term (data_list_term h) (Pair_Term (data_list_term (map data_list_term hs))
      (data_list_term (hpre@hpost))))\<in>positive_meaning native_settled_system"
    using data_selection_complete[of hpre "data_list_term h" hpost] choices choices_data
    by (simp add: native_settled_selection)
  have formed_all: "\<forall>a\<in>schema_variables settled_step_schema. term_formed (?f a)"
  proof -
    have vars: "schema_variables settled_step_schema={0,1,2,3,4,5,6,7,8}"
      by (auto simp: settled_step_schema_def schema_variables_def)
    have "term_formed (data_list_term (epre@epost))" "term_formed (data_list_term (apre@apost))"
      "term_formed (data_list_term (hpre@hpost))" "term_formed (data_list_term h)"
      using entries entries_data answers answers_data choices choices_data
      by (auto simp: data_list_term_formed)
    moreover have "term_formed (readiness_table_term T)" "term_formed (data_list_term A)"
      "term_formed (data_list_term (map data_list_term hs))"
      using entries_data answers_data choices_data by (auto simp: readiness_table_term_def data_list_term_formed)
    ultimately show ?thesis using vars key_data zs_formed by auto
  qed
  have result: "(200,evaluate_pattern ?f (schema_conclusion settled_step_schema))\<in>positive_meaning native_settled_system"
  proof (rule ordinary_positive_valuation_step[OF clause _ formed_all])
    show "schema_material_premises settled_step_schema={}" by (simp add: settled_step_schema_def)
    show "schema_call_formed native_settled_system 200 (evaluate_pattern ?f (schema_conclusion settled_step_schema))"
      using formed_all by (auto simp: native_settled_call settled_step_schema_def schema_variables_def)
    show "\<forall>s e p. (s,e,p)\<in>schema_premises settled_step_schema \<longrightarrow>
        (e,evaluate_pattern ?f p)\<in>positive_meaning native_settled_system"
      using entry_call answer_call choice_call settled_list settle.prems by (auto simp: settled_step_schema_def)
  qed
  then show ?case by (simp add: settled_step_schema_def)
qed

theorem native_settled_exact:
  assumes data: "readiness_table_data T A"
  shows "(200,Pair_Term (readiness_context_term T A) z)\<in>positive_meaning native_settled_system \<longleftrightarrow>
    (\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A))"
proof
  assume "(200,Pair_Term (readiness_context_term T A) z)\<in>positive_meaning native_settled_system"
  then show "\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)"
    by (rule native_settled_sound) simp
next
  assume "\<exists>zs. z=data_list_term zs \<and> (\<forall>x\<in>set zs. x\<in>table_settled T A)"
  then obtain zs where z: "z=data_list_term zs" and all: "\<forall>x\<in>set zs. x\<in>table_settled T A" by blast
  have "(200,Pair_Term (readiness_context_term T A) (data_list_term zs))\<in>positive_meaning native_settled_system"
    using all
  proof (induction zs)
    case Nil
    show ?case by (rule native_settled_nil[OF data])
  next
    case (Cons y ys)
    then show ?case using native_settled_complete[OF data] by simp
  qed
  then show "(200,Pair_Term (readiness_context_term T A) z)\<in>positive_meaning native_settled_system" by (simp add: z)
qed

text \<open>
  Native settlement is the stated closure on every table whose keys and decompositions are data: the
  program's least fixed point and the closure coincide, which is what Isabelle verifies of it.
\<close>

section \<open>The contract of native readiness\<close>

lemma native_readiness_clause [simp]:
  "((202,c),S)\<in>system_clauses native_readiness_system \<longleftrightarrow> c=0 \<and> S=ready_schema"
proof -
  have owned: "((202,c),S)\<in>system_clauses native_decompositions_system \<Longrightarrow>
    202\<in>system_definitions native_decompositions_system"
    using native_decompositions_system_formed unfolding schema_system_formed_def by blast
  have absent: "((202,c),S)\<notin>system_clauses native_decompositions_system"
    using owned by (auto simp: bag_comparison_definitions)
  show ?thesis using absent by (auto simp: native_readiness_system_def)
qed

lemma native_readiness_call:
  "schema_call_formed native_readiness_system d t \<longleftrightarrow>
    d\<in>system_definitions native_readiness_system \<and> term_formed t"
proof -
  have prior: "schema_call_formed native_decompositions_system d t \<longleftrightarrow>
      d\<in>system_definitions native_decompositions_system \<and> term_formed t" for d t
    by (rule native_decompositions_call)
  show ?thesis using added_variable_calls[OF native_decompositions_system_formed
    native_readiness_system_formed[unfolded native_readiness_system_def] prior]
    by (simp only: native_readiness_system_def[symmetric])
qed

lemma native_readiness_selection:
  "(5,t)\<in>positive_meaning native_readiness_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  using native_readiness_old_meaning[of 5 t] native_decompositions_old_meaning[of 5 t] native_settled_selection[of t]
  by (simp add: bag_comparison_definitions)

lemma native_readiness_every:
  "(201,t)\<in>positive_meaning native_readiness_system \<longleftrightarrow> (201,t)\<in>positive_meaning native_decompositions_system"
  by (rule native_readiness_old_meaning) simp

theorem native_every_settled_exact:
  assumes data: "readiness_table_data T A"
  shows "(201,Pair_Term (readiness_context_term T A) (data_list_term hs))\<in>positive_meaning native_decompositions_system \<longleftrightarrow>
    (\<forall>H\<in>set hs. \<exists>h. H=data_list_term h \<and> (\<forall>x\<in>set h. x\<in>table_settled T A))"
proof -
  have formed: "term_formed (readiness_context_term T A)"
    using readiness_entries_data[OF data] data
    by (simp add: readiness_table_term_def data_list_term_formed readiness_table_data_def)
  have element: "\<And>H. (200,Pair_Term (readiness_context_term T A) H)\<in>positive_meaning native_decompositions_system \<longleftrightarrow>
      (\<exists>h. H=data_list_term h \<and> (\<forall>x\<in>set h. x\<in>table_settled T A))"
    using native_decompositions_old_meaning[of 200] native_settled_exact[OF data] by simp
  show ?thesis using formed element
    by (simp add: native_decompositions.exact data_list_term_injective)
qed

theorem native_ready_exact:
  assumes data: "readiness_table_data T A" and open_data: "data_elements Opn"
  shows "(202,Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) p)\<in>positive_meaning native_readiness_system \<longleftrightarrow>
    p\<in>set Opn \<and> (\<exists>hs. (p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))"
proof
  assume holds: "(202,Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) p)\<in>positive_meaning native_readiness_system"
  have "\<forall>q. Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) p=Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) q \<longrightarrow>
      q\<in>set Opn \<and> (\<exists>hs. (q,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=202 \<longrightarrow> (\<forall>q.
      t=Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) q \<longrightarrow>
      q\<in>set Opn \<and> (\<exists>hs. (q,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A)))", THEN mp],
      simp_all only: simp_thms)
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses native_readiness_system"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning native_readiness_system \<and>
        (e=202 \<longrightarrow> (\<forall>q. evaluate_pattern f p=Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) q \<longrightarrow>
          q\<in>set Opn \<and> (\<exists>hs. (q,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))))"
    show "d=202 \<longrightarrow> (\<forall>q. evaluate_pattern f (schema_conclusion S)=Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) q \<longrightarrow>
      q\<in>set Opn \<and> (\<exists>hs. (q,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A)))"
    proof (intro impI allI)
      fix q assume defined: "d=202"
        and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) q"
      have schema: "S=ready_schema" using clause defined by simp
      have fields: "f 0=readiness_table_term T" "f 1=data_list_term A" "f 2=data_list_term Opn" "f 3=q"
        using shape schema by (simp_all add: ready_schema_def)
      have opened: "(5,Pair_Term (f 3) (Pair_Term (f 2) (f 4)))\<in>positive_meaning bag_comparison_system"
        using support[rule_format, of 0 5] schema native_readiness_selection by (auto simp: ready_schema_def)
      obtain y opre opost where opened_shape: "Pair_Term (f 3) (Pair_Term (f 2) (f 4))=
          Pair_Term y (Pair_Term (data_list_term (opre@y#opost)) (data_list_term (opre@opost)))"
        using data_selection_sound[OF opened] by blast
      have in_open: "q\<in>set Opn" using opened_shape fields by (auto simp: data_list_term_injective)
      have entry: "(5,Pair_Term (Pair_Term (f 3) (f 5)) (Pair_Term (f 0) (f 6)))\<in>positive_meaning bag_comparison_system"
        using support[rule_format, of 1 5] schema native_readiness_selection by (auto simp: ready_schema_def)
      obtain x pre post where entry_shape: "Pair_Term (Pair_Term (f 3) (f 5)) (Pair_Term (f 0) (f 6))=
          Pair_Term x (Pair_Term (data_list_term (pre@x#post)) (data_list_term (pre@post)))"
        using data_selection_sound[OF entry] by blast
      have "map readiness_entry T=pre@x#post" and x: "x=Pair_Term (f 3) (f 5)"
        using entry_shape fields by (simp_all add: readiness_table_term_def data_list_term_injective)
      then obtain e where e: "e\<in>set T" and ex: "readiness_entry e=Pair_Term (f 3) (f 5)"
        by (metis in_set_conv_decomp list.set_intros(1) set_append Un_iff imageE list.set_map)
      have key: "fst e=q" and decompositions: "f 5=data_list_term (map data_list_term (snd e))"
        using ex fields by (simp_all add: readiness_entry_def)
      have every: "(201,Pair_Term (readiness_context_term T A) (data_list_term (map data_list_term (snd e))))\<in>positive_meaning native_decompositions_system"
        using support[rule_format, of 2 201] schema native_readiness_every fields decompositions
        by (auto simp: ready_schema_def)
      have settled_all: "\<forall>h\<in>set (snd e). \<forall>x\<in>set h. x\<in>table_settled T A"
        using every by (auto simp: native_every_settled_exact[OF data] data_list_term_injective)
      show "q\<in>set Opn \<and> (\<exists>hs. (q,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))"
        using in_open e key settled_all by (cases e) auto
    qed
  qed
  then show "p\<in>set Opn \<and> (\<exists>hs. (p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))" by blast
next
  assume "p\<in>set Opn \<and> (\<exists>hs. (p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A))"
  then obtain hs where in_open: "p\<in>set Opn" and row: "(p,hs)\<in>set T"
    and settled_all: "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A" by blast
  obtain epre epost where entries: "map readiness_entry T=epre@readiness_entry (p,hs)#epost"
    using row by (metis in_set_conv_decomp map_append list.simps(9))
  obtain opre opost where opens: "Opn=opre@p#opost" using in_open by (metis in_set_conv_decomp)
  let ?f="(!) [readiness_table_term T,data_list_term A,data_list_term Opn,p,data_list_term (opre@opost),
    data_list_term (map data_list_term hs),data_list_term (epre@epost)]"
  have entries_data: "data_elements (map readiness_entry T)" by (rule readiness_entries_data[OF data])
  have choices_data: "data_elements (map data_list_term hs)" using readiness_decompositions_data[OF data row] by simp
  have opened_call: "(5,Pair_Term p (Pair_Term (data_list_term Opn) (data_list_term (opre@opost))))\<in>positive_meaning native_readiness_system"
    using data_selection_complete[of opre p opost] opens open_data by (simp add: native_readiness_selection)
  have entry_call: "(5,Pair_Term (Pair_Term p (data_list_term (map data_list_term hs)))
      (Pair_Term (readiness_table_term T) (data_list_term (epre@epost))))\<in>positive_meaning native_readiness_system"
    using data_selection_complete[of epre "readiness_entry (p,hs)" epost] entries entries_data
    by (simp add: native_readiness_selection readiness_table_term_def readiness_entry_def)
  have every_call: "(201,Pair_Term (readiness_context_term T A) (data_list_term (map data_list_term hs)))\<in>positive_meaning native_readiness_system"
    using settled_all by (auto simp: native_readiness_every native_every_settled_exact[OF data])
  have formed_all: "\<forall>a\<in>schema_variables ready_schema. term_formed (?f a)"
  proof -
    have vars: "schema_variables ready_schema={0,1,2,3,4,5,6}"
      by (auto simp: ready_schema_def schema_variables_def)
    have "term_formed (readiness_table_term T)" "term_formed (data_list_term A)" "term_formed (data_list_term Opn)"
      "term_formed p" "term_formed (data_list_term (opre@opost))" "term_formed (data_list_term (map data_list_term hs))"
      "term_formed (data_list_term (epre@epost))"
      using entries_data data open_data in_open choices_data opens entries
      by (auto simp: readiness_table_term_def data_list_term_formed readiness_table_data_def)
    then show ?thesis using vars by auto
  qed
  have result: "(202,evaluate_pattern ?f (schema_conclusion ready_schema))\<in>positive_meaning native_readiness_system"
  proof (rule ordinary_positive_valuation_step[OF _ _ formed_all])
    show "((202,0),ready_schema)\<in>system_clauses native_readiness_system" by simp
    show "schema_material_premises ready_schema={}" by (simp add: ready_schema_def)
    show "schema_call_formed native_readiness_system 202 (evaluate_pattern ?f (schema_conclusion ready_schema))"
      using formed_all by (auto simp: native_readiness_call ready_schema_def schema_variables_def)
    show "\<forall>s e q. (s,e,q)\<in>schema_premises ready_schema \<longrightarrow>
        (e,evaluate_pattern ?f q)\<in>positive_meaning native_readiness_system"
      using opened_call entry_call every_call by (auto simp: ready_schema_def)
  qed
  then show "(202,Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) p)\<in>positive_meaning native_readiness_system"
    by (simp add: ready_schema_def)
qed

text \<open>
  The program's own clauses state the empty payload, which ends every data list, and no other octet:
  problems are compared only for equality. Its contract states its meaning on every table whose keys and
  decompositions are data: settlement is the closure \<open>table_settled\<close>, and a key is ready exactly when
  it is open and every premise of every one of its decompositions is settled. Connecting that closure to
  the development's readiness over its problems, and the selection question evaluating this program on
  its actual subjects, are the next steps; until then the loop's selection still admits a table.
\<close>

end
