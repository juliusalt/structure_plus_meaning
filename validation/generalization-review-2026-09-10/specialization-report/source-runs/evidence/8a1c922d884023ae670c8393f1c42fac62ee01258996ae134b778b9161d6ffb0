theory Factor_Row_Values
  imports Factor_Application_Reading
begin

section \<open>Complete row values retain their order and multiplicity\<close>

definition row_values_cons_schema :: "(nat,nat,nat) factor_schema" where
  "row_values_cons_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) (Pattern_Pair data_y data_w))
    {(0,59,Pattern_Pair data_z data_w)}"

definition row_values_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "row_values_clauses={(0,bag_nil_schema),(1,row_values_cons_schema)}"

definition row_values_system :: "(nat,nat,nat,nat) schema_system" where
  "row_values_system=add_view_definition application_reading_system 59 data_x row_values_clauses"

lemma row_values_system_formed [simp]: "schema_system_formed row_values_system"
  unfolding row_values_system_def
  by (rule add_recursive_definition_formed[OF application_reading_system_formed])
    (auto simp: row_values_clauses_def bag_nil_schema_def row_values_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma row_values_definitions [simp]:
  "system_definitions row_values_system=insert 59 (system_definitions application_reading_system)"
  by (simp add: row_values_system_def)

lemma row_values_call:
  "schema_call_formed row_values_system d t \<longleftrightarrow>
    d\<in>system_definitions row_values_system \<and> term_formed t"
  using added_variable_calls[OF application_reading_system_formed
    row_values_system_formed[unfolded row_values_system_def] application_reading_call]
  by (simp only: row_values_system_def[symmetric])

lemma row_values_old_meaning:
  assumes "d\<in>system_definitions application_reading_system"
  shows "(d,t)\<in>positive_meaning row_values_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning application_reading_system"
  using added_definition_preserves_old(2)[OF application_reading_system_formed
    row_values_system_formed[unfolded row_values_system_def], of d t] assms
  by (auto simp: row_values_system_def)

lemma row_values_clause [simp]:
  "((59,c),S)\<in>system_clauses row_values_system \<longleftrightarrow> (c,S)\<in>row_values_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses application_reading_system \<Longrightarrow>
    d\<in>system_definitions application_reading_system" for d c S
    using application_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((59,c),S)\<notin>system_clauses application_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: row_values_system_def)
qed

theorem row_values_sound:
  assumes holds: "(59,t)\<in>positive_meaning row_values_system"
  shows "\<exists>xs. t=Pair_Term (pair_list_term xs) (data_list_term (map snd xs)) \<and>
    term_formed (pair_list_term xs)"
proof -
  let ?Q="\<lambda>t. \<exists>xs. t=Pair_Term (pair_list_term xs) (data_list_term (map snd xs)) \<and>
    term_formed (pair_list_term xs)"
  have invariant: "(59::nat)=59 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=59 \<longrightarrow> ?Q t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses row_values_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed row_values_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning row_values_system \<and>
        (e=59 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=59 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=59"
      then have alternatives: "S=bag_nil_schema \<or> S=row_values_cons_schema"
        using clause by (auto simp: row_values_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=bag_nil_schema"
        show ?thesis by (rule exI[of _ "[]"]) (simp add: schema bag_nil_schema_def octets_formed_def)
      next
        assume schema: "S=row_values_cons_schema"
        have first: "term_formed (h 0)" "term_formed (h 1)"
          using assignment by (auto simp: schema row_values_cons_schema_def schema_variables_def)
        obtain xs where tail: "h 2=pair_list_term xs" "h 3=data_list_term (map snd xs)"
          "term_formed (pair_list_term xs)"
          using support[rule_format, of 0 59 "Pattern_Pair data_z data_w"]
          by (auto simp: schema row_values_cons_schema_def)
        show ?thesis by (rule exI[of _ "(h 0,h 1)#xs"])
          (use first tail in \<open>simp add: schema row_values_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem row_values_complete:
  assumes "term_formed (pair_list_term xs)"
  shows "(59,Pair_Term (pair_list_term xs) (data_list_term (map snd xs)))\<in>positive_meaning row_values_system"
  using assms
proof (induction xs)
  case Nil
  have result: "(59,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion bag_nil_schema))
    \<in>positive_meaning row_values_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (auto simp: row_values_clauses_def bag_nil_schema_def schema_variables_def row_values_call octets_formed_def)
  show ?case using result by (simp add: bag_nil_schema_def)
next
  case (Cons z xs)
  obtain k v where row: "z=(k,v)" by (cases z) auto
  have tail: "(59,Pair_Term (pair_list_term xs) (data_list_term (map snd xs)))\<in>positive_meaning row_values_system"
    using Cons by simp
  let ?h="\<lambda>i::nat. if i=0 then k else if i=1 then v else if i=2 then pair_list_term xs
    else data_list_term (map snd xs)"
  have result: "(59,evaluate_pattern ?h (schema_conclusion row_values_cons_schema))\<in>positive_meaning row_values_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems tail in \<open>auto simp: row row_values_clauses_def row_values_cons_schema_def
        schema_variables_def row_values_call pair_list_term_formed_iff data_list_term_formed\<close>)
  show ?case using result by (simp add: row row_values_cons_schema_def)
qed

theorem row_values_exact:
  "(59,t)\<in>positive_meaning row_values_system \<longleftrightarrow>
    (\<exists>xs. t=Pair_Term (pair_list_term xs) (data_list_term (map snd xs)) \<and>
      term_formed (pair_list_term xs))"
  using row_values_sound row_values_complete by blast

corollary row_values_at_rows:
  "(59,Pair_Term (pair_list_term xs) k)\<in>positive_meaning row_values_system \<longleftrightarrow>
    term_formed (pair_list_term xs) \<and> k=data_list_term (map snd xs)"
  by (simp only: row_values_exact factor_term.inject pair_list_term_injective) auto

text \<open>
  This ordinary recursion projects every second component in the supplied row
  order, preserving repeated values. Both row components may be any formed
  term, including a literal target. No data-only recognizer restricts the result.
  All earlier meanings remain unchanged.
\<close>

end
