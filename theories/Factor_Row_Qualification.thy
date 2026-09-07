theory Factor_Row_Qualification
  imports Factor_Proof_Graph_Membership
begin

section \<open>One ordinary operation qualifies row keys and preserves their values\<close>

abbreviation row_qualification_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "row_qualification_argument u xs ys \<equiv> Pair_Term u (Pair_Term xs ys)"

abbreviation row_qualification_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "row_qualification_pattern u xs ys \<equiv> Pattern_Pair u (Pattern_Pair xs ys)"

abbreviation qualified_rows_term where
  "qualified_rows_term u xs \<equiv> pair_list_term (map (\<lambda>(k,v). (Pair_Term u k,v)) xs)"

abbreviation row_qualification_result :: "factor_term \<Rightarrow> bool" where
  "row_qualification_result z \<equiv> \<exists>u xs.
    z=row_qualification_argument u (pair_list_term xs) (qualified_rows_term u xs) \<and>
    term_formed u \<and> term_formed (pair_list_term xs)"

definition row_qualification_nil_schema :: "(nat,nat,nat) factor_schema" where
  "row_qualification_nil_schema=data_rule
    (row_qualification_pattern data_x (Pattern_Payload []) (Pattern_Payload [])) {}"

definition row_qualification_cons_schema :: "(nat,nat,nat) factor_schema" where
  "row_qualification_cons_schema=data_rule
    (row_qualification_pattern data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w)
      (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z) (Pattern_Variable 4)))
    {(0,99,row_qualification_pattern data_x data_w (Pattern_Variable 4))}"

definition row_qualification_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "row_qualification_clauses={(0,row_qualification_nil_schema),(1,row_qualification_cons_schema)}"

definition row_qualification_system :: "(nat,nat,nat,nat) schema_system" where
  "row_qualification_system=add_view_definition proof_graph_membership_system 99 data_x row_qualification_clauses"

lemma row_qualification_system_formed [simp]: "schema_system_formed row_qualification_system"
  unfolding row_qualification_system_def
  by (rule add_recursive_definition_formed[OF proof_graph_membership_system_formed])
    (auto simp: row_qualification_clauses_def row_qualification_nil_schema_def row_qualification_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma row_qualification_definitions [simp]:
  "system_definitions row_qualification_system=insert 99 (system_definitions proof_graph_membership_system)"
  by (simp add: row_qualification_system_def)

lemma row_qualification_call:
  "schema_call_formed row_qualification_system d t \<longleftrightarrow>
    d\<in>system_definitions row_qualification_system \<and> term_formed t"
  using added_variable_calls[OF proof_graph_membership_system_formed
    row_qualification_system_formed[unfolded row_qualification_system_def] proof_graph_membership_call]
  by (simp only: row_qualification_system_def[symmetric])

lemma row_qualification_old_meaning:
  assumes "d\<in>system_definitions proof_graph_membership_system"
  shows "(d,t)\<in>positive_meaning row_qualification_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_membership_system"
  using added_definition_preserves_old(2)[OF proof_graph_membership_system_formed
    row_qualification_system_formed[unfolded row_qualification_system_def], of d t] assms
  by (auto simp: row_qualification_system_def)

lemma row_qualification_clause [simp]:
  "((99,c),S)\<in>system_clauses row_qualification_system \<longleftrightarrow> (c,S)\<in>row_qualification_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses proof_graph_membership_system \<Longrightarrow> d\<in>system_definitions proof_graph_membership_system" for d c S
    using proof_graph_membership_system_formed unfolding schema_system_formed_def by blast
  have absent: "((99,c),S)\<notin>system_clauses proof_graph_membership_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: row_qualification_system_def)
qed

theorem row_qualification_sound:
  assumes holds: "(99,z)\<in>positive_meaning row_qualification_system"
  shows "row_qualification_result z"
proof -
  let ?Q="\<lambda>z. row_qualification_result z"
  have invariant: "(99::nat)=99 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=99 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses row_qualification_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed row_qualification_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning row_qualification_system \<and>
        (e=99 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=99 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=99"
      then consider (nil) "S=row_qualification_nil_schema" | (cons) "S=row_qualification_cons_schema"
        using clause by (auto simp: row_qualification_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        have formed: "term_formed (h 0)" using assignment by (simp add: nil row_qualification_nil_schema_def schema_variables_def)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "[]"])
          (use formed in \<open>simp add: nil row_qualification_nil_schema_def octets_formed_def\<close>)
      next
        case cons
        obtain xs where tail: "h 3=pair_list_term xs" "h 4=qualified_rows_term (h 0) xs"
          "term_formed (h 0)" "term_formed (pair_list_term xs)"
          using support by (auto simp: cons row_qualification_cons_schema_def)
        have formed: "term_formed (h 1)" "term_formed (h 2)"
          using assignment by (auto simp: cons row_qualification_cons_schema_def schema_variables_def)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "(h 1,h 2)#xs"])
          (use tail formed in \<open>simp add: cons row_qualification_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem row_qualification_complete:
  assumes "term_formed u" "term_formed (pair_list_term xs)"
  shows "(99,row_qualification_argument u (pair_list_term xs) (qualified_rows_term u xs))\<in>positive_meaning row_qualification_system"
  using assms
proof (induction xs)
  case Nil
  have result: "(99,evaluate_pattern (\<lambda>_. u) (schema_conclusion row_qualification_nil_schema))\<in>positive_meaning row_qualification_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use Nil.prems in \<open>auto simp: row_qualification_clauses_def row_qualification_nil_schema_def
        schema_variables_def row_qualification_call octets_formed_def\<close>)
  show ?case using result by (simp add: row_qualification_nil_schema_def)
next
  case (Cons x xs)
  obtain k v where row: "x=(k,v)" by (cases x)
  have tail: "(99,row_qualification_argument u (pair_list_term xs) (qualified_rows_term u xs))\<in>positive_meaning row_qualification_system"
    using Cons by (simp add: row)
  have output_formed: "term_formed (qualified_rows_term u xs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?h="\<lambda>j::nat. if j=0 then u else if j=1 then k else if j=2 then v else if j=3 then pair_list_term xs
    else qualified_rows_term u xs"
  have result: "(99,evaluate_pattern ?h (schema_conclusion row_qualification_cons_schema))\<in>positive_meaning row_qualification_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems tail output_formed in \<open>auto simp: row row_qualification_clauses_def row_qualification_cons_schema_def
        schema_variables_def row_qualification_call\<close>)
  show ?case using result by (simp add: row row_qualification_cons_schema_def)
qed

theorem row_qualification_exact:
  "(99,z)\<in>positive_meaning row_qualification_system \<longleftrightarrow> row_qualification_result z"
  using row_qualification_sound row_qualification_complete by blast

corollary row_qualification_lists:
  "(99,row_qualification_argument u (pair_list_term xs) y)\<in>positive_meaning row_qualification_system \<longleftrightarrow>
    term_formed u \<and> term_formed (pair_list_term xs) \<and> y=qualified_rows_term u xs"
  by (simp only: row_qualification_exact factor_term.inject pair_list_term_injective; blast)

lemma row_qualification_keyed:
  "qualified_rows_term u (map (\<lambda>(k,v). (key k,val v)) xs)=
    keyed_rows_term (\<lambda>k. Pair_Term u (key k)) val xs"
  by (simp add: comp_def case_prod_unfold)

text \<open>
  The same pair construction qualifies binding and premise keys. It preserves
  each value, every row occurrence, and the supplied order. Keys, values, and
  the qualifier may be arbitrary formed terms. Any stronger key profile is
  checked by the operation that uses these rows.
\<close>

end
