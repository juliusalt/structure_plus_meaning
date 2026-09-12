theory Factor_Keyed_Row_Join
  imports Factor_Row_Qualification
begin

section \<open>Each input row requires one complete child value\<close>

abbreviation keyed_row_join_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "keyed_row_join_argument b xs ys \<equiv> Pair_Term b (Pair_Term xs ys)"

abbreviation keyed_row_join_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "keyed_row_join_pattern b xs ys \<equiv> Pattern_Pair b (Pattern_Pair xs ys)"

fun keyed_row_join ::
  "factor_term \<Rightarrow> (factor_term\<times>factor_term) list \<Rightarrow>
    (factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "keyed_row_join b [] qs \<longleftrightarrow> qs=[]"
| "keyed_row_join b ((s,n)#ds) qs \<longleftrightarrow>
    term_formed s \<and> (\<exists>js v ts. b=pair_list_term js \<and> formed_key_rows js \<and>
      term_formed n \<and> self_contained_term n \<and> key_values n js=[v] \<and>
      qs=(s,v)#ts \<and> keyed_row_join b ds ts)"

abbreviation keyed_row_join_result :: "factor_term \<Rightarrow> bool" where
  "keyed_row_join_result z \<equiv> \<exists>b ds qs.
    z=keyed_row_join_argument b (pair_list_term ds) (pair_list_term qs) \<and>
    term_formed b \<and> keyed_row_join b ds qs"

lemma keyed_row_join_formed:
  assumes "keyed_row_join b ds qs"
  shows "term_formed (pair_list_term ds) \<and> term_formed (pair_list_term qs)"
  using assms
proof (induction ds arbitrary: qs)
  case Nil
  then show ?case by (simp add: octets_formed_def)
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  obtain js v ts where parts: "formed_key_rows js" "term_formed s" "term_formed n"
    "key_values n js=[v]" "qs=(s,v)#ts" "keyed_row_join b ds ts"
    using Cons.prems by (simp only: row keyed_row_join.simps; blast)
  have member: "(n,v)\<in>set js" using parts(4) key_values_set[of n js] by auto
  have row_value: "term_formed v" using parts(1) member by auto
  show ?case using Cons.IH[OF parts(6)] parts(2,3,5) row_value by (simp add: row)
qed

lemma keyed_row_join_entries:
  assumes joined: "keyed_row_join (pair_list_term js) ds qs"
  shows "map fst qs=map fst ds \<and>
    (\<forall>s n. (s,n)\<in>set ds \<longrightarrow> (\<exists>v. (s,v)\<in>set qs \<and> key_values n js=[v])) \<and>
    (\<forall>s v. (s,v)\<in>set qs \<longrightarrow> (\<exists>n. (s,n)\<in>set ds \<and> key_values n js=[v]))"
  using joined
proof (induction ds arbitrary: qs)
  case Nil
  then show ?case by simp
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  obtain v ts where parts: "key_values n js=[v]" "qs=(s,v)#ts"
    "keyed_row_join (pair_list_term js) ds ts"
    using Cons.prems by (simp only: row keyed_row_join.simps pair_list_term_injective; blast)
  show ?case using Cons.IH[OF parts(3)] parts(1,2) by (auto simp: row; blast)
qed

lemma keyed_row_join_row_values:
  assumes rows: "formed_key_rows js"
    and fibres: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
      term_formed (key s) \<and> term_formed (target n) \<and> self_contained_term (target n) \<and>
      key_values (target n) js=[val (f s n)]"
  shows "keyed_row_join (pair_list_term js)
    (map (\<lambda>(s,n). (key s,target n)) ds) (map (\<lambda>(s,n). (key s,val (f s n))) ds)"
  using fibres
proof (induction ds)
  case Nil
  then show ?case by simp
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  have first: "term_formed (key s)" "term_formed (target n)" "self_contained_term (target n)"
    "key_values (target n) js=[val (f s n)]" using Cons.prems by (auto simp: row)
  have tail: "keyed_row_join (pair_list_term js)
      (map (\<lambda>(s,n). (key s,target n)) ds) (map (\<lambda>(s,n). (key s,val (f s n))) ds)"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case by (simp only: row list.map case_prod_conv keyed_row_join.simps)
    (use rows first tail in blast)
qed

lemma keyed_row_join_mapped:
  assumes rows: "formed_key_rows js"
    and fibres: "\<forall>s n. (s,n)\<in>set ds \<longrightarrow>
      term_formed (key s) \<and> term_formed (target n) \<and> self_contained_term (target n) \<and>
      key_values (target n) js=[val (f s)]"
  shows "keyed_row_join (pair_list_term js)
    (map (\<lambda>(s,n). (key s,target n)) ds) (map (\<lambda>(s,n). (key s,val (f s))) ds)"
  by (rule keyed_row_join_row_values[OF rows, where f="\<lambda>s n. f s"]) (rule fibres)

lemma keyed_row_join_output_unique:
  assumes "keyed_row_join b ds xs" "keyed_row_join b ds ys"
  shows "xs=ys"
  using assms
proof (induction ds arbitrary: xs ys)
  case Nil
  then show ?case by simp
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  obtain js v tail where first: "b=pair_list_term js" "key_values n js=[v]"
    "xs=(s,v)#tail" "keyed_row_join b ds tail"
    using Cons.prems(1) by (simp only: row keyed_row_join.simps; blast)
  obtain ks w rest where second: "b=pair_list_term ks" "key_values n ks=[w]"
    "ys=(s,w)#rest" "keyed_row_join b ds rest"
    using Cons.prems(2) by (simp only: row keyed_row_join.simps; blast)
  have same: "js=ks" using first(1) second(1) by (simp only: pair_list_term_injective)
  have selected_value: "v=w" using first(2) second(2) same by simp
  have tail: "tail=rest" by (rule Cons.IH[OF first(4) second(4)])
  show ?case by (simp only: first(3) second(3) selected_value tail)
qed

definition keyed_row_join_nil_schema :: "(nat,nat,nat) factor_schema" where
  "keyed_row_join_nil_schema=data_rule
    (keyed_row_join_pattern data_x (Pattern_Payload []) (Pattern_Payload [])) {}"

definition keyed_row_join_cons_schema :: "(nat,nat,nat) factor_schema" where
  "keyed_row_join_cons_schema=data_rule
    (keyed_row_join_pattern data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w)
      (Pattern_Pair (Pattern_Pair data_y (Pattern_Variable 4)) (Pattern_Variable 5)))
    {(0,28,Pattern_Pair data_z (Pattern_Pair data_x (data_list_pattern [Pattern_Variable 4]))),
     (1,100,keyed_row_join_pattern data_x data_w (Pattern_Variable 5))}"

definition keyed_row_join_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "keyed_row_join_clauses={(0,keyed_row_join_nil_schema),(1,keyed_row_join_cons_schema)}"

definition keyed_row_join_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_row_join_system=add_view_definition row_qualification_system 100 data_x keyed_row_join_clauses"

lemma keyed_row_join_system_formed [simp]: "schema_system_formed keyed_row_join_system"
  unfolding keyed_row_join_system_def
  by (rule add_recursive_definition_formed[OF row_qualification_system_formed])
    (auto simp: keyed_row_join_clauses_def keyed_row_join_nil_schema_def keyed_row_join_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma keyed_row_join_definitions [simp]:
  "system_definitions keyed_row_join_system=insert 100 (system_definitions row_qualification_system)"
  by (simp add: keyed_row_join_system_def)

lemma keyed_row_join_call:
  "schema_call_formed keyed_row_join_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_row_join_system \<and> term_formed t"
  using added_variable_calls[OF row_qualification_system_formed
    keyed_row_join_system_formed[unfolded keyed_row_join_system_def] row_qualification_call]
  by (simp only: keyed_row_join_system_def[symmetric])

lemma keyed_row_join_old_meaning:
  assumes "d\<in>system_definitions row_qualification_system"
  shows "(d,t)\<in>positive_meaning keyed_row_join_system \<longleftrightarrow> (d,t)\<in>positive_meaning row_qualification_system"
  using added_definition_preserves_old(2)[OF row_qualification_system_formed
    keyed_row_join_system_formed[unfolded keyed_row_join_system_def], of d t] assms
  by (auto simp: keyed_row_join_system_def)

lemma keyed_row_join_clause [simp]:
  "((100,c),S)\<in>system_clauses keyed_row_join_system \<longleftrightarrow> (c,S)\<in>keyed_row_join_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses row_qualification_system \<Longrightarrow> d\<in>system_definitions row_qualification_system" for d c S
    using row_qualification_system_formed unfolding schema_system_formed_def by blast
  have absent: "((100,c),S)\<notin>system_clauses row_qualification_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: keyed_row_join_system_def)
qed

lemma keyed_row_join_graph_meaning:
  assumes "d\<in>system_definitions proof_graph_membership_system"
  shows "(d,t)\<in>positive_meaning keyed_row_join_system \<longleftrightarrow> (d,t)\<in>positive_meaning proof_graph_membership_system"
  using keyed_row_join_old_meaning[of d t] row_qualification_old_meaning[OF assms, of t] assms by auto

lemma keyed_row_join_fibre:
  "(28,t)\<in>positive_meaning keyed_row_join_system \<longleftrightarrow> (28,t)\<in>positive_meaning key_fibre_system"
  using keyed_row_join_graph_meaning[of 28 t] proof_graph_membership_old_meaning[of 28 t]
    proof_graph_admission_components(2)[of t] by auto

lemma keyed_row_join_empty:
  assumes "term_formed b"
  shows "(100,keyed_row_join_argument b (Payload_Term []) (Payload_Term []))\<in>positive_meaning keyed_row_join_system"
proof -
  have result: "(100,evaluate_pattern (\<lambda>_. b) (schema_conclusion keyed_row_join_nil_schema))\<in>positive_meaning keyed_row_join_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use assms in \<open>auto simp: keyed_row_join_clauses_def keyed_row_join_nil_schema_def
        schema_variables_def keyed_row_join_call octets_formed_def\<close>)
  show ?thesis using result by (simp add: keyed_row_join_nil_schema_def)
qed

lemma keyed_row_join_step:
  assumes key: "term_formed s"
    and lookup: "(28,key_fibre_argument n b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
    and tail: "(100,keyed_row_join_argument b ds qs)\<in>positive_meaning keyed_row_join_system"
  shows "(100,keyed_row_join_argument b (Pair_Term (Pair_Term s n) ds) (Pair_Term (Pair_Term s v) qs))
    \<in>positive_meaning keyed_row_join_system"
proof -
  have formed: "term_formed b" "term_formed n" "term_formed v" "term_formed ds" "term_formed qs"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?h="\<lambda>j::nat. if j=0 then b else if j=1 then s else if j=2 then n else if j=3 then ds else if j=4 then v else qs"
  have result: "(100,evaluate_pattern ?h (schema_conclusion keyed_row_join_cons_schema))\<in>positive_meaning keyed_row_join_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use assms formed in \<open>auto simp: keyed_row_join_clauses_def keyed_row_join_cons_schema_def
        schema_variables_def keyed_row_join_call keyed_row_join_fibre\<close>)
  show ?thesis using result by (simp add: keyed_row_join_cons_schema_def)
qed

theorem keyed_row_join_sound:
  assumes holds: "(100,z)\<in>positive_meaning keyed_row_join_system"
  shows "keyed_row_join_result z"
proof -
  let ?Q="\<lambda>z. keyed_row_join_result z"
  have invariant: "(100::nat)=100 \<longrightarrow> ?Q z"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d z. d=100 \<longrightarrow> ?Q z"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses keyed_row_join_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed keyed_row_join_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning keyed_row_join_system \<and>
        (e=100 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=100 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=100"
      then consider (nil) "S=keyed_row_join_nil_schema" | (cons) "S=keyed_row_join_cons_schema"
        using clause by (auto simp: keyed_row_join_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof cases
        case nil
        have formed: "term_formed (h 0)" using assignment by (simp add: nil keyed_row_join_nil_schema_def schema_variables_def)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "[]"], rule exI[of _ "[]"])
          (use formed in \<open>simp add: nil keyed_row_join_nil_schema_def\<close>)
      next
        case cons
        have recursive: "?Q (keyed_row_join_argument (h 0) (h 3) (h 5))"
          using support[rule_format, of 1 100 "keyed_row_join_pattern data_x data_w (Pattern_Variable 5)"]
          by (simp add: cons keyed_row_join_cons_schema_def)
        obtain ds qs where tail: "h 3=pair_list_term ds" "h 5=pair_list_term qs"
          "term_formed (h 0)" "keyed_row_join (h 0) ds qs"
          using recursive by (simp only: factor_term.inject; blast)
        have lookup: "(28,key_fibre_argument (h 2) (h 0) (data_list_term [h 4]))\<in>positive_meaning key_fibre_system"
          using support by (auto simp: cons keyed_row_join_cons_schema_def keyed_row_join_fibre)
        obtain js where rows: "h 0=pair_list_term js" "formed_key_rows js" "term_formed (h 2)"
          "self_contained_term (h 2)" "key_values (h 2) js=[h 4]"
          by (rule key_fibre_singleton_rows[OF lookup]) (rule that; assumption)
        have key: "term_formed (h 1)" using assignment by (auto simp: cons keyed_row_join_cons_schema_def schema_variables_def)
        have joined: "keyed_row_join (h 0) ((h 1,h 2)#ds) ((h 1,h 4)#qs)"
          by (simp only: keyed_row_join.simps; use rows key tail(4) in blast)
        show ?thesis by (rule exI[of _ "h 0"], rule exI[of _ "(h 1,h 2)#ds"], rule exI[of _ "(h 1,h 4)#qs"])
          (use tail joined in \<open>simp add: cons keyed_row_join_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem keyed_row_join_complete:
  assumes "term_formed b" "keyed_row_join b ds qs"
  shows "(100,keyed_row_join_argument b (pair_list_term ds) (pair_list_term qs))\<in>positive_meaning keyed_row_join_system"
  using assms
proof (induction ds arbitrary: qs)
  case Nil
  then show ?case using keyed_row_join_empty by auto
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  obtain js v ts where parts: "term_formed s" "b=pair_list_term js" "formed_key_rows js"
    "term_formed n" "self_contained_term n" "key_values n js=[v]" "qs=(s,v)#ts" "keyed_row_join b ds ts"
    using Cons.prems(2) by (simp only: row keyed_row_join.simps; blast)
  have lookup: "(28,key_fibre_argument n b (data_list_term [v]))\<in>positive_meaning key_fibre_system"
    by (simp only: parts(2) key_fibre_lists) (use parts(3-6) in simp)
  have tail: "(100,keyed_row_join_argument b (pair_list_term ds) (pair_list_term ts))\<in>positive_meaning keyed_row_join_system"
    by (rule Cons.IH[OF Cons.prems(1) parts(8)])
  show ?case using keyed_row_join_step[OF parts(1) lookup tail] by (simp add: row parts(7))
qed

theorem keyed_row_join_exact:
  "(100,z)\<in>positive_meaning keyed_row_join_system \<longleftrightarrow> keyed_row_join_result z"
  using keyed_row_join_sound keyed_row_join_complete by blast

corollary keyed_row_join_lists:
  "(100,keyed_row_join_argument b (pair_list_term ds) (pair_list_term qs))\<in>positive_meaning keyed_row_join_system \<longleftrightarrow>
    term_formed b \<and> keyed_row_join b ds qs"
  by (simp only: keyed_row_join_exact factor_term.inject pair_list_term_injective; blast)

text \<open>
  Every input row keeps its key and requires a singleton complete fibre at its
  target. Missing targets and repeated target-key occurrences are rejected.
  Different rows may share one target. Their values are copied unchanged and
  need only be formed terms, including when they contain literal targets.

  The empty input needs only a formed table operand. A nonempty input checks
  the whole table through its actual lookups. Each output row corresponds to
  one input occurrence in the same order; no global key distinctness condition
  is imposed by this join.
\<close>

end
