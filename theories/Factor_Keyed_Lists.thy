theory Factor_Keyed_Lists
  imports Factor_Coordinate_Admission
begin

section \<open>Keys are checked independently of the values' profiles\<close>

abbreviation pair_list_term :: "(factor_term\<times>factor_term) list \<Rightarrow> factor_term" where
  "pair_list_term xs \<equiv> data_list_term (map (\<lambda>(k,v). Pair_Term k v) xs)"

lemma pair_list_term_injective:
  "pair_list_term xs=pair_list_term ys \<longleftrightarrow> xs=ys"
proof -
  have injective: "inj (\<lambda>(k,v). Pair_Term k v)"
    by (rule injI; rename_tac x y; case_tac x; case_tac y) simp
  show ?thesis by (simp add: data_list_term_injective injective_mapped_lists[OF injective])
qed

abbreviation formed_key_rows :: "(factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "formed_key_rows xs \<equiv> \<forall>(k,v)\<in>set xs. term_formed k \<and> self_contained_term k \<and> term_formed v"

lemma pair_list_term_formed_iff:
  "term_formed (pair_list_term xs) \<longleftrightarrow>
    (\<forall>(k,v)\<in>set xs. term_formed k \<and> term_formed v)"
  by (auto simp: data_list_term_formed)

lemma pair_list_term_formed:
  assumes "formed_key_rows xs"
  shows "term_formed (pair_list_term xs)"
  using assms by (auto simp: pair_list_term_formed_iff)

definition key_absence_nil_schema :: "(nat,nat,nat) factor_schema" where
  "key_absence_nil_schema=data_rule (Pattern_Pair data_x (Pattern_Payload [])) {(0,2,data_x)}"

definition key_absence_cons_schema :: "(nat,nat,nat) factor_schema" where
  "key_absence_cons_schema=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_w))
    {(0,3,Pattern_Pair data_x data_y),(1,20,Pattern_Pair data_x data_w)}"

definition key_absence_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "key_absence_clauses={(0,key_absence_nil_schema),(1,key_absence_cons_schema)}"

definition key_absence_system :: "(nat,nat,nat,nat) schema_system" where
  "key_absence_system=add_view_definition coordinate_admission_system 20 data_x (key_absence_clauses)"

lemma key_absence_system_formed [simp]: "schema_system_formed key_absence_system"
  unfolding key_absence_system_def
  by (rule add_recursive_definition_formed[OF coordinate_admission_system_formed])
    (auto simp: key_absence_clauses_def key_absence_nil_schema_def key_absence_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma key_absence_definitions [simp]:
  "system_definitions key_absence_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}"
  by (auto simp: key_absence_system_def)

lemma key_absence_call:
  "schema_call_formed key_absence_system d t \<longleftrightarrow>
    d\<in>system_definitions key_absence_system \<and> term_formed t"
  using added_variable_calls[OF coordinate_admission_system_formed
    key_absence_system_formed[unfolded key_absence_system_def] coordinate_admission_call]
  by (simp only: key_absence_system_def[symmetric])

lemma key_absence_previous_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19}"
  shows "(d,t)\<in>positive_meaning key_absence_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning coordinate_admission_system"
  using added_definition_preserves_old(2)[OF coordinate_admission_system_formed
    key_absence_system_formed[unfolded key_absence_system_def], of d t] assms
  by (auto simp: key_absence_system_def)

lemma key_absence_clause [simp]:
  "((20,c),S)\<in>system_clauses key_absence_system \<longleftrightarrow> (c,S)\<in>(key_absence_clauses)"
proof -
  have owned: "((d,c),S)\<in>system_clauses coordinate_admission_system \<Longrightarrow>
    d\<in>system_definitions coordinate_admission_system" for d c S
    using coordinate_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((20,c),S)\<notin>system_clauses coordinate_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: key_absence_system_def)
qed

lemma key_absence_base_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6}"
  shows "(d,t)\<in>positive_meaning key_absence_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using key_absence_previous_meaning[of d t] coordinate_admission_old_meaning[of d t]
    environment_comparison_old_meaning[of d t] environment_bag_base_meaning[OF assms, of t] assms by auto

lemma key_absence_data:
  "(2,t)\<in>positive_meaning key_absence_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using key_absence_base_meaning[of 2 t] bag_comparison_recognizes[of t] by auto

lemma key_absence_inequality:
  "(3,Pair_Term x y)\<in>positive_meaning key_absence_system \<longleftrightarrow>
    term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y \<and> x\<noteq>y"
  using key_absence_base_meaning[of 3 "Pair_Term x y"] bag_comparison_old_meaning[of 3 "Pair_Term x y"]
    data_comparison_exact[of "Pair_Term x y"] by auto

theorem key_absence_sound:
  assumes holds: "(20,t)\<in>positive_meaning key_absence_system"
  shows "\<exists>k xs. t=Pair_Term k (pair_list_term xs) \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs)"
proof -
  let ?Q="\<lambda>t. \<exists>k xs. t=Pair_Term k (pair_list_term xs) \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs)"
  have invariant: "(20::nat)=20 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=20 \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses key_absence_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed key_absence_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning key_absence_system \<and>
        (e=20 \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=20 \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=20"
      then have cases: "S=key_absence_nil_schema \<or> S=key_absence_cons_schema"
        using clause by (auto simp: key_absence_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=key_absence_nil_schema"
        have key: "term_formed (f 0) \<and> self_contained_term (f 0)"
          using support schema by (auto simp: key_absence_nil_schema_def key_absence_data)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "[]"])
          (use key in \<open>simp add: schema key_absence_nil_schema_def\<close>)
      next
        assume schema: "S=key_absence_cons_schema"
        have keys: "term_formed (f 0)" "self_contained_term (f 0)" "term_formed (f 1)"
          "self_contained_term (f 1)" "f 0\<noteq>f 1"
          using support[rule_format, of 0 3 "Pattern_Pair data_x data_y"] schema
          by (auto simp: key_absence_cons_schema_def key_absence_inequality)
        have value_formed: "term_formed (f 2)"
          using assignment schema by (auto simp: key_absence_cons_schema_def schema_variables_def)
        obtain xs where tail: "f 3=pair_list_term xs" "formed_key_rows xs" "f 0\<notin>set (map fst xs)"
          using support[rule_format, of 1 20 "Pattern_Pair data_x data_w"] schema
          by (auto simp: key_absence_cons_schema_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "(f 1,f 2)#xs"])
          (use keys value_formed tail in \<open>auto simp: schema key_absence_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem key_absence_complete:
  assumes "term_formed k" "self_contained_term k" "formed_key_rows xs" "k\<notin>set (map fst xs)"
  shows "(20,Pair_Term k (pair_list_term xs))\<in>positive_meaning key_absence_system"
  using assms
proof (induction xs)
  case Nil
  have child: "(2,k)\<in>positive_meaning key_absence_system"
    using Nil.prems by (simp add: key_absence_data)
  have result: "(20,evaluate_pattern (\<lambda>_. k) (schema_conclusion key_absence_nil_schema))
    \<in>positive_meaning key_absence_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use Nil.prems child in \<open>auto simp: key_absence_clauses_def key_absence_nil_schema_def
        schema_variables_def key_absence_call octets_formed_def\<close>)
  show ?case using result by (simp add: key_absence_nil_schema_def)
next
  case (Cons z xs)
  obtain j w where row: "z=(j,w)" by (cases z) auto
  have tail: "(20,Pair_Term k (pair_list_term xs))\<in>positive_meaning key_absence_system"
    using Cons by auto
  have comparison: "(3,Pair_Term k j)\<in>positive_meaning key_absence_system"
    using Cons.prems by (auto simp: row key_absence_inequality)
  let ?f="\<lambda>i::nat. if i=0 then k else if i=1 then j else if i=2 then w else pair_list_term xs"
  have result: "(20,evaluate_pattern ?f (schema_conclusion key_absence_cons_schema))
    \<in>positive_meaning key_absence_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems tail comparison in \<open>auto simp: row key_absence_clauses_def key_absence_cons_schema_def
        schema_variables_def key_absence_call data_list_term_formed\<close>)
  show ?case using result by (simp add: row key_absence_cons_schema_def)
qed

theorem key_absence_exact:
  "(20,t)\<in>positive_meaning key_absence_system \<longleftrightarrow>
    (\<exists>k xs. t=Pair_Term k (pair_list_term xs) \<and> term_formed k \<and> self_contained_term k \<and>
      formed_key_rows xs \<and> k\<notin>set (map fst xs))"
  using key_absence_sound key_absence_complete by blast

section \<open>No key occurs twice in the complete list\<close>

definition keyed_list_cons_schema :: "(nat,nat,nat) factor_schema" where
  "keyed_list_cons_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,20,Pattern_Pair data_x data_z),(1,21,data_z)}"

definition keyed_list_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "keyed_list_clauses={(0,data_list_nil_schema),(1,keyed_list_cons_schema)}"

definition keyed_list_system :: "(nat,nat,nat,nat) schema_system" where
  "keyed_list_system=add_view_definition key_absence_system 21 data_x (keyed_list_clauses)"

lemma keyed_list_system_formed [simp]: "schema_system_formed keyed_list_system"
  unfolding keyed_list_system_def
  by (rule add_recursive_definition_formed[OF key_absence_system_formed])
    (auto simp: keyed_list_clauses_def data_list_nil_schema_def keyed_list_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma keyed_list_definitions [simp]:
  "system_definitions keyed_list_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21}"
  by (auto simp: keyed_list_system_def)

lemma keyed_list_call:
  "schema_call_formed keyed_list_system d t \<longleftrightarrow>
    d\<in>system_definitions keyed_list_system \<and> term_formed t"
  using added_variable_calls[OF key_absence_system_formed
    keyed_list_system_formed[unfolded keyed_list_system_def] key_absence_call]
  by (simp only: keyed_list_system_def[symmetric])

lemma keyed_list_previous_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20}"
  shows "(d,t)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning key_absence_system"
  using added_definition_preserves_old(2)[OF key_absence_system_formed
    keyed_list_system_formed[unfolded keyed_list_system_def], of d t] assms
  by (auto simp: keyed_list_system_def)

lemma keyed_list_clause [simp]:
  "((21,c),S)\<in>system_clauses keyed_list_system \<longleftrightarrow> (c,S)\<in>(keyed_list_clauses)"
proof -
  have owned: "((d,c),S)\<in>system_clauses key_absence_system \<Longrightarrow>
    d\<in>system_definitions key_absence_system" for d c S
    using key_absence_system_formed unfolding schema_system_formed_def by blast
  have absent: "((21,c),S)\<notin>system_clauses key_absence_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: keyed_list_system_def)
qed

theorem keyed_list_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19}"
  shows "(d,t)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning coordinate_admission_system"
  using keyed_list_previous_meaning[of d t] key_absence_previous_meaning[OF assms, of t] assms by auto

lemma keyed_list_absence:
  "(20,t)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    (\<exists>k xs. t=Pair_Term k (pair_list_term xs) \<and> term_formed k \<and> self_contained_term k \<and>
      formed_key_rows xs \<and> k\<notin>set (map fst xs))"
  using keyed_list_previous_meaning[of 20 t] key_absence_exact[of t] by auto

theorem keyed_list_sound:
  assumes holds: "(21,t)\<in>positive_meaning keyed_list_system"
  shows "\<exists>xs. t=pair_list_term xs \<and> formed_key_rows xs \<and> distinct (map fst xs)"
proof -
  let ?Q="\<lambda>t. \<exists>xs. t=pair_list_term xs \<and> formed_key_rows xs \<and> distinct (map fst xs)"
  have invariant: "(21::nat)=21 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=21 \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses keyed_list_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed keyed_list_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning keyed_list_system \<and>
        (e=21 \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=21 \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=21"
      then have cases: "S=data_list_nil_schema \<or> S=keyed_list_cons_schema"
        using clause by (auto simp: keyed_list_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume "S=data_list_nil_schema"
        then show ?thesis by (intro exI[of _ "[]"]) (simp add: data_list_nil_schema_def)
      next
        assume schema: "S=keyed_list_cons_schema"
        obtain xs where tail: "f 2=pair_list_term xs" "formed_key_rows xs" "distinct (map fst xs)"
          using support[rule_format, of 1 21 data_z] schema by (auto simp: keyed_list_cons_schema_def)
        obtain ys where absence: "f 2=pair_list_term ys" "term_formed (f 0)"
          "self_contained_term (f 0)" "f 0\<notin>set (map fst ys)"
          using support[rule_format, of 0 20 "Pattern_Pair data_x data_z"] schema
          by (auto simp: keyed_list_cons_schema_def keyed_list_absence)
        have same: "ys=xs" using tail(1) absence(1) by (simp add: pair_list_term_injective)
        have value_formed: "term_formed (f 1)"
          using assignment schema by (auto simp: keyed_list_cons_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "(f 0,f 1)#xs"])
          (use tail absence same value_formed in \<open>auto simp: schema keyed_list_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem keyed_list_complete:
  assumes "formed_key_rows xs" "distinct (map fst xs)"
  shows "(21,pair_list_term xs)\<in>positive_meaning keyed_list_system"
  using assms
proof (induction xs)
  case Nil
  have result: "(21,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion data_list_nil_schema))
    \<in>positive_meaning keyed_list_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (auto simp: keyed_list_clauses_def data_list_nil_schema_def schema_variables_def
        keyed_list_call octets_formed_def)
  show ?case using result by (simp add: data_list_nil_schema_def)
next
  case (Cons z xs)
  obtain k v where row: "z=(k,v)" by (cases z) auto
  have tail: "(21,pair_list_term xs)\<in>positive_meaning keyed_list_system" using Cons by auto
  have absence: "(20,Pair_Term k (pair_list_term xs))\<in>positive_meaning keyed_list_system"
    using Cons.prems by (auto simp: row keyed_list_absence)
  let ?f="\<lambda>i::nat. if i=0 then k else if i=1 then v else pair_list_term xs"
  have result: "(21,evaluate_pattern ?f (schema_conclusion keyed_list_cons_schema))\<in>positive_meaning keyed_list_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems tail absence in \<open>auto simp: row keyed_list_clauses_def keyed_list_cons_schema_def
        schema_variables_def keyed_list_call data_list_term_formed\<close>)
  show ?case using result by (simp add: row keyed_list_cons_schema_def)
qed

theorem keyed_list_exact:
  "(21,t)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    (\<exists>xs. t=pair_list_term xs \<and> formed_key_rows xs \<and> distinct (map fst xs))"
  using keyed_list_sound keyed_list_complete by blast

section \<open>The same key check applies to relational presentations\<close>

lemma list_all2_pair_entries:
  assumes read: "list_all2 R xs ts"
    and shape: "\<And>z t. R z t \<Longrightarrow> \<exists>v. t=Pair_Term (key z) v"
  shows "\<exists>rows. ts=map (\<lambda>(k,v). Pair_Term k v) rows \<and> map fst rows=map key xs"
  using read
proof (induction xs arbitrary: ts)
  case Nil
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons z xs)
  obtain t us where parts: "ts=t#us" "R z t" "list_all2 R xs us"
    using Cons.prems by (auto simp: list_all2_Cons1)
  obtain v where first: "t=Pair_Term (key z) v" using shape[OF parts(2)] by blast
  obtain rows where tail: "us=map (\<lambda>(k,v). Pair_Term k v) rows" "map fst rows=map key xs"
    using Cons.IH[OF parts(3)] by blast
  show ?case by (intro exI[of _ "(key z,v)#rows"]) (use parts(1) first tail in simp)
qed

theorem keyed_list_relational:
  assumes read: "list_all2 R xs ts" and data: "data_elements ts"
    and shape: "\<And>z t. R z t \<Longrightarrow> \<exists>v. t=Pair_Term (key z) v"
  shows "(21,data_list_term ts)\<in>positive_meaning keyed_list_system \<longleftrightarrow> distinct (map key xs)"
proof -
  obtain rows where parts: "ts=map (\<lambda>(k,v). Pair_Term k v) rows" "map fst rows=map key xs"
    using list_all2_pair_entries[where R=R and key=key, OF read shape] by blast
  have formed: "formed_key_rows rows" using data parts(1) by auto
  have input: "data_list_term ts=pair_list_term rows" using parts(1) by simp
  show ?thesis using formed parts(2)
    by (auto simp: input keyed_list_exact pair_list_term_injective)
qed

theorem keyed_list_encoded_keys:
  assumes read: "list_all2 R xs ts" and data: "data_elements ts" and injective: "inj f"
    and shape: "\<And>z t. R z t \<Longrightarrow> \<exists>v. t=Pair_Term (f (fst z)) v"
  shows "(21,data_list_term ts)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    distinct xs \<and> single_valued (set xs)"
proof -
  have exact: "(21,data_list_term ts)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    distinct (map (\<lambda>z. f (fst z)) xs)"
    by (rule keyed_list_relational[where R=R and key="\<lambda>z. f (fst z)", OF read data shape])
  have mapped: "map (\<lambda>z. f (fst z)) xs=map f (map fst xs)" by simp
  have restricted: "inj_on f (set (map fst xs))" using injective by (auto simp: inj_on_def inj_def)
  have keys: "distinct (map (\<lambda>z. f (fst z)) xs) \<longleftrightarrow> distinct (map fst xs)"
    using restricted by (simp only: mapped distinct_map) blast
  show ?thesis using exact keys by (simp only: distinct_keys_iff)
qed

text \<open>
  The two ordinary recursive definitions inspect the whole supplied list.
  Key absence calls the existing self-contained-data and inequality
  definitions; key uniqueness checks each head key against its entire tail.
  No negative premise or external table predicate is added.

  Keys must be formed self-contained data. Values need only be formed terms;
  a caller supplies any stronger value profile separately. The relational
  presentation theorem therefore transports the same actual program check
  to both artifact rows and source-slot binding rows without choosing an
  order or a canonical representation of their values.

  Earlier meanings are preserved. The complete program has twenty-two
  definitions and forty-two clauses.
\<close>

end
