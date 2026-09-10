theory Factor_Scoped_Instantiation
  imports Factor_Pattern_Instantiation
begin

section \<open>The enclosing scope and its actual instance\<close>

abbreviation scoped_instantiation_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "scoped_instantiation_argument e u r b t i k \<equiv> term_quotation_argument e u r (Pair_Term b t) i k"

abbreviation scoped_instantiation_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "scoped_instantiation_pattern e u r b t i k \<equiv> term_quotation_pattern e u r (Pattern_Pair b t) i k"

abbreviation scoped_instantiation_result :: "factor_term \<Rightarrow> bool" where
  "scoped_instantiation_result z \<equiv> \<exists>E e u r xs p t Is Ks.
    z=scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
    environment_value_presents E e \<and> distinct xs \<and> distinct Is \<and> distinct Ks \<and>
    scoped_pattern_at E u r p (set Is) (set Ks) \<and>
    term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t"

lemma scoped_instantiation_result_at_source:
  assumes source: "environment_value_presents E e"
  shows "scoped_instantiation_result (scoped_instantiation_argument e u r b t i k) \<longleftrightarrow>
    (\<exists>v a xs p Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> b=binding_rows_term xs \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct xs \<and> distinct Is \<and> distinct Ks \<and> scoped_pattern_at E v a p (set Is) (set Ks) \<and>
      term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t)"
proof
  assume admitted: "scoped_instantiation_result (scoped_instantiation_argument e u r b t i k)"
  obtain F v a xs p Is Ks where parts: "environment_value_presents F e" "u=use_data_term v" "r=Payload_Term a"
    "b=binding_rows_term xs" "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)"
    "distinct xs" "distinct Is" "distinct Ks" "scoped_pattern_at F v a p (set Is) (set Ks)"
    "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p t"
    using admitted by (simp only: factor_term.inject) blast
  have same: "F=E" by (rule environment_value_presents_unique[OF parts(1) source])
  show "\<exists>v a xs p Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> b=binding_rows_term xs \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct xs \<and> distinct Is \<and> distinct Ks \<and> scoped_pattern_at E v a p (set Is) (set Ks) \<and>
      term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t"
    by (rule exI[of _ v], rule exI[of _ a], rule exI[of _ xs], rule exI[of _ p], rule exI[of _ Is], rule exI[of _ Ks])
      (use parts same in auto)
next
  assume "\<exists>v a xs p Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> b=binding_rows_term xs \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct xs \<and> distinct Is \<and> distinct Ks \<and> scoped_pattern_at E v a p (set Is) (set Ks) \<and>
      term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t"
  then obtain v a xs p Is Ks where parts: "u=use_data_term v" "r=Payload_Term a" "b=binding_rows_term xs"
    "i=data_list_term (map Payload_Term Is)" "k=data_list_term (map Payload_Term Ks)" "distinct xs" "distinct Is" "distinct Ks"
    "scoped_pattern_at E v a p (set Is) (set Ks)" "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p t"
    by blast
  show "scoped_instantiation_result (scoped_instantiation_argument e u r b t i k)"
    by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ v], rule exI[of _ a], rule exI[of _ xs],
      rule exI[of _ p], rule exI[of _ t], rule exI[of _ Is], rule exI[of _ Ks]) (use parts source in auto)
qed

section \<open>One ordinary join checks the complete declared scope\<close>

definition scoped_instantiation_schema :: "(nat,nat,nat) factor_schema" where
  "scoped_instantiation_schema=data_rule
    (scoped_instantiation_pattern data_x data_y data_z data_w (Pattern_Variable 4) (Pattern_Variable 5) (Pattern_Variable 6))
    {(0,37,artifact_lookup_pattern data_x data_y (Pattern_Variable 7)),
     (1,34,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) data_z)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 10),
         Pattern_Pair (Pattern_Variable 9) (Pattern_Variable 11)])),
     (2,54,Pattern_Pair (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 10)) (Pattern_Variable 12)),
     (3,55,pattern_instantiation_pattern data_x data_y (Pattern_Variable 12) data_w
       (Pattern_Variable 11) (Pattern_Variable 4) (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 6)),
     (4,6,Pattern_Pair (Pattern_Variable 13) (Pattern_Variable 12)),
     (5,46,collection_join_pattern (data_list_pattern [data_z,Pattern_Variable 8,Pattern_Variable 9])
       (Pattern_Pair (Pattern_Variable 10) (Pattern_Variable 12)) (Pattern_Variable 15)),
     (6,46,collection_join_pattern (Pattern_Variable 15) (Pattern_Variable 14) (Pattern_Variable 16)),
     (7,6,Pattern_Pair (Pattern_Variable 16) (Pattern_Variable 5)),
     (8,49,Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))}"

definition scoped_instantiation_system :: "(nat,nat,nat,nat) schema_system" where
  "scoped_instantiation_system=add_view_definition pattern_instantiation_system 56 data_x {(0,scoped_instantiation_schema)}"

interpretation scoped_instantiation_view: positive_view pattern_instantiation_system 56 data_x "{(0,scoped_instantiation_schema)}"
  by (rule positive_view.intro)
    (auto simp: scoped_instantiation_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma scoped_instantiation_system_formed [simp]: "schema_system_formed scoped_instantiation_system"
  using scoped_instantiation_view.formed by (simp only: scoped_instantiation_system_def)

lemma scoped_instantiation_definitions [simp]:
  "system_definitions scoped_instantiation_system=insert 56 (system_definitions pattern_instantiation_system)"
  by (simp add: scoped_instantiation_system_def)

lemma scoped_instantiation_call:
  "schema_call_formed scoped_instantiation_system d t \<longleftrightarrow>
    d\<in>system_definitions scoped_instantiation_system \<and> term_formed t"
  using added_variable_calls[OF pattern_instantiation_system_formed
    scoped_instantiation_system_formed[unfolded scoped_instantiation_system_def] pattern_instantiation_call]
  by (simp only: scoped_instantiation_system_def[symmetric])

lemma scoped_instantiation_old_meaning:
  assumes "d\<in>system_definitions pattern_instantiation_system"
  shows "(d,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning pattern_instantiation_system"
  using added_definition_preserves_old(2)[OF pattern_instantiation_system_formed
    scoped_instantiation_system_formed[unfolded scoped_instantiation_system_def], of d t] assms
  by (auto simp: scoped_instantiation_system_def)

lemma scoped_instantiation_clause [simp]:
  "((56,c),S)\<in>system_clauses scoped_instantiation_system \<longleftrightarrow> (c,S)\<in>{(0,scoped_instantiation_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses pattern_instantiation_system \<Longrightarrow>
    d\<in>system_definitions pattern_instantiation_system" for d c S
    using pattern_instantiation_system_formed unfolding schema_system_formed_def by blast
  have absent: "((56,c),S)\<notin>system_clauses pattern_instantiation_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: scoped_instantiation_system_def)
qed

lemma scoped_instantiation_components:
  "(37,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(34,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (34,t)\<in>positive_meaning record_admission_system"
  "(54,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (54,t)\<in>positive_meaning binder_admission_system"
  "(55,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (55,t)\<in>positive_meaning pattern_instantiation_system"
  "(6,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(46,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(49,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using scoped_instantiation_old_meaning[of 37 t] pattern_instantiation_components(6)[of t]
    scoped_instantiation_old_meaning[of 34 t] pattern_instantiation_components(7)[of t]
    scoped_instantiation_old_meaning[of 54 t] pattern_instantiation_old_meaning[of 54 t]
    scoped_instantiation_old_meaning[of 55 t]
    scoped_instantiation_old_meaning[of 6 t] pattern_instantiation_components(9)[of t]
    scoped_instantiation_old_meaning[of 46 t] pattern_instantiation_components(8)[of t]
    scoped_instantiation_old_meaning[of 49 t] pattern_instantiation_components(4)[of t] by auto

lemma scoped_instantiation_step:
  assumes lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and rec: "(34,rooted_rows_argument a r (data_list_term [Pair_Term p b,Pair_Term s q]))
      \<in>positive_meaning record_admission_system"
    and scope_read: "(54,rooted_rows_argument a b v)\<in>positive_meaning binder_admission_system"
    and body: "(55,pattern_instantiation_argument e u v table q t w j k)\<in>positive_meaning pattern_instantiation_system"
    and variables: "(6,Pair_Term w v)\<in>positive_meaning bag_comparison_system"
    and prefix: "(46,collection_join_argument (data_list_term [r,p,s]) (Pair_Term b v) d)\<in>positive_meaning data_append_system"
    and joined: "(46,collection_join_argument d j l)\<in>positive_meaning data_append_system"
    and interior: "(6,Pair_Term l i)\<in>positive_meaning bag_comparison_system"
    and boundary: "(49,Pair_Term i k)\<in>positive_meaning payload_disjoint_system"
  shows "(56,scoped_instantiation_argument e u r table t i k)\<in>positive_meaning scoped_instantiation_system"
proof -
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed table" "term_formed t"
    "term_formed i" "term_formed k" "term_formed a" "term_formed p" "term_formed s" "term_formed b" "term_formed q"
    "term_formed v" "term_formed w" "term_formed j" "term_formed d" "term_formed l"
    using schema_call_formed_target[OF positive_meaning_formed[OF lookup]]
      schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]]
      schema_call_formed_target[OF positive_meaning_formed[OF variables]]
      schema_call_formed_target[OF positive_meaning_formed[OF prefix]]
      schema_call_formed_target[OF positive_meaning_formed[OF joined]]
      schema_call_formed_target[OF positive_meaning_formed[OF interior]]
      schema_call_formed_target[OF positive_meaning_formed[OF boundary]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then u else if n=2 then r else if n=3 then table
    else if n=4 then t else if n=5 then i else if n=6 then k else if n=7 then a else if n=8 then p
    else if n=9 then s else if n=10 then b else if n=11 then q else if n=12 then v else if n=13 then w
    else if n=14 then j else if n=15 then d else l"
  have result: "(56,evaluate_pattern ?h (schema_conclusion scoped_instantiation_schema))\<in>positive_meaning scoped_instantiation_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed assms in \<open>auto simp: scoped_instantiation_schema_def schema_variables_def
        scoped_instantiation_call scoped_instantiation_components\<close>)
  show ?thesis using result by (simp add: scoped_instantiation_schema_def)
qed

lemma scoped_instantiation_valuation:
  "(56,z)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}. term_formed (h i)) \<and>
      z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 7) (h 2)
        (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system \<and>
      (54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system \<and>
      (55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
        \<in>positive_meaning pattern_instantiation_system \<and>
      (6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system \<and>
      (46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
        \<in>positive_meaning data_append_system \<and>
      (46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system \<and>
      (6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system \<and>
      (49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system)"
proof
  assume holds: "(56,z)\<in>positive_meaning scoped_instantiation_system"
  have expansion: "(56,z)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    (\<exists>c S h. ((56,c),S)\<in>system_clauses scoped_instantiation_system \<and>
      (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
      z=evaluate_pattern h (schema_conclusion S) \<and> schema_call_formed scoped_instantiation_system 56 z \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning scoped_instantiation_system))"
    by (rule ordinary_positive_entry_valuation) (auto simp: scoped_instantiation_schema_def)
  obtain c S h where clause: "((56,c),S)\<in>system_clauses scoped_instantiation_system"
    and assignment: "\<forall>i\<in>schema_variables S. term_formed (h i)"
    and head: "z=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern h p)\<in>positive_meaning scoped_instantiation_system"
    using holds by (simp only: expansion) blast
  have schema: "S=scoped_instantiation_schema" using clause by auto
  have assigned: "\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}. term_formed (h i)"
    using assignment by (auto simp: schema scoped_instantiation_schema_def schema_variables_def)
  have result: "z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)"
    using head by (simp add: schema scoped_instantiation_schema_def)
  have calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 7) (h 2)
      (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system"
    "(54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system"
    "(55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
      \<in>positive_meaning pattern_instantiation_system"
    "(6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system"
    "(46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
      \<in>positive_meaning data_append_system"
    "(46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system"
    "(6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system"
    "(49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system"
    using support by (auto simp: schema scoped_instantiation_schema_def scoped_instantiation_components)
  show "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}. term_formed (h i)) \<and>
      z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 7) (h 2)
        (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system \<and>
      (54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system \<and>
      (55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
        \<in>positive_meaning pattern_instantiation_system \<and>
      (6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system \<and>
      (46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
        \<in>positive_meaning data_append_system \<and>
      (46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system \<and>
      (6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system \<and>
      (49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system"
    by (rule exI[of _ h]) (use assigned result calls in blast)
next
  assume "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}. term_formed (h i)) \<and>
      z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) \<and>
      (37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system \<and>
      (34,rooted_rows_argument (h 7) (h 2)
        (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system \<and>
      (54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system \<and>
      (55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
        \<in>positive_meaning pattern_instantiation_system \<and>
      (6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system \<and>
      (46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
        \<in>positive_meaning data_append_system \<and>
      (46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system \<and>
      (6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system \<and>
      (49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system"
  then obtain h :: "nat\<Rightarrow>factor_term" where head:
    "z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)"
    and calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 7) (h 2)
      (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system"
    "(54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system"
    "(55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
      \<in>positive_meaning pattern_instantiation_system"
    "(6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system"
    "(46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
      \<in>positive_meaning data_append_system"
    "(46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system"
    "(6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system"
    "(49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system" by blast
  show "(56,z)\<in>positive_meaning scoped_instantiation_system"
    using scoped_instantiation_step[OF calls] by (simp only: head)
qed

section \<open>Exact agreement with the existing scoped-pattern judgment\<close>

theorem scoped_instantiation_sound:
  assumes holds: "(56,z)\<in>positive_meaning scoped_instantiation_system"
  shows "scoped_instantiation_result z"
proof -
  obtain h :: "nat\<Rightarrow>factor_term" where shape:
    "z=scoped_instantiation_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)"
    and calls: "(37,artifact_lookup_argument (h 0) (h 1) (h 7))\<in>positive_meaning artifact_lookup_system"
    "(34,rooted_rows_argument (h 7) (h 2)
      (data_list_term [Pair_Term (h 8) (h 10),Pair_Term (h 9) (h 11)]))\<in>positive_meaning record_admission_system"
    "(54,rooted_rows_argument (h 7) (h 10) (h 12))\<in>positive_meaning binder_admission_system"
    "(55,pattern_instantiation_argument (h 0) (h 1) (h 12) (h 3) (h 11) (h 4) (h 13) (h 14) (h 6))
      \<in>positive_meaning pattern_instantiation_system"
    "(6,Pair_Term (h 13) (h 12))\<in>positive_meaning bag_comparison_system"
    "(46,collection_join_argument (data_list_term [h 2,h 8,h 9]) (Pair_Term (h 10) (h 12)) (h 15))
      \<in>positive_meaning data_append_system"
    "(46,collection_join_argument (h 15) (h 14) (h 16))\<in>positive_meaning data_append_system"
    "(6,Pair_Term (h 16) (h 5))\<in>positive_meaning bag_comparison_system"
    "(49,Pair_Term (h 5) (h 6))\<in>positive_meaning payload_disjoint_system"
    using holds by (simp only: scoped_instantiation_valuation) blast
  obtain E u R where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
    "artifact_at E u R" "artifact_value_presents R (h 7)" using calls(1) by (auto simp: artifact_lookup_exact)
  obtain r a c b q where rec: "h 2=Payload_Term r" "h 8=Payload_Term a" "h 10=Payload_Term c"
    "h 9=Payload_Term b" "h 11=Payload_Term q" "record_at R r [a,b] [c,q]"
    using calls(2) by (simp only: record_admission_pair_fields[OF source(4)]) blast
  obtain Vs where scope_read: "h 12=data_list_term (map Payload_Term Vs)" "distinct Vs" "binder_scope_at R c (set Vs)"
    using calls(3) by (simp only: rec(3) binder_admission_at_source[OF source(4)] factor_term.inject) auto
  obtain xs p Us Js Ks where table: "h 3=binding_rows_term xs" "distinct xs" "term_bindings_formed (set Vs) (set xs)"
    and body: "h 13=data_list_term (map Payload_Term Us)" "h 14=data_list_term (map Payload_Term Js)"
    "h 6=data_list_term (map Payload_Term Ks)" "distinct Us" "distinct Js" "distinct Ks"
    "pattern_quoted_at E u (set Vs) q p (set Js) (set Ks)" "pattern_variables p=set Us" "pattern_instance (set xs) p (h 4)"
    using calls(4) by (simp only: source(2) rec(5) scope_read(1) pattern_instantiation_at_source[OF source(1)]
      data_list_term_injective injective_mapped_lists[OF payload_term_inj] factor_term.inject)
      (auto simp: inj_eq[OF use_data_term_injective])
  have counts: "mset Us=mset Vs"
    using calls(5) by (simp only: body(1) scope_read(1) bag_comparison_lists injective_mapped_multisets[OF payload_term_inj])
  have scope: "set Vs=pattern_variables p" using body(8) mset_eq_setD[OF counts] by simp
  obtain Is where boundary: "h 5=data_list_term (map Payload_Term Is)" "distinct Is" "set Is\<inter>set Ks={}"
    using calls(9) by (auto simp: body(3) payload_disjoint_exact data_list_term_injective
      injective_mapped_lists[OF payload_term_inj])
  have binder_list: "Pair_Term (h 10) (h 12)=data_list_term (map Payload_Term (c#Vs))"
    by (simp add: rec(3) scope_read(1))
  have prefix: "h 15=data_list_term (map Payload_Term (r#a#b#c#Vs))"
    using calls(6) by (simp only: binder_list rec(1,2,4) data_append_at_lists) auto
  have joined: "h 16=data_list_term (map Payload_Term (r#a#b#c#Vs@Js))"
    using calls(7) by (simp only: prefix body(2) data_append_at_lists) auto
  have comparison: "mset (r#a#b#c#Vs@Js)=mset Is"
    using calls(8) by (simp only: joined boundary(1) bag_comparison_lists injective_mapped_multisets[OF payload_term_inj])
  have ports: "distinct [a,b]" "r\<notin>set [a,b]"
    using record_at_preserves_socket_occurrences[OF rec(6)] by auto
  have binder_distinct: "distinct (c#Vs)"
    using scope_read(2) binder_scope_properties(3)[OF scope_read(3)] by simp
  have separation: "insert r (set [a,b])\<inter>(insert c (set Vs)\<union>set Js)={}"
    "insert c (set Vs)\<inter>set Js={}" "set Is=insert r (set [a,b]\<union>insert c (set Vs)\<union>set Js)"
    using quotation_interior_lists[OF ports binder_distinct body(5) boundary(2)] comparison by auto
  have formed: "environment_formed E" using environment_value_presents_formed[OF source(1)] by blast
  have reading: "scoped_pattern_at E u r p (set Is) (set Ks)"
    unfolding scoped_pattern_at_def
    by (intro conjI, rule formed, rule exI[of _ R], rule exI[of _ "[a,b]"], rule exI[of _ c], rule exI[of _ q],
      rule exI[of _ "set Vs"], rule exI[of _ "set Js"])
      (use source(3) rec(6) scope_read(3) body(7) scope separation boundary(3) in auto)
  have bindings: "term_bindings_formed (pattern_variables p) (set xs)" using table(3) scope by simp
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ "h 0"], rule exI[of _ u], rule exI[of _ r], rule exI[of _ xs],
      rule exI[of _ p], rule exI[of _ "h 4"], rule exI[of _ Is], rule exI[of _ Ks])
      (use shape source rec table body boundary reading bindings in auto)
qed

theorem scoped_instantiation_complete:
  assumes quote: "scoped_pattern_at E u r p I K" and source: "environment_value_presents E e"
    and bindings: "term_bindings_formed (pattern_variables p) (set xs)"
    and order: "distinct xs" "distinct Is" "distinct Ks" and collections: "set Is=I" "set Ks=K"
    and inst: "pattern_instance (set xs) p t"
  shows "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
proof -
  obtain R ps b q V J where parts: "artifact_at E u R" "record_at R r ps [b,q]" "binder_scope_at R b V"
    "pattern_quoted_at E u V q p J K" "V=pattern_variables p"
    "insert r (set ps)\<inter>(insert b V\<union>J)={}" "insert b V\<inter>J={}"
    "I=insert r (set ps\<union>insert b V\<union>J)" "I\<inter>K={}"
    using quote by (auto simp: scoped_pattern_at_def)
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have rf: "exact_formed R" using ef parts(1) by (auto simp: environment_formed_def)
  obtain material where presented: "artifact_value_presents R material" using artifact_value_presents_total[OF rf] by blast
  obtain Vs where vs: "set Vs=V" "distinct Vs" using finite_distinct_list[OF binder_scope_properties(1)[OF parts(3)]] by blast
  obtain Js where js: "set Js=J" "distinct Js"
    using finite_distinct_list[of J] pattern_quoted_boundary[OF parts(4)] by blast
  obtain a c where ports: "ps=[a,c]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: length_Suc_conv)
  have ports_distinct: "distinct [a,c]" "r\<notin>set [a,c]"
    using record_at_preserves_socket_occurrences[OF parts(2)] by (auto simp: ports)
  have scope_read: "(54,rooted_rows_argument material (Payload_Term b) (data_list_term (map Payload_Term Vs)))
      \<in>positive_meaning binder_admission_system"
    by (simp only: binder_admission_on_values[OF presented]) (use parts(3) vs in auto)
  have scope_bytes: "\<forall>a\<in>set Vs. octets_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF scope_read]] by (auto simp: data_list_term_formed)
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))
      \<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use vs order(1) scope_bytes bindings parts(5) in auto)
  have used_set: "set Vs=pattern_variables p" using vs(1) parts(5) by simp
  have body: "(55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term q) t (data_list_term (map Payload_Term Vs))
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning pattern_instantiation_system"
    by (rule pattern_instantiation_complete[OF parts(4) source table vs(1) vs(2) js(2) order(3) used_set js(1) collections(2) inst])
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) material)\<in>positive_meaning artifact_lookup_system"
    using source parts(1) presented by (auto simp: artifact_lookup_exact)
  have rec: "(34,rooted_rows_argument material (Payload_Term r)
      (data_list_term [Pair_Term (Payload_Term a) (Payload_Term b),Pair_Term (Payload_Term c) (Payload_Term q)]))
      \<in>positive_meaning record_admission_system"
    by (simp only: record_admission_pair_fields[OF presented]) (use parts(2) in \<open>auto simp: ports\<close>)
  have operands: "octets_formed r" "octets_formed a" "octets_formed c" "octets_formed b"
    "\<forall>a\<in>set Vs. octets_formed a" "\<forall>a\<in>set Js. octets_formed a" "\<forall>a\<in>set Ks. octets_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF rec]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope_read]]
      schema_call_formed_target[OF positive_meaning_formed[OF body]]
    by (auto simp: data_list_term_formed)
  have data: "data_elements (map Payload_Term (r#a#c#b#Vs))" "data_elements (map Payload_Term Js)"
    "data_elements (map Payload_Term Is)" "data_elements (map Payload_Term Ks)" "data_elements (map Payload_Term Vs)"
    using operands by (auto simp: collections(1) parts(8) ports vs(1) js(1))
  have variables: "(6,Pair_Term (data_list_term (map Payload_Term Vs)) (data_list_term (map Payload_Term Vs)))
      \<in>positive_meaning bag_comparison_system"
    by (simp only: bag_comparison_lists) (use data in auto)
  have binder_distinct: "distinct (b#Vs)" using vs binder_scope_properties(3)[OF parts(3)] by auto
  have comparison: "mset (r#a#c#b#Vs@Js)=mset Is"
    using quotation_interior_lists[OF ports_distinct binder_distinct js(2) order(2)]
      parts(6-8) collections(1) by (auto simp: ports vs(1) js(1))
  let ?d="data_list_term (map Payload_Term (r#a#c#b#Vs))"
  let ?j="data_list_term (map Payload_Term (r#a#c#b#Vs@Js))"
  have binder_list: "Pair_Term (Payload_Term b) (data_list_term (map Payload_Term Vs))=data_list_term (map Payload_Term (b#Vs))"
    by simp
  have prefix: "(46,collection_join_argument (data_list_term [Payload_Term r,Payload_Term a,Payload_Term c])
      (Pair_Term (Payload_Term b) (data_list_term (map Payload_Term Vs))) ?d)\<in>positive_meaning data_append_system"
    by (simp only: binder_list data_append_at_lists) (use data in auto)
  have joined: "(46,collection_join_argument ?d (data_list_term (map Payload_Term Js)) ?j)\<in>positive_meaning data_append_system"
    by (simp only: data_append_at_lists) (use data in auto)
  have interior: "(6,Pair_Term ?j (data_list_term (map Payload_Term Is)))\<in>positive_meaning bag_comparison_system"
    by (simp only: bag_comparison_lists injective_mapped_multisets[OF payload_term_inj]) (use data comparison in auto)
  have boundary: "(49,Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning payload_disjoint_system"
    by (simp only: payload_disjoint_lists) (use data order(2,3) collections parts(9) in auto)
  show ?thesis by (rule scoped_instantiation_step[OF lookup rec scope_read body variables prefix joined interior boundary])
qed

theorem scoped_instantiation_exact:
  "(56,z)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> scoped_instantiation_result z"
  using scoped_instantiation_sound scoped_instantiation_complete by blast

corollary scoped_instantiation_at_source:
  assumes source: "environment_value_presents E e"
  shows "(56,scoped_instantiation_argument e u r b t i k)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    (\<exists>v a xs p Is Ks. u=use_data_term v \<and> r=Payload_Term a \<and> b=binding_rows_term xs \<and>
      i=data_list_term (map Payload_Term Is) \<and> k=data_list_term (map Payload_Term Ks) \<and>
      distinct xs \<and> distinct Is \<and> distinct Ks \<and> scoped_pattern_at E v a p (set Is) (set Ks) \<and>
      term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t)"
  by (simp only: scoped_instantiation_exact scoped_instantiation_result_at_source[OF source])

corollary scoped_instantiation_on_values:
  assumes source: "environment_value_presents E e"
  shows "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    distinct xs \<and> distinct Is \<and> distinct Ks \<and> (\<exists>p. scoped_pattern_at E u r p (set Is) (set Ks) \<and>
      term_bindings_formed (pattern_variables p) (set xs) \<and> pattern_instance (set xs) p t)"
  by (subst scoped_instantiation_at_source[OF source],
    simp only: binding_rows_term_injective inj_eq[OF use_data_term_injective] factor_term.inject)
    (auto simp: data_list_term_injective injective_mapped_lists[OF payload_term_inj])

corollary scoped_instantiation_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(56,scoped_instantiation_argument e u r b t i k)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow>
    (56,scoped_instantiation_argument f u r b t i k)\<in>positive_meaning scoped_instantiation_system"
  by (simp only: scoped_instantiation_at_source[OF assms(1)] scoped_instantiation_at_source[OF assms(2)])

corollary scoped_instantiation_orders:
  assumes source: "environment_value_presents E e" and same: "mset xs=mset ys" "mset Is=mset Js" "mset Ks=mset Ls"
  shows "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system
      \<longleftrightarrow>
    (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term ys) t
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))\<in>positive_meaning scoped_instantiation_system"
  using mset_eq_imp_distinct_iff[OF same(1)] mset_eq_imp_distinct_iff[OF same(2)] mset_eq_imp_distinct_iff[OF same(3)]
    mset_eq_setD[OF same(1)] mset_eq_setD[OF same(2)] mset_eq_setD[OF same(3)]
  by (simp only: scoped_instantiation_on_values[OF source])

corollary scoped_instantiation_bindings_exact:
  assumes source: "environment_value_presents E e" and quote: "scoped_pattern_at E u r p I K"
    and holds: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
  shows "rel_dom (set xs)=pattern_variables p"
proof -
  obtain q where raw: "scoped_pattern_at E u r q (set Is) (set Ks)" and table: "term_bindings_formed (pattern_variables q) (set xs)"
    using holds by (simp only: scoped_instantiation_on_values[OF source]) blast
  have same: "p=q" using scoped_pattern_unique[OF quote raw] by blast
  show ?thesis using table same by (simp add: term_bindings_formed_def)
qed

corollary scoped_instantiation_result_unique:
  assumes source: "environment_value_presents E e"
    and first: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    and second: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) s
      (data_list_term (map Payload_Term Js)) (data_list_term (map Payload_Term Ls)))\<in>positive_meaning scoped_instantiation_system"
  shows "t=s \<and> mset Is=mset Js \<and> mset Ks=mset Ls"
proof -
  obtain p where left: "distinct Is" "distinct Ks" "scoped_pattern_at E u r p (set Is) (set Ks)"
    "term_bindings_formed (pattern_variables p) (set xs)" "pattern_instance (set xs) p t"
    using first by (simp only: scoped_instantiation_on_values[OF source]) blast
  obtain q where right: "distinct Js" "distinct Ls" "scoped_pattern_at E u r q (set Js) (set Ls)" "pattern_instance (set xs) q s"
    using second by (simp only: scoped_instantiation_on_values[OF source]) blast
  have same: "p=q" "set Is=set Js" "set Ks=set Ls" using scoped_pattern_unique[OF left(3) right(3)] by auto
  have single: "single_valued (set xs)" using left(4) by (simp add: term_bindings_formed_def)
  have other: "pattern_instance (set xs) p s" using right(4) same(1) by simp
  have terms: "t=s" by (rule pattern_instance_unique[OF single left(5) other])
  show ?thesis using terms same(2,3) left(1,2) right(1,2)
    distinct_source_mset[OF left(1), of Js] distinct_source_mset[OF left(2), of Ls] by auto
qed

corollary scoped_instantiation_total:
  assumes quote: "scoped_pattern_at E u r p I K" and source: "environment_value_presents E e"
    and table: "term_bindings_formed (pattern_variables p) (set xs)"
    and order: "distinct xs" "distinct Is" "distinct Ks" and collections: "set Is=I" "set Ks=K"
  shows "\<exists>!t. (56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
proof -
  have formed: "pattern_formed p" using scoped_pattern_formed[OF quote] by blast
  obtain t where inst: "pattern_instance (set xs) p t"
    using scoped_pattern_has_one_instance[OF table formed subset_refl] by blast
  have first: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    by (rule scoped_instantiation_complete[OF quote source table order collections inst])
  show ?thesis
  proof (rule ex1I[of _ t])
    show "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) t
        (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
      by (rule first)
  next
    fix s
    assume second: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) (binding_rows_term xs) s
        (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning scoped_instantiation_system"
    show "s=t" using scoped_instantiation_result_unique[OF source second first] by blast
  qed
qed

section \<open>One closed native program precedes every future operand\<close>

abbreviation pattern_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "pattern_operation_result d t \<equiv>
    (d=55 \<and> pattern_instantiation_result t) \<or> (d=56 \<and> scoped_instantiation_result t)"

lemma pattern_operations_exact:
  assumes "d\<in>{55,56}"
  shows "(d,t)\<in>positive_meaning scoped_instantiation_system \<longleftrightarrow> pattern_operation_result d t"
proof (cases "d=55")
  case True
  then show ?thesis by (simp add: scoped_instantiation_components(4) pattern_instantiation_exact)
next
  case False
  then have "d=56" using assms by auto
  then show ?thesis by (simp add: scoped_instantiation_exact)
qed

theorem native_pattern_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {55::nat,56} \<and>
    (\<forall>d\<in>{55,56}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> pattern_operation_result d t)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions scoped_instantiation_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions scoped_instantiation_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed scoped_instantiation_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning scoped_instantiation_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF scoped_instantiation_system_formed] by blast
  have sites: "inj_on g {55,56}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {55,56}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{55,56}" and tf: "term_formed t"
    have member: "d\<in>system_definitions scoped_instantiation_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed scoped_instantiation_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning scoped_instantiation_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> pattern_operation_result d t)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member pattern_operations_exact[OF selected] in \<open>auto simp: scoped_instantiation_call\<close>)
  qed
qed

text \<open>
  The body retains its complete admitted table and exact used-variable set.
  Counted comparison with the actual binder family requires every declaration
  to be used. The outer interior contains the record, binder root, every binder
  occurrence, and the body interior. Its counted comparison enforces all required
  separations, and the final slot boundary includes the entire binder scope.

  Every complete table order and every distinct interior and slot order is
  admitted under every complete environment presentation. Malformed operands,
  omitted or extra declarations, repeated metadata, and incorrect instances
  are excluded by the exact all-term theorem. Each valid scoped pattern and
  complete functional table has one resulting term; the table domain is exactly
  the recovered pattern's variables.

  The two entries add four ordinary clauses, preserve all prior meanings, and
  compile to distinct sites in one fixed native program before future operands.
  Its canonical environment is unchanged. Schema and package admission, finite
  correctness evidence, and the complete transition protocol remain separate.
\<close>

end
