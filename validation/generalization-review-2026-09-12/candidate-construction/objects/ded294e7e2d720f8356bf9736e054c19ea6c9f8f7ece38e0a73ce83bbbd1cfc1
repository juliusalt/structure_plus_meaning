theory Factor_Fragment_Equations
  imports Factor_Fragment_Clauses
begin

section \<open>Every equation follows the complete ordinary clause family\<close>

lemma fragment_payload_inside_valuation:
  "(189,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      ((1,h 0)\<in>positive_meaning fragment_system \<and>
      (5,Pair_Term (h 1) (Pair_Term (h 0) (h 2)))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_payload_inside_calls:
  "(189,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x r. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (5,Pair_Term (x) (Pair_Term (p) (r)))\<in>positive_meaning fragment_system))"
proof
  assume "(189,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p x r. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (5,Pair_Term (x) (Pair_Term (p) (r)))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_payload_inside_valuation; blast)
next
  assume "\<exists>p x r. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (5,Pair_Term (x) (Pair_Term (p) (r)))\<in>positive_meaning fragment_system)"
  then obtain p x r where shape: "t=Pair_Term (p) (x)"
    and supported: "((1,p)\<in>positive_meaning fragment_system \<and>
      (5,Pair_Term (x) (Pair_Term (p) (r)))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed x" "term_formed r"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then x else r"
  show "(189,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_payload_inside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_payload_outside_valuation:
  "(190,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      ((1,h 0)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term (h 1) (h 0))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_payload_outside_calls:
  "(190,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [x])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term (x) (p))\<in>positive_meaning fragment_system))"
proof
  assume "(190,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p x. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [x])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term (x) (p))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_payload_outside_valuation; blast)
next
  assume "\<exists>p x. t=Pair_Term (p) (x) \<and>
      ((1,p)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [x])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term (x) (p))\<in>positive_meaning fragment_system)"
  then obtain p x where shape: "t=Pair_Term (p) (x)"
    and supported: "((1,p)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [x])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term (x) (p))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed x"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else x"
  show "(190,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_payload_outside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_attachment_inside_valuation:
  "(191,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
      ((189,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_attachment_inside_calls:
  "(191,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
proof
  assume "(191,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)"
    by (simp only: fragment_attachment_inside_valuation; blast)
next
  assume "\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)"
  then obtain p a b where shape: "t=Pair_Term (p) (Pair_Term (a) (b))"
    and supported: "((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else b"
  show "(191,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_attachment_inside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_attachment_outside_valuation:
  "(192,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
      ((190,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_attachment_outside_calls:
  "(192,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
proof
  assume "(192,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)"
    by (simp only: fragment_attachment_outside_valuation; blast)
next
  assume "\<exists>p a b. t=Pair_Term (p) (Pair_Term (a) (b)) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)"
  then obtain p a b where shape: "t=Pair_Term (p) (Pair_Term (a) (b))"
    and supported: "((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else b"
  show "(192,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_attachment_outside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_incidence_inside_valuation:
  "(193,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      ((189,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_incidence_inside_calls:
  "(193,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (c))\<in>positive_meaning fragment_system))"
proof
  assume "(193,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (c))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_incidence_inside_valuation; blast)
next
  assume "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (c))\<in>positive_meaning fragment_system)"
  then obtain p a b c where shape: "t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c)))"
    and supported: "((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (189,Pair_Term (p) (c))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b" "term_formed c"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else if i=2 then b else c"
  show "(193,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_incidence_inside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_incidence_outside_valuation:
  "(195,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      ((190,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_incidence_outside_calls:
  "(195,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (c))\<in>positive_meaning fragment_system))"
proof
  assume "(195,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (c))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_incidence_outside_valuation; blast)
next
  assume "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      ((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (c))\<in>positive_meaning fragment_system)"
  then obtain p a b c where shape: "t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c)))"
    and supported: "((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (190,Pair_Term (p) (c))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b" "term_formed c"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else if i=2 then b else c"
  show "(195,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_incidence_outside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_incidence_not_inside_valuation:
  "(194,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      (((190,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system)))"
proof -
  have rows: "((194,c),S)\<in>system_clauses fragment_system \<longleftrightarrow>
      (c,S)\<in>fragment_clause_family 194" for c S
    by (rule fragment_clause) simp
  have ordinary: "\<And>c S. ((194,c),S)\<in>system_clauses fragment_system \<Longrightarrow>
      schema_material_premises S={}"
    by (auto simp: rows fragment_clause_family_def fragment_incidence_alternative_schema_def)
  have member: "194\<in>system_definitions fragment_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning fragment_system)"
  let ?B="\<lambda>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
    t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
  have valuation: "(194,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>c S. (c,S)\<in>fragment_clause_family 194 \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=fragment_system and d=194 and t=t, OF ordinary]
    by (simp only: rows fragment_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>fragment_clause_family 194 \<and> F S) \<longleftrightarrow>
      F (fragment_incidence_alternative_schema 190 0) \<or>
      F (fragment_incidence_alternative_schema 190 1) \<or>
      F (fragment_incidence_alternative_schema 190 2)" for F
    by (auto simp: fragment_clause_family_def)
  have fields:
    "?A (fragment_incidence_alternative_schema 190 0) h \<longleftrightarrow> ?B h \<and>
      (190,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system"
    "?A (fragment_incidence_alternative_schema 190 1) h \<longleftrightarrow> ?B h \<and>
      (190,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system"
    "?A (fragment_incidence_alternative_schema 190 2) h \<longleftrightarrow> ?B h \<and>
      (190,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system" for h
    by (auto simp: fragment_incidence_alternative_schema_def schema_variables_def
      numeral_2_eq_2[symmetric] insert_Diff_if)
  show ?thesis by (simp only: valuation clauses fields; blast)
qed

lemma fragment_incidence_not_inside_calls:
  "(194,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)))"
proof
  assume "(194,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
    by (simp only: fragment_incidence_not_inside_valuation; blast)
next
  assume "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
  then obtain p a b c where shape: "t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c)))"
    and supported: "(((190,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((190,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b" "term_formed c"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else if i=2 then b else c"
  show "(194,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_incidence_not_inside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_incidence_not_outside_valuation:
  "(196,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      (((189,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system)))"
proof -
  have rows: "((196,c),S)\<in>system_clauses fragment_system \<longleftrightarrow>
      (c,S)\<in>fragment_clause_family 196" for c S
    by (rule fragment_clause) simp
  have ordinary: "\<And>c S. ((196,c),S)\<in>system_clauses fragment_system \<Longrightarrow>
      schema_material_premises S={}"
    by (auto simp: rows fragment_clause_family_def fragment_incidence_alternative_schema_def)
  have member: "196\<in>system_definitions fragment_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning fragment_system)"
  let ?B="\<lambda>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
    t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
  have valuation: "(196,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>c S. (c,S)\<in>fragment_clause_family 196 \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=fragment_system and d=196 and t=t, OF ordinary]
    by (simp only: rows fragment_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>fragment_clause_family 196 \<and> F S) \<longleftrightarrow>
      F (fragment_incidence_alternative_schema 189 0) \<or>
      F (fragment_incidence_alternative_schema 189 1) \<or>
      F (fragment_incidence_alternative_schema 189 2)" for F
    by (auto simp: fragment_clause_family_def)
  have fields:
    "?A (fragment_incidence_alternative_schema 189 0) h \<longleftrightarrow> ?B h \<and>
      (189,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system"
    "?A (fragment_incidence_alternative_schema 189 1) h \<longleftrightarrow> ?B h \<and>
      (189,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 3])\<in>positive_meaning fragment_system"
    "?A (fragment_incidence_alternative_schema 189 2) h \<longleftrightarrow> ?B h \<and>
      (189,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 1])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [h 2])\<in>positive_meaning fragment_system" for h
    by (auto simp: fragment_incidence_alternative_schema_def schema_variables_def
      numeral_2_eq_2[symmetric] insert_Diff_if)
  show ?thesis by (simp only: valuation clauses fields; blast)
qed

lemma fragment_incidence_not_outside_calls:
  "(196,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system)))"
proof
  assume "(196,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
    by (simp only: fragment_incidence_not_outside_valuation; blast)
next
  assume "\<exists>p a b c. t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c))) \<and>
      (((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))"
  then obtain p a b c where shape: "t=Pair_Term (p) (Pair_Term (a) (Pair_Term (b) (c)))"
    and supported: "(((189,Pair_Term (p) (a))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
      ((189,Pair_Term (p) (c))\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [a])\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [b])\<in>positive_meaning fragment_system))" by blast
  have formed: "term_formed p" "term_formed a" "term_formed b" "term_formed c"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then a else if i=2 then b else c"
  show "(196,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_incidence_not_outside_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_admission_valuation:
  "(205,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4) \<and>
      ((11,artifact_fields_term (h 0) (h 1) (h 2) (h 3))\<in>positive_meaning fragment_system \<and>
      (197,Pair_Term (h 4) (Pair_Term (h 0) (h 5)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (h 5) (h 4))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_admission_calls:
  "(205,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a e b f c q. t=Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c) \<and>
      ((11,artifact_fields_term (a) (e) (b) (f))\<in>positive_meaning fragment_system \<and>
      (197,Pair_Term (c) (Pair_Term (a) (q)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (q) (c))\<in>positive_meaning fragment_system))"
proof
  assume "(205,t)\<in>positive_meaning fragment_system"
  then show "\<exists>a e b f c q. t=Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c) \<and>
      ((11,artifact_fields_term (a) (e) (b) (f))\<in>positive_meaning fragment_system \<and>
      (197,Pair_Term (c) (Pair_Term (a) (q)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (q) (c))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_admission_valuation; blast)
next
  assume "\<exists>a e b f c q. t=Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c) \<and>
      ((11,artifact_fields_term (a) (e) (b) (f))\<in>positive_meaning fragment_system \<and>
      (197,Pair_Term (c) (Pair_Term (a) (q)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (q) (c))\<in>positive_meaning fragment_system)"
  then obtain a e b f c q where shape: "t=Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)"
    and supported: "((11,artifact_fields_term (a) (e) (b) (f))\<in>positive_meaning fragment_system \<and>
      (197,Pair_Term (c) (Pair_Term (a) (q)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (q) (c))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed c" "term_formed q"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then c else q"
  show "(205,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_admission_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_material_valuation:
  "(206,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4)) (h 5) \<and>
      ((205,Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4))\<in>positive_meaning fragment_system \<and>
      (11,h 5)\<in>positive_meaning fragment_system \<and>
      (201,Pair_Term (h 4) (Pair_Term (h 1) (h 6)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (h 4) (Pair_Term (h 2) (h 7)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (h 4) (Pair_Term (h 3) (h 8)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (h 4) (h 6) (h 7) (h 8)) (h 5))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_material_calls:
  "(206,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a e b f c q u w z. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (201,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (b) (w)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (f) (z)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (c) (u) (w) (z)) (q))\<in>positive_meaning fragment_system))"
proof
  assume "(206,t)\<in>positive_meaning fragment_system"
  then show "\<exists>a e b f c q u w z. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (201,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (b) (w)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (f) (z)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (c) (u) (w) (z)) (q))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_material_valuation; blast)
next
  assume "\<exists>a e b f c q u w z. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (201,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (b) (w)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (f) (z)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (c) (u) (w) (z)) (q))\<in>positive_meaning fragment_system)"
  then obtain a e b f c q u w z where shape: "t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q)"
    and supported: "((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (201,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (b) (w)))\<in>positive_meaning fragment_system \<and>
      (199,Pair_Term (c) (Pair_Term (f) (z)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (c) (u) (w) (z)) (q))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed c" "term_formed q" "term_formed u" "term_formed w" "term_formed z"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then c else if i=5 then q else if i=6 then u else if i=7 then w else z"
  show "(206,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_material_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_remainder_valuation:
  "(207,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4)) (h 5) \<and>
      ((205,Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4))\<in>positive_meaning fragment_system \<and>
      (11,h 5)\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (h 4) (Pair_Term (h 0) (h 6)))\<in>positive_meaning fragment_system \<and>
      (202,Pair_Term (h 4) (Pair_Term (h 1) (h 7)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (h 4) (Pair_Term (h 2) (h 8)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (h 4) (Pair_Term (h 3) (h 9)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (h 6) (h 7) (h 8) (h 9)) (h 5))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_remainder_calls:
  "(207,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a e b f c q u w z y. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (202,Pair_Term (c) (Pair_Term (e) (w)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (b) (z)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (f) (y)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (u) (w) (z) (y)) (q))\<in>positive_meaning fragment_system))"
proof
  assume "(207,t)\<in>positive_meaning fragment_system"
  then show "\<exists>a e b f c q u w z y. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (202,Pair_Term (c) (Pair_Term (e) (w)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (b) (z)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (f) (y)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (u) (w) (z) (y)) (q))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_remainder_valuation; blast)
next
  assume "\<exists>a e b f c q u w z y. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (202,Pair_Term (c) (Pair_Term (e) (w)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (b) (z)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (f) (y)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (u) (w) (z) (y)) (q))\<in>positive_meaning fragment_system)"
  then obtain a e b f c q u w z y where shape: "t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q)"
    and supported: "((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (202,Pair_Term (c) (Pair_Term (e) (w)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (b) (z)))\<in>positive_meaning fragment_system \<and>
      (200,Pair_Term (c) (Pair_Term (f) (y)))\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term (artifact_fields_term (u) (w) (z) (y)) (q))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed c" "term_formed q" "term_formed u" "term_formed w" "term_formed z" "term_formed y"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then c else if i=5 then q else if i=6 then u else if i=7 then w else if i=8 then z else y"
  show "(207,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_remainder_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_omission_valuation:
  "(208,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4)) (h 5) \<and>
      ((205,Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4))\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (h 4) (Pair_Term (h 0) (h 6)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (h 6) (h 5))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_omission_calls:
  "(208,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a e b f c q u. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (u) (q))\<in>positive_meaning fragment_system))"
proof
  assume "(208,t)\<in>positive_meaning fragment_system"
  then show "\<exists>a e b f c q u. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (u) (q))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_omission_valuation; blast)
next
  assume "\<exists>a e b f c q u. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (u) (q))\<in>positive_meaning fragment_system)"
  then obtain a e b f c q u where shape: "t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q)"
    and supported: "((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (198,Pair_Term (c) (Pair_Term (a) (u)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (u) (q))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed c" "term_formed q" "term_formed u"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then c else if i=5 then q else u"
  show "(208,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_omission_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_boundary_valuation:
  "(209,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4)) (h 5) \<and>
      ((205,Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3)) (h 4))\<in>positive_meaning fragment_system \<and>
      (203,Pair_Term (h 4) (Pair_Term (h 1) (h 6)))\<in>positive_meaning fragment_system \<and>
      (204,Pair_Term (h 4) (Pair_Term (h 6) (h 7)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (h 7) (h 5))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_boundary_calls:
  "(209,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a e b f c q u w. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (203,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (204,Pair_Term (c) (Pair_Term (u) (w)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (w) (q))\<in>positive_meaning fragment_system))"
proof
  assume "(209,t)\<in>positive_meaning fragment_system"
  then show "\<exists>a e b f c q u w. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (203,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (204,Pair_Term (c) (Pair_Term (u) (w)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (w) (q))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_boundary_valuation; blast)
next
  assume "\<exists>a e b f c q u w. t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q) \<and>
      ((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (203,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (204,Pair_Term (c) (Pair_Term (u) (w)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (w) (q))\<in>positive_meaning fragment_system)"
  then obtain a e b f c q u w where shape: "t=Pair_Term (Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c)) (q)"
    and supported: "((205,Pair_Term (artifact_fields_term (a) (e) (b) (f)) (c))\<in>positive_meaning fragment_system \<and>
      (203,Pair_Term (c) (Pair_Term (e) (u)))\<in>positive_meaning fragment_system \<and>
      (204,Pair_Term (c) (Pair_Term (u) (w)))\<in>positive_meaning fragment_system \<and>
      (6,Pair_Term (w) (q))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f" "term_formed c" "term_formed q" "term_formed u" "term_formed w"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f else if i=4 then c else if i=5 then q else if i=6 then u else w"
  show "(209,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_boundary_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

lemma fragment_report_valuation:
  "(210,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))) \<and>
      ((206,Pair_Term (h 0) (h 1))\<in>positive_meaning fragment_system \<and>
      (209,Pair_Term (h 0) (h 2))\<in>positive_meaning fragment_system \<and>
      (207,Pair_Term (h 0) (h 3))\<in>positive_meaning fragment_system))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: fragment_clause fragment_clause_family_def fragment_schema_defs
      schema_variables_def fragment_call)

lemma fragment_report_calls:
  "(210,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p m b r. t=Pair_Term (p) (Pair_Term (m) (Pair_Term (b) (r))) \<and>
      ((206,Pair_Term (p) (m))\<in>positive_meaning fragment_system \<and>
      (209,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (207,Pair_Term (p) (r))\<in>positive_meaning fragment_system))"
proof
  assume "(210,t)\<in>positive_meaning fragment_system"
  then show "\<exists>p m b r. t=Pair_Term (p) (Pair_Term (m) (Pair_Term (b) (r))) \<and>
      ((206,Pair_Term (p) (m))\<in>positive_meaning fragment_system \<and>
      (209,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (207,Pair_Term (p) (r))\<in>positive_meaning fragment_system)"
    by (simp only: fragment_report_valuation; blast)
next
  assume "\<exists>p m b r. t=Pair_Term (p) (Pair_Term (m) (Pair_Term (b) (r))) \<and>
      ((206,Pair_Term (p) (m))\<in>positive_meaning fragment_system \<and>
      (209,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (207,Pair_Term (p) (r))\<in>positive_meaning fragment_system)"
  then obtain p m b r where shape: "t=Pair_Term (p) (Pair_Term (m) (Pair_Term (b) (r)))"
    and supported: "((206,Pair_Term (p) (m))\<in>positive_meaning fragment_system \<and>
      (209,Pair_Term (p) (b))\<in>positive_meaning fragment_system \<and>
      (207,Pair_Term (p) (r))\<in>positive_meaning fragment_system)" by blast
  have formed: "term_formed p" "term_formed m" "term_formed b" "term_formed r"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then m else if i=2 then b else r"
  show "(210,t)\<in>positive_meaning fragment_system"
    by (simp only: fragment_report_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

text \<open>
  These equations expose all ordinary premises and every source coordinate.
  The existential valuation supplies only the finite clause assignment; it
  adds no semantic witness or observation primitive. Admission of assigned
  terms follows from the actual positive child calls.
\<close>

end
