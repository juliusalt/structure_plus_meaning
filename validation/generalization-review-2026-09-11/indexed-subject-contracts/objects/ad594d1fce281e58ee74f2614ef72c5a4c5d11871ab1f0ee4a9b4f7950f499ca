theory Factor_Generation_Equations
  imports Factor_Generation_Clauses
begin

section \<open>Comparison admits both complete records before inspecting their fields\<close>

lemma generation_identity_valuation:
  "(140,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
        (Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7)))) \<and>
      (139,Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))\<in>positive_meaning generation_value_system \<and>
      (139,Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7))))\<in>positive_meaning generation_value_system \<and>
      (135,Pair_Term (h 0) (h 4))\<in>positive_meaning generation_value_system \<and>
      (145,Pair_Term (h 1) (h 5))\<in>positive_meaning generation_value_system \<and>
      (135,Pair_Term (h 2) (h 6))\<in>positive_meaning generation_value_system \<and>
      (135,Pair_Term (h 3) (h 7))\<in>positive_meaning generation_value_system)"
proof -
  have ordinary: "\<And>c S. ((140,c),S)\<in>system_clauses generation_value_system \<Longrightarrow> schema_material_premises S={}"
    by (auto simp: generation_identity_schema_def)
  show ?thesis using ordinary_positive_entry_valuation[where P=generation_value_system and d=140 and t=t, OF ordinary]
    by (auto simp: generation_value_call generation_identity_schema_def schema_variables_def)
qed

lemma generation_difference_valuation:
  "(141,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
        (Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7)))) \<and>
      (139,Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))\<in>positive_meaning generation_value_system \<and>
      (139,Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7))))\<in>positive_meaning generation_value_system \<and>
      ((136,Pair_Term (h 0) (h 4))\<in>positive_meaning generation_value_system \<or>
       (146,Pair_Term (h 1) (h 5))\<in>positive_meaning generation_value_system \<or>
       (136,Pair_Term (h 2) (h 6))\<in>positive_meaning generation_value_system \<or>
       (136,Pair_Term (h 3) (h 7))\<in>positive_meaning generation_value_system))"
proof -
  have ordinary: "\<And>c S. ((141,c),S)\<in>system_clauses generation_value_system \<Longrightarrow> schema_material_premises S={}"
    by (auto simp: generation_difference_schema_def)
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning generation_value_system)"
  let ?B="\<lambda>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
    t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))
      (Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7)))) \<and>
    (139,Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3))))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term (h 4) (Pair_Term (h 5) (Pair_Term (h 6) (h 7))))\<in>positive_meaning generation_value_system"
  have valuation: "(141,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (\<exists>c S. (c,S)\<in>generation_group_clauses 141 \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=generation_value_system and d=141 and t=t, OF ordinary]
    by (simp only: generation_value_clauses generation_value_call generation_value_definitions
      generation_group_clauses_def if_True if_False; auto)
  have clauses: "(\<exists>c S. (c,S)\<in>generation_group_clauses 141 \<and> F S) \<longleftrightarrow>
      F (generation_difference_schema 0) \<or> F (generation_difference_schema 1) \<or>
      F (generation_difference_schema 2) \<or> F (generation_difference_schema 3)" for F
    by (auto simp: generation_group_clauses_def)
  have locus: "?A (generation_difference_schema 0) h \<longleftrightarrow> ?B h \<and>
      (136,Pair_Term (h 0) (h 4))\<in>positive_meaning generation_value_system" for h
    by (auto simp: generation_difference_schema_def schema_variables_def)
  have predecessors: "?A (generation_difference_schema 1) h \<longleftrightarrow> ?B h \<and>
      (146,Pair_Term (h 1) (h 5))\<in>positive_meaning generation_value_system" for h
    by (auto simp: generation_difference_schema_def schema_variables_def)
  have payload: "?A (generation_difference_schema 2) h \<longleftrightarrow> ?B h \<and>
      (136,Pair_Term (h 2) (h 6))\<in>positive_meaning generation_value_system" for h
    by (auto simp: generation_difference_schema_def schema_variables_def)
  have cause: "?A (generation_difference_schema 3) h \<longleftrightarrow> ?B h \<and>
      (136,Pair_Term (h 3) (h 7))\<in>positive_meaning generation_value_system" for h
    by (auto simp: generation_difference_schema_def schema_variables_def)
  show ?thesis by (simp only: valuation clauses locus predecessors payload cause; blast)
qed

lemma generation_comparison_admitted:
  "(140,t)\<in>positive_meaning generation_value_system \<Longrightarrow>
    \<exists>p q. t=Pair_Term p q \<and> (139,p)\<in>positive_meaning generation_value_system \<and>
      (139,q)\<in>positive_meaning generation_value_system"
  "(141,t)\<in>positive_meaning generation_value_system \<Longrightarrow>
    \<exists>p q. t=Pair_Term p q \<and> (139,p)\<in>positive_meaning generation_value_system \<and>
      (139,q)\<in>positive_meaning generation_value_system"
  using generation_identity_valuation[of t] generation_difference_valuation[of t] by blast+

lemma generation_identity_fields:
  "(140,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
      (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term a e)\<in>positive_meaning generation_value_system \<and>
    (145,Pair_Term b f)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term c g)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term d h)\<in>positive_meaning generation_value_system"
proof
  assume "(140,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
    (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system"
  then show "(139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term a e)\<in>positive_meaning generation_value_system \<and>
    (145,Pair_Term b f)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term c g)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term d h)\<in>positive_meaning generation_value_system"
    by (auto simp: generation_identity_valuation)
next
  assume supported: "(139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term a e)\<in>positive_meaning generation_value_system \<and>
    (145,Pair_Term b f)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term c g)\<in>positive_meaning generation_value_system \<and>
    (135,Pair_Term d h)\<in>positive_meaning generation_value_system"
  have formed: "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    "term_formed e" "term_formed f" "term_formed g" "term_formed h"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(140,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
    (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system"
    by (simp only: generation_identity_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d
        else if i=4 then e else if i=5 then f else if i=6 then g else h"])
      (use supported formed in auto)
qed

lemma generation_difference_fields:
  "(141,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
      (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    ((136,Pair_Term a e)\<in>positive_meaning generation_value_system \<or>
     (146,Pair_Term b f)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term c g)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term d h)\<in>positive_meaning generation_value_system)"
proof
  assume "(141,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
    (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system"
  then show "(139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    ((136,Pair_Term a e)\<in>positive_meaning generation_value_system \<or>
     (146,Pair_Term b f)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term c g)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term d h)\<in>positive_meaning generation_value_system)"
    by (auto simp: generation_difference_valuation)
next
  assume supported: "(139,Pair_Term a (Pair_Term b (Pair_Term c d)))\<in>positive_meaning generation_value_system \<and>
    (139,Pair_Term e (Pair_Term f (Pair_Term g h)))\<in>positive_meaning generation_value_system \<and>
    ((136,Pair_Term a e)\<in>positive_meaning generation_value_system \<or>
     (146,Pair_Term b f)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term c g)\<in>positive_meaning generation_value_system \<or>
     (136,Pair_Term d h)\<in>positive_meaning generation_value_system)"
  have formed: "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    "term_formed e" "term_formed f" "term_formed g" "term_formed h"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  show "(141,Pair_Term (Pair_Term a (Pair_Term b (Pair_Term c d)))
    (Pair_Term e (Pair_Term f (Pair_Term g h))))\<in>positive_meaning generation_value_system"
    by (simp only: generation_difference_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d
        else if i=4 then e else if i=5 then f else if i=6 then g else h"])
      (use supported formed in auto)
qed

section \<open>Every recursively admitted value has a complete data boundary\<close>

lemma generation_predecessor_term_height:
  assumes "t=Pair_Term a (Pair_Term (data_list_term ps) (Pair_Term c d))" "p\<in>set ps"
  shows "term_height p<term_height t"
proof -
  have first: "term_height p<term_height (data_list_term ps)"
    by (rule data_list_term_member_height[OF assms(2)])
  have second: "term_height (data_list_term ps)<term_height t" by (simp add: assms(1))
  show ?thesis by (rule less_trans[OF first second])
qed

lemma generation_admission_closed_data:
  assumes holds: "(139,t)\<in>positive_meaning generation_value_system"
  shows "self_contained_term t"
  using holds
proof (induction t rule: measure_induct_rule[of term_height])
  case (less t)
  obtain a b c d l p q where fields: "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    "target_value_presents l a" "(143,b)\<in>positive_meaning generation_value_system"
    "target_value_presents p c" "target_value_presents q d"
    using less.prems by (simp only: generation_admission_fields) blast
  obtain ps where members: "b=data_list_term ps" "\<forall>x\<in>set ps. (139,x)\<in>positive_meaning generation_value_system"
    using generation_collections.collection_sound[OF fields(3)] by blast
  have shape: "t=Pair_Term a (Pair_Term (data_list_term ps) (Pair_Term c d))"
    using fields(1) members(1) by simp
  have each: "\<forall>x\<in>set ps. self_contained_term x"
  proof (intro ballI)
    fix x assume member: "x\<in>set ps"
    have smaller: "term_height x<term_height t" by (rule generation_predecessor_term_height[OF shape member])
    show "self_contained_term x" using less.IH[OF smaller] members(2) member by blast
  qed
  show ?case using target_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(4)]
    target_value_presents_formed[OF fields(5)] each
    by (simp add: shape data_list_term_self_contained)
qed

lemma generation_admission_data:
  assumes "(139,t)\<in>positive_meaning generation_value_system"
  shows "term_formed t \<and> self_contained_term t"
  using generation_admission_closed_data[OF assms]
    schema_call_formed_target[OF positive_meaning_formed[OF assms]] by blast

lemma generation_comparison_data:
  "(140,Pair_Term p q)\<in>positive_meaning generation_value_system \<Longrightarrow>
    term_formed p \<and> self_contained_term p \<and> term_formed q \<and> self_contained_term q"
  "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<Longrightarrow>
    term_formed p \<and> self_contained_term p \<and> term_formed q \<and> self_contained_term q"
  using generation_comparison_admitted generation_admission_data by auto

interpretation generation_bags:
  related_bag_difference generation_value_system 2 4 140 144 145 141 142 146
  by (unfold_locales)
    (auto simp: generation_value_call generation_value_components dest: generation_comparison_data)

text \<open>
  The equations follow from the actual ordinary clauses and their complete
  valuation boundaries. They are not assumed semantic callbacks. Admission's
  data boundary follows by descent through the actual predecessor list. Both
  comparison entries inherit that boundary from their complete operands.

  This permits the existing related-bag and complete-list theories to apply
  inside the same positive group. Their comparison relations are the actual
  calls at the group's equality and inequality definitions. Exact recovery of
  the independent generation cores is established jointly in the next layer.
\<close>

end
