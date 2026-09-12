theory Factor_Artifact_Difference
  imports Factor_Bag_Difference
begin

section \<open>Every artifact field retains its complete admission boundary\<close>

abbreviation artifact_fields_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "artifact_fields_pattern a e b f \<equiv> Pattern_Pair a (Pattern_Pair e (Pattern_Pair b f))"

abbreviation artifact_left_pattern :: "nat term_pattern" where
  "artifact_left_pattern \<equiv> artifact_fields_pattern (Pattern_Variable 0) (Pattern_Variable 1)
    (Pattern_Variable 2) (Pattern_Variable 3)"

abbreviation artifact_right_pattern :: "nat term_pattern" where
  "artifact_right_pattern \<equiv> artifact_fields_pattern (Pattern_Variable 4) (Pattern_Variable 5)
    (Pattern_Variable 6) (Pattern_Variable 7)"

definition artifact_difference_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "artifact_difference_schema i=data_rule (Pattern_Pair artifact_left_pattern artifact_right_pattern)
    {(0,11,artifact_left_pattern),(1,11,artifact_right_pattern),
     (2,133,Pattern_Pair (Pattern_Variable i) (Pattern_Variable (i+4)))}"

definition artifact_difference_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "artifact_difference_clauses={(0,artifact_difference_schema 0),(1,artifact_difference_schema 1),
    (2,artifact_difference_schema 2),(3,artifact_difference_schema 3)}"

lemma artifact_identity_bag_agreement:
  "systems_agree_on bag_comparison_system artifact_identity_system (system_definitions bag_comparison_system)"
  by (simp add: artifact_identity_system_def artifact_admission_system_def artifact_projection_system_def
    material_data_system_def atom_lookup_system_def artifact_comparison_system_def systems_agree_on_added)

lemma artifact_bag_difference_agreement:
  "systems_agree_on artifact_identity_system bag_difference_system
    (system_definitions artifact_identity_system \<inter> system_definitions bag_difference_system)"
proof -
  have agreement: "systems_agree_on artifact_identity_system bag_difference_system
      (system_definitions bag_comparison_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF artifact_identity_bag_agreement]
      bag_difference_base_agreement])
  have overlap: "system_definitions artifact_identity_system \<inter> system_definitions bag_difference_system=
      system_definitions bag_comparison_system" by auto
  show ?thesis using agreement by (simp only: overlap)
qed

definition artifact_difference_base_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_difference_base_system=system_union artifact_identity_system bag_difference_system"

lemma artifact_difference_base_formed [simp]: "schema_system_formed artifact_difference_base_system"
  unfolding artifact_difference_base_system_def
  by (rule system_union_agree_formed[OF artifact_identity_system_formed bag_difference_system_formed
    artifact_bag_difference_agreement])

lemma artifact_difference_base_definitions [simp]:
  "system_definitions artifact_difference_base_system=
    system_definitions artifact_identity_system \<union> system_definitions bag_difference_system"
  by (simp add: artifact_difference_base_system_def)

lemma artifact_difference_base_call:
  "schema_call_formed artifact_difference_base_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_difference_base_system \<and> term_formed t"
  using system_union_agree_call[OF artifact_identity_system_formed bag_difference_system_formed
    artifact_bag_difference_agreement, of d t]
  by (simp only: artifact_difference_base_system_def system_union_definitions artifact_identity_definitions artifact_identity_call
    bag_difference_call Un_iff; blast)

definition artifact_difference_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_difference_system=add_view_definition artifact_difference_base_system 134 data_x artifact_difference_clauses"

interpretation artifact_difference_view:
  positive_view artifact_difference_base_system 134 data_x artifact_difference_clauses
  by (rule positive_view.intro)
    (auto simp: artifact_difference_clauses_def artifact_difference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma artifact_difference_system_formed [simp]: "schema_system_formed artifact_difference_system"
  using artifact_difference_view.formed by (simp only: artifact_difference_system_def)

lemma artifact_difference_definitions [simp]:
  "system_definitions artifact_difference_system=insert 134 (system_definitions artifact_difference_base_system)"
  by (simp add: artifact_difference_system_def)

lemma artifact_difference_call:
  "schema_call_formed artifact_difference_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_difference_system \<and> term_formed t"
  using added_variable_calls[OF artifact_difference_base_formed
    artifact_difference_system_formed[unfolded artifact_difference_system_def] artifact_difference_base_call]
  by (simp only: artifact_difference_system_def[symmetric])

lemma artifact_difference_old_meaning:
  assumes "d\<in>system_definitions bag_difference_system"
  shows "(d,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_difference_system"
  using artifact_difference_view.old_meaning[of d t]
    system_union_agree_right_locality(2)[OF artifact_identity_system_formed bag_difference_system_formed
      artifact_bag_difference_agreement assms, of t] assms
  by (auto simp: artifact_difference_system_def artifact_difference_base_system_def)

lemma artifact_difference_clause [simp]:
  "((134,c),S)\<in>system_clauses artifact_difference_system \<longleftrightarrow> (c,S)\<in>artifact_difference_clauses"
  using artifact_difference_view.no_old_clause[of c S] by (auto simp: artifact_difference_system_def)

lemma artifact_difference_identity_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}"
  shows "(d,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_identity_system"
  using artifact_difference_view.old_meaning[of d t]
    system_union_agree_left_locality(2)[OF artifact_identity_system_formed bag_difference_system_formed
      artifact_bag_difference_agreement, of d t] assms
  by (auto simp: artifact_difference_system_def artifact_difference_base_system_def)

lemma artifact_difference_base_agreement:
  "systems_agree_on artifact_identity_system artifact_difference_system (system_definitions artifact_identity_system)"
  using system_union_agree_left[OF bag_difference_system_formed artifact_bag_difference_agreement]
  by (simp add: artifact_difference_system_def artifact_difference_base_system_def systems_agree_on_added)

lemma artifact_difference_components:
  "(11,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
  "(133,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow> (133,t)\<in>positive_meaning bag_difference_system"
  using artifact_difference_identity_meaning[of 11 t] artifact_identity_admission[of t]
    artifact_difference_old_meaning[of 133 t] by auto

lemma artifact_difference_valuation:
  "(134,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3))
        (artifact_fields_term (h 4) (h 5) (h 6) (h 7)) \<and>
      (\<exists>R. artifact_value_presents R (artifact_fields_term (h 0) (h 1) (h 2) (h 3))) \<and>
      (\<exists>S. artifact_value_presents S (artifact_fields_term (h 4) (h 5) (h 6) (h 7))) \<and>
      ((133,Pair_Term (h 0) (h 4))\<in>positive_meaning bag_difference_system \<or>
       (133,Pair_Term (h 1) (h 5))\<in>positive_meaning bag_difference_system \<or>
       (133,Pair_Term (h 2) (h 6))\<in>positive_meaning bag_difference_system \<or>
       (133,Pair_Term (h 3) (h 7))\<in>positive_meaning bag_difference_system))"
proof -
  have ordinary: "\<And>c S. ((134,c),S)\<in>system_clauses artifact_difference_system \<Longrightarrow>
      schema_material_premises S={}"
    by (auto simp: artifact_difference_clauses_def artifact_difference_schema_def)
  have member: "134\<in>system_definitions artifact_difference_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning artifact_difference_system)"
  let ?B="\<lambda>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
    t=Pair_Term (artifact_fields_term (h 0) (h 1) (h 2) (h 3))
      (artifact_fields_term (h 4) (h 5) (h 6) (h 7)) \<and>
    (\<exists>R. artifact_value_presents R (artifact_fields_term (h 0) (h 1) (h 2) (h 3))) \<and>
    (\<exists>S. artifact_value_presents S (artifact_fields_term (h 4) (h 5) (h 6) (h 7)))"
  have valuation: "(134,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
      (\<exists>c S. (c,S)\<in>artifact_difference_clauses \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=artifact_difference_system and d=134 and t=t, OF ordinary]
    by (simp only: artifact_difference_clause artifact_difference_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>artifact_difference_clauses \<and> F S) \<longleftrightarrow>
      F (artifact_difference_schema 0) \<or> F (artifact_difference_schema 1) \<or>
      F (artifact_difference_schema 2) \<or> F (artifact_difference_schema 3)" for F
    by (auto simp: artifact_difference_clauses_def)
  have fields:
    "?A (artifact_difference_schema 0) h \<longleftrightarrow> ?B h \<and>
      (133,Pair_Term (h 0) (h 4))\<in>positive_meaning bag_difference_system"
    "?A (artifact_difference_schema 1) h \<longleftrightarrow> ?B h \<and>
      (133,Pair_Term (h 1) (h 5))\<in>positive_meaning bag_difference_system"
    "?A (artifact_difference_schema 2) h \<longleftrightarrow> ?B h \<and>
      (133,Pair_Term (h 2) (h 6))\<in>positive_meaning bag_difference_system"
    "?A (artifact_difference_schema 3) h \<longleftrightarrow> ?B h \<and>
      (133,Pair_Term (h 3) (h 7))\<in>positive_meaning bag_difference_system" for h
    by (auto simp: artifact_difference_schema_def schema_variables_def artifact_difference_components)
  show ?thesis by (simp only: valuation clauses fields; blast)
qed

lemma artifact_difference_fields:
  assumes left: "artifact_value_presents R (artifact_fields_term a e b f)"
    and right: "artifact_value_presents S (artifact_fields_term a' e' b' f')"
  shows "(134,Pair_Term (artifact_fields_term a e b f) (artifact_fields_term a' e' b' f'))
      \<in>positive_meaning artifact_difference_system \<longleftrightarrow>
    (133,Pair_Term a a')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term e e')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term b b')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term f f')\<in>positive_meaning bag_difference_system"
proof
  assume "(134,Pair_Term (artifact_fields_term a e b f) (artifact_fields_term a' e' b' f'))
    \<in>positive_meaning artifact_difference_system"
  then show "(133,Pair_Term a a')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term e e')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term b b')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term f f')\<in>positive_meaning bag_difference_system"
    by (auto simp: artifact_difference_valuation)
next
  assume difference: "(133,Pair_Term a a')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term e e')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term b b')\<in>positive_meaning bag_difference_system \<or>
    (133,Pair_Term f f')\<in>positive_meaning bag_difference_system"
  have formed: "term_formed a" "term_formed e" "term_formed b" "term_formed f"
    "term_formed a'" "term_formed e'" "term_formed b'" "term_formed f'"
    using artifact_value_presents_formed[OF left] artifact_value_presents_formed[OF right] by auto
  show "(134,Pair_Term (artifact_fields_term a e b f) (artifact_fields_term a' e' b' f'))
      \<in>positive_meaning artifact_difference_system"
    by (simp only: artifact_difference_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then e else if i=2 then b else if i=3 then f
        else if i=4 then a' else if i=5 then e' else if i=6 then b' else f'"])
      (use formed left right difference in auto)
qed

theorem artifact_difference_on_values:
  assumes left: "artifact_value_presents R x" and right: "artifact_value_presents S y"
  shows "(134,Pair_Term x y)\<in>positive_meaning artifact_difference_system \<longleftrightarrow> R\<noteq>S"
proof -
  obtain A E B F where first: "artifact_enumeration R A E B F" "x=artifact_data_term A E B F"
    using left unfolding artifact_value_presents_def by blast
  obtain A' E' B' F' where second: "artifact_enumeration S A' E' B' F'" "y=artifact_data_term A' E' B' F'"
    using right unfolding artifact_value_presents_def by blast
  have data: "data_elements (map Payload_Term A)" "data_elements (map incidence_data E)"
    "data_elements (map address_pair_data B)" "data_elements (map address_pair_data F)"
    "data_elements (map Payload_Term A')" "data_elements (map incidence_data E')"
    "data_elements (map address_pair_data B')" "data_elements (map address_pair_data F')"
    using artifact_data_term_formed[OF first(1)] artifact_data_term_formed[OF second(1)]
      artifact_data_term_self_contained[of A E B F] artifact_data_term_self_contained[of A' E' B' F']
    by (auto simp: artifact_data_term_def data_list_term_formed data_list_term_self_contained)
  have difference: "(134,Pair_Term x y)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
      \<not> (7,Pair_Term x y)\<in>positive_meaning artifact_comparison_system"
    using data
    by (simp only: first(2) second(2) artifact_data_term_def
      artifact_difference_fields[OF left[unfolded first(2) artifact_data_term_def]
        right[unfolded second(2) artifact_data_term_def]]
      artifact_comparison_fields bag_difference_lists bag_comparison_lists; blast)
  show ?thesis using difference artifact_comparison_exact[OF left right] by blast
qed

abbreviation artifact_difference_result :: "factor_term \<Rightarrow> bool" where
  "artifact_difference_result t \<equiv> \<exists>R S x y. t=Pair_Term x y \<and>
    artifact_value_presents R x \<and> artifact_value_presents S y \<and> R\<noteq>S"

theorem artifact_difference_exact:
  "(134,t)\<in>positive_meaning artifact_difference_system \<longleftrightarrow> artifact_difference_result t"
proof
  assume holds: "(134,t)\<in>positive_meaning artifact_difference_system"
  obtain R S x y where fields: "t=Pair_Term x y" "artifact_value_presents R x" "artifact_value_presents S y"
    using holds by (auto simp: artifact_difference_valuation)
  have different: "R\<noteq>S" using holds fields(1) artifact_difference_on_values[OF fields(2,3)] by blast
  show "artifact_difference_result t" using fields different by blast
next
  assume "artifact_difference_result t"
  then show "(134,t)\<in>positive_meaning artifact_difference_system"
    using artifact_difference_on_values by blast
qed

interpretation artifact_difference_contract: presented_relation_contract
  artifact_value_presents exact_formed "\<lambda>t. (11,t)\<in>positive_meaning artifact_admission_system"
  artifact_value_presents exact_formed "\<lambda>t. (11,t)\<in>positive_meaning artifact_admission_system"
  "(\<noteq>)" "\<lambda>p q. (134,Pair_Term p q)\<in>positive_meaning artifact_difference_system"
  by (unfold_locales)
    (use artifact_presentations.presentation_class_axioms artifact_difference_exact in
      \<open>auto simp: presentation_class_def presented_relation_def\<close>)

corollary artifact_difference_presentation_invariance:
  assumes "artifact_value_presents R x" "artifact_value_presents R x'"
    "artifact_value_presents S y" "artifact_value_presents S y'"
  shows "(134,Pair_Term x y)\<in>positive_meaning artifact_difference_system \<longleftrightarrow>
    (134,Pair_Term x' y')\<in>positive_meaning artifact_difference_system"
  by (rule artifact_difference_contract.invariance[OF assms(1,3,2,4)])

text \<open>
  Four ordinary clauses inspect the same complete artifact pair. Every clause
  admits both artifacts and witnesses a difference in one actual data field.
  The counted-list checker preserves every occurrence, including repetitions
  in the anonymous attachment field. The other fields retain the distinctness
  conditions already required by complete artifact admission.

  The existing artifact equality proof then gives exact inequality of the
  represented artifacts across all their presentations. The complement occurs
  only in that mathematical proof; the native program contains positive calls
  to explicit admission and difference definitions.

  The artifact reader combines its own existing program with the local bag
  program. Their complete shared definitions agree, so the general program
  composition theorem preserves both meanings. This module owns and exports
  the artifact inequality contract; later notions use that contract directly.
\<close>

end
