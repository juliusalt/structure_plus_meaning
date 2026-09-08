theory Factor_Target_Comparison
  imports Factor_Artifact_Difference Factor_Target_Presentations Factor_Separated_Lists
begin

section \<open>Admitted targets retain their actual artifact and occurrence\<close>

lemma target_admission_artifact_agreement:
  "systems_agree_on artifact_identity_system target_admission_system (system_definitions artifact_identity_system)"
  by (simp add: systems_agree_on_added
    target_admission_system_def record_admission_system_def socket_chain_system_def
    family_admission_system_def family_sockets_system_def family_socket_system_def
    headed_material_system_def key_fibre_system_def environment_identity_system_def
    environment_admission_system_def binding_entries_system_def binding_entry_system_def
    artifact_entries_system_def artifact_entry_admission_system_def keyed_list_system_def
    key_absence_system_def coordinate_admission_system_def natural_list_system_def
    natural_admission_system_def environment_comparison_system_def environment_bag_system_def
    environment_selection_system_def environment_entry_system_def)

lemma target_artifact_difference_agreement:
  "systems_agree_on target_admission_system artifact_difference_system
    (system_definitions target_admission_system \<inter> system_definitions artifact_difference_system)"
proof -
  have agreement: "systems_agree_on target_admission_system artifact_difference_system
      (system_definitions artifact_identity_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF target_admission_artifact_agreement]
      artifact_difference_base_agreement])
  have overlap: "system_definitions target_admission_system \<inter> system_definitions artifact_difference_system=
      system_definitions artifact_identity_system" by auto
  show ?thesis using agreement by (simp only: overlap)
qed

definition target_comparison_base_system :: "(nat,nat,nat,nat) schema_system" where
  "target_comparison_base_system=system_union target_admission_system artifact_difference_system"

lemma target_comparison_base_formed [simp]: "schema_system_formed target_comparison_base_system"
  unfolding target_comparison_base_system_def
  by (rule system_union_agree_formed[OF target_admission_system_formed artifact_difference_system_formed
    target_artifact_difference_agreement])

lemma target_comparison_base_definitions [simp]:
  "system_definitions target_comparison_base_system=
    system_definitions target_admission_system \<union> system_definitions artifact_difference_system"
  by (simp add: target_comparison_base_system_def)

lemma target_comparison_base_call:
  "schema_call_formed target_comparison_base_system d t \<longleftrightarrow>
    d\<in>system_definitions target_comparison_base_system \<and> term_formed t"
  using system_union_agree_call[OF target_admission_system_formed artifact_difference_system_formed
    target_artifact_difference_agreement, of d t]
  by (simp only: target_comparison_base_system_def system_union_definitions target_admission_call
    artifact_difference_call Un_iff; blast)

lemma comparison_target_admission_meaning:
  "(35,t)\<in>positive_meaning target_comparison_base_system \<longleftrightarrow>
    (35,t)\<in>positive_meaning target_admission_system"
  using system_union_agree_left_locality(2)[OF target_admission_system_formed artifact_difference_system_formed
    target_artifact_difference_agreement, of 35 t]
  by (simp add: target_comparison_base_system_def)

definition target_identity_schema :: "(nat,nat,nat) factor_schema" where
  "target_identity_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_z) (Pattern_Pair data_y data_z))
    {(0,35,Pattern_Pair data_x data_z),(1,35,Pattern_Pair data_y data_z),(2,12,Pattern_Pair data_x data_y)}"

definition target_identity_system :: "(nat,nat,nat,nat) schema_system" where
  "target_identity_system=add_view_definition target_comparison_base_system 135 data_x {(0,target_identity_schema)}"

interpretation target_identity_view:
  positive_view target_comparison_base_system 135 data_x "{(0,target_identity_schema)}"
  by (rule positive_view.intro)
    (auto simp: target_identity_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma target_identity_system_formed [simp]: "schema_system_formed target_identity_system"
  using target_identity_view.formed by (simp only: target_identity_system_def)

lemma target_identity_definitions [simp]:
  "system_definitions target_identity_system=insert 135 (system_definitions target_comparison_base_system)"
  by (simp add: target_identity_system_def)

lemma target_identity_call:
  "schema_call_formed target_identity_system d t \<longleftrightarrow>
    d\<in>system_definitions target_identity_system \<and> term_formed t"
  using added_variable_calls[OF target_comparison_base_formed
    target_identity_system_formed[unfolded target_identity_system_def] target_comparison_base_call]
  by (simp only: target_identity_system_def[symmetric])

lemma target_identity_old_meaning:
  assumes "d\<in>system_definitions artifact_difference_system"
  shows "(d,t)\<in>positive_meaning target_identity_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_difference_system"
  using target_identity_view.old_meaning[of d t]
    system_union_agree_right_locality(2)[OF target_admission_system_formed artifact_difference_system_formed
      target_artifact_difference_agreement assms, of t] assms
  by (auto simp: target_identity_system_def target_comparison_base_system_def)

lemma target_identity_base_meaning:
  assumes "d\<in>system_definitions target_comparison_base_system"
  shows "(d,t)\<in>positive_meaning target_identity_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_comparison_base_system"
  using target_identity_view.old_meaning[OF assms, of t] by (simp only: target_identity_system_def)

lemma target_identity_clause [simp]:
  "((135,c),S)\<in>system_clauses target_identity_system \<longleftrightarrow> (c,S)\<in>{(0,target_identity_schema)}"
  using target_identity_view.no_old_clause[of c S] by (auto simp: target_identity_system_def)

lemma target_identity_components:
  "(35,t)\<in>positive_meaning target_identity_system \<longleftrightarrow> (\<exists>x. target_value_presents x t)"
  "(12,t)\<in>positive_meaning target_identity_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
  using target_identity_base_meaning[of 35 t] comparison_target_admission_meaning[of t] target_admission_exact[of t]
    target_identity_old_meaning[of 12 t] artifact_difference_identity_meaning[of 12 t] by auto

lemma target_identity_valuation:
  "(135,t)\<in>positive_meaning target_identity_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (h 2)) (Pair_Term (h 1) (h 2)) \<and>
      (\<exists>x. target_value_presents x (Pair_Term (h 0) (h 2))) \<and>
      (\<exists>y. target_value_presents y (Pair_Term (h 1) (h 2))) \<and>
      (12,Pair_Term (h 0) (h 1))\<in>positive_meaning artifact_identity_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: target_identity_schema_def schema_variables_def target_identity_call target_identity_components)

lemma target_identity_fields:
  "(135,t)\<in>positive_meaning target_identity_system \<longleftrightarrow>
    (\<exists>x y a b k. t=Pair_Term (Pair_Term a k) (Pair_Term b k) \<and>
      target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b k) \<and>
      (12,Pair_Term a b)\<in>positive_meaning artifact_identity_system)"
proof
  assume "(135,t)\<in>positive_meaning target_identity_system"
  then show "\<exists>x y a b k. t=Pair_Term (Pair_Term a k) (Pair_Term b k) \<and>
    target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b k) \<and>
    (12,Pair_Term a b)\<in>positive_meaning artifact_identity_system"
    by (simp only: target_identity_valuation) blast
next
  assume "\<exists>x y a b k. t=Pair_Term (Pair_Term a k) (Pair_Term b k) \<and>
    target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b k) \<and>
    (12,Pair_Term a b)\<in>positive_meaning artifact_identity_system"
  then obtain x y a b k where fields: "t=Pair_Term (Pair_Term a k) (Pair_Term b k)"
    "target_value_presents x (Pair_Term a k)" "target_value_presents y (Pair_Term b k)"
    "(12,Pair_Term a b)\<in>positive_meaning artifact_identity_system" by blast
  have formed: "term_formed a" "term_formed b" "term_formed k"
    using target_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(3)] by auto
  show "(135,t)\<in>positive_meaning target_identity_system"
    by (simp only: target_identity_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then b else k"])
      (use fields formed in auto)
qed

theorem target_identity_on_values:
  assumes left: "target_value_presents x p" and right: "target_value_presents y q"
  shows "(135,Pair_Term p q)\<in>positive_meaning target_identity_system \<longleftrightarrow> x=y"
proof -
  obtain a where first: "artifact_value_presents (target_artifact x) a"
    "p=Pair_Term a (optional_payload_term (target_occurrence x))"
    using left by (auto simp: target_value_presents_def)
  obtain b where second: "artifact_value_presents (target_artifact y) b"
    "q=Pair_Term b (optional_payload_term (target_occurrence y))"
    using right by (auto simp: target_value_presents_def)
  have coordinates: "optional_payload_term (target_occurrence x)=optional_payload_term (target_occurrence y)
      \<longleftrightarrow> target_occurrence x=target_occurrence y"
    using optional_payload_term_injective by (auto dest: injD)
  have fields: "(135,Pair_Term p q)\<in>positive_meaning target_identity_system \<longleftrightarrow>
      optional_payload_term (target_occurrence x)=optional_payload_term (target_occurrence y) \<and>
      (12,Pair_Term a b)\<in>positive_meaning artifact_identity_system"
    using left right by (auto simp: target_identity_fields first(2) second(2); blast)
  show ?thesis using artifact_identity_contract.at[OF first(1) second(1)]
    by (simp only: fields coordinates exact_target_identity; blast)
qed

abbreviation target_identity_result :: "factor_term \<Rightarrow> bool" where
  "target_identity_result t \<equiv> \<exists>x p q. t=Pair_Term p q \<and> target_value_presents x p \<and> target_value_presents x q"

theorem target_identity_exact:
  "(135,t)\<in>positive_meaning target_identity_system \<longleftrightarrow> target_identity_result t"
proof
  assume holds: "(135,t)\<in>positive_meaning target_identity_system"
  obtain x y p q where fields: "t=Pair_Term p q" "target_value_presents x p" "target_value_presents y q"
    using holds by (auto simp: target_identity_fields)
  have same: "x=y" using holds fields(1) target_identity_on_values[OF fields(2,3)] by blast
  show "target_identity_result t" using fields same by blast
next
  assume "target_identity_result t"
  then show "(135,t)\<in>positive_meaning target_identity_system" using target_identity_on_values by blast
qed

interpretation target_identity_contract: presented_relation_contract
  target_value_presents target_formed "\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  target_value_presents target_formed "\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  "(=)" "\<lambda>p q. (135,Pair_Term p q)\<in>positive_meaning target_identity_system"
  by (unfold_locales)
    (use target_value_presentation_class target_identity_exact in
      \<open>auto simp: presentation_class_def presented_relation_def\<close>)

section \<open>Target inequality observes either independently required field\<close>

definition target_artifact_difference_schema :: "(nat,nat,nat) factor_schema" where
  "target_artifact_difference_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,35,Pattern_Pair data_x data_y),(1,35,Pattern_Pair data_z data_w),(2,134,Pattern_Pair data_x data_z)}"

definition target_occurrence_difference_schema :: "(nat,nat,nat) factor_schema" where
  "target_occurrence_difference_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,35,Pattern_Pair data_x data_y),(1,35,Pattern_Pair data_z data_w),(2,3,Pattern_Pair data_y data_w)}"

definition target_difference_clauses :: "(nat\<times>(nat,nat,nat) factor_schema) set" where
  "target_difference_clauses={(0,target_artifact_difference_schema),(1,target_occurrence_difference_schema)}"

definition target_difference_system :: "(nat,nat,nat,nat) schema_system" where
  "target_difference_system=add_view_definition target_identity_system 136 data_x target_difference_clauses"

interpretation target_difference_view:
  positive_view target_identity_system 136 data_x target_difference_clauses
  by (rule positive_view.intro)
    (auto simp: target_difference_clauses_def target_artifact_difference_schema_def target_occurrence_difference_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma target_difference_system_formed [simp]: "schema_system_formed target_difference_system"
  using target_difference_view.formed by (simp only: target_difference_system_def)

lemma target_difference_definitions [simp]:
  "system_definitions target_difference_system=insert 136 (system_definitions target_identity_system)"
  by (simp add: target_difference_system_def)

lemma target_difference_call:
  "schema_call_formed target_difference_system d t \<longleftrightarrow>
    d\<in>system_definitions target_difference_system \<and> term_formed t"
  using added_variable_calls[OF target_identity_system_formed
    target_difference_system_formed[unfolded target_difference_system_def] target_identity_call]
  by (simp only: target_difference_system_def[symmetric])

lemma target_difference_old_meaning:
  assumes "d\<in>system_definitions target_identity_system"
  shows "(d,t)\<in>positive_meaning target_difference_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_identity_system"
  using target_difference_view.old_meaning[OF assms, of t] by (simp only: target_difference_system_def)

lemma target_difference_clause [simp]:
  "((136,c),S)\<in>system_clauses target_difference_system \<longleftrightarrow> (c,S)\<in>target_difference_clauses"
  using target_difference_view.no_old_clause[of c S] by (auto simp: target_difference_system_def)

lemma target_difference_components:
  "(35,t)\<in>positive_meaning target_difference_system \<longleftrightarrow> (\<exists>x. target_value_presents x t)"
  "(134,t)\<in>positive_meaning target_difference_system \<longleftrightarrow> (134,t)\<in>positive_meaning artifact_difference_system"
  "(3,t)\<in>positive_meaning target_difference_system \<longleftrightarrow> (3,t)\<in>positive_meaning data_comparison_system"
  using target_difference_old_meaning[of 35 t] target_identity_components(1)[of t]
    target_difference_old_meaning[of 134 t] target_identity_old_meaning[of 134 t]
    target_difference_old_meaning[of 3 t] target_identity_old_meaning[of 3 t]
    artifact_difference_identity_meaning[of 3 t] artifact_identity_old_meaning[of 3 t]
    artifact_comparison_old_meaning[of 3 t] bag_comparison_old_meaning[of 3 t] by auto

lemma target_difference_valuation:
  "(136,t)\<in>positive_meaning target_difference_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)) \<and>
      (\<exists>x. target_value_presents x (Pair_Term (h 0) (h 1))) \<and>
      (\<exists>y. target_value_presents y (Pair_Term (h 2) (h 3))) \<and>
      ((134,Pair_Term (h 0) (h 2))\<in>positive_meaning artifact_difference_system \<or>
       (3,Pair_Term (h 1) (h 3))\<in>positive_meaning data_comparison_system))"
proof -
  have ordinary: "\<And>c S. ((136,c),S)\<in>system_clauses target_difference_system \<Longrightarrow>
      schema_material_premises S={}"
    by (auto simp: target_difference_clauses_def target_artifact_difference_schema_def target_occurrence_difference_schema_def)
  have member: "136\<in>system_definitions target_difference_system" by simp
  let ?A="\<lambda>(S::(nat,nat,nat) factor_schema) (h::nat\<Rightarrow>factor_term).
    (\<forall>i\<in>schema_variables S. term_formed (h i)) \<and>
    t=evaluate_pattern h (schema_conclusion S) \<and> term_formed t \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning target_difference_system)"
  let ?B="\<lambda>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
    t=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (h 2) (h 3)) \<and>
    (\<exists>x. target_value_presents x (Pair_Term (h 0) (h 1))) \<and>
    (\<exists>y. target_value_presents y (Pair_Term (h 2) (h 3)))"
  have valuation: "(136,t)\<in>positive_meaning target_difference_system \<longleftrightarrow>
      (\<exists>c S. (c,S)\<in>target_difference_clauses \<and> (\<exists>h. ?A S h))"
    using ordinary_positive_entry_valuation[where P=target_difference_system and d=136 and t=t, OF ordinary]
    by (simp only: target_difference_clause target_difference_call member simp_thms ex_simps)
  have clauses: "(\<exists>c S. (c,S)\<in>target_difference_clauses \<and> F S) \<longleftrightarrow>
      F target_artifact_difference_schema \<or> F target_occurrence_difference_schema" for F
    by (auto simp: target_difference_clauses_def)
  have artifact: "?A target_artifact_difference_schema h \<longleftrightarrow> ?B h \<and>
      (134,Pair_Term (h 0) (h 2))\<in>positive_meaning artifact_difference_system" for h
    by (auto simp: target_artifact_difference_schema_def schema_variables_def target_difference_components)
  have occurrence: "?A target_occurrence_difference_schema h \<longleftrightarrow> ?B h \<and>
      (3,Pair_Term (h 1) (h 3))\<in>positive_meaning data_comparison_system" for h
    by (auto simp: target_occurrence_difference_schema_def schema_variables_def target_difference_components)
  show ?thesis by (simp only: valuation clauses artifact occurrence; blast)
qed

lemma target_difference_fields:
  "(136,t)\<in>positive_meaning target_difference_system \<longleftrightarrow>
    (\<exists>x y a k b l. t=Pair_Term (Pair_Term a k) (Pair_Term b l) \<and>
      target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b l) \<and>
      ((134,Pair_Term a b)\<in>positive_meaning artifact_difference_system \<or>
       (3,Pair_Term k l)\<in>positive_meaning data_comparison_system))"
proof
  assume "(136,t)\<in>positive_meaning target_difference_system"
  then show "\<exists>x y a k b l. t=Pair_Term (Pair_Term a k) (Pair_Term b l) \<and>
    target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b l) \<and>
    ((134,Pair_Term a b)\<in>positive_meaning artifact_difference_system \<or>
     (3,Pair_Term k l)\<in>positive_meaning data_comparison_system)"
    by (simp only: target_difference_valuation) blast
next
  assume "\<exists>x y a k b l. t=Pair_Term (Pair_Term a k) (Pair_Term b l) \<and>
    target_value_presents x (Pair_Term a k) \<and> target_value_presents y (Pair_Term b l) \<and>
    ((134,Pair_Term a b)\<in>positive_meaning artifact_difference_system \<or>
     (3,Pair_Term k l)\<in>positive_meaning data_comparison_system)"
  then obtain x y a k b l where fields: "t=Pair_Term (Pair_Term a k) (Pair_Term b l)"
    "target_value_presents x (Pair_Term a k)" "target_value_presents y (Pair_Term b l)"
    "(134,Pair_Term a b)\<in>positive_meaning artifact_difference_system \<or>
      (3,Pair_Term k l)\<in>positive_meaning data_comparison_system" by blast
  have formed: "term_formed a" "term_formed k" "term_formed b" "term_formed l"
    using target_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(3)] by auto
  show "(136,t)\<in>positive_meaning target_difference_system"
    by (simp only: target_difference_valuation,
      rule exI[of _ "\<lambda>i::nat. if i=0 then a else if i=1 then k else if i=2 then b else l"])
      (use fields formed in auto)
qed

theorem target_difference_on_values:
  assumes left: "target_value_presents x p" and right: "target_value_presents y q"
  shows "(136,Pair_Term p q)\<in>positive_meaning target_difference_system \<longleftrightarrow> x\<noteq>y"
proof -
  obtain a where first: "artifact_value_presents (target_artifact x) a"
    "p=Pair_Term a (optional_payload_term (target_occurrence x))"
    using left by (auto simp: target_value_presents_def)
  obtain b where second: "artifact_value_presents (target_artifact y) b"
    "q=Pair_Term b (optional_payload_term (target_occurrence y))"
    using right by (auto simp: target_value_presents_def)
  have formed: "term_formed (optional_payload_term (target_occurrence x))"
    "term_formed (optional_payload_term (target_occurrence y))"
    using target_value_presents_formed[OF left] target_value_presents_formed[OF right]
    by (simp_all add: first(2) second(2))
  have coordinates: "optional_payload_term (target_occurrence x)=optional_payload_term (target_occurrence y)
      \<longleftrightarrow> target_occurrence x=target_occurrence y"
    using optional_payload_term_injective by (auto dest: injD)
  have difference: "(136,Pair_Term p q)\<in>positive_meaning target_difference_system \<longleftrightarrow>
      (134,Pair_Term a b)\<in>positive_meaning artifact_difference_system \<or>
      (3,Pair_Term (optional_payload_term (target_occurrence x))
        (optional_payload_term (target_occurrence y)))\<in>positive_meaning data_comparison_system"
    using left right by (auto simp: target_difference_fields first(2) second(2); blast)
  show ?thesis using formed artifact_difference_contract.at[OF first(1) second(1)]
    by (auto simp: difference data_comparison_exact coordinates exact_target_identity)
qed

abbreviation target_difference_result :: "factor_term \<Rightarrow> bool" where
  "target_difference_result t \<equiv> \<exists>x y p q. t=Pair_Term p q \<and>
    target_value_presents x p \<and> target_value_presents y q \<and> x\<noteq>y"

theorem target_difference_exact:
  "(136,t)\<in>positive_meaning target_difference_system \<longleftrightarrow> target_difference_result t"
proof
  assume holds: "(136,t)\<in>positive_meaning target_difference_system"
  obtain x y p q where fields: "t=Pair_Term p q" "target_value_presents x p" "target_value_presents y q"
    using holds by (auto simp: target_difference_fields)
  have different: "x\<noteq>y" using holds fields(1) target_difference_on_values[OF fields(2,3)] by blast
  show "target_difference_result t" using fields different by blast
next
  assume "target_difference_result t"
  then show "(136,t)\<in>positive_meaning target_difference_system" using target_difference_on_values by blast
qed

interpretation target_difference_contract: presented_relation_contract
  target_value_presents target_formed "\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  target_value_presents target_formed "\<lambda>t. (35,t)\<in>positive_meaning target_admission_system"
  "(\<noteq>)" "\<lambda>p q. (136,Pair_Term p q)\<in>positive_meaning target_difference_system"
  by (unfold_locales)
    (use target_value_presentation_class target_difference_exact in
      \<open>auto simp: presentation_class_def presented_relation_def\<close>)

corollary target_comparison_presentation_invariance:
  assumes "target_value_presents x p" "target_value_presents x p'"
    "target_value_presents y q" "target_value_presents y q'"
  shows "(135,Pair_Term p q)\<in>positive_meaning target_identity_system \<longleftrightarrow>
      (135,Pair_Term p' q')\<in>positive_meaning target_identity_system"
    and "(136,Pair_Term p q)\<in>positive_meaning target_difference_system \<longleftrightarrow>
      (136,Pair_Term p' q')\<in>positive_meaning target_difference_system"
  using target_identity_contract.invariance[OF assms(1,3,2,4)]
    target_difference_contract.invariance[OF assms(1,3,2,4)] by blast+

section \<open>The generic separation clauses admit every finite target collection\<close>

definition target_separation_system :: "(nat,nat,nat,nat) schema_system" where
  "target_separation_system=add_view_definition target_difference_system 137 data_x (context_list_clauses 136 137)"

lemma target_separation_system_formed [simp]: "schema_system_formed target_separation_system"
  unfolding target_separation_system_def
  by (rule add_recursive_definition_formed[OF target_difference_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma target_separation_definitions [simp]:
  "system_definitions target_separation_system=insert 137 (system_definitions target_difference_system)"
  by (simp add: target_separation_system_def)

lemma target_separation_call:
  "schema_call_formed target_separation_system d t \<longleftrightarrow>
    d\<in>system_definitions target_separation_system \<and> term_formed t"
  using added_variable_calls[OF target_difference_system_formed
    target_separation_system_formed[unfolded target_separation_system_def] target_difference_call]
  by (simp only: target_separation_system_def[symmetric])

lemma target_separation_old_meaning:
  assumes "d\<in>system_definitions target_difference_system"
  shows "(d,t)\<in>positive_meaning target_separation_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_difference_system"
  using added_definition_preserves_old(2)[OF target_difference_system_formed
    target_separation_system_formed[unfolded target_separation_system_def], of d t] assms
  by (auto simp: target_separation_system_def)

lemma target_separation_clause [simp]:
  "((137,c),S)\<in>system_clauses target_separation_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 136 137"
proof -
  have owned: "((137,c),S)\<in>system_clauses target_difference_system \<Longrightarrow>
    137\<in>system_definitions target_difference_system"
    using target_difference_system_formed unfolding schema_system_formed_def by blast
  have absent: "((137,c),S)\<notin>system_clauses target_difference_system" using owned by auto
  show ?thesis using absent by (simp add: target_separation_system_def)
qed

interpretation target_separation: context_list_profile target_separation_system 136 137
  by (rule context_list_profile.intro) (auto simp: target_separation_call)

abbreviation target_separation_result :: "factor_term \<Rightarrow> bool" where
  "target_separation_result t \<equiv> \<exists>p qs. t=Pair_Term p (data_list_term qs) \<and> term_formed p \<and>
    (\<forall>q\<in>set qs. target_difference_result (Pair_Term p q))"

theorem target_separation_exact:
  "(137,t)\<in>positive_meaning target_separation_system \<longleftrightarrow> target_separation_result t"
  using target_separation_old_meaning[of 136]
  by (auto simp: target_separation.exact target_difference_exact)

definition target_collection_system :: "(nat,nat,nat,nat) schema_system" where
  "target_collection_system=add_view_definition target_separation_system 138 data_x (separated_list_clauses 35 137 138)"

lemma target_collection_system_formed [simp]: "schema_system_formed target_collection_system"
  unfolding target_collection_system_def
  by (rule add_recursive_definition_formed[OF target_separation_system_formed])
    (auto simp: separated_list_clauses_def data_list_nil_schema_def separated_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma target_collection_definitions [simp]:
  "system_definitions target_collection_system=insert 138 (system_definitions target_separation_system)"
  by (simp add: target_collection_system_def)

lemma target_collection_call:
  "schema_call_formed target_collection_system d t \<longleftrightarrow>
    d\<in>system_definitions target_collection_system \<and> term_formed t"
  using added_variable_calls[OF target_separation_system_formed
    target_collection_system_formed[unfolded target_collection_system_def] target_separation_call]
  by (simp only: target_collection_system_def[symmetric])

lemma target_collection_old_meaning:
  assumes "d\<in>system_definitions target_separation_system"
  shows "(d,t)\<in>positive_meaning target_collection_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_separation_system"
  using added_definition_preserves_old(2)[OF target_separation_system_formed
    target_collection_system_formed[unfolded target_collection_system_def], of d t] assms
  by (auto simp: target_collection_system_def)

lemma target_collection_clauses [simp]:
  "((138,c),S)\<in>system_clauses target_collection_system \<longleftrightarrow> (c,S)\<in>separated_list_clauses 35 137 138"
  "((137,c),S)\<in>system_clauses target_collection_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 136 137"
proof -
  have owned: "((138,c),S)\<in>system_clauses target_separation_system \<Longrightarrow>
    138\<in>system_definitions target_separation_system"
    using target_separation_system_formed unfolding schema_system_formed_def by blast
  have absent: "((138,c),S)\<notin>system_clauses target_separation_system" using owned by auto
  show "((138,c),S)\<in>system_clauses target_collection_system \<longleftrightarrow> (c,S)\<in>separated_list_clauses 35 137 138"
    using absent by (simp add: target_collection_system_def)
  show "((137,c),S)\<in>system_clauses target_collection_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 136 137"
    by (simp add: target_collection_system_def)
qed

interpretation target_collections: separated_list_profile target_collection_system 136 137 35 138
  by (unfold_locales) (auto simp: target_collection_call)

lemma target_collection_components:
  "(35,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (35,t)\<in>positive_meaning target_admission_system"
  "(135,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (135,t)\<in>positive_meaning target_identity_system"
  "(136,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (136,t)\<in>positive_meaning target_difference_system"
  "(137,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (137,t)\<in>positive_meaning target_separation_system"
  using target_collection_old_meaning[of 35 t] target_separation_old_meaning[of 35 t]
    target_difference_old_meaning[of 35 t] target_identity_base_meaning[of 35 t] comparison_target_admission_meaning[of t]
    target_collection_old_meaning[of 135 t] target_separation_old_meaning[of 135 t] target_difference_old_meaning[of 135 t]
    target_collection_old_meaning[of 136 t] target_separation_old_meaning[of 136 t]
    target_collection_old_meaning[of 137 t] by auto

theorem target_collection_presentation_class:
  "presentation_class (data_collection_presents target_value_presents)
    (\<lambda>A. finite A \<and> (\<forall>x\<in>A. target_formed x)) (\<lambda>t. (138,t)\<in>positive_meaning target_collection_system)"
  by (rule target_collections.collection_presentation_class)
    (use target_difference_contract.presented_relation_contract_axioms in
      \<open>simp only: target_collection_components\<close>)

interpretation target_collection_presentations:
  presentation_class "data_collection_presents target_value_presents"
    "\<lambda>A. finite A \<and> (\<forall>x\<in>A. target_formed x)" "\<lambda>t. (138,t)\<in>positive_meaning target_collection_system"
  by (rule target_collection_presentation_class)

theorem target_collection_exact:
  "(138,t)\<in>positive_meaning target_collection_system \<longleftrightarrow>
    (\<exists>A. data_collection_presents target_value_presents A t)"
  by (rule target_collection_presentations.admissible_iff)

theorem target_comparison_presented_relations:
  "(135,Pair_Term p q)\<in>positive_meaning target_collection_system \<longleftrightarrow>
    presented_relation target_value_presents target_value_presents (=) p q"
  "(136,Pair_Term p q)\<in>positive_meaning target_collection_system \<longleftrightarrow>
    presented_relation target_value_presents target_value_presents (\<noteq>) p q"
  by (simp_all only: target_collection_components target_identity_contract.exact target_difference_contract.exact)

corollary target_collection_two_members:
  assumes "target_value_presents x p" "target_value_presents y q"
  shows "(138,data_list_term [p,q])\<in>positive_meaning target_collection_system \<longleftrightarrow> x\<noteq>y"
  using target_collections.collection_lists[of "[p,q]"] assms target_difference_contract.at[OF assms]
  by (auto simp: target_collections.collection_lists target_collection_components target_admission_exact)

corollary target_collection_repeated_subject:
  assumes "target_value_presents x p" "target_value_presents x q"
  shows "(138,data_list_term [p,q])\<notin>positive_meaning target_collection_system"
  using target_collection_two_members[OF assms] by simp

corollary target_collection_empty:
  "(138,Payload_Term [])\<in>positive_meaning target_collection_system"
  by (simp add: target_collections.collection_lists[of "[]", simplified])

corollary target_collection_total:
  assumes "finite A" "\<forall>x\<in>A. target_formed x"
  shows "\<exists>t. data_collection_presents target_value_presents A t \<and>
    (138,t)\<in>positive_meaning target_collection_system"
  using target_collection_presentations.total assms
    target_collection_presentations.presentation_boundary by blast

corollary target_whole_occurrence_distinct:
  assumes source: "artifact_value_presents R a" and inside: "r\<in>rra_carrier (object_structure R)"
  shows "(136,Pair_Term (Pair_Term a (Payload_Term []))
      (Pair_Term a (Pair_Term (Payload_Term r) (Payload_Term []))))\<in>positive_meaning target_difference_system"
proof -
  have whole: "target_value_presents (Whole_Artifact R) (Pair_Term a (Payload_Term []))"
    using source by (auto simp: target_value_whole)
  have occurrence: "target_value_presents (Occurrence_Anchor (R,r))
      (Pair_Term a (Pair_Term (Payload_Term r) (Payload_Term [])))"
    using source inside by (auto simp: target_value_occurrence)
  show ?thesis using target_difference_on_values[OF whole occurrence] by simp
qed

section \<open>Complete local contracts remain available for program composition\<close>

lemma target_comparison_operation_components:
  "(132,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (132,t)\<in>positive_meaning data_absence_system"
  "(133,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (133,t)\<in>positive_meaning bag_difference_system"
  "(134,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> (134,t)\<in>positive_meaning artifact_difference_system"
  using target_collection_old_meaning[of 132 t] target_separation_old_meaning[of 132 t]
    target_difference_old_meaning[of 132 t] target_identity_old_meaning[of 132 t]
    artifact_difference_old_meaning[of 132 t] bag_difference_old_meaning[of 132 t]
    target_collection_old_meaning[of 133 t] target_separation_old_meaning[of 133 t]
    target_difference_old_meaning[of 133 t] target_identity_old_meaning[of 133 t] artifact_difference_old_meaning[of 133 t]
    target_collection_old_meaning[of 134 t] target_separation_old_meaning[of 134 t]
    target_difference_old_meaning[of 134 t] target_identity_old_meaning[of 134 t] by auto

lemma target_collection_base_agreement:
  "systems_agree_on target_admission_system target_collection_system (system_definitions target_admission_system)"
  using system_union_agree_left[OF artifact_difference_system_formed target_artifact_difference_agreement]
  by (simp add: target_collection_system_def target_separation_system_def target_difference_system_def
    target_identity_system_def target_comparison_base_system_def systems_agree_on_added)

abbreviation target_comparison_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "target_comparison_operation_result d t \<equiv>
    if d=132 then data_absence_result t else if d=133 then bag_difference_result t
    else if d=134 then artifact_difference_result t else if d=135 then target_identity_result t
    else if d=136 then target_difference_result t else if d=137 then target_separation_result t
    else \<exists>A. data_collection_presents target_value_presents A t"

theorem target_comparison_operations_exact:
  assumes "d\<in>{132,133,134,135,136,137,138}"
  shows "(d,t)\<in>positive_meaning target_collection_system \<longleftrightarrow> target_comparison_operation_result d t"
  using assms by (auto simp: target_comparison_operation_components target_collection_components
    data_absence_exact bag_difference_exact artifact_difference_exact target_identity_exact
    target_difference_exact target_separation_exact target_collection_exact)

text \<open>
  Target equality and inequality compare the actual complete artifact and its
  optional occurrence under admission of both targets. A whole artifact and an
  occurrence at the empty address remain different. Artifact enumeration
  changes do not alter either result, and occurrence membership is still
  checked against that very artifact.

  The complete target collection instantiates the generic separation profile
  and derives its class through the existing finite-collection construction.
  Every order and every member presentation is admitted; two terms presenting
  the same target cannot supply two distinct members. The empty collection is
  admitted. The intermediate context-list helper requires only context
  formation when its comparison list is empty, as its exact contract states.

  Seven definitions with sixteen ordinary clauses supply data absence,
  counted-list and artifact inequality, target equality and inequality, and
  the two target-collection traversals. The local program has seven distinct
  entries available for later native compilation. The separate
  comparison-program module joins this local program to replay and preserves
  both complete meanings. Recursive generation admission and the higher
  protocol still require their own complete native checks.
\<close>

end
