theory Factor_Judgment_Dependency_Reading
  imports Factor_Judgment_Source_Admission
begin

section \<open>The slot query follows both actual grammars\<close>

lemma judgment_demanded_slot_valuation:
  "(179,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (h 5) \<and>
      (178,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning judgment_retention_system \<and>
      (119,Pair_Term (package_context_term (h 0) (h 1) (h 2)) (h 5))\<in>positive_meaning package_slot_reading_system) \<or>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (Pair_Term (h 3) (h 5)) \<and>
      (178,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning judgment_retention_system \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 6) (h 7) (h 8) (h 9))
        \<in>positive_meaning application_reading_system \<and>
      (5,Pair_Term (h 5) (Pair_Term (h 9) (h 10)))\<in>positive_meaning bag_comparison_system)"
proof -
  let ?B="\<lambda>S h. (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and>
    z=evaluate_pattern h (schema_conclusion S) \<and> schema_call_formed judgment_retention_system 179 z \<and>
    (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning judgment_retention_system)"
  have raw: "(179,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (\<exists>c S h. ((179,c),S)\<in>system_clauses judgment_retention_system \<and> ?B S h)"
    by (rule ordinary_positive_entry_valuation)
      (auto simp: judgment_program_slot_schema_def judgment_application_slot_schema_def)
  have alternatives: "(179,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (\<exists>h. ?B judgment_program_slot_schema h) \<or> (\<exists>h. ?B judgment_application_slot_schema h)"
    by (simp only: raw judgment_retention_clauses(2)) blast
  have program: "?B judgment_program_slot_schema h \<longleftrightarrow>
      (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (h 5) \<and>
      (178,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning judgment_retention_system \<and>
      (119,Pair_Term (package_context_term (h 0) (h 1) (h 2)) (h 5))\<in>positive_meaning package_slot_reading_system" for h
    by (auto simp: judgment_program_slot_schema_def schema_variables_def judgment_retention_call judgment_retention_components)
  have application: "?B judgment_application_slot_schema h \<longleftrightarrow>
      (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (Pair_Term (h 3) (h 5)) \<and>
      (178,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning judgment_retention_system \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 6) (h 7) (h 8) (h 9))
        \<in>positive_meaning application_reading_system \<and>
      (5,Pair_Term (h 5) (Pair_Term (h 9) (h 10)))\<in>positive_meaning bag_comparison_system" for h
    by (auto simp: judgment_application_slot_schema_def schema_variables_def judgment_retention_call judgment_retention_components)
  show ?thesis by (simp only: alternatives program application)
qed

lemma judgment_program_slot_step:
  assumes source: "(178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system"
    and slot: "(119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system"
  shows "(179,Pair_Term (judgment_context_term e pu pr au ar) x)\<in>positive_meaning judgment_retention_system"
proof -
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar" "term_formed x"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF slot]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then pu else if i=2 then pr else if i=3 then au else if i=4 then ar else x"
  show ?thesis by (simp only: judgment_demanded_slot_valuation; rule disjI1, rule exI[of _ ?h])
    (use source slot formed in auto)
qed

lemma judgment_application_slot_step:
  assumes source: "(178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system"
    and app: "(58,application_reading_argument e au ar d t i ks)\<in>positive_meaning application_reading_system"
    and slot: "selected_data_member k ks"
  shows "(179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term au k))\<in>positive_meaning judgment_retention_system"
proof -
  obtain rest where selected: "(5,Pair_Term k (Pair_Term ks rest))\<in>positive_meaning bag_comparison_system"
    using slot by blast
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    "term_formed k" "term_formed d" "term_formed t" "term_formed i" "term_formed ks" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF app]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au
    else if j=4 then ar else if j=5 then k else if j=6 then d else if j=7 then t else if j=8 then i else if j=9 then ks else rest"
  show ?thesis by (simp only: judgment_demanded_slot_valuation; rule disjI2, rule exI[of _ ?h])
    (use source app selected formed in auto)
qed

lemma judgment_demanded_slot_fields:
  "(179,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>e pu pr au ar x. z=Pair_Term (judgment_context_term e pu pr au ar) x \<and>
      (178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      ((119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<or>
       (\<exists>k d t i ks. x=Pair_Term au k \<and>
         (58,application_reading_argument e au ar d t i ks)\<in>positive_meaning application_reading_system \<and>
         selected_data_member k ks)))"
proof
  assume "(179,z)\<in>positive_meaning judgment_retention_system"
  then show "\<exists>e pu pr au ar x. z=Pair_Term (judgment_context_term e pu pr au ar) x \<and>
    (178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
    ((119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<or>
     (\<exists>k d t i ks. x=Pair_Term au k \<and>
       (58,application_reading_argument e au ar d t i ks)\<in>positive_meaning application_reading_system \<and>
       selected_data_member k ks))"
    by (simp only: judgment_demanded_slot_valuation) blast
next
  assume "\<exists>e pu pr au ar x. z=Pair_Term (judgment_context_term e pu pr au ar) x \<and>
    (178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
    ((119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<or>
     (\<exists>k d t i ks. x=Pair_Term au k \<and>
       (58,application_reading_argument e au ar d t i ks)\<in>positive_meaning application_reading_system \<and>
       selected_data_member k ks))"
  then show "(179,z)\<in>positive_meaning judgment_retention_system"
    using judgment_program_slot_step judgment_application_slot_step by blast
qed

lemma judgment_demanded_slot_at_context:
  "(179,Pair_Term (judgment_context_term e pu pr au ar) x)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
    ((119,Pair_Term (package_context_term e pu pr) x)\<in>positive_meaning package_slot_reading_system \<or>
     (\<exists>k d t i ks. x=Pair_Term au k \<and>
       (58,application_reading_argument e au ar d t i ks)\<in>positive_meaning application_reading_system \<and>
       selected_data_member k ks))"
  by (simp only: judgment_demanded_slot_fields factor_term.inject) blast

theorem judgment_demanded_slot_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K"
  shows "(179,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) x)
      \<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>u k. x=site_data_term u k \<and> (u,k)\<in>native_judgment_demands E pu pr au ar)"
proof -
  have admitted: "(178,judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_source_on_values[OF source]) (use package app in blast)
  have unique: "L=K" if "native_application_at E au ar c v J L" for c v J L
    using native_application_unique[OF that app] by blast
  have application: "(\<exists>k c v i ks. x=Pair_Term (use_data_term au) k \<and>
      (58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
        \<in>positive_meaning application_reading_system \<and> selected_data_member k ks) \<longleftrightarrow>
    (\<exists>k. x=site_data_term au k \<and> k\<in>K)"
  proof
    assume "\<exists>k c v i ks. x=Pair_Term (use_data_term au) k \<and>
      (58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
        \<in>positive_meaning application_reading_system \<and> selected_data_member k ks"
    then obtain y c v i ks where shape: "x=Pair_Term (use_data_term au) y"
      and read: "(58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
        \<in>positive_meaning application_reading_system" and selected: "selected_data_member y ks" by blast
    have observed: "\<exists>c v i ks. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
      \<in>positive_meaning application_reading_system \<and> selected_data_member y ks" using read selected by blast
    obtain k c v J L where fields: "y=Payload_Term k" "native_application_at E au ar c v J L" "k\<in>L"
      using observed by (simp only: application_slot_observation[OF source]) blast
    have same: "L=K" by (rule unique[OF fields(2)])
    show "\<exists>k. x=site_data_term au k \<and> k\<in>K"
      by (rule exI[of _ k]) (use shape fields same in \<open>simp add: site_data_term_def\<close>)
  next
    assume "\<exists>k. x=site_data_term au k \<and> k\<in>K"
    then obtain k where shape: "x=site_data_term au k" and member: "k\<in>K" by blast
    have observed: "\<exists>c v i ks. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
      \<in>positive_meaning application_reading_system \<and> selected_data_member (Payload_Term k) ks"
      by (simp only: application_slot_observation[OF source]) (use app member in blast)
    show "\<exists>k c v i ks. x=Pair_Term (use_data_term au) k \<and>
      (58,application_reading_argument e (use_data_term au) (Payload_Term ar) c v i ks)
        \<in>positive_meaning application_reading_system \<and> selected_data_member k ks"
      using observed shape by (simp only: site_data_term_def) blast
  qed
  show ?thesis
    by (simp only: judgment_demanded_slot_at_context admitted package_slot_reading_at_read[OF source package] application
        native_judgment_demands_def native_application_demands_at[OF app];
      auto simp: site_data_term_def)
qed

lemma judgment_demanded_slot_source:
  assumes "(179,t)\<in>positive_meaning judgment_retention_system"
  shows "\<exists>z p q. t=Pair_Term p q \<and> judgment_source_presents z p"
  using assms by (simp only: judgment_demanded_slot_fields judgment_source_exact) blast

theorem judgment_demanded_slot_at_presentation:
  assumes source: "judgment_source_presents z p"
  shows "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>a. site_coordinate_presents a q \<and> a\<in>judgment_required_slots z)"
proof -
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d t I K where presented: "environment_value_presents E e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using source by (simp only: coordinates judgment_source_presentation_fields) blast
  show ?thesis by (simp only: shape judgment_demanded_slot_at_read[OF presented reads] coordinates fst_conv snd_conv)
    (auto simp: site_data_term_def)
qed

abbreviation judgment_demanded_slot_result :: "factor_term \<Rightarrow> bool" where
  "judgment_demanded_slot_result t \<equiv> \<exists>z p a.
    t=Pair_Term p (definition_site_value a) \<and> judgment_source_presents z p \<and> a\<in>judgment_required_slots z"

theorem judgment_demanded_slot_exact:
  "(179,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_demanded_slot_result t"
proof
  assume holds: "(179,t)\<in>positive_meaning judgment_retention_system"
  obtain z p q where shape: "t=Pair_Term p q" and source: "judgment_source_presents z p"
    using judgment_demanded_slot_source[OF holds] by blast
  have query: "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system" using holds by (simp only: shape)
  obtain a where reported_site: "site_coordinate_presents a q" "a\<in>judgment_required_slots z"
    using query by (simp only: judgment_demanded_slot_at_presentation[OF source]) blast
  show "judgment_demanded_slot_result t"
    by (rule exI[of _ z], rule exI[of _ p], rule exI[of _ a]) (use shape source reported_site in simp)
next
  assume "judgment_demanded_slot_result t"
  then obtain z p a where shape: "t=Pair_Term p (definition_site_value a)"
    and source: "judgment_source_presents z p" and member: "a\<in>judgment_required_slots z" by blast
  show "(179,t)\<in>positive_meaning judgment_retention_system"
    by (simp only: shape judgment_demanded_slot_at_presentation[OF source]; rule exI[of _ a])
      (use member in simp)
qed

section \<open>Required uses have an actual source or demanded-binding role\<close>

lemma judgment_required_root_step:
  assumes source: "(178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system"
  shows "(180,Pair_Term (judgment_context_term e pu pr au ar) (if application then au else pu))
    \<in>positive_meaning judgment_retention_system"
proof -
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then pu else if i=2 then pr else if i=3 then au else ar"
  have result: "(180,evaluate_pattern ?h (schema_conclusion (judgment_required_root_schema application)))
      \<in>positive_meaning judgment_retention_system"
    by (rule ordinary_positive_valuation_step[where c="if application then 1 else 0"])
      (use source formed in \<open>auto simp: judgment_required_root_schema_def schema_variables_def
        judgment_retention_call split: if_splits\<close>)
  show ?thesis using result by (cases application) (simp_all add: judgment_required_root_schema_def)
qed

lemma judgment_required_definition_step:
  assumes source: "(178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system"
    and selected_definition: "(83,package_subject_argument e pu pr (Pair_Term v a))\<in>positive_meaning package_membership_system"
  shows "(180,Pair_Term (judgment_context_term e pu pr au ar) v)\<in>positive_meaning judgment_retention_system"
proof -
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar" "term_formed v" "term_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected_definition]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then pu else if i=2 then pr else if i=3 then au
    else if i=4 then ar else if i=5 then v else a"
  have result: "(180,evaluate_pattern ?h (schema_conclusion judgment_required_definition_schema))\<in>positive_meaning judgment_retention_system"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use source selected_definition formed in \<open>auto simp: judgment_required_definition_schema_def schema_variables_def
        judgment_retention_call judgment_retention_components\<close>)
  show ?thesis using result by (simp add: judgment_required_definition_schema_def)
qed

lemma judgment_required_target_step:
  assumes slot: "(179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term u k))\<in>positive_meaning judgment_retention_system"
    and binding: "(38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system"
  shows "(180,Pair_Term (judgment_context_term e pu pr au ar) v)\<in>positive_meaning judgment_retention_system"
proof -
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    "term_formed v" "term_formed u" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF slot]]
      schema_call_formed_target[OF positive_meaning_formed[OF binding]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then pu else if i=2 then pr else if i=3 then au
    else if i=4 then ar else if i=5 then v else if i=6 then u else k"
  have result: "(180,evaluate_pattern ?h (schema_conclusion judgment_required_target_schema))\<in>positive_meaning judgment_retention_system"
    by (rule ordinary_positive_valuation_step[where c=3])
      (use slot binding formed in \<open>auto simp: judgment_required_target_schema_def schema_variables_def
        judgment_retention_call judgment_retention_components\<close>)
  show ?thesis using result by (simp add: judgment_required_target_schema_def)
qed

lemma judgment_required_use_fields:
  "(180,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>e pu pr au ar v. t=Pair_Term (judgment_context_term e pu pr au ar) v \<and>
      (((178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
        (v=pu \<or> v=au \<or> (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term v a))
          \<in>positive_meaning package_membership_system))) \<or>
       (\<exists>u k. (179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term u k))
          \<in>positive_meaning judgment_retention_system \<and>
        (38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system)))"
proof
  assume holds: "(180,t)\<in>positive_meaning judgment_retention_system"
  have valuation: "(180,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>c S h. ((180,c),S)\<in>system_clauses judgment_retention_system \<and>
      (\<forall>a\<in>schema_variables S. term_formed (h a)) \<and> t=evaluate_pattern h (schema_conclusion S) \<and>
      schema_call_formed judgment_retention_system 180 t \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern h p)\<in>positive_meaning judgment_retention_system))"
    by (rule ordinary_positive_entry_valuation)
      (auto simp: judgment_required_root_schema_def judgment_required_definition_schema_def judgment_required_target_schema_def)
  obtain c S h where clause: "((180,c),S)\<in>system_clauses judgment_retention_system"
    and shape: "t=evaluate_pattern h (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning judgment_retention_system"
    using holds by (simp only: valuation) blast
  show "\<exists>e pu pr au ar v. t=Pair_Term (judgment_context_term e pu pr au ar) v \<and>
    (((178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      (v=pu \<or> v=au \<or> (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term v a))
        \<in>positive_meaning package_membership_system))) \<or>
     (\<exists>u k. (179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term u k))
        \<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system))"
  proof -
    let ?p="judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)"
    consider (program) "S=judgment_required_root_schema False"
      | (application) "S=judgment_required_root_schema True"
      | (defined) "S=judgment_required_definition_schema"
      | (target) "S=judgment_required_target_schema"
      using clause by auto
    then show ?thesis
    proof cases
      case program
      have encoded: "t=Pair_Term ?p (h 1)" using shape by (simp add: program judgment_required_root_schema_def)
      have read: "(178,?p)\<in>positive_meaning judgment_retention_system"
        using support[rule_format, of 0 178 "judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)"]
        by (simp add: program judgment_required_root_schema_def)
      show ?thesis
        by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
          rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 1"])
          (use encoded read in blast)
    next
      case application
      have encoded: "t=Pair_Term ?p (h 3)" using shape by (simp add: application judgment_required_root_schema_def)
      have read: "(178,?p)\<in>positive_meaning judgment_retention_system"
        using support[rule_format, of 0 178 "judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)"]
        by (simp add: application judgment_required_root_schema_def)
      show ?thesis
        by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
          rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 3"])
          (use encoded read in blast)
    next
      case defined
      have encoded: "t=Pair_Term ?p (h 5)" using shape by (simp add: defined judgment_required_definition_schema_def)
      have read: "(178,?p)\<in>positive_meaning judgment_retention_system"
        using support[rule_format, of 0 178 "judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4)"]
        by (simp add: defined judgment_required_definition_schema_def)
      have member: "(83,package_subject_argument (h 0) (h 1) (h 2) (Pair_Term (h 5) (h 6)))
          \<in>positive_meaning package_membership_system"
        using support[rule_format, of 1 83 "package_subject_pattern data_x data_y data_z
          (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))"]
        by (simp add: defined judgment_required_definition_schema_def judgment_retention_components)
      show ?thesis
        by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
          rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"])
          (use encoded read member in blast)
    next
      case target
      have encoded: "t=Pair_Term ?p (h 5)" using shape by (simp add: target judgment_required_target_schema_def)
      have slot: "(179,Pair_Term ?p (Pair_Term (h 6) (h 7)))\<in>positive_meaning judgment_retention_system"
        using support[rule_format, of 0 179 "Pattern_Pair
          (judgment_context_pattern data_x data_y data_z data_w (Pattern_Variable 4))
          (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7))"]
        by (simp add: target judgment_required_target_schema_def)
      have binding: "(38,binding_lookup_argument (h 0) (h 6) (h 7) (h 5))\<in>positive_meaning binding_lookup_system"
        using support[rule_format, of 1 38 "binding_lookup_pattern data_x (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 5)"]
        by (simp add: target judgment_required_target_schema_def judgment_retention_components)
      show ?thesis
        by (rule exI[of _ "h 0"], rule exI[of _ "h 1"], rule exI[of _ "h 2"],
          rule exI[of _ "h 3"], rule exI[of _ "h 4"], rule exI[of _ "h 5"])
          (use encoded slot binding in blast)
    qed
  qed
next
  assume "\<exists>e pu pr au ar v. t=Pair_Term (judgment_context_term e pu pr au ar) v \<and>
    (((178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      (v=pu \<or> v=au \<or> (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term v a))
        \<in>positive_meaning package_membership_system))) \<or>
     (\<exists>u k. (179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term u k))
        \<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system))"
  then show "(180,t)\<in>positive_meaning judgment_retention_system"
    using judgment_required_root_step[where application=False] judgment_required_root_step[where application=True]
      judgment_required_definition_step judgment_required_target_step by auto
qed

lemma judgment_required_use_at_context:
  "(180,Pair_Term (judgment_context_term e pu pr au ar) v)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    ((178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      (v=pu \<or> v=au \<or> (\<exists>a. (83,package_subject_argument e pu pr (Pair_Term v a))
        \<in>positive_meaning package_membership_system))) \<or>
    (\<exists>u k. (179,Pair_Term (judgment_context_term e pu pr au ar) (Pair_Term u k))
      \<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k v)\<in>positive_meaning binding_lookup_system)"
  by (simp only: judgment_required_use_fields factor_term.inject) blast

theorem judgment_required_use_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K"
  shows "(180,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) x)
      \<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> v\<in>read_environment_uses E (native_judgment_sources E pu pr au)
      (native_judgment_demands E pu pr au ar))"
proof -
  have admitted: "(178,judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_source_on_values[OF source]) (use package app in blast)
  have unique: "Q=P" if "native_package_at E pu pr Q" for Q by (rule native_package_unique[OF that package])
  have definitions: "(\<exists>a. (83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term x a))
      \<in>positive_meaning package_membership_system) \<longleftrightarrow>
    (\<exists>v a. x=use_data_term v \<and> (v,a)\<in>system_definitions P)"
  proof
    assume "\<exists>a. (83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term x a))
      \<in>positive_meaning package_membership_system"
    then obtain a where member: "(83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term x a))
      \<in>positive_meaning package_membership_system" by blast
    obtain q Q where fields: "Pair_Term x a=definition_site_value q" "native_package_at E pu pr Q" "q\<in>system_definitions Q"
      using member by (simp only: package_membership_at_source[OF source])
        (auto simp: inj_eq[OF use_data_term_injective])
    have same: "Q=P" by (rule unique[OF fields(2)])
    have encoded_value: "x=use_data_term (fst q)" using fields(1) by (simp add: site_data_term_def)
    show "\<exists>v a. x=use_data_term v \<and> (v,a)\<in>system_definitions P"
      by (rule exI[of _ "fst q"], rule exI[of _ "snd q"]) (use fields(3) same encoded_value in simp)
  next
    assume "\<exists>v a. x=use_data_term v \<and> (v,a)\<in>system_definitions P"
    then obtain v a where fields: "x=use_data_term v" "(v,a)\<in>system_definitions P" by blast
    have member: "(83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value (v,a)))
      \<in>positive_meaning package_membership_system"
      by (simp only: package_membership_at_package[OF source package]; rule fields(2))
    show "\<exists>a. (83,package_subject_argument e (use_data_term pu) (Payload_Term pr) (Pair_Term x a))
      \<in>positive_meaning package_membership_system"
      by (rule exI[of _ "Payload_Term a"]) (use member in \<open>simp add: fields(1) site_data_term_def\<close>)
  qed
  let ?j="judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
  have targets: "(\<exists>u k. (179,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) (Pair_Term u k))
        \<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system) \<longleftrightarrow>
    (\<exists>v a w. x=use_data_term w \<and> (v,a)\<in>native_judgment_demands E pu pr au ar \<and> binds_slot E v a w)"
  proof
    assume "\<exists>u k. (179,Pair_Term ?j (Pair_Term u k))\<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system"
    then obtain u k where slot: "(179,Pair_Term ?j (Pair_Term u k))\<in>positive_meaning judgment_retention_system"
      and binding: "(38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system" by blast
    obtain v a w where fields: "u=use_data_term v" "k=Payload_Term a" "x=use_data_term w" "binds_slot E v a w"
      using binding by (simp only: binding_lookup_at_source[OF source]) blast
    have demand: "(v,a)\<in>native_judgment_demands E pu pr au ar"
      using slot by (simp only: fields(1,2) judgment_demanded_slot_at_read[OF source package app])
        (auto simp: site_data_term_def inj_eq[OF use_data_term_injective])
    show "\<exists>v a w. x=use_data_term w \<and> (v,a)\<in>native_judgment_demands E pu pr au ar \<and> binds_slot E v a w"
      by (rule exI[of _ v], rule exI[of _ a], rule exI[of _ w]) (use fields(3,4) demand in blast)
  next
    assume "\<exists>v a w. x=use_data_term w \<and> (v,a)\<in>native_judgment_demands E pu pr au ar \<and> binds_slot E v a w"
    then obtain v a w where fields: "x=use_data_term w" "(v,a)\<in>native_judgment_demands E pu pr au ar" "binds_slot E v a w" by blast
    have slot: "(179,Pair_Term ?j (Pair_Term (use_data_term v) (Payload_Term a)))\<in>positive_meaning judgment_retention_system"
      by (simp only: judgment_demanded_slot_at_read[OF source package app]; rule exI[of _ v], rule exI[of _ a])
        (use fields(2) in \<open>simp add: site_data_term_def\<close>)
    have binding: "(38,binding_lookup_argument e (use_data_term v) (Payload_Term a) x)\<in>positive_meaning binding_lookup_system"
      by (simp only: binding_lookup_at_source[OF source]; rule exI[of _ v], rule exI[of _ a], rule exI[of _ w])
        (use fields(1,3) in blast)
    show "\<exists>u k. (179,Pair_Term ?j (Pair_Term u k))\<in>positive_meaning judgment_retention_system \<and>
      (38,binding_lookup_argument e u k x)\<in>positive_meaning binding_lookup_system"
      by (rule exI[of _ "use_data_term v"], rule exI[of _ "Payload_Term a"]) (use slot binding in blast)
  qed
  show ?thesis
    apply (simp only: judgment_required_use_at_context admitted definitions targets
      native_judgment_sources_def native_package_sources_def native_package_projection(3)[OF package, symmetric]
      read_environment_uses_def)
    apply auto
    subgoal for v a
      by (rule exI[of _ v]) (auto intro: rev_image_eqI)
    done
qed

lemma judgment_required_use_source:
  assumes "(180,t)\<in>positive_meaning judgment_retention_system"
  shows "\<exists>z p q. t=Pair_Term p q \<and> judgment_source_presents z p"
  using assms judgment_demanded_slot_source
  by (simp only: judgment_required_use_fields judgment_source_exact) blast

theorem judgment_required_use_at_presentation:
  assumes source: "judgment_source_presents z p"
  shows "(180,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>v. q=use_data_term v \<and> v\<in>judgment_required_uses z)"
proof -
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d t I K where presented: "environment_value_presents E e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using source by (simp only: coordinates judgment_source_presentation_fields) blast
  show ?thesis by (simp only: shape judgment_required_use_at_read[OF presented reads] coordinates fst_conv snd_conv)
qed

abbreviation judgment_required_use_result :: "factor_term \<Rightarrow> bool" where
  "judgment_required_use_result t \<equiv> \<exists>z p v.
    t=Pair_Term p (use_data_term v) \<and> judgment_source_presents z p \<and> v\<in>judgment_required_uses z"

theorem judgment_required_use_exact:
  "(180,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_required_use_result t"
  using judgment_required_use_source judgment_required_use_at_presentation by blast

text \<open>
  Slot membership is the union of the program's actual demands and every
  slot returned by the actual application reading. All outputs preserve
  their source use and local slot address.

  A required use is a program or call source, a reached definition source,
  or the actual target of a demanded binding. An unrelated stored binding
  cannot justify retaining its own target. Both queries retain source
  readability and reject every unsupported or malformed output.
\<close>

end
