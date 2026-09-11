theory Factor_Environment_Comparison
  imports Factor_Artifact_Admission Factor_Related_Bags Factor_Environment_Values
begin

section \<open>Artifact uses retain their exact coordinates\<close>

definition environment_entry_schema :: "(nat,nat,nat) factor_schema" where
  "environment_entry_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_x data_z))
    {(0,2,data_x),(1,12,Pattern_Pair data_y data_z)}"

definition environment_entry_system :: "(nat,nat,nat,nat) schema_system" where
  "environment_entry_system=add_view_definition artifact_identity_system 13 data_x {(0,environment_entry_schema)}"

interpretation environment_entry_view: positive_view artifact_identity_system 13 data_x "{(0,environment_entry_schema)}"
  by (rule positive_view.intro)
    (auto simp: environment_entry_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def)

lemma environment_entry_system_formed [simp]: "schema_system_formed environment_entry_system"
  using environment_entry_view.formed by (simp only: environment_entry_system_def)

lemma environment_entry_definitions [simp]:
  "system_definitions environment_entry_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13}"
  by (auto simp: environment_entry_system_def)

lemma environment_entry_call:
  "schema_call_formed environment_entry_system d t \<longleftrightarrow>
    d\<in>system_definitions environment_entry_system \<and> term_formed t"
proof -
  have prior: "schema_call_formed artifact_identity_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_identity_system \<and> term_formed t"
    by (simp add: artifact_identity_call)
  show ?thesis using added_variable_calls[OF artifact_identity_system_formed
    environment_entry_system_formed[unfolded environment_entry_system_def] prior]
    by (simp only: environment_entry_system_def[symmetric])
qed

theorem environment_entry_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}"
  shows "(d,t)\<in>positive_meaning environment_entry_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_identity_system"
  using environment_entry_view.old_meaning[of d t] assms by (simp add: environment_entry_system_def)

lemma environment_entry_clause [simp]:
  "((13,c),S)\<in>system_clauses environment_entry_system \<longleftrightarrow> c=0 \<and> S=environment_entry_schema"
  using environment_entry_view.no_old_clause[of c S] by (auto simp: environment_entry_system_def)

lemma environment_entry_data:
  "(2,t)\<in>positive_meaning environment_entry_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using environment_entry_old_meaning[of 2 t] artifact_identity_old_meaning[of 2 t]
    artifact_comparison_old_meaning[of 2 t] bag_comparison_recognizes[of t] by auto

lemma environment_entry_artifacts:
  "(12,t)\<in>positive_meaning environment_entry_system \<longleftrightarrow>
    (\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y)"
  using environment_entry_old_meaning[of 12 t] artifact_identity_exact[of t] by auto

theorem environment_entry_exact:
  "(13,t)\<in>positive_meaning environment_entry_system \<longleftrightarrow>
    (\<exists>k R x y. t=Pair_Term (Pair_Term k x) (Pair_Term k y) \<and>
      term_formed k \<and> self_contained_term k \<and>
      artifact_value_presents R x \<and> artifact_value_presents R y)"
proof
  assume holds: "(13,t)\<in>positive_meaning environment_entry_system"
  have consequence: "(13,t)\<in>schema_consequences environment_entry_system (positive_meaning environment_entry_system)"
    using holds positive_meaning_unfold[of environment_entry_system] by blast
  obtain c S v where clause: "((13,c),S)\<in>system_clauses environment_entry_system"
    and head: "t=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning environment_entry_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=environment_entry_schema" using clause by simp
  have key: "term_formed (v 0) \<and> self_contained_term (v 0)"
    and subjects: "\<exists>R. artifact_value_presents R (v 1) \<and> artifact_value_presents R (v 2)"
    using support by (auto simp: schema environment_entry_schema_def environment_entry_data environment_entry_artifacts)
  show "\<exists>k R x y. t=Pair_Term (Pair_Term k x) (Pair_Term k y) \<and>
    term_formed k \<and> self_contained_term k \<and> artifact_value_presents R x \<and> artifact_value_presents R y"
    using head key subjects by (auto simp: schema environment_entry_schema_def)
next
  assume "\<exists>k R x y. t=Pair_Term (Pair_Term k x) (Pair_Term k y) \<and>
    term_formed k \<and> self_contained_term k \<and> artifact_value_presents R x \<and> artifact_value_presents R y"
  then obtain k R x y where shape: "t=Pair_Term (Pair_Term k x) (Pair_Term k y)"
    and key: "term_formed k" "self_contained_term k"
    and left: "artifact_value_presents R x" and right: "artifact_value_presents R y" by blast
  have formed: "term_formed x" "term_formed y"
    using artifact_value_presents_formed[OF left] artifact_value_presents_formed[OF right] by auto
  have children: "(2,k)\<in>positive_meaning environment_entry_system"
    "(12,Pair_Term x y)\<in>positive_meaning environment_entry_system"
    using key left right by (auto simp: environment_entry_data environment_entry_artifacts)
  let ?v="\<lambda>i::nat. if i=0 then k else if i=1 then x else y"
  have result: "(13,evaluate_pattern ?v (schema_conclusion environment_entry_schema))\<in>positive_meaning environment_entry_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use key formed children in \<open>auto simp: environment_entry_schema_def schema_variables_def environment_entry_call\<close>)
  show "(13,t)\<in>positive_meaning environment_entry_system"
    using result by (simp add: shape environment_entry_schema_def)
qed

lemma environment_entry_domain:
  assumes "(13,Pair_Term x y)\<in>positive_meaning environment_entry_system"
  shows "term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y"
  using assms artifact_value_presents_formed by (auto simp: environment_entry_exact; blast)

theorem environment_entry_presentation_comparison:
  assumes left: "environment_artifact_entry_presents z x"
    and right: "environment_artifact_entry_presents w y"
  shows "(13,Pair_Term x y)\<in>positive_meaning environment_entry_system \<longleftrightarrow> z=w"
proof -
  obtain a where first: "x=Pair_Term (use_data_term (fst z)) a" "artifact_value_presents (snd z) a"
    using left unfolding environment_artifact_entry_presents_def by blast
  obtain b where second: "y=Pair_Term (use_data_term (fst w)) b" "artifact_value_presents (snd w) b"
    using right unfolding environment_artifact_entry_presents_def by blast
  have coordinates: "use_data_term u=use_data_term v \<longleftrightarrow> u=v" for u v
    using use_data_term_injective by (auto dest: injD)
  have artifacts: "(\<exists>R. artifact_value_presents R a \<and> artifact_value_presents R b) \<longleftrightarrow> snd z=snd w"
    using admitted_artifact_comparison[OF first(2) second(2)] by (simp add: artifact_identity_exact)
  show ?thesis by (auto simp: environment_entry_exact first(1) second(1) coordinates artifacts prod_eq_iff)
qed

section \<open>Complete artifact-use collections are compared through their entries\<close>

definition environment_selection_system :: "(nat,nat,nat,nat) schema_system" where
  "environment_selection_system=add_view_definition environment_entry_system 14 data_x
    (related_selection_clauses 2 4 13 14)"

definition environment_bag_system :: "(nat,nat,nat,nat) schema_system" where
  "environment_bag_system=add_view_definition environment_selection_system 15 data_x (related_bag_clauses 14 15)"

lemma environment_selection_system_formed [simp]: "schema_system_formed environment_selection_system"
  unfolding environment_selection_system_def
  by (rule add_recursive_definition_formed[OF environment_entry_system_formed])
    (auto simp: related_selection_clauses_def related_selection_here_schema_def selection_later_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma environment_selection_definitions [simp]:
  "system_definitions environment_selection_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14}"
  by (auto simp: environment_selection_system_def)

lemma environment_bag_system_formed [simp]: "schema_system_formed environment_bag_system"
  unfolding environment_bag_system_def
  by (rule add_recursive_definition_formed[OF environment_selection_system_formed])
    (auto simp: related_bag_clauses_def bag_nil_schema_def bag_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma environment_bag_definitions [simp]:
  "system_definitions environment_bag_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}"
  by (auto simp: environment_bag_system_def)

lemma environment_selection_call:
  "schema_call_formed environment_selection_system d t \<longleftrightarrow>
    d\<in>system_definitions environment_selection_system \<and> term_formed t"
  using added_variable_calls[OF environment_entry_system_formed
    environment_selection_system_formed[unfolded environment_selection_system_def] environment_entry_call]
  by (simp only: environment_selection_system_def[symmetric])

lemma environment_bag_call:
  "schema_call_formed environment_bag_system d t \<longleftrightarrow>
    d\<in>system_definitions environment_bag_system \<and> term_formed t"
  using added_variable_calls[OF environment_selection_system_formed
    environment_bag_system_formed[unfolded environment_bag_system_def] environment_selection_call]
  by (simp only: environment_bag_system_def[symmetric])

lemma environment_selection_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13}"
  shows "(d,t)\<in>positive_meaning environment_selection_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_entry_system"
  using added_definition_preserves_old(2)[OF environment_entry_system_formed
    environment_selection_system_formed[unfolded environment_selection_system_def], of d t] assms
  by (auto simp: environment_selection_system_def)

lemma environment_bag_previous_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14}"
  shows "(d,t)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_selection_system"
  using added_definition_preserves_old(2)[OF environment_selection_system_formed
    environment_bag_system_formed[unfolded environment_bag_system_def], of d t] assms
  by (auto simp: environment_bag_system_def)

theorem environment_bag_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13}"
  shows "(d,t)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_entry_system"
  using environment_bag_previous_meaning[of d t] environment_selection_old_meaning[OF assms, of t] assms by auto

lemma environment_bag_base_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6}"
  shows "(d,t)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using environment_bag_old_meaning[of d t] environment_entry_old_meaning[of d t]
    artifact_identity_old_meaning[of d t] artifact_comparison_old_meaning[OF assms, of t] assms by auto

lemma environment_bag_families [simp]:
  "((14,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow>
    (c,S)\<in>related_selection_clauses 2 4 13 14"
  "((15,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow> (c,S)\<in>related_bag_clauses 14 15"
proof -
  have owned: "((d,c),S)\<in>system_clauses environment_entry_system \<Longrightarrow>
    d\<in>system_definitions environment_entry_system" for d c S
    using environment_entry_system_formed unfolding schema_system_formed_def by blast
  have absent: "d\<in>{14,15} \<Longrightarrow> ((d,c),S)\<notin>system_clauses environment_entry_system" for d c S
    by (auto dest: owned)
  show "((14,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow>
    (c,S)\<in>related_selection_clauses 2 4 13 14"
    "((15,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow> (c,S)\<in>related_bag_clauses 14 15"
    using absent by (auto simp: environment_bag_system_def environment_selection_system_def)
qed

interpretation environment_bags: related_bags environment_bag_system 2 4 13 14 15
proof (rule related_bags.intro)
  show "schema_system_formed environment_bag_system" by simp
  show "\<And>c S. ((14,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow>
    (c,S)\<in>related_selection_clauses 2 4 13 14" by simp
  show "\<And>c S. ((15,c),S)\<in>system_clauses environment_bag_system \<longleftrightarrow>
    (c,S)\<in>related_bag_clauses 14 15" by simp
  show "\<And>t. schema_call_formed environment_bag_system 14 t \<longleftrightarrow> term_formed t"
    by (simp add: environment_bag_call)
  show "\<And>t. schema_call_formed environment_bag_system 15 t \<longleftrightarrow> term_formed t"
    by (simp add: environment_bag_call)
  show "(2,t)\<in>positive_meaning environment_bag_system \<longleftrightarrow> term_formed t \<and> self_contained_term t" for t
    using environment_bag_base_meaning[of 2 t] bag_comparison_recognizes[of t] by auto
  show "(4,t)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    (\<exists>xs. t=data_list_term xs \<and> data_elements xs)" for t
    using environment_bag_base_meaning[of 4 t] data_list_exact[of t] by auto
  show "(13,Pair_Term x y)\<in>positive_meaning environment_bag_system \<Longrightarrow>
    term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y" for x y
    using environment_bag_old_meaning[of 13 "Pair_Term x y"] environment_entry_domain[of x y] by auto
qed

theorem environment_artifact_collection_comparison:
  assumes left: "data_collection_presents environment_artifact_entry_presents A a"
    and right: "data_collection_presents environment_artifact_entry_presents B b"
  shows "(15,Pair_Term a b)\<in>positive_meaning environment_bag_system \<longleftrightarrow> A=B"
proof (rule environment_bags.comparison_collections[OF left right])
  fix z w x y
  assume first: "environment_artifact_entry_presents z x" and second: "environment_artifact_entry_presents w y"
  show "(13,Pair_Term x y)\<in>positive_meaning environment_bag_system \<longleftrightarrow> z=w"
    using environment_bag_old_meaning[of 13 "Pair_Term x y"]
      environment_entry_presentation_comparison[OF first second] by auto
qed

lemma environment_binding_collection_comparison:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and left: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E) a"
    and right: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings F) b"
  shows "(6,Pair_Term a b)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    environment_bindings E=environment_bindings F"
proof -
  obtain xs where first: "distinct xs" "set xs=environment_bindings E" "a=data_list_term (map binding_data xs)"
    using left by (auto simp: data_collection_presents_function)
  obtain ys where second: "distinct ys" "set ys=environment_bindings F" "b=data_list_term (map binding_data ys)"
    using right by (auto simp: data_collection_presents_function)
  have data: "data_elements (map binding_data xs)" "data_elements (map binding_data ys)"
    using first(2) second(2) binding_data_formed[OF ef] binding_data_formed[OF ff] by auto
  have identity: "mset (map binding_data xs)=mset (map binding_data ys) \<longleftrightarrow>
    environment_bindings E=environment_bindings F"
    using set_eq_iff_mset_eq_distinct[OF first(1) second(1)] first(2) second(2)
    by (simp only: injective_mapped_multisets[OF binding_data_injective]; blast)
  show ?thesis using environment_bag_base_meaning[of 6 "Pair_Term a b"] data identity
    by (simp only: first(3) second(3) bag_comparison_lists; blast)
qed

section \<open>Both complete environment fields determine exact identity\<close>

definition environment_comparison_schema :: "(nat,nat,nat) factor_schema" where
  "environment_comparison_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair data_z data_w))
    {(0,15,Pattern_Pair data_x data_z),(1,6,Pattern_Pair data_y data_w)}"

definition environment_comparison_system :: "(nat,nat,nat,nat) schema_system" where
  "environment_comparison_system=add_view_definition environment_bag_system 16 data_x {(0,environment_comparison_schema)}"

interpretation environment_comparison_view: positive_view environment_bag_system 16 data_x "{(0,environment_comparison_schema)}"
  by (rule positive_view.intro)
    (auto simp: environment_comparison_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def)

lemma environment_comparison_system_formed [simp]: "schema_system_formed environment_comparison_system"
  using environment_comparison_view.formed by (simp only: environment_comparison_system_def)

lemma environment_comparison_definitions [simp]:
  "system_definitions environment_comparison_system={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}"
  by (auto simp: environment_comparison_system_def)

lemma environment_comparison_call:
  "schema_call_formed environment_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions environment_comparison_system \<and> term_formed t"
  using added_variable_calls[OF environment_bag_system_formed
    environment_comparison_system_formed[unfolded environment_comparison_system_def] environment_bag_call]
  by (simp only: environment_comparison_system_def[symmetric])

theorem environment_comparison_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15}"
  shows "(d,t)\<in>positive_meaning environment_comparison_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_bag_system"
  using environment_comparison_view.old_meaning[of d t] assms by (simp add: environment_comparison_system_def)

theorem environment_comparison_artifact_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12}"
  shows "(d,t)\<in>positive_meaning environment_comparison_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_identity_system"
  using environment_comparison_old_meaning[of d t] environment_bag_old_meaning[of d t]
    environment_entry_old_meaning[OF assms, of t] assms by auto

lemma environment_comparison_clause [simp]:
  "((16,c),S)\<in>system_clauses environment_comparison_system \<longleftrightarrow> c=0 \<and> S=environment_comparison_schema"
  using environment_comparison_view.no_old_clause[of c S] by (auto simp: environment_comparison_system_def)

theorem environment_comparison_raw:
  "(16,t)\<in>positive_meaning environment_comparison_system \<longleftrightarrow>
    (\<exists>a b c d. t=Pair_Term (Pair_Term a b) (Pair_Term c d) \<and>
      (15,Pair_Term a c)\<in>positive_meaning environment_bag_system \<and>
      (6,Pair_Term b d)\<in>positive_meaning environment_bag_system)"
proof
  assume holds: "(16,t)\<in>positive_meaning environment_comparison_system"
  have consequence: "(16,t)\<in>schema_consequences environment_comparison_system (positive_meaning environment_comparison_system)"
    using holds positive_meaning_unfold[of environment_comparison_system] by blast
  obtain c S v where clause: "((16,c),S)\<in>system_clauses environment_comparison_system"
    and head: "t=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning environment_comparison_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=environment_comparison_schema" using clause by simp
  have children: "(15,Pair_Term (v 0) (v 2))\<in>positive_meaning environment_bag_system"
    "(6,Pair_Term (v 1) (v 3))\<in>positive_meaning environment_bag_system"
    using support environment_comparison_old_meaning[of 15] environment_comparison_old_meaning[of 6]
    by (auto simp: schema environment_comparison_schema_def)
  show "\<exists>a b c d. t=Pair_Term (Pair_Term a b) (Pair_Term c d) \<and>
    (15,Pair_Term a c)\<in>positive_meaning environment_bag_system \<and>
    (6,Pair_Term b d)\<in>positive_meaning environment_bag_system"
    using head children by (auto simp: schema environment_comparison_schema_def)
next
  assume "\<exists>a b c d. t=Pair_Term (Pair_Term a b) (Pair_Term c d) \<and>
    (15,Pair_Term a c)\<in>positive_meaning environment_bag_system \<and>
    (6,Pair_Term b d)\<in>positive_meaning environment_bag_system"
  then obtain a b c d where shape: "t=Pair_Term (Pair_Term a b) (Pair_Term c d)"
    and children: "(15,Pair_Term a c)\<in>positive_meaning environment_bag_system"
      "(6,Pair_Term b d)\<in>positive_meaning environment_bag_system" by blast
  have formed: "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    using children by (auto dest: positive_meaning_formed simp: environment_bag_call)
  have lifted: "(15,Pair_Term a c)\<in>positive_meaning environment_comparison_system"
    "(6,Pair_Term b d)\<in>positive_meaning environment_comparison_system"
    using children environment_comparison_old_meaning[of 15] environment_comparison_old_meaning[of 6] by auto
  let ?v="\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then c else d"
  have result: "(16,evaluate_pattern ?v (schema_conclusion environment_comparison_schema))
    \<in>positive_meaning environment_comparison_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed lifted in \<open>auto simp: environment_comparison_schema_def schema_variables_def environment_comparison_call\<close>)
  show "(16,t)\<in>positive_meaning environment_comparison_system"
    using result by (simp add: shape environment_comparison_schema_def)
qed

corollary environment_comparison_fields:
  "(16,Pair_Term (Pair_Term a b) (Pair_Term c d))\<in>positive_meaning environment_comparison_system \<longleftrightarrow>
    (15,Pair_Term a c)\<in>positive_meaning environment_bag_system \<and>
    (6,Pair_Term b d)\<in>positive_meaning environment_bag_system"
  by (simp add: environment_comparison_raw)

theorem environment_comparison_exact:
  assumes left: "environment_value_presents E x" and right: "environment_value_presents F y"
  shows "(16,Pair_Term x y)\<in>positive_meaning environment_comparison_system \<longleftrightarrow> E=F"
proof -
  obtain a b where ef: "environment_formed E" and first:
    "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E) b" "x=Pair_Term a b"
    using left unfolding environment_value_presents_def by blast
  obtain c d where ff: "environment_formed F" and second:
    "data_collection_presents environment_artifact_entry_presents (environment_artifacts F) c"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings F) d" "y=Pair_Term c d"
    using right unfolding environment_value_presents_def by blast
  have artifacts: "(15,Pair_Term a c)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    environment_artifacts E=environment_artifacts F"
    by (rule environment_artifact_collection_comparison[OF first(1) second(1)])
  have bindings: "(6,Pair_Term b d)\<in>positive_meaning environment_bag_system \<longleftrightarrow>
    environment_bindings E=environment_bindings F"
    by (rule environment_binding_collection_comparison[OF ef ff first(2) second(2)])
  have identity: "E=F \<longleftrightarrow>
    environment_artifacts E=environment_artifacts F \<and> environment_bindings E=environment_bindings F"
    by (cases E; cases F) auto
  show ?thesis by (simp only: first(3) second(3) environment_comparison_fields artifacts bindings identity)
qed

corollary environment_comparison_presentation_invariance:
  assumes "environment_value_presents E x" "environment_value_presents E x'"
    "environment_value_presents F y" "environment_value_presents F y'"
  shows "(16,Pair_Term x y)\<in>positive_meaning environment_comparison_system \<longleftrightarrow>
    (16,Pair_Term x' y')\<in>positive_meaning environment_comparison_system"
  using environment_comparison_exact[OF assms(1,3)] environment_comparison_exact[OF assms(2,4)] by blast

section \<open>One closed native program serves all future presented environments\<close>

theorem native_environment_comparison:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d. closed_native_package_at E pu [] Q \<and>
    (\<forall>A B x y. environment_value_presents A x \<longrightarrow> environment_value_presents B y \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] d (Pair_Term x y) I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> A=B)))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions environment_comparison_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed environment_comparison_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning environment_comparison_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF environment_comparison_system_formed] by blast
  have member: "16\<in>system_definitions environment_comparison_system" by simp
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g 16"], intro conjI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
  next
    fix A B x y assume left: "environment_value_presents A x" and right: "environment_value_presents B y"
    have tf: "term_formed (Pair_Term x y)"
      using environment_value_presents_formed[OF left] environment_value_presents_formed[OF right] by simp
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g 16) (Pair_Term x y) I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed environment_comparison_system 16 (Pair_Term x y)"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (16,Pair_Term x y)\<in>positive_meaning environment_comparison_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g 16) (Pair_Term x y) I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> A=B)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf environment_comparison_exact[OF left right]
          in \<open>auto simp: environment_comparison_call\<close>)
  qed
qed

text \<open>
  The complete artifact-use field is compared through the entry definition.
  Its repeated key variable preserves the exact use coordinate, while its
  artifact callee admits both values and compares their represented artifacts.
  Different valid artifact presentations therefore remain comparable at the
  same use. Equal artifacts at different uses remain different entries.

  The binding field uses the earlier exact bag rule. Its source use, original
  slot address, and target use have an injective data encoding. Complete
  distinct-entry presentations therefore recover equality of the entire
  binding relation, including cycles. No use graph is recursively expanded.

  The environment identity theorem assumes both complete formed environment
  presentations. The displayed comparison rules also describe their full raw
  input behavior; they do not enforce the environment's single-valued tables,
  binding-source slot membership, or target-use existence. Admission of those
  laws remains a separate native checking obligation.

  Every earlier interface and meaning is preserved. The resulting ordinary
  extensions give seventeen definitions and thirty-two clauses in the complete
  program, including the inherited material clauses. One fixed closed native
  package compares every future pair of presented environments and retains
  its canonical program environment.
\<close>

end
