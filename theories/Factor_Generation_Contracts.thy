theory Factor_Generation_Contracts
  imports Factor_Generation_Admission
begin

section \<open>The generation notion exports its complete native contracts\<close>

theorem generation_native_presentation_class:
  "presentation_class generation_value_presents generation_formed
    (\<lambda>t. (139,t)\<in>positive_meaning generation_value_system)"
  using generation_value_presentation_class by (simp only: generation_admission_exact)

interpretation generation_native_presentations: presentation_class generation_value_presents generation_formed
  "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  by (rule generation_native_presentation_class)

abbreviation generation_identity_result :: "factor_term \<Rightarrow> bool" where
  "generation_identity_result t \<equiv> \<exists>G H p q. t=Pair_Term p q \<and>
    generation_value_presents G p \<and> generation_value_presents H q \<and> G=H"

abbreviation generation_difference_result :: "factor_term \<Rightarrow> bool" where
  "generation_difference_result t \<equiv> \<exists>G H p q. t=Pair_Term p q \<and>
    generation_value_presents G p \<and> generation_value_presents H q \<and> G\<noteq>H"

theorem generation_identity_exact:
  "(140,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_identity_result t"
proof
  assume holds: "(140,t)\<in>positive_meaning generation_value_system"
  obtain p q where parts: "t=Pair_Term p q" "(139,p)\<in>positive_meaning generation_value_system"
    "(139,q)\<in>positive_meaning generation_value_system"
    using generation_comparison_admitted(1)[OF holds] by blast
  obtain G H where read: "generation_value_presents G p" "generation_value_presents H q"
    using parts(2,3) by (simp only: generation_admission_exact) blast
  have equal: "G=H" using holds parts(1) generation_identity_on_values[OF read] by blast
  show "generation_identity_result t" using parts(1) read equal by blast
next
  assume "generation_identity_result t"
  then show "(140,t)\<in>positive_meaning generation_value_system" using generation_identity_on_values by blast
qed

theorem generation_difference_exact:
  "(141,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_difference_result t"
proof
  assume holds: "(141,t)\<in>positive_meaning generation_value_system"
  obtain p q where parts: "t=Pair_Term p q" "(139,p)\<in>positive_meaning generation_value_system"
    "(139,q)\<in>positive_meaning generation_value_system"
    using generation_comparison_admitted(2)[OF holds] by blast
  obtain G H where read: "generation_value_presents G p" "generation_value_presents H q"
    using parts(2,3) by (simp only: generation_admission_exact) blast
  have different: "G\<noteq>H" using holds parts(1) generation_difference_on_values[OF read] by blast
  show "generation_difference_result t" using parts(1) read different by blast
next
  assume "generation_difference_result t"
  then show "(141,t)\<in>positive_meaning generation_value_system" using generation_difference_on_values by blast
qed

interpretation generation_identity_contract: presented_relation_contract
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  "(=)" "\<lambda>p q. (140,Pair_Term p q)\<in>positive_meaning generation_value_system"
  by (unfold_locales)
    (use generation_native_presentation_class generation_identity_exact in
      \<open>auto simp: presentation_class_def presented_relation_def\<close>)

interpretation generation_difference_contract: presented_relation_contract
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  "(\<noteq>)" "\<lambda>p q. (141,Pair_Term p q)\<in>positive_meaning generation_value_system"
  by (unfold_locales)
    (use generation_native_presentation_class generation_difference_exact in
      \<open>auto simp: presentation_class_def presented_relation_def\<close>)

theorem generation_collection_presentation_class:
  "presentation_class (data_collection_presents generation_value_presents)
    (\<lambda>A. finite A \<and> (\<forall>G\<in>A. generation_formed G))
    (\<lambda>t. (143,t)\<in>positive_meaning generation_value_system)"
  by (rule generation_collections.collection_presentation_class)
    (rule generation_difference_contract.presented_relation_contract_axioms)

interpretation generation_collection_presentations:
  presentation_class "data_collection_presents generation_value_presents"
    "\<lambda>A. finite A \<and> (\<forall>G\<in>A. generation_formed G)" "\<lambda>t. (143,t)\<in>positive_meaning generation_value_system"
  by (rule generation_collection_presentation_class)

theorem generation_collection_exact:
  "(143,t)\<in>positive_meaning generation_value_system \<longleftrightarrow>
    (\<exists>A. data_collection_presents generation_value_presents A t)"
  by (rule generation_collection_presentations.admissible_iff)

corollary generation_comparison_invariance:
  assumes "generation_value_presents G p" "generation_value_presents H q"
    "generation_value_presents G p'" "generation_value_presents H q'"
  shows "(140,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (140,Pair_Term p' q')\<in>positive_meaning generation_value_system"
    and "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow>
      (141,Pair_Term p' q')\<in>positive_meaning generation_value_system"
  using generation_identity_contract.invariance[OF assms]
    generation_difference_contract.invariance[OF assms] by blast+

corollary generation_collection_two_members:
  assumes "generation_value_presents G p" "generation_value_presents H q"
  shows "(143,data_list_term [p,q])\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
  using generation_collections.collection_lists[of "[p,q]"] assms
    generation_difference_contract.at[OF assms] by (auto simp: generation_admission_exact)

corollary generation_duplicate_predecessors_rejected:
  assumes "generation_value_presents G p" "generation_value_presents G q"
  shows "(139,Pair_Term a (Pair_Term (data_list_term [p,q]) (Pair_Term c d)))\<notin>positive_meaning generation_value_system"
  using generation_collection_two_members[OF assms] by (auto simp: generation_admission_fields)

corollary generation_collection_empty:
  "(143,Payload_Term [])\<in>positive_meaning generation_value_system"
  by (simp add: generation_collections.collection_lists[of "[]", simplified])

corollary generation_native_total:
  assumes "generation_formed G"
  shows "\<exists>t. generation_value_presents G t \<and> (139,t)\<in>positive_meaning generation_value_system"
  using generation_native_presentations.total[OF assms]
    generation_native_presentations.presentation_boundary by blast

corollary generation_base_native_total:
  assumes "target_formed l" "target_formed p" "target_formed q"
  shows "\<exists>t. generation_value_presents (Generation l {||} p q) t \<and>
    (139,t)\<in>positive_meaning generation_value_system"
  by (rule generation_native_total, rule generation_formed.formed[OF assms]) simp

corollary generation_successor_native_total:
  assumes "generation_formed G" "target_formed l" "target_formed p" "target_formed q"
  shows "\<exists>t. generation_value_presents (Generation l {|G|} p q) t \<and>
    (139,t)\<in>positive_meaning generation_value_system"
  by (rule generation_native_total, rule generation_formed.formed[OF assms(2-4)]) (use assms(1) in simp)

corollary generation_collection_native_total:
  assumes "finite A" "\<forall>G\<in>A. generation_formed G"
  shows "\<exists>t. data_collection_presents generation_value_presents A t \<and>
    (143,t)\<in>positive_meaning generation_value_system"
  using generation_collection_presentations.total assms
    generation_collection_presentations.presentation_boundary by blast

section \<open>Auxiliary operations retain their complete raw domains\<close>

lemma generation_comparison_relations:
  "(\<lambda>p q. (140,Pair_Term p q)\<in>positive_meaning generation_value_system)=
    presented_relation generation_value_presents generation_value_presents (=)"
  "(\<lambda>p q. (141,Pair_Term p q)\<in>positive_meaning generation_value_system)=
    presented_relation generation_value_presents generation_value_presents (\<noteq>)"
  by (intro ext; rule generation_identity_contract.exact | intro ext; rule generation_difference_contract.exact)+

abbreviation generation_separation_result :: "factor_term \<Rightarrow> bool" where
  "generation_separation_result t \<equiv> \<exists>x xs. t=Pair_Term x (data_list_term xs) \<and> term_formed x \<and>
    (\<forall>y\<in>set xs. presented_relation generation_value_presents generation_value_presents (\<noteq>) x y)"

abbreviation generation_selection_result :: "factor_term \<Rightarrow> bool" where
  "generation_selection_result t \<equiv> \<exists>x y pre post. t=Pair_Term x
    (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))) \<and>
    data_elements (pre@y#post) \<and> presented_relation generation_value_presents generation_value_presents (=) x y"

abbreviation generation_bag_identity_result :: "factor_term \<Rightarrow> bool" where
  "generation_bag_identity_result t \<equiv> \<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and>
    rel_mset (presented_relation generation_value_presents generation_value_presents (=)) (mset xs) (mset ys)"

abbreviation generation_bag_difference_result :: "factor_term \<Rightarrow> bool" where
  "generation_bag_difference_result t \<equiv> \<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and>
    bag_difference_witness (presented_relation generation_value_presents generation_value_presents (=))
      (presented_relation generation_value_presents generation_value_presents (\<noteq>)) xs ys"

theorem generation_helper_operations_exact:
  "(142,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_separation_result t"
  "(144,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_selection_result t"
  "(145,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_bag_identity_result t"
  "(146,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_bag_difference_result t"
  by (simp_all only: generation_bags.absence_exact generation_bags.selection_exact
    generation_bags.comparison_exact generation_bags.difference_exact generation_comparison_relations
    generation_identity_contract.exact generation_difference_contract.exact)

corollary generation_absence_on_values:
  assumes "generation_value_presents G p" "data_collection_presents generation_value_presents A t"
  shows "(142,Pair_Term p t)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<notin>A"
proof -
  obtain xs ps where parts: "set xs=A" "list_all2 generation_value_presents xs ps" "t=data_list_term ps"
    using assms(2) unfolding data_collection_presents_def by blast
  have members: "(\<forall>H\<in>A. \<exists>q\<in>set ps. generation_value_presents H q) \<and>
      (\<forall>q\<in>set ps. \<exists>H\<in>A. generation_value_presents H q)"
    using list_all2_members[OF parts(2)] parts(1) by blast
  have compare: "(141,Pair_Term p q)\<in>positive_meaning generation_value_system \<longleftrightarrow> G\<noteq>H"
    if "generation_value_presents H q" for H q
    by (rule generation_difference_contract.at[OF assms(1) that])
  have formed: "term_formed p" using generation_value_presents_formed[OF assms(1)] by blast
  show ?thesis using members compare formed by (simp only: parts(3) generation_bags.absence_lists; blast)
qed

abbreviation generation_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_operation_result d t \<equiv>
    if d=139 then (\<exists>G. generation_value_presents G t)
    else if d=140 then generation_identity_result t
    else if d=141 then generation_difference_result t
    else if d=142 then generation_separation_result t
    else if d=143 then (\<exists>A. data_collection_presents generation_value_presents A t)
    else if d=144 then generation_selection_result t
    else if d=145 then generation_bag_identity_result t
    else generation_bag_difference_result t"

theorem generation_operations_exact:
  assumes "d\<in>{139,140,141,142,143,144,145,146}"
  shows "(d,t)\<in>positive_meaning generation_value_system \<longleftrightarrow> generation_operation_result d t"
  using assms by (auto simp: generation_admission_exact generation_identity_exact generation_difference_exact
    generation_collection_exact generation_helper_operations_exact data_list_term_injective)

theorem native_generation_value_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {139::nat,140,141,142,143,144,145,146} \<and>
    (\<forall>d\<in>{139,140,141,142,143,144,145,146}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> generation_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{139,140,141,142,143,144,145,146}\<subseteq>system_definitions generation_value_system" by auto
  have calls: "schema_call_formed generation_value_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{139,140,141,142,143,144,145,146}" for d t
    using generation_value_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF generation_value_system_formed selected calls generation_operations_exact])
qed

text \<open>
  Generation admission, identity, inequality, and finite collection admission
  now export local contracts for the existing independent core and its entire
  recursive presentation class. The generic collection construction consumes
  the exported inequality contract. Presentation changes, specialization,
  and composition use the general contract laws; they require no new client
  proof about predecessor enumerations or concrete data layouts.

  Auxiliary entries retain their stated raw boundaries. Selection compares
  one member and retains every skipped data occurrence. The difference helper
  recognizes a positive witness on complete data lists. Whole generation
  comparison additionally admits both complete cores. An empty absence list
  requires only context formation, as the general context-list theorem states.

  One closed native program fixes eight distinct sites before every future
  formed operand. Compilation preserves the complete original program scope,
  every artifact, and every outgoing binding. The cause field is still an
  exact recorded target. Ordinary reading of an actual generation source and
  its cited predecessors, cause validity, and higher protocol admission are
  separate remaining relations.
\<close>

end
