theory Factor_Term_Sequence_Contracts
  imports Factor_Term_Sequence_Presentations Factor_Term_Sequence_Operations Factor_Compiled_Applications
begin

section \<open>The existing fold realizes complete function contracts\<close>

lemma term_pair_fold_presented:
  "(233,collection_join_argument (fst p) (snd p) q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    presented_relation term_seed_sequence_presents formed_term_presents
      (\<lambda>z y. y=foldr Pair_Term (snd z) (fst z)) p q"
  by (auto simp: term_sequence_fold_exact presented_relation_def formed_sequence_presents_iff
    term_sequence_pair_formed; metis fst_conv snd_conv)

interpretation term_pair_folding: presented_function_contract
  term_seed_sequence_presents term_seed_sequence_domain "\<lambda>p. \<exists>z. term_seed_sequence_presents z p"
  formed_term_presents term_formed term_formed "\<lambda>z. foldr Pair_Term (snd z) (fst z)"
  "\<lambda>p q. (233,collection_join_argument (fst p) (snd p) q)\<in>positive_meaning term_sequence_system"
  using term_seed_sequence_class formed_term_presentation_class term_pair_fold_presented
  by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def term_sequence_pair_formed)

lemma term_count_fold_presented:
  "(235,collection_join_argument (fst p) (snd p) q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    presented_relation term_seed_sequence_presents formed_term_presents
      (\<lambda>z y. y=foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) (snd z) (fst z)) p q"
  by (auto simp: term_sequence_count_exact presented_relation_def formed_sequence_presents_iff
    term_sequence_count_formed; metis fst_conv snd_conv)

interpretation term_count_folding: presented_function_contract
  term_seed_sequence_presents term_seed_sequence_domain "\<lambda>p. \<exists>z. term_seed_sequence_presents z p"
  formed_term_presents term_formed term_formed
  "\<lambda>z. foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) (snd z) (fst z)"
  "\<lambda>p q. (235,collection_join_argument (fst p) (snd p) q)\<in>positive_meaning term_sequence_system"
  using term_seed_sequence_class formed_term_presentation_class term_count_fold_presented
  by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def term_sequence_count_formed)

lemma term_sequence_native_class:
  "presentation_class formed_sequence_presents (\<lambda>xs. \<forall>x\<in>set xs. term_formed x)
    (\<lambda>p. (233,collection_join_argument (Payload_Term []) p p)\<in>positive_meaning term_sequence_system)"
  using formed_sequence_presentation_class by (simp only: term_sequence_list_guard)

section \<open>Changing the complete terminator preserves the actual sequence\<close>

theorem term_sequence_enumeration_exact:
  "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)
    \<in>positive_meaning term_sequence_system \<longleftrightarrow>
    term_formed p \<and> enumeration_retermination p q"
proof -
  have seed: "term_formed (Target_Term (Whole_Artifact empty_artifact))" by simp
  show ?thesis by (simp only: term_sequence_fold_at_seed[OF seed] term_sequence_pair_boundaries)
    (auto simp: enumeration_retermination_def data_list_term_formed data_list_term_injective)
qed

interpretation term_enumeration_change: presented_function_contract
  formed_sequence_presents "\<lambda>xs. \<forall>x\<in>set xs. term_formed x"
  "\<lambda>p. \<exists>xs. (\<forall>x\<in>set xs. term_formed x) \<and> p=data_list_term xs"
  formed_enumeration_presents "\<lambda>xs. \<forall>x\<in>set xs. term_formed x"
  "\<lambda>q. \<exists>xs. formed_enumeration_presents xs q" id
  "\<lambda>p q. (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)
    \<in>positive_meaning term_sequence_system"
  using formed_sequence_presentation_class formed_enumeration_presentation_class
  by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def presented_relation_def
    term_sequence_enumeration_exact enumeration_retermination_def formed_sequence_presents_iff
    data_list_term_formed data_list_term_injective)

theorem finite_table_native_retermination:
  "(term_formed q \<and> finite_table_presents K V Q q) \<longleftrightarrow>
    (\<exists>p. data_table_presents (\<lambda>k t. t=K k) V Q p \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)
        \<in>positive_meaning term_sequence_system)"
  by (auto simp: finite_table_retermination composed_presentation_def term_sequence_enumeration_exact
    enumeration_retermination_def data_list_term_formed enumeration_term_formed)

lemma natural_sequence_boundaries:
  "natural_data_term n=data_list_term (replicate n (Payload_Term []))"
  "natural_term n=enumeration_term (replicate n (Payload_Term []))"
  by (induction n) auto

theorem natural_term_native_retermination:
  "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (natural_data_term n) q)
    \<in>positive_meaning term_sequence_system \<longleftrightarrow> q=natural_term n"
proof -
  have source: "formed_sequence_presents (replicate n (Payload_Term [])) (natural_data_term n)"
    by (simp add: formed_sequence_presents_iff natural_sequence_boundaries octets_formed_def)
  show ?thesis using term_enumeration_change.output[OF source, of q]
    by (simp add: natural_sequence_boundaries octets_formed_def)
qed

section \<open>Literal selection has a complete contract on term positions\<close>

lemma term_index_presented:
  "(236,Pair_Term p q)\<in>positive_meaning term_sequence_system \<longleftrightarrow>
    presented_relation term_index_presents formed_term_presents (\<lambda>z y. y=fst z!snd z) p q"
  by (auto simp: term_sequence_index_exact presented_relation_def term_index_presents_def
    factor_pair_presents_def formed_sequence_presents_iff; metis fst_conv snd_conv nth_mem)

lemma term_index_native_class:
  "presentation_class term_index_presents term_index_domain
    (\<lambda>p. \<exists>q. (236,Pair_Term p q)\<in>positive_meaning term_sequence_system)"
proof -
  have boundary: "(\<exists>q. (236,Pair_Term p q)\<in>positive_meaning term_sequence_system) \<longleftrightarrow>
      (\<exists>z. term_index_presents z p)" for p
    by (auto simp: term_sequence_index_exact term_index_presents_def factor_pair_presents_def
      formed_sequence_presents_iff; metis fst_conv snd_conv)
  show ?thesis using term_index_presentation_class by (simp only: boundary)
qed

interpretation term_index_reading: presented_function_contract
  term_index_presents term_index_domain "\<lambda>p. \<exists>q. (236,Pair_Term p q)\<in>positive_meaning term_sequence_system"
  formed_term_presents term_formed term_formed "\<lambda>z. fst z!snd z"
  "\<lambda>p q. (236,Pair_Term p q)\<in>positive_meaning term_sequence_system"
  using term_index_native_class formed_term_presentation_class term_index_presented
  by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def)

theorem term_index_at_bound:
  assumes "length xs\<le>n"
  shows "\<not>(236,Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) y)
    \<in>positive_meaning term_sequence_system"
  using assms by (simp add: term_sequence_index_at)

theorem term_index_allows_targets_and_repetitions:
  assumes "exact_formed R"
  shows "(236,Pair_Term (Pair_Term
      (data_list_term [Target_Term (Whole_Artifact R),Payload_Term [],Target_Term (Whole_Artifact R)])
      (natural_data_term 0)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning term_sequence_system"
    "(236,Pair_Term (Pair_Term
      (data_list_term [Target_Term (Whole_Artifact R),Payload_Term [],Target_Term (Whole_Artifact R)])
      (natural_data_term 2)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning term_sequence_system"
proof -
  let ?xs="[Target_Term (Whole_Artifact R),Payload_Term [],Target_Term (Whole_Artifact R)]"
  show "(236,Pair_Term (Pair_Term (data_list_term ?xs) (natural_data_term 0))
      (Target_Term (Whole_Artifact R)))\<in>positive_meaning term_sequence_system"
    using term_sequence_index_at[where xs="?xs" and n=0 and y="Target_Term (Whole_Artifact R)"] assms
    by (simp add: octets_formed_def)
  show "(236,Pair_Term (Pair_Term (data_list_term ?xs) (natural_data_term 2))
      (Target_Term (Whole_Artifact R)))\<in>positive_meaning term_sequence_system"
    using term_sequence_index_at[where xs="?xs" and n=2 and y="Target_Term (Whole_Artifact R)"] assms
    by (simp add: octets_formed_def)
qed

theorem term_index_checks_unused_suffix:
  assumes "term_formed x"
  shows "(233,collection_join_argument (Pair_Term x (Payload_Term [0])) (data_list_term [])
      (Pair_Term x (Payload_Term [0])))\<in>positive_meaning term_sequence_system \<and>
    (235,collection_join_argument (Payload_Term []) (data_list_term []) (natural_data_term 0))
      \<in>positive_meaning term_sequence_system \<and>
    \<not>(236,Pair_Term (Pair_Term (Pair_Term x (Payload_Term [0])) (natural_data_term 0)) x)
      \<in>positive_meaning term_sequence_system"
proof -
  have tail: "data_list_term ys\<noteq>Payload_Term [0]" for ys by (cases ys) auto
  have malformed: "Pair_Term x (Payload_Term [0])\<noteq>data_list_term ys" for ys
  proof (cases ys)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a zs)
    show ?thesis using tail[of zs] by (auto simp: Cons)
  qed
  have prefix: "(233,collection_join_argument (Pair_Term x (Payload_Term [0])) (data_list_term [])
      (Pair_Term x (Payload_Term [0])))\<in>positive_meaning term_sequence_system"
    by (simp only: term_pair_fold.at_list fold_relation_simps)
      (use assms in \<open>simp add: octets_formed_def\<close>)
  have count: "(235,collection_join_argument (Payload_Term []) (data_list_term []) (natural_data_term 0))
      \<in>positive_meaning term_sequence_system"
    by (simp only: term_count_fold.at_list fold_relation_simps)
      (simp add: octets_formed_def)
  have rejected: "\<not>(236,Pair_Term (Pair_Term (Pair_Term x (Payload_Term [0])) (natural_data_term 0)) x)
      \<in>positive_meaning term_sequence_system"
    using malformed by (auto simp only: term_sequence_index_exact factor_term.inject)
  show ?thesis using prefix count rejected by blast
qed

section \<open>One fixed native program precedes every future operand\<close>

abbreviation term_sequence_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_sequence_operation_result d t \<equiv>
    if d=233 then (\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs) (foldr Pair_Term xs z))
    else if d=235 then (\<exists>z xs. term_formed z \<and> (\<forall>x\<in>set xs. term_formed x) \<and>
      t=collection_join_argument z (data_list_term xs) (foldr (\<lambda>_ a. Pair_Term (Payload_Term []) a) xs z))
    else (\<exists>xs n. (\<forall>x\<in>set xs. term_formed x) \<and> n<length xs \<and>
      t=Pair_Term (Pair_Term (data_list_term xs) (natural_data_term n)) (xs!n))"

lemma term_sequence_operations_exact:
  assumes "d\<in>{233,235,236}"
  shows "(d,t)\<in>positive_meaning term_sequence_system \<longleftrightarrow> term_sequence_operation_result d t"
proof -
  consider (pair) "d=233" | (count) "d=235" | (index) "d=236" using assms by auto
  then show ?thesis
  proof cases
    case pair
    show ?thesis by (simp only: pair term_sequence_fold_exact; simp)
  next
    case count
    show ?thesis by (simp only: count term_sequence_count_exact; simp)
  next
    case index
    show ?thesis by (simp only: index term_sequence_index_exact; simp)
  qed
qed

theorem native_term_sequence_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {233::nat,235,236} \<and>
    (\<forall>d\<in>{233,235,236}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> term_sequence_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{233,235,236}\<subseteq>system_definitions term_sequence_system" by auto
  have calls: "schema_call_formed term_sequence_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{233,235,236}" for d t using term_sequence_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF term_sequence_system_formed selected calls term_sequence_operations_exact])
qed

text \<open>
  The complete contracts cover arbitrary formed terms, including references
  to whole artifacts. The native functions supply every output in their
  declared term classes. Clients inherit totality, invariance, adaptation,
  and composition from the general function contract.

  Changing a terminator preserves the actual list and all its occurrences.
  The finite-table theorem changes that same supplied row enumeration. It
  does not claim a native identity operation between every reordered table
  presentation. Global construction permission remains a separate condition.

  The three public sites share one closed five-definition program, fixed
  before future operands and preserving its exact scope, artifacts, and
  bindings. Native presentations of the mathematical contracts and their
  proofs remain a separate obligation.
\<close>

end
