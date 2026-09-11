theory Factor_Observation_Contracts
  imports Factor_Observation_Results
begin

section \<open>Ordered computations return witnesses in the complete result class\<close>

abbreviation observation_profile_subject where
  "observation_profile_subject z \<equiv> finite_candidate_profile (fst (fst z)) (snd z) (snd (fst z))"

abbreviation observation_losses_subject where
  "observation_losses_subject z \<equiv> finite_candidate_losses (fst (fst z)) (snd z)
    (fst (snd (fst z))) (snd (snd (fst z)))"

lemma observation_values_at_computed:
  assumes "observation_values_presents V p"
  shows "(219,Pair_Term p q)\<in>positive_meaning observation_result_system \<longleftrightarrow>
    observation_values_presents V q"
proof -
  obtain xs where source: "\<forall>(f,w)\<in>set xs. data_elements [f,w]"
    "fset_of_list xs=V" "p=data_list_term (map observation_value_term xs)"
    using assms by (simp only: observation_values_fields) blast
  show ?thesis using observation_values_comparison[OF source(1), of q]
    by (simp only: observation_result_components source)
qed

lemma observation_profile_computed_presents:
  assumes rows: "observation_rows_data rows"
  shows "observation_values_presents (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c)
    (data_list_term (map observation_value_term (observation_profile_list fs rows c)))"
  by (simp only: observation_values_fields; rule exI[of _ "observation_profile_list fs rows c"])
    (use observation_profile_values_data[OF rows, of fs c] in
      \<open>simp only: observation_profile_list_fset; blast\<close>)

theorem observation_profile_witness:
  "presented_function_witness (observation_query_presents observation_datum_presents)
    (observation_query_domain observation_datum)
    (\<lambda>p. \<exists>z. observation_query_presents observation_datum_presents z p)
    observation_values_presents observation_values_domain (\<lambda>q. \<exists>V. observation_values_presents V q)
    observation_profile_subject
    (\<lambda>p q. (301,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system)"
proof (rule presented_function_witness.intro[OF observation_query_class[OF observation_datum_class]
    observation_values_class]; unfold_locales)
  fix p q
  assume run: "(301,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
  obtain fs rows c where source: "data_elements fs" "observation_datum c" "observation_rows_data rows"
    "fst p=Pair_Term (data_list_term fs) (c)"
    "snd p=data_list_term (map observation_row_term rows)"
    using run by (auto simp only: observation_result_components observation_profile_exact factor_term.inject)
  have read: "observation_query_presents observation_datum_presents
      ((fset_of_list fs,c),fset_of_list rows) p"
    by (cases p; simp only: observation_query_fields)
      (use source in \<open>auto intro!: exI[of _ fs] exI[of _ rows]\<close>)
  show "\<exists>z. observation_query_presents observation_datum_presents z p" using read by blast
next
  fix z p q
  assume read: "observation_query_presents observation_datum_presents z p"
    and run: "(301,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
  obtain F T c where z: "z=((F,c),T)" by (cases z; case_tac a;  auto)
  obtain fs rows where source: "data_elements fs" "observation_datum c" "observation_rows_data rows"
    "fset_of_list fs=F" "fset_of_list rows=T"
    "fst p=Pair_Term (data_list_term fs) (c)"
    "snd p=data_list_term (map observation_row_term rows)"
    using read by (cases p; simp only: z observation_query_fields) auto
  have result: "q=data_list_term (map observation_value_term (observation_profile_list fs rows c))"
    using run source by (simp only: observation_result_components observation_encoded_profile)
  show "observation_values_presents (observation_profile_subject z) q"
    using observation_profile_computed_presents[OF source(3), of fs c]
    by (simp only: z fst_conv snd_conv source result)
next
  fix p assume "\<exists>z. observation_query_presents observation_datum_presents z p"
  then obtain z where read: "observation_query_presents observation_datum_presents z p" by blast
  obtain F T c where z: "z=((F,c),T)" by (cases z; case_tac a;  auto)
  obtain fs rows where source: "data_elements fs" "observation_datum c" "observation_rows_data rows"
    "fst p=Pair_Term (data_list_term fs) (c)"
    "snd p=data_list_term (map observation_row_term rows)"
    using read by (cases p; simp only: z observation_query_fields) auto
  show "\<exists>q. (301,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
    by (rule exI[of _ "data_list_term (map observation_value_term (observation_profile_list fs rows c))"])
      (use source in \<open>simp only: observation_result_components observation_encoded_profile; blast\<close>)
qed

theorem observation_profile_contract:
  "presented_function_contract (observation_query_presents observation_datum_presents)
    (observation_query_domain observation_datum)
    (\<lambda>p. \<exists>z. observation_query_presents observation_datum_presents z p)
    observation_values_presents observation_values_domain (\<lambda>q. \<exists>V. observation_values_presents V q)
    observation_profile_subject
    (\<lambda>p q. (302,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system)"
  by (rule observation_profile_comparison.presented_contract[OF observation_profile_witness
    observation_values_at_computed])

lemma observation_losses_computed_presents:
  assumes rows: "observation_rows_data rows"
  shows "observation_values_presents (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) c d)
    (data_list_term (map observation_value_term (observation_losses_list fs rows c d)))"
  by (simp only: observation_values_fields; rule exI[of _ "observation_losses_list fs rows c d"])
    (use observation_losses_values_data[OF rows, of fs c d] in
      \<open>simp only: observation_losses_list_fset; blast\<close>)

theorem observation_losses_witness:
  "presented_function_witness (observation_query_presents observation_value_presents)
    (observation_query_domain (\<lambda>(c,d). data_elements [c,d]))
    (\<lambda>p. \<exists>z. observation_query_presents observation_value_presents z p)
    observation_values_presents observation_values_domain (\<lambda>q. \<exists>V. observation_values_presents V q)
    observation_losses_subject
    (\<lambda>p q. (306,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system)"
proof (rule presented_function_witness.intro[OF observation_query_class[OF observation_value_class]
    observation_values_class]; unfold_locales)
  fix p q
  assume run: "(306,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
  obtain fs rows c d where source: "data_elements fs" "data_elements [c,d]" "observation_rows_data rows"
    "fst p=Pair_Term (data_list_term fs) (Pair_Term c d)"
    "snd p=data_list_term (map observation_row_term rows)"
    using run by (auto simp only: observation_result_components observation_losses_exact factor_term.inject)
  have read: "observation_query_presents observation_value_presents
      ((fset_of_list fs,(c,d)),fset_of_list rows) p"
    by (cases p; simp only: observation_query_fields; simp only: observation_value_graph)
      (use source in \<open>auto intro!: exI[of _ fs] exI[of _ rows]\<close>)
  show "\<exists>z. observation_query_presents observation_value_presents z p" using read by blast
next
  fix z p q
  assume read: "observation_query_presents observation_value_presents z p"
    and run: "(306,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
  obtain F T c d where z: "z=((F,(c,d)),T)" by (cases z; case_tac a; case_tac b; auto)
  obtain fs rows where source: "data_elements fs" "data_elements [c,d]" "observation_rows_data rows"
    "fset_of_list fs=F" "fset_of_list rows=T"
    "fst p=Pair_Term (data_list_term fs) (Pair_Term c d)"
    "snd p=data_list_term (map observation_row_term rows)"
    using read by (cases p; simp only: z observation_query_fields; simp only: observation_value_graph) auto
  have result: "q=data_list_term (map observation_value_term (observation_losses_list fs rows c d))"
    using run source by (simp only: observation_result_components observation_encoded_losses)
  show "observation_values_presents (observation_losses_subject z) q"
    using observation_losses_computed_presents[OF source(3), of fs c d]
    by (simp only: z fst_conv snd_conv source result)
next
  fix p assume "\<exists>z. observation_query_presents observation_value_presents z p"
  then obtain z where read: "observation_query_presents observation_value_presents z p" by blast
  obtain F T c d where z: "z=((F,(c,d)),T)" by (cases z; case_tac a; case_tac b; auto)
  obtain fs rows where source: "data_elements fs" "data_elements [c,d]" "observation_rows_data rows"
    "fst p=Pair_Term (data_list_term fs) (Pair_Term c d)"
    "snd p=data_list_term (map observation_row_term rows)"
    using read by (cases p; simp only: z observation_query_fields; simp only: observation_value_graph) auto
  show "\<exists>q. (306,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system"
    by (rule exI[of _ "data_list_term (map observation_value_term (observation_losses_list fs rows c d))"])
      (use source in \<open>simp only: observation_result_components observation_encoded_losses; blast\<close>)
qed

theorem observation_losses_contract:
  "presented_function_contract (observation_query_presents observation_value_presents)
    (observation_query_domain (\<lambda>(c,d). data_elements [c,d]))
    (\<lambda>p. \<exists>z. observation_query_presents observation_value_presents z p)
    observation_values_presents observation_values_domain (\<lambda>q. \<exists>V. observation_values_presents V q)
    observation_losses_subject
    (\<lambda>p q. (307,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning observation_result_system)"
  by (rule observation_losses_comparison.presented_contract[OF observation_losses_witness
    observation_values_at_computed])

section \<open>The contracts cover every argument and every future native application\<close>

abbreviation observation_profile_set_result :: "factor_term \<Rightarrow> bool" where
  "observation_profile_set_result t \<equiv> \<exists>fs rows c q.
    data_elements fs \<and> observation_datum c \<and> observation_rows_data rows \<and>
    t=context_relation_argument (Pair_Term (data_list_term fs) (c))
      (data_list_term (map observation_row_term rows)) q \<and>
    observation_values_presents (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c) q"

theorem observation_profile_set_exact:
  "(302,t)\<in>positive_meaning observation_result_system \<longleftrightarrow> observation_profile_set_result t"
proof
  assume run: "(302,t)\<in>positive_meaning observation_result_system"
  obtain p input q w where parts: "t=context_relation_argument p input q"
    "(301,context_relation_argument p input w)\<in>positive_meaning observation_result_system"
    using run by (simp only: observation_profile_comparison.exact) blast
  obtain fs rows c where source: "data_elements fs" "observation_datum c" "observation_rows_data rows"
    "p=Pair_Term (data_list_term fs) (c)"
    "input=data_list_term (map observation_row_term rows)"
    using parts(2) by (auto simp only: observation_result_components observation_profile_exact factor_term.inject)
  have result: "observation_values_presents (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c) q"
    using run source by (simp only: parts(1) observation_profile_result_encoded)
  show "observation_profile_set_result t" using source parts(1) result by blast
next
  assume "observation_profile_set_result t"
  then obtain fs rows c q where source: "data_elements fs" "observation_datum c" "observation_rows_data rows"
    "t=context_relation_argument (Pair_Term (data_list_term fs) (c))
      (data_list_term (map observation_row_term rows)) q"
    "observation_values_presents (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c) q" by blast
  show "(302,t)\<in>positive_meaning observation_result_system"
    using source by (simp only: observation_profile_result_encoded)
qed

abbreviation observation_losses_set_result :: "factor_term \<Rightarrow> bool" where
  "observation_losses_set_result t \<equiv> \<exists>fs rows c d q.
    data_elements fs \<and> data_elements [c,d] \<and> observation_rows_data rows \<and>
    t=context_relation_argument (Pair_Term (data_list_term fs) (Pair_Term c d))
      (data_list_term (map observation_row_term rows)) q \<and>
    observation_values_presents (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) c d) q"

theorem observation_losses_set_exact:
  "(307,t)\<in>positive_meaning observation_result_system \<longleftrightarrow> observation_losses_set_result t"
proof
  assume run: "(307,t)\<in>positive_meaning observation_result_system"
  obtain p input q w where parts: "t=context_relation_argument p input q"
    "(306,context_relation_argument p input w)\<in>positive_meaning observation_result_system"
    using run by (simp only: observation_losses_comparison.exact) blast
  obtain fs rows c d where source: "data_elements fs" "data_elements [c,d]" "observation_rows_data rows"
    "p=Pair_Term (data_list_term fs) (Pair_Term c d)"
    "input=data_list_term (map observation_row_term rows)"
    using parts(2) by (auto simp only: observation_result_components observation_losses_exact factor_term.inject)
  have result: "observation_values_presents (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) c d) q"
    using run source by (simp only: parts(1) observation_losses_result_encoded)
  show "observation_losses_set_result t" using source parts(1) result by blast
next
  assume "observation_losses_set_result t"
  then obtain fs rows c d q where source: "data_elements fs" "data_elements [c,d]" "observation_rows_data rows"
    "t=context_relation_argument (Pair_Term (data_list_term fs) (Pair_Term c d))
      (data_list_term (map observation_row_term rows)) q"
    "observation_values_presents (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) c d) q" by blast
  show "(307,t)\<in>positive_meaning observation_result_system"
    using source by (simp only: observation_losses_result_encoded)
qed

abbreviation observation_set_result where
  "observation_set_result d t \<equiv> if d=302 then observation_profile_set_result t else observation_losses_set_result t"

lemma observation_set_operations_exact:
  assumes "d\<in>{302,307}"
  shows "(d,t)\<in>positive_meaning observation_result_system \<longleftrightarrow> observation_set_result d t"
proof (cases "d=302")
  case True then show ?thesis by (simp only: True if_True observation_profile_set_exact)
next
  case False
  have selected: "d=307" using assms False by auto
  show ?thesis by (simp only: selected observation_losses_set_exact) simp
qed

theorem observation_set_complete_quotation:
  assumes "d\<in>{302,307}" "(d,t)\<in>positive_meaning observation_result_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have data: "observation_datum t"
  proof (cases "d=302")
    case True
    obtain fs rows c q where parts: "data_elements fs" "observation_datum c" "observation_rows_data rows"
      "t=context_relation_argument (Pair_Term (data_list_term fs) (c))
        (data_list_term (map observation_row_term rows)) q"
      "observation_values_presents (finite_candidate_profile (fset_of_list fs) (fset_of_list rows) c) q"
      using assms(2) by (simp only: True observation_profile_set_exact) blast
    have result: "observation_datum q" by (rule observation_values_presented_data[OF parts(5)])
    show ?thesis using parts(1-4) result
      by (auto simp: data_list_term_formed data_list_term_self_contained split: prod.splits)
  next
    case False
    have selected: "d=307" using assms(1) False by auto
    obtain fs rows c e q where parts: "data_elements fs" "data_elements [c,e]" "observation_rows_data rows"
      "t=context_relation_argument (Pair_Term (data_list_term fs) (Pair_Term c e))
        (data_list_term (map observation_row_term rows)) q"
      "observation_values_presents (finite_candidate_losses (fset_of_list fs) (fset_of_list rows) c e) q"
      using assms(2) by (simp only: selected observation_losses_set_exact) blast
    have result: "observation_datum q" by (rule observation_values_presented_data[OF parts(5)])
    show ?thesis using parts(1-4) result
      by (auto simp: data_list_term_formed data_list_term_self_contained split: prod.splits)
  qed
  show ?thesis using complete_data_quotation_total[OF conjunct1[OF data] conjunct2[OF data]] by blast
qed

theorem native_observation_sets:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {302::nat,307} \<and>
    (\<forall>d\<in>{302,307}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> observation_set_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{302,307}\<subseteq>system_definitions observation_result_system" by auto
  have calls: "schema_call_formed observation_result_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{302,307}" for d t using observation_result_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF observation_result_system_formed selected calls
    observation_set_operations_exact])
qed

text \<open>
  The ordered computations return witnesses in the same complete classes used
  by the public operations. Both complete function contracts follow from one
  native result-comparison construction. Reordering or repeating displayed
  facets, table rows, or result rows preserves the represented finite subjects.
  Every supplied row field remains part of the input admission, including rows
  that contribute no selected observation.

  Compilation fixes one closed package before any future argument. The exact
  contract is the independently defined finite profile or loss, with complete
  data quotation of accepted calls. These operations do not yet implement the
  entire investigation report or a native checker for its mathematical proofs.
\<close>

end
