theory Factor_Data_Set_Comparison_Contracts
  imports Factor_Data_Set_Comparison Factor_Collection_Comparisons Presentation_Contracts
    Factor_Compiled_Applications
begin

section \<open>The complete contract compares sets while retaining list subjects\<close>

theorem data_set_comparison_contract:
  "presented_relation_contract
    (\<lambda>xs p. data_elements xs \<and> p=data_list_term xs) data_elements
    (\<lambda>p. \<exists>xs. data_elements xs \<and> p=data_list_term xs)
    (\<lambda>ys q. data_elements ys \<and> q=data_list_term ys) data_elements
    (\<lambda>q. \<exists>ys. data_elements ys \<and> q=data_list_term ys)
    (\<lambda>xs ys. set xs=set ys) (\<lambda>p q. (219,Pair_Term p q)\<in>positive_meaning data_set_comparison_system)"
proof -
  have lists: "presentation_class (\<lambda>xs p. data_elements xs \<and> p=data_list_term xs) data_elements
      (\<lambda>p. \<exists>xs. data_elements xs \<and> p=data_list_term xs)"
    by (rule injective_presentation_class) (auto simp: inj_on_def data_list_term_injective)
  have exact: "(219,Pair_Term p q)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
      presented_relation (\<lambda>xs p. data_elements xs \<and> p=data_list_term xs)
        (\<lambda>ys q. data_elements ys \<and> q=data_list_term ys) (\<lambda>xs ys. set xs=set ys) p q" for p q
    by (auto simp: data_set_comparison_exact presented_relation_def)
  show ?thesis using lists exact
    by (simp add: presented_relation_contract_def presented_relation_contract_axioms_def)
qed

theorem data_set_comparison_mapped:
  assumes "inj f"
  shows "(219,Pair_Term (data_list_term (map f xs)) (data_list_term (map f ys)))
      \<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
    data_elements (map f xs) \<and> data_elements (map f ys) \<and> set xs=set ys"
  by (simp only: data_set_comparison_lists set_map inj_image_eq_iff[OF assms])

theorem data_set_comparison_collection:
  assumes injective: "inj f"
    and source: "data_elements (map f xs)"
    and "output": "data_collection_presents (\<lambda>a p. D a \<and> p=f a) X q"
    and data: "\<And>a. a\<in>X \<Longrightarrow> term_formed (f a) \<and> self_contained_term (f a)"
  shows "(219,Pair_Term (data_list_term (map f xs)) q)\<in>positive_meaning data_set_comparison_system
    \<longleftrightarrow> set xs=X"
proof -
  obtain ys where second: "set ys=X" "q=data_list_term (map f ys)"
    using assms(3) by (simp only: data_collection_presents_constrain data_collection_presents_function; blast)
  have formed: "data_elements (map f ys)" using data second(1) by auto
  show ?thesis using source formed
    by (simp only: second(2) data_set_comparison_mapped[OF injective] second(1); blast)
qed

section \<open>Equal sets can have different attachment counts\<close>

theorem data_set_comparison_allows_repetitions:
  assumes "term_formed x" "self_contained_term x"
  shows "(219,Pair_Term (data_list_term [x,x]) (data_list_term [x]))\<in>positive_meaning data_set_comparison_system \<and>
    (6,Pair_Term (data_list_term [x,x]) (data_list_term [x]))\<notin>positive_meaning bag_comparison_system \<and>
    [x,x]\<noteq>[x]"
  using assms by (simp only: data_set_comparison_lists bag_comparison_lists) simp

theorem data_set_comparison_complete_quotation:
  assumes "(219,t)\<in>positive_meaning data_set_comparison_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have data: "term_formed t" "self_contained_term t"
    using assms by (auto simp: data_set_comparison_exact data_list_term_formed data_list_term_self_contained)
  show ?thesis using complete_data_quotation_total[OF data] by blast
qed

section \<open>The fixed native operation covers every future operand\<close>

theorem native_data_set_comparison:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {219::nat} \<and>
    (\<forall>d\<in>{219}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>xs ys. data_elements xs \<and> data_elements ys \<and> set xs=set ys \<and>
            t=Pair_Term (data_list_term xs) (data_list_term ys))) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{219}\<subseteq>system_definitions data_set_comparison_system" by auto
  have calls: "schema_call_formed data_set_comparison_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{219}" for d t using data_set_comparison_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
      (\<exists>xs ys. data_elements xs \<and> data_elements ys \<and> set xs=set ys \<and>
        t=Pair_Term (data_list_term xs) (data_list_term ys))"
    if "d\<in>{219}" for d t using that data_set_comparison_exact[of t] by simp
  show ?thesis by (rule compiled_exact_operations[OF data_set_comparison_system_formed selected calls result])
qed

text \<open>
  The independently specified subjects are actual lists. Their comparison
  relation is equality after taking their sets, so a successful comparison
  need not identify the subjects or their bags. A complete collection output
  can consequently be compared with an image list containing repetitions.
  This distinction is needed when gluing merges incidence or functional rows;
  the existing bag comparison must still check counted attachments.

  The native entry is fixed before every future operand. Compilation retains
  the exact package scope, artifacts, and bindings. The table operations and
  this comparison are reusable components; complete native assembly and its
  construction-permission invariance remain separate obligations.
\<close>

end
