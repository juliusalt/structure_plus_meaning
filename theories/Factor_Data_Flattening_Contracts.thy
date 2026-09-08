theory Factor_Data_Flattening_Contracts
  imports Factor_Data_Flattening Factor_Related_List_Maps
begin

section \<open>The complete subject is a sequence of actual data terms\<close>

theorem data_flatten_function_contract:
  "presented_function_contract
    (\<lambda>xss p. (\<forall>xs\<in>set xss. data_elements xs) \<and> p=data_list_term (map data_list_term xss))
    (\<lambda>xss. \<forall>xs\<in>set xss. data_elements xs)
    (\<lambda>p. \<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and> p=data_list_term (map data_list_term xss))
    (\<lambda>xs q. data_elements xs \<and> q=data_list_term xs) data_elements
    (\<lambda>q. \<exists>xs. data_elements xs \<and> q=data_list_term xs)
    concat (\<lambda>p q. (218,Pair_Term p q)\<in>positive_meaning data_flatten_system)"
proof -
  have injective: "inj data_list_term" by (simp add: inj_def data_list_term_injective)
  have left_injective: "inj_on (\<lambda>xss. data_list_term (map data_list_term xss))
      {xss. \<forall>xs\<in>set xss. data_elements xs}"
    by (auto simp: inj_on_def data_list_term_injective inj_map_eq_map[OF injective])
  have left: "presentation_class
      (\<lambda>xss p. (\<forall>xs\<in>set xss. data_elements xs) \<and> p=data_list_term (map data_list_term xss))
      (\<lambda>xss. \<forall>xs\<in>set xss. data_elements xs)
      (\<lambda>p. \<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and> p=data_list_term (map data_list_term xss))"
    by (rule injective_presentation_class[OF left_injective])
  have right: "presentation_class (\<lambda>xs q. data_elements xs \<and> q=data_list_term xs) data_elements
      (\<lambda>q. \<exists>xs. data_elements xs \<and> q=data_list_term xs)"
    by (rule injective_presentation_class) (use injective in \<open>auto simp: inj_on_def inj_def\<close>)
  have exact: "(218,Pair_Term p q)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
      presented_relation
        (\<lambda>xss p. (\<forall>xs\<in>set xss. data_elements xs) \<and> p=data_list_term (map data_list_term xss))
        (\<lambda>xs q. data_elements xs \<and> q=data_list_term xs)
        (\<lambda>xss xs. xs=concat xss) p q" for p q
    by (auto simp: data_flatten_exact presented_relation_def)
  show ?thesis using left right exact
    by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
      presented_relation_contract_def presented_relation_contract_axioms_def)
qed

section \<open>A mapped list of contributions composes with concatenation\<close>

context related_list_profile
begin

theorem flattened_output:
  assumes formed: "term_formed a"
    and element: "\<And>x y. x\<in>set xs \<Longrightarrow> related a (h x) y \<longleftrightarrow> y=data_list_term (g x)"
    and data: "\<And>x. x\<in>set xs \<Longrightarrow> data_elements (g x)"
    and flatten: "\<And>xss q. (flatten_site,Pair_Term (data_list_term (map data_list_term xss)) q)
      \<in>positive_meaning P \<longleftrightarrow>
      (\<forall>ys\<in>set xss. data_elements ys) \<and> q=data_list_term (concat xss)"
  shows "(\<exists>p. (list_site,context_relation_argument a (data_list_term (map h xs)) p)\<in>positive_meaning P \<and>
      (flatten_site,Pair_Term p q)\<in>positive_meaning P)
    \<longleftrightarrow> q=data_list_term (concat (map g xs))"
proof -
  have mapped: "(list_site,context_relation_argument a (data_list_term (map h xs)) p)\<in>positive_meaning P
      \<longleftrightarrow> p=data_list_term (map data_list_term (map g xs))" for p
    using encoded_input[where a=a and xs=xs and f=h and g="\<lambda>x. data_list_term (g x)" and q=p,
      OF formed element] by (simp add: comp_def)
  have all_data: "\<forall>ys\<in>set (map g xs). data_elements ys" using data by auto
  have finished: "(flatten_site,Pair_Term (data_list_term (map data_list_term (map g xs))) q)
      \<in>positive_meaning P \<longleftrightarrow> q=data_list_term (concat (map g xs))"
    using all_data by (simp only: flatten; blast)
  show ?thesis using finished by (simp only: mapped; blast)
qed

end

section \<open>Empty contributions and repeated occurrences remain distinct cases\<close>

corollary data_flatten_empty:
  "(218,Pair_Term (data_list_term []) q)\<in>positive_meaning data_flatten_system
    \<longleftrightarrow> q=data_list_term []"
  using data_flatten_at_lists[of "[]" q] by simp

theorem data_flatten_keeps_repeated_occurrences:
  assumes "term_formed x" "self_contained_term x"
  shows "(218,Pair_Term (data_list_term (map data_list_term [[x],[],[x]])) (data_list_term [x,x]))
      \<in>positive_meaning data_flatten_system \<and>
    (218,Pair_Term (data_list_term (map data_list_term [[x],[],[x]])) (data_list_term [x]))
      \<notin>positive_meaning data_flatten_system"
  by (simp only: data_flatten_at_lists) (use assms in simp)

theorem data_flatten_complete_quotation:
  assumes "(218,t)\<in>positive_meaning data_flatten_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have data: "term_formed t" "self_contained_term t"
    using assms by (auto simp: data_flatten_exact data_list_term_formed data_list_term_self_contained)
  show ?thesis using complete_data_quotation_total[OF data] by blast
qed

section \<open>The native operation is fixed before every future operand\<close>

theorem native_data_flattening:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {218::nat} \<and>
    (\<forall>d\<in>{218}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and>
            t=Pair_Term (data_list_term (map data_list_term xss)) (data_list_term (concat xss)))) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{218}\<subseteq>system_definitions data_flatten_system" by auto
  have calls: "schema_call_formed data_flatten_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{218}" for d t using data_flatten_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
      (\<exists>xss. (\<forall>xs\<in>set xss. data_elements xs) \<and>
        t=Pair_Term (data_list_term (map data_list_term xss)) (data_list_term (concat xss)))"
    if "d\<in>{218}" for d t using that data_flatten_exact[of t] by simp
  show ?thesis by (rule compiled_exact_operations[OF data_flatten_system_formed selected calls result])
qed

text \<open>
  Concatenation has a complete function contract for sequences of actual
  self-contained data terms. Literal copying therefore keeps all details of
  that independently declared subject. No equation identifies different
  presentations of another semantic value. The general copy criterion states
  exactly when such a further identity contract would hold.

  Mapping and concatenation compose through the whole intermediate list.
  Their owned contracts settle the recursive traversal, its order, and its
  multiplicities; a consumer supplies only the local element equation and
  its data boundary. A two-premise native composition can consume these
  same results in a combined program after its callee agreements are proved.

  The compiled concatenation entry is available before all future operands,
  with the existing program's scope, artifacts, and bindings preserved.
  Native assembly still needs origin lookup, complete coverage, and the
  output-field comparisons. Native checking of these mathematical proofs
  remains a separate obligation.
\<close>

end
