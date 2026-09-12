theory Factor_Data_Product_Contracts
  imports Factor_Data_Product_Equations
begin

section \<open>The independent subject is the product of two finite data sets\<close>

definition data_pair_product :: "factor_term fset \<Rightarrow> factor_term fset \<Rightarrow> factor_term fset" where
  "data_pair_product X Y=ffUnion (fimage (\<lambda>x. fimage (Pair_Term x) Y) X)"

lemma data_pair_product_members:
  "fset (data_pair_product X Y)={Pair_Term x y | x y. x\<in>fset X \<and> y\<in>fset Y}"
  by (auto simp: data_pair_product_def ffUnion.rep_eq fimage.rep_eq)

lemma data_pair_product_lists:
  "data_pair_product (fset_of_list xs) (fset_of_list ys)=fset_of_list (data_product_list xs ys)"
  by (rule fset_inject[THEN iffD1])
    (simp only: data_pair_product_members fset_of_list.rep_eq data_product_list_set)

abbreviation data_product_operands_presents where
  "data_product_operands_presents z p \<equiv>
    data_finite_set_presents (fst z) (fst p) \<and> data_finite_set_presents (snd z) (snd p)"

abbreviation data_product_operands_domain where
  "data_product_operands_domain z \<equiv> data_finite_set_domain (fst z) \<and> data_finite_set_domain (snd z)"

lemma data_product_operands_class:
  "presentation_class data_product_operands_presents data_product_operands_domain
    (\<lambda>p. \<exists>z. data_product_operands_presents z p)"
  by (rule presentation_class.recovered_admission[OF presentation_class_product[
    OF data_finite_set_class data_finite_set_class]])

section \<open>Ordered witnesses and complete comparison compose at their owned classes\<close>

theorem data_product_witness:
  "presented_function_witness data_product_operands_presents data_product_operands_domain
    (\<lambda>p. \<exists>z. data_product_operands_presents z p)
    data_finite_set_presents data_finite_set_domain (\<lambda>q. \<exists>S. data_finite_set_presents S q)
    (\<lambda>z. data_pair_product (snd z) (fst z))
    (\<lambda>p q. (324,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning data_product_system)"
proof (rule presented_function_witness.intro[OF data_product_operands_class
    presentation_class.recovered_admission[OF data_finite_set_class]]; unfold_locales)
  fix p q assume run: "(324,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning data_product_system"
  obtain xs ys where parts: "data_elements xs" "data_elements ys"
    "fst p=data_list_term ys" "snd p=data_list_term xs"
    using run by (auto simp only: data_product_ordered_exact factor_term.inject)
  show "\<exists>z. data_product_operands_presents z p"
    by (rule exI[of _ "(fset_of_list ys,fset_of_list xs)"])
      (use parts in \<open>simp only: fst_conv snd_conv data_finite_set_at_list; blast\<close>)
next
  fix z p q assume read: "data_product_operands_presents z p"
    and run: "(324,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning data_product_system"
  obtain ys where second: "data_elements ys" "fset_of_list ys=fst z" "fst p=data_list_term ys"
    using read by (simp only: data_finite_set_fields) blast
  obtain xs where first: "data_elements xs" "fset_of_list xs=snd z" "snd p=data_list_term xs"
    using read by (simp only: data_finite_set_fields) blast
  have result: "q=data_list_term (data_product_list xs ys)"
    using run by (simp only: first second data_product_ordered_lists; blast)
  show "data_finite_set_presents (data_pair_product (snd z) (fst z)) q"
    using data_product_list_data[OF first(1) second(1)]
    by (simp only: result data_finite_set_at_list first(2)[symmetric] second(2)[symmetric]
      data_pair_product_lists; blast)
next
  fix p assume "\<exists>z. data_product_operands_presents z p"
  then obtain xs ys where parts: "data_elements xs" "data_elements ys"
    "fst p=data_list_term ys" "snd p=data_list_term xs"
    by (simp only: data_finite_set_fields; blast)
  show "\<exists>q. (324,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning data_product_system"
    by (rule exI[of _ "data_list_term (data_product_list xs ys)"])
      (use parts in \<open>simp only: data_product_ordered_lists; blast\<close>)
qed

lemma data_product_compared_output:
  assumes "data_finite_set_presents S p"
  shows "(219,Pair_Term p q)\<in>positive_meaning data_product_system \<longleftrightarrow> data_finite_set_presents S q"
  by (simp only: data_product_components data_set_comparison_finite_set_output[OF assms])

theorem data_product_contract:
  "presented_function_contract data_product_operands_presents data_product_operands_domain
    (\<lambda>p. \<exists>z. data_product_operands_presents z p)
    data_finite_set_presents data_finite_set_domain (\<lambda>q. \<exists>S. data_finite_set_presents S q)
    (\<lambda>z. data_pair_product (snd z) (fst z))
    (\<lambda>p q. (325,context_relation_argument (fst p) (snd p) q)\<in>positive_meaning data_product_system)"
  by (rule data_product_comparison.presented_contract[OF data_product_witness data_product_compared_output])

corollary data_product_at_presentations:
  assumes "data_finite_set_presents X p" "data_finite_set_presents Y r"
  shows "(325,context_relation_argument r p q)\<in>positive_meaning data_product_system \<longleftrightarrow>
    data_finite_set_presents (data_pair_product X Y) q"
proof -
  have read: "data_product_operands_presents (Y,X) (r,p)" using assms by simp
  show ?thesis using presented_function_contract.output[OF data_product_contract read, of q] by simp
qed

corollary data_product_presentation_invariance:
  assumes "data_finite_set_presents X p" "data_finite_set_presents X p'"
    "data_finite_set_presents Y r" "data_finite_set_presents Y r'"
    "data_finite_set_presents Z q" "data_finite_set_presents Z q'"
  shows "((325,context_relation_argument r p q)\<in>positive_meaning data_product_system) =
    ((325,context_relation_argument r' p' q')\<in>positive_meaning data_product_system)"
  using data_product_at_presentations[OF assms(1,3), of q]
    data_product_at_presentations[OF assms(2,4), of q'] assms(5,6)
    presentation_class.recovery[OF data_finite_set_class] by blast

section \<open>The fixed native package applies to every future complete operand\<close>

theorem data_product_complete_quotation:
  assumes "(325,t)\<in>positive_meaning data_product_system"
  shows "complete_data_quoted_at (term_syntax t) [] t"
proof -
  have data: "term_formed t" "self_contained_term t"
    using assms by (auto simp: data_product_exact data_list_term_formed data_list_term_self_contained)
  show ?thesis using complete_data_quotation_total[OF data] by blast
qed

theorem native_data_product:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {325::nat} \<and>
    (\<forall>d\<in>{325}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (\<exists>xs ys zs. data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
            t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs) \<and>
            set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys})) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{325}\<subseteq>system_definitions data_product_system" by auto
  have calls: "schema_call_formed data_product_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{325}" for d t using data_product_call[of d t] selected that by blast
  have result: "(d,t)\<in>positive_meaning data_product_system \<longleftrightarrow>
      (\<exists>xs ys zs. data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
        t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs) \<and>
        set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys})"
    if "d\<in>{325}" for d t using that data_product_exact[of t] by simp
  show ?thesis by (rule compiled_exact_operations[OF data_product_system_formed selected calls result])
qed

text \<open>
  The subject product is defined directly from the two finite sets. The
  source class allows all orders and repetitions of each input independently.
  A complete function contract follows by composing the ordered witness
  with the existing finite-set identity comparison. Its output theorem and
  recovery account for both accepted and rejected comparisons across all
  presentations. The context position supplies the second product factor;
  the traversed operand supplies the first.

  The complete native package is fixed before all future formed operands.
  Quotation includes the complete admitted data. Isabelle checks these
  mathematical contracts; native checking of those proofs remains separate.
\<close>

end
