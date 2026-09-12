theory Factor_Admission_Goal_Support
  imports Factor_Admission_Request_Primitives
begin

section \<open>Every leaf in the actual goal structure must belong to the source\<close>

definition admission_supported_goal_result :: "nat set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "admission_supported_goal_result D z \<longleftrightarrow>
    (\<exists>g. admission_goal_sites g\<subseteq>D \<and> z=admission_goal_value g)"

theorem admission_supported_goal_sound:
  assumes finite: "finite D"
    and holds: "(363,z)\<in>positive_meaning (admission_request_system D)"
  shows "admission_supported_goal_result D z"
proof -
  have invariant: "(363::nat)=363 \<longrightarrow> admission_supported_goal_result D z"
  proof (rule positive_valuation_induct[OF holds,
      where property="\<lambda>d t. d=363 \<longrightarrow> admission_supported_goal_result D t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses (admission_request_system D)"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and head: "schema_call_formed (admission_request_system D) d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning (admission_request_system D) \<and>
        (e=363 \<longrightarrow> admission_supported_goal_result D (evaluate_pattern f p))"
    show "d=363 \<longrightarrow> admission_supported_goal_result D (evaluate_pattern f (schema_conclusion S))"
    proof
      assume root: "d=363"
      consider (leaf) "S=admission_supported_leaf_schema" | (pair) "S=admission_supported_pair_schema"
        | (collection) "S=admission_supported_list_schema"
        using clause root by (auto simp: admission_request_clauses admission_request_family_def
          admission_supported_goal_clauses_def)
      then show "admission_supported_goal_result D (evaluate_pattern f (schema_conclusion S))"
      proof cases
        case leaf
        have child: "(362,f 0)\<in>positive_meaning (admission_request_system D)"
          using support by (auto simp: leaf admission_supported_leaf_schema_def)
        obtain a where fields: "a\<in>D" "f 0=admission_counter a"
          using child by (simp only: admission_supported_site_exact[OF finite]) blast
        show ?thesis unfolding admission_supported_goal_result_def
          by (rule exI[of _ "Existing_Admission a"])
            (use fields in \<open>simp add: leaf admission_supported_leaf_schema_def\<close>)
      next
        case pair
        have left: "admission_supported_goal_result D (f 0)"
          and right: "admission_supported_goal_result D (f 1)"
          using support by (auto simp: pair admission_supported_pair_schema_def)
        obtain g h where fields: "admission_goal_sites g\<subseteq>D" "admission_goal_sites h\<subseteq>D"
          "f 0=admission_goal_value g" "f 1=admission_goal_value h"
          using left right by (auto simp: admission_supported_goal_result_def)
        show ?thesis unfolding admission_supported_goal_result_def
          by (rule exI[of _ "Paired_Admission g h"])
            (use fields in \<open>simp add: pair admission_supported_pair_schema_def\<close>)
      next
        case collection
        have child: "admission_supported_goal_result D (f 0)"
          using support by (auto simp: collection admission_supported_list_schema_def)
        obtain g where fields: "admission_goal_sites g\<subseteq>D" "f 0=admission_goal_value g"
          using child by (auto simp: admission_supported_goal_result_def)
        show ?thesis unfolding admission_supported_goal_result_def
          by (rule exI[of _ "Collected_Admission g"])
            (use fields in \<open>simp add: collection admission_supported_list_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem admission_supported_goal_complete:
  assumes finite: "finite D" and supported: "admission_goal_sites g\<subseteq>D"
  shows "(363,admission_goal_value g)\<in>positive_meaning (admission_request_system D)"
  using supported
proof (induction g)
  case (Existing_Admission a)
  have child: "(362,admission_counter a)\<in>positive_meaning (admission_request_system D)"
    using Existing_Admission.prems by (simp only: admission_supported_site_at_counter[OF finite]; simp)
  have result: "(363,evaluate_pattern (\<lambda>_. admission_counter a)
      (schema_conclusion admission_supported_leaf_schema))\<in>positive_meaning (admission_request_system D)"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use child in \<open>auto simp: admission_request_clauses admission_request_family_def
        admission_supported_goal_clauses_def admission_supported_leaf_schema_def schema_variables_def
        admission_request_call octets_formed_def\<close>)
  show ?case using result by (simp add: admission_supported_leaf_schema_def)
next
  case (Paired_Admission g h)
  have left: "(363,admission_goal_value g)\<in>positive_meaning (admission_request_system D)"
    and right: "(363,admission_goal_value h)\<in>positive_meaning (admission_request_system D)"
    using Paired_Admission.IH Paired_Admission.prems by auto
  let ?f="\<lambda>i::nat. if i=0 then admission_goal_value g else admission_goal_value h"
  have result: "(363,evaluate_pattern ?f (schema_conclusion admission_supported_pair_schema))
      \<in>positive_meaning (admission_request_system D)"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use left right in \<open>auto simp: admission_request_clauses admission_request_family_def
        admission_supported_goal_clauses_def admission_supported_pair_schema_def schema_variables_def
        admission_request_call octets_formed_def\<close>)
  show ?case using result by (simp add: admission_supported_pair_schema_def)
next
  case (Collected_Admission g)
  have child: "(363,admission_goal_value g)\<in>positive_meaning (admission_request_system D)"
    using Collected_Admission.IH Collected_Admission.prems by simp
  have result: "(363,evaluate_pattern (\<lambda>_. admission_goal_value g)
      (schema_conclusion admission_supported_list_schema))\<in>positive_meaning (admission_request_system D)"
    by (rule ordinary_positive_valuation_step[where c=2])
      (use child in \<open>auto simp: admission_request_clauses admission_request_family_def
        admission_supported_goal_clauses_def admission_supported_list_schema_def schema_variables_def
        admission_request_call octets_formed_def\<close>)
  show ?case using result by (simp add: admission_supported_list_schema_def)
qed

theorem admission_supported_goal_exact:
  assumes "finite D"
  shows "(363,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    admission_supported_goal_result D z"
  using admission_supported_goal_sound[OF assms] admission_supported_goal_complete[OF assms]
  by (auto simp: admission_supported_goal_result_def)

theorem admission_supported_goal_at_value:
  assumes "finite D"
  shows "(363,admission_goal_value g)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    admission_goal_sites g\<subseteq>D"
  by (simp only: admission_supported_goal_exact[OF assms] admission_supported_goal_result_def
    admission_goal_value_injective; auto)

interpretation admission_supported_goals:
  list_profile "admission_request_system D" 363 364
  by (rule list_profile.intro)
    (auto simp: admission_request_clauses admission_request_family_def admission_request_call)

theorem admission_supported_goals_at_values:
  assumes "finite D"
  shows "(364,data_list_term (map admission_goal_value gs))\<in>positive_meaning (admission_request_system D)
    \<longleftrightarrow> (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>D)"
  by (simp only: admission_supported_goals.lists)
    (simp add: admission_supported_goal_at_value[OF assms])

text \<open>
  This is admission of the full submitted goal structure. Every original leaf
  is checked against the fixed complete source domain; an unsupported leaf
  inside a pair or a collection remains unsupported. Repetition and order do
  not erase any occurrence. The outer list may be empty, which is why the
  allocation condition is independently required by the request constructor.
\<close>

end
