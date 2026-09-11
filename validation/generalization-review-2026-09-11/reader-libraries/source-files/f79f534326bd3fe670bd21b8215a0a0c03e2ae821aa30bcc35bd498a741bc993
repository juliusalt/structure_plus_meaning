theory Factor_Investigation_Input_Development_Execution
  imports Factor_Investigation_Input_Development Factor_Investigation_Input_Investigation
begin

lemma investigation_input_source_336:
  "admission_source investigation_input_base_system 336"
proof -
  have collection: "\<forall>d\<in>system_definitions observation_collection_system. d<336"
    using observation_base_subdomain data_set_comparison_base_subdomain by auto
  have base: "\<forall>d\<in>system_definitions observation_scope_base_system. d<336"
    using observation_scope_base_subdomain collection by blast
  have scope: "\<forall>d\<in>system_definitions observation_scope_system. d<336"
    using base by auto
  show ?thesis using investigation_input_base_subdomain scope
    by (auto simp: admission_source_def)
qed

abbreviation generated_input_example where
  "generated_input_example c \<equiv> Pair_Term (input_example_scope c)
    (data_list_term (map data_pair_term (input_example_relation c)))"

lemma generated_input_example_exact:
  assumes "336\<le>n"
  shows "(Suc (Suc n),generated_input_example c)\<in>positive_meaning (generated_investigation_input_system n)
    \<longleftrightarrow> input_example_admitted c"
proof -
  have source: "admission_source investigation_input_base_system n"
    by (rule admission_source_weaken[OF investigation_input_source_336 assms])
  have original: "(338,generated_input_example c)\<in>positive_meaning investigation_input_system
      \<longleftrightarrow> input_example_admitted c"
    by (simp only: investigation_input_encoded input_example_admitted_def)
  show ?thesis by (simp only: generated_investigation_input_contract(3)[OF source]
    investigation_input_exact[symmetric] original)
qed

definition generated_input_execution where
  "generated_input_execution n=(n\<ge>336,admission_plan investigation_input_goal n,
    if n<336 then [] else map (\<lambda>c.
      (Suc (Suc n),generated_input_example c)\<in>positive_meaning (generated_investigation_input_system n))
      [0,1,2,3,4,5,6,7,8,9,10])"

lemma generated_input_execution_code [code]:
  "generated_input_execution n=(n\<ge>336,admission_plan investigation_input_goal n,
    if n<336 then [] else map input_example_admitted [0,1,2,3,4,5,6,7,8,9,10])"
proof (cases "n<336")
  case True
  then show ?thesis by (simp add: generated_input_execution_def)
next
  case False
  have bound: "336\<le>n" using False by simp
  have decisions: "map (\<lambda>c. (Suc (Suc n),generated_input_example c)\<in>
      positive_meaning (generated_investigation_input_system n)) ids=map input_example_admitted ids" for ids
    by (rule map_cong) (simp_all only: generated_input_example_exact[OF bound])
  show ?thesis by (simp only: generated_input_execution_def decisions)
qed

text \<open>
  Execution retains the plan actually computed from the independent input
  goal, including all allocated entries and constructor arguments. Its eleven
  decisions concern the resulting installed native program. The proved code
  equation reuses that program's all-term contract. The supplied execution
  family starts at 336 or above; a smaller counter yields no decision list
  and an explicit failed execution-domain check. This is not a claim that
  every smaller counter collides with the source program.
\<close>

end
