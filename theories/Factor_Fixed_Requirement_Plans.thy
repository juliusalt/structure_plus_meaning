theory Factor_Fixed_Requirement_Plans
  imports Factor_Request_Quotation_Base Factor_Pattern_Restrictions
begin

abbreviation requirement_request_value where
  "requirement_request_value gs n \<equiv>
    Pair_Term (data_list_term (map admission_goal_value gs)) (admission_counter n)"

lemma admission_goal_values_injective [simp]:
  "data_list_term (map admission_goal_value gs)=data_list_term (map admission_goal_value hs) \<longleftrightarrow> gs=hs"
proof -
  have goals: "inj admission_goal_value" by (rule injI) simp
  show ?thesis by (simp add: data_list_term_injective goals)
qed

lemma requirement_request_value_injective [simp]:
  "requirement_request_value gs n=requirement_request_value hs m \<longleftrightarrow> gs=hs \<and> n=m"
  by simp

definition fixed_requirement_system :: "nat set \<Rightarrow> admission_goal list \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat,nat) schema_system" where
  "fixed_requirement_system D gs n=restrict_call_system (request_quotation_system D) 368
    (Pattern_Pair (exact_term_pattern (requirement_request_value gs n)) data_x) 367"

interpretation fixed_requirements: pattern_restriction "request_quotation_system D" 368 367
  "Pattern_Pair (exact_term_pattern (requirement_request_value gs n)) data_x"
  by (rule pattern_restriction.intro)
    (auto simp: data_list_term_formed octets_formed_def)

lemma fixed_requirement_formed [simp]: "schema_system_formed (fixed_requirement_system D gs n)"
  using fixed_requirements.formed by (simp only: fixed_requirement_system_def)

lemma fixed_requirement_definitions [simp]:
  "system_definitions (fixed_requirement_system D gs n)=insert 368 (system_definitions (request_quotation_system D))"
  by (simp add: fixed_requirement_system_def restrict_call_system_def)

lemma fixed_requirement_old_meaning:
  assumes "d\<in>system_definitions (request_quotation_system D)"
  shows "(d,t)\<in>positive_meaning (fixed_requirement_system D gs n) \<longleftrightarrow>
    (d,t)\<in>positive_meaning (request_quotation_system D)"
  using fixed_requirements.old_meaning[OF assms, where t=t and gs=gs and n=n]
  by (simp only: fixed_requirement_system_def)

theorem fixed_requirement_exact:
  "(368,z)\<in>positive_meaning (fixed_requirement_system D gs n) \<longleftrightarrow>
    (\<exists>out. z=Pair_Term (requirement_request_value gs n) out) \<and>
    (367,z)\<in>positive_meaning (admission_request_system D)"
proof -
  have formed: "term_formed (requirement_request_value gs n)"
    by (simp add: data_list_term_formed octets_formed_def)
  have target_formed: "term_formed z" if "(367,z)\<in>positive_meaning (admission_request_system D)"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  show ?thesis by (simp only: fixed_requirement_system_def fixed_requirements.exact
    request_quotation_components(3) tagged_pattern_accepts[OF formed])
    (use target_formed in auto)
qed

theorem fixed_requirement_at_values:
  assumes "finite D"
  shows "(368,admission_plan_argument (data_list_term (map admission_goal_value hs)) (admission_counter m)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning (fixed_requirement_system D gs n)
    \<longleftrightarrow> hs=gs \<and> m=n \<and> checked_admission_sequence D gs n=Some (ds,k,cs)"
  by (simp only: fixed_requirement_exact checked_admission_sequence_at_values[OF assms]
    factor_term.inject admission_goal_values_injective admission_counter_injective; auto)

corollary fixed_requirement_rejects_changed_request:
  assumes "hs\<noteq>gs \<or> m\<noteq>n"
  shows "(368,Pair_Term (requirement_request_value hs m) out)
    \<notin>positive_meaning (fixed_requirement_system D gs n)"
  using assms by (simp only: fixed_requirement_exact factor_term.inject
    admission_goal_values_injective admission_counter_injective; auto)

theorem fixed_requirement_result:
  assumes finite: "finite D"
  shows "(368,z)\<in>positive_meaning (fixed_requirement_system D gs n) \<longleftrightarrow>
    (\<exists>ds k cs. checked_admission_sequence D gs n=Some (ds,k,cs) \<and>
      z=admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"
  by (simp only: fixed_requirement_exact checked_admission_sequence_exact[OF finite]
    checked_admission_sequence_result_def factor_term.inject admission_goal_values_injective
    admission_counter_injective; auto)

text \<open>
  The independently fixed goal family and initial counter occur in the
  installed interface itself. A different request cannot use this entry,
  even if that different request has its own successful construction. The
  original complete source domain still governs leaf support and allocation.
\<close>

end
