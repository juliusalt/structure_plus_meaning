theory Factor_Checked_Requirement_Plans
  imports Factor_Admission_Goal_Support
begin

section \<open>The admitted context is the same request used by the planner\<close>

interpretation admission_requests: admitted_pair_profile "admission_request_system D" 366 364 365
  by (rule admitted_pair_profile.intro)
    (auto simp: admission_request_clauses admission_request_family_def admission_request_call)

interpretation checked_admission_sequences: admitted_context_profile "admission_request_system D" 367 366 361
  by (rule admitted_context_profile.intro)
    (auto simp: admission_request_clauses admission_request_family_def admission_request_call)

theorem admission_request_at_values:
  assumes "finite D"
  shows "(366,Pair_Term (data_list_term (map admission_goal_value gs)) (admission_counter n))
      \<in>positive_meaning (admission_request_system D) \<longleftrightarrow> admission_request_supported D gs n"
  by (simp only: admission_requests.exact)
    (auto simp: admission_supported_goals_at_values[OF assms]
      admission_fresh_counter_at_counter admission_request_supported_def)

theorem checked_admission_sequence_at_values:
  assumes "finite D"
  shows "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning (admission_request_system D)
    \<longleftrightarrow> checked_admission_sequence D gs n=Some (ds,k,cs)"
proof -
  have sequence: "(361,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
      (361,z)\<in>positive_meaning admission_sequence_system" for z
    by (rule admission_request_old_meaning) simp
  show ?thesis by (simp only: checked_admission_sequences.at_input admission_request_at_values[OF assms]
    sequence admission_sequence_at_values checked_admission_sequence_def; auto)
qed

definition checked_admission_sequence_result :: "nat set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "checked_admission_sequence_result D z \<longleftrightarrow>
    (\<exists>gs n ds k cs. checked_admission_sequence D gs n=Some (ds,k,cs) \<and>
      z=admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"

theorem checked_admission_sequence_exact:
  assumes finite: "finite D"
  shows "(367,z)\<in>positive_meaning (admission_request_system D) \<longleftrightarrow>
    checked_admission_sequence_result D z"
proof
  assume holds: "(367,z)\<in>positive_meaning (admission_request_system D)"
  have underlying: "(361,z)\<in>positive_meaning (admission_request_system D)"
    using holds by (simp only: checked_admission_sequences.exact; blast)
  have sequence: "admission_sequence_result z"
    using underlying by (simp only: admission_request_components(4))
  obtain gs n ds k cs where shape:
    "z=admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs))"
    using sequence by (auto simp: admission_sequence_result_def)
  have checked: "checked_admission_sequence D gs n=Some (ds,k,cs)"
    using holds by (simp only: shape checked_admission_sequence_at_values[OF finite])
  show "checked_admission_sequence_result D z"
    using checked shape unfolding checked_admission_sequence_result_def by blast
next
  assume "checked_admission_sequence_result D z"
  then obtain gs n ds k cs where checked: "checked_admission_sequence D gs n=Some (ds,k,cs)"
    and shape: "z=admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs))"
    unfolding checked_admission_sequence_result_def by blast
  show "(367,z)\<in>positive_meaning (admission_request_system D)"
    by (simp only: shape checked_admission_sequence_at_values[OF finite] checked)
qed

theorem checked_native_requirement_installation:
  assumes source: "schema_system_formed P"
    and native: "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))
        \<in>positive_meaning (admission_request_system (system_definitions P))"
  shows "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    "k\<notin>system_definitions P"
proof -
  have checked: "checked_admission_sequence (system_definitions P) gs n=Some (ds,k,cs)"
    using native by (simp only: checked_admission_sequence_at_values[OF system_definitions_finite[OF source]])
  show "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
    "schema_call_formed (required_admission_system P ds k cs) k t \<longleftrightarrow> term_formed t"
    "k\<notin>system_definitions P"
    by (rule checked_admission_sequence_installed[OF source checked])+
qed

theorem checked_requirement_rejects_unsupported:
  assumes finite: "finite D" and member: "g\<in>set gs" and absent: "d\<in>admission_goal_sites g" "d\<notin>D"
  shows "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<notin>positive_meaning (admission_request_system D)"
  using member absent by (auto simp: checked_admission_sequence_at_values[OF finite]
    checked_admission_sequence_def admission_request_supported_def)

theorem checked_requirement_rejects_occupied_counter:
  assumes finite: "finite D" and occupied: "d\<in>D" "n\<le>d"
  shows "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<notin>positive_meaning (admission_request_system D)"
  using occupied by (auto simp: checked_admission_sequence_at_values[OF finite]
    checked_admission_sequence_def admission_request_supported_def admission_source_floor_exact[OF finite])

text \<open>
  The native verdict now supplies support and allocation together with the
  exact constructed plan. Successful planning alone cannot admit an unsupported
  request, and an empty requirement family cannot bypass the allocation check.
  Installation consumes the actual source program's domain, established before
  the request, and preserves that source's complete old meanings.

  The problem must still supply its independently justified complete goal
  family and actual subject contract. These theorems do not allow a candidate
  to remove a requirement, replace the source domain, or authorize its own
  handoff. Native development-generation admission remains a further join.
\<close>

end
