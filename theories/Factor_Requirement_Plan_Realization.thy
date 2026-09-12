theory Factor_Requirement_Plan_Realization
  imports Factor_Requirement_Plans Factor_Admission_Sequence_Exact
begin

section \<open>Native output supplies the actual installation arguments\<close>

theorem admission_sequence_at_values:
  "(361,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning admission_sequence_system
    \<longleftrightarrow> admission_sequence gs n=(ds,k,cs)"
proof -
  have goals: "inj admission_goal_value" and instructions: "inj admission_instruction_value"
    and counters: "inj admission_counter" by (rule injI; simp)+
  show ?thesis by (auto simp: admission_sequence_exact admission_sequence_result_def
    data_list_term_injective goals instructions counters)
qed

theorem native_required_admission_installed:
  assumes native: "(361,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning admission_sequence_system"
    and source: "admission_source P n"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
  shows "admission_source (required_admission_system P ds k cs) (Suc k)"
    "admission_extension P (required_admission_system P ds k cs)"
    "(k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t)"
  using required_admission_installed[OF source supported
    native[unfolded admission_sequence_at_values]] by blast+

theorem native_required_admission_total:
  assumes source: "admission_source P n"
    and supported: "\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions P"
  shows "\<exists>ds k cs.
    (361,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning admission_sequence_system \<and>
    admission_source (required_admission_system P ds k cs) (Suc k) \<and>
    admission_extension P (required_admission_system P ds k cs) \<and>
    (\<forall>t. (k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t))"
proof -
  obtain ds k cs where sequence: "admission_sequence gs n=(ds,k,cs)"
    by (cases "admission_sequence gs n") auto
  show ?thesis by (rule exI[of _ ds], rule exI[of _ k], rule exI[of _ cs])
    (use required_admission_installed[OF source supported sequence] sequence
      in \<open>simp only: admission_sequence_at_values; blast\<close>)
qed

section \<open>One closed native planner precedes every future requirement family\<close>

theorem closed_requirement_planner:
  "\<exists>E :: local_address option artifact_environment. \<exists>u Q d.
    closed_native_package_at E u [] Q \<and> native_package_environment E u []=E \<and>
    d\<in>system_definitions Q \<and>
    (\<forall>z. schema_call_formed Q d z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (d,z)\<in>positive_meaning Q \<longleftrightarrow> admission_sequence_result z)"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and u Q where compiled:
    "inj_on g (system_definitions admission_sequence_system)"
    "closed_native_package_at E u [] Q" "native_package_environment E u []=E"
    "system_alpha_variant (rename_system g admission_sequence_system) Q"
    "positive_meaning Q=map_prod g id ` positive_meaning admission_sequence_system"
    using program_compilation_total[OF admission_sequence_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have member: "361\<in>system_definitions admission_sequence_system" by simp
  have definitions: "system_definitions Q=g ` system_definitions admission_sequence_system"
    using compiled(4) unfolding system_alpha_variant_def renamed_system_definitions by blast
  have entry: "g 361\<in>system_definitions Q" using member definitions by blast
  have call: "schema_call_formed Q (g 361) z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF admission_sequence_system_formed
      compiled(1,4) member] admission_sequence_call; simp)
  have meaning: "(g 361,z)\<in>positive_meaning Q \<longleftrightarrow> admission_sequence_result z" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) member compiled(5)] admission_sequence_exact)
  show ?thesis by (rule exI[of _ E], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ "g 361"])
    (use compiled(2,3) entry call meaning in blast)
qed

text \<open>
  The complete native output fixes the installation's entries, next counter,
  and component instructions. The source program keeps its previous meanings.
  The new predicate holds precisely when every original goal holds on that
  same formed subject. Its own conclusion supplies none of those prerequisites.

  The fixed closed native planner is independent of future goal families and
  their subjects. This joins native construction to its bootstrap installation
  contract. It does not admit a mathematical proof, establish a problem's full
  requirement boundary, or authorize a development generation by itself.
\<close>

end
