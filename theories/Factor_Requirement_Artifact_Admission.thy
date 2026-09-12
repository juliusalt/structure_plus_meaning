theory Factor_Requirement_Artifact_Admission
  imports Factor_Fixed_Requirement_Plans Factor_Quoted_Body_Guards
begin

section \<open>The exact artifact body carries the checked construction of the original request\<close>

definition requirement_artifact_admitted ::
  "nat set \<Rightarrow> admission_goal list \<Rightarrow> nat \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "requirement_artifact_admitted D gs n R \<longleftrightarrow>
    (\<exists>r ds k cs. checked_admission_sequence D gs n=Some (ds,k,cs) \<and>
      complete_data_quoted_at R r
        (admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
          (data_list_term (map admission_counter ds)) (admission_counter k)
          (data_list_term (map admission_instruction_value cs))))"

definition requirement_artifact_system :: "nat set \<Rightarrow> admission_goal list \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat,nat) schema_system" where
  "requirement_artifact_system D gs n=add_view_definition (fixed_requirement_system D gs n) 369 data_x
    {(0,quoted_body_guard_schema 10 123 368)}"

interpretation requirement_artifacts:
  quoted_body_guard_extension "fixed_requirement_system D gs n" 369 10 123 368
proof (rule quoted_body_guard_extension.intro)
  show "schema_system_formed (fixed_requirement_system D gs n)" by simp
  show "369\<notin>system_definitions (fixed_requirement_system D gs n)" by simp
  show "{10,123,368}\<subseteq>system_definitions (fixed_requirement_system D gs n)" by auto
  show "(10,t)\<in>positive_meaning (fixed_requirement_system D gs n) \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system" for t
    using fixed_requirement_old_meaning[where d=10 and t=t and D=D and gs=gs and n=n]
      request_quotation_components(1)[where t=t and D=D] by auto
  show "(123,t)\<in>positive_meaning (fixed_requirement_system D gs n) \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system" for t
    using fixed_requirement_old_meaning[where d=123 and t=t and D=D and gs=gs and n=n]
      request_quotation_components(2)[where t=t and D=D] by auto
qed

lemma requirement_artifact_system_formed [simp]: "schema_system_formed (requirement_artifact_system D gs n)"
  using requirement_artifacts.installed.formed by (simp only: requirement_artifact_system_def)

lemma requirement_artifact_system_definitions [simp]:
  "system_definitions (requirement_artifact_system D gs n)=insert 369 (system_definitions (fixed_requirement_system D gs n))"
  by (simp add: requirement_artifact_system_def)

lemma requirement_artifact_call:
  "schema_call_formed (requirement_artifact_system D gs n) 369 z \<longleftrightarrow> term_formed z"
  by (simp only: requirement_artifact_system_def requirement_artifacts.installed.view_call; simp)

theorem requirement_artifact_exact:
  assumes "finite D"
  shows "(369,z)\<in>positive_meaning (requirement_artifact_system D gs n) \<longleftrightarrow>
    (\<exists>R. z=Target_Term (Whole_Artifact R) \<and> requirement_artifact_admitted D gs n R)"
  by (simp only: requirement_artifact_system_def requirement_artifacts.exact
    fixed_requirement_result[OF assms] requirement_artifact_admitted_def; blast)

corollary requirement_artifact_at_literal:
  assumes "finite D"
  shows "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning (requirement_artifact_system D gs n)
    \<longleftrightarrow> requirement_artifact_admitted D gs n R"
  by (simp only: requirement_artifact_exact[OF assms] factor_term.inject exact_target.inject; blast)

theorem requirement_artifact_on_complete_body:
  assumes finite: "finite D" and quoted:
    "complete_data_quoted_at R r
      (admission_plan_argument (data_list_term (map admission_goal_value hs)) (admission_counter m)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"
  shows "requirement_artifact_admitted D gs n R \<longleftrightarrow>
    hs=gs \<and> m=n \<and> checked_admission_sequence D gs n=Some (ds,k,cs)"
  using requirement_artifacts.on_complete_body[OF quoted, where D=D and gs=gs and n=n]
  by (simp only: requirement_artifact_system_def[symmetric] requirement_artifact_at_literal[OF finite]
    fixed_requirement_at_values[OF finite])

theorem requirement_artifact_installation:
  assumes source: "schema_system_formed P" and admitted: "requirement_artifact_admitted (system_definitions P) gs n R"
  shows "\<exists>r ds k cs.
    complete_data_quoted_at R r
      (admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs))) \<and>
    admission_source (required_admission_system P ds k cs) (Suc k) \<and>
    admission_extension P (required_admission_system P ds k cs) \<and>
    (\<forall>t. (k,t)\<in>positive_meaning (required_admission_system P ds k cs) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning P) g t))"
proof -
  obtain r ds k cs where checked: "checked_admission_sequence (system_definitions P) gs n=Some (ds,k,cs)"
    and quoted: "complete_data_quoted_at R r
      (admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
        (data_list_term (map admission_counter ds)) (admission_counter k)
        (data_list_term (map admission_instruction_value cs)))"
    using admitted unfolding requirement_artifact_admitted_def by blast
  have native: "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))
        \<in>positive_meaning (admission_request_system (system_definitions P))"
    by (simp only: checked_admission_sequence_at_values[OF system_definitions_finite[OF source]] checked)
  show ?thesis by (rule exI[of _ r], rule exI[of _ ds], rule exI[of _ k], rule exI[of _ cs])
    (use quoted checked_native_requirement_installation[OF source native] in blast)
qed

text \<open>
  The native predicate reads the literal artifact's complete body and applies
  the fixed original request check to it. Whole quotation rules out ignored
  attachments. The constructor's result entries and instructions therefore
  come from this exact artifact, and their installation satisfies every
  original requirement on the same future subject.

  This local admission does not establish that the chosen requirement family
  is adequate for a larger problem or that a history permits the generation.
  Those remain distinct obligations with their own actual subjects.
\<close>

end
