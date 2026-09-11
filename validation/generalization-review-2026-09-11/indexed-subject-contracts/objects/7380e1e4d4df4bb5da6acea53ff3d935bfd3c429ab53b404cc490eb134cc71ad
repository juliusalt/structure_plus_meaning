theory Factor_Scope_Programs
  imports Factor_Judgment_Scope_Reading Factor_Program_Scope_Reports
begin

section \<open>The two independent scope readers share complete definitions\<close>

lemma scope_program_overlap:
  "system_definitions judgment_scope_reading_system\<inter>system_definitions program_scope_reports_system=
    system_definitions judgment_scope_base_system\<inter>system_definitions program_report_base_system"
proof -
  have fresh: "{160,161,164,165,166}\<inter>system_definitions scope_reading_components_system={}"
    using context_base_subdomain by (auto dest: subsetD)
  have separate: "{160::nat,161}\<inter>{164,165,166}={}"
    by simp
  show ?thesis
    using judgment_scope_base_subdomain program_report_base_subdomain fresh separate
    unfolding judgment_scope_reading_definitions program_scope_reports_definitions by blast
qed

lemma scope_program_agreement:
  "systems_agree_on judgment_scope_reading_system program_scope_reports_system
    (system_definitions judgment_scope_reading_system\<inter>system_definitions program_scope_reports_system)"
proof -
  let ?U="system_definitions judgment_scope_base_system\<inter>system_definitions program_report_base_system"
  have first: "systems_agree_on judgment_scope_reading_system scope_reading_components_system ?U"
    by (rule systems_agree_on_subdomain[OF systems_agree_on_sym[OF judgment_scope_reading_agreement]]) auto
  have second: "systems_agree_on scope_reading_components_system program_scope_reports_system ?U"
    by (rule systems_agree_on_subdomain[OF program_scope_reports_agreement]) auto
  show ?thesis by (simp only: scope_program_overlap; rule systems_agree_on_transitive[OF first second])
qed

definition scope_programs_system :: "(nat,nat,nat,nat) schema_system" where
  "scope_programs_system=system_union judgment_scope_reading_system program_scope_reports_system"

lemma scope_programs_formed [simp]: "schema_system_formed scope_programs_system"
  unfolding scope_programs_system_def
  by (rule system_union_agree_formed[OF judgment_scope_reading_formed program_scope_reports_formed scope_program_agreement])

lemma scope_programs_definitions [simp]:
  "system_definitions scope_programs_system=
    system_definitions judgment_scope_reading_system\<union>system_definitions program_scope_reports_system"
  by (simp add: scope_programs_system_def)

lemma scope_programs_call:
  "schema_call_formed scope_programs_system d t \<longleftrightarrow>
    d\<in>system_definitions scope_programs_system \<and> term_formed t"
  using system_union_agree_call[OF judgment_scope_reading_formed program_scope_reports_formed
    scope_program_agreement, of d t]
  by (simp only: scope_programs_system_def system_union_definitions judgment_scope_reading_call
    program_scope_reports_call Un_iff; blast)

lemma scope_programs_judgment_agreement:
  "systems_agree_on judgment_scope_reading_system scope_programs_system
    (system_definitions judgment_scope_reading_system)"
  using system_union_agree_left[OF program_scope_reports_formed scope_program_agreement]
  by (simp only: scope_programs_system_def)

lemma scope_programs_program_agreement:
  "systems_agree_on program_scope_reports_system scope_programs_system
    (system_definitions program_scope_reports_system)"
proof -
  have reverse: "systems_agree_on program_scope_reports_system judgment_scope_reading_system
      (system_definitions program_scope_reports_system\<inter>system_definitions judgment_scope_reading_system)"
    using systems_agree_on_sym[OF scope_program_agreement] by (simp only: Int_commute)
  show ?thesis using system_union_agree_left[OF judgment_scope_reading_formed reverse]
    by (simp only: scope_programs_system_def system_union_commute)
qed

lemma scope_programs_base_agreement:
  "systems_agree_on scope_reading_components_system scope_programs_system
    (system_definitions judgment_scope_base_system\<union>system_definitions program_report_base_system)"
proof -
  have j: "systems_agree_on scope_reading_components_system scope_programs_system
      (system_definitions judgment_scope_base_system)"
    by (rule systems_agree_on_transitive[OF judgment_scope_reading_agreement
      systems_agree_on_subdomain[OF scope_programs_judgment_agreement]]) auto
  have p: "systems_agree_on scope_reading_components_system scope_programs_system
      (system_definitions program_report_base_system)"
    by (rule systems_agree_on_transitive[OF program_scope_reports_agreement
      systems_agree_on_subdomain[OF scope_programs_program_agreement]]) auto
  show ?thesis using j p by (auto simp: systems_agree_on_def)
qed

theorem scope_programs_judgment_locality:
  assumes "d\<in>system_definitions judgment_scope_reading_system"
  shows "schema_call_formed scope_programs_system d t \<longleftrightarrow>
      schema_call_formed judgment_scope_reading_system d t"
    and "(d,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning judgment_scope_reading_system"
  using system_union_agree_left_locality[OF judgment_scope_reading_formed program_scope_reports_formed
    scope_program_agreement assms, of t]
  by (simp_all only: scope_programs_system_def)

theorem scope_programs_program_locality:
  assumes "d\<in>system_definitions program_scope_reports_system"
  shows "schema_call_formed scope_programs_system d t \<longleftrightarrow>
      schema_call_formed program_scope_reports_system d t"
    and "(d,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning program_scope_reports_system"
  using system_union_agree_right_locality[OF judgment_scope_reading_formed program_scope_reports_formed
    scope_program_agreement assms, of t]
  by (simp_all only: scope_programs_system_def)

lemma scope_programs_components:
  "(160,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
    (160,t)\<in>positive_meaning judgment_scope_reading_system"
  "(161,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
    (161,t)\<in>positive_meaning judgment_scope_reading_system"
  "(164,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
    (164,t)\<in>positive_meaning program_scope_reports_system"
  "(165,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
    (165,t)\<in>positive_meaning program_scope_reports_system"
  "(166,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow>
    (166,t)\<in>positive_meaning program_scope_reports_system"
  using scope_programs_judgment_locality(2)[of 160 t] scope_programs_judgment_locality(2)[of 161 t]
    scope_programs_program_locality(2)[of 164 t] scope_programs_program_locality(2)[of 165 t]
    scope_programs_program_locality(2)[of 166 t] by auto

lemma scope_programs_boundary:
  "system_definitions scope_programs_system\<subseteq>
    system_definitions scope_reading_components_system\<union>{160,161,164,165,166}"
  using judgment_scope_base_subdomain program_report_base_subdomain by auto

section \<open>One fixed program provides every future scope operation\<close>

abbreviation scope_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "scope_operation_result d t \<equiv>
    if d=160 then (\<exists>c v. t=Pair_Term c v \<and> presentation_transport judgment_artifact_presents judgment_context_presents c v)
    else if d=161 then (\<exists>j. judgment_artifact_presents j t)
    else if d=164 then (\<exists>p q. t=Pair_Term p q \<and> presentation_transport program_scope_value_presents program_scope_value_presents p q)
    else if d=165 then (\<exists>c v. t=Pair_Term c v \<and> presentation_transport program_artifact_presents program_scope_value_presents c v)
    else (\<exists>k. program_artifact_presents k t)"

theorem scope_operations_exact:
  assumes "d\<in>{160,161,164,165,166}"
  shows "(d,t)\<in>positive_meaning scope_programs_system \<longleftrightarrow> scope_operation_result d t"
  using assms by (auto simp: scope_programs_components judgment_scope_report_exact judgment_scope_reading_exact
    program_scope_identity_exact program_scope_report_exact program_scope_artifact_exact; blast)

theorem native_scope_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {160::nat,161,164,165,166} \<and>
    (\<forall>d\<in>{160,161,164,165,166}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> scope_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{160,161,164,165,166}\<subseteq>system_definitions scope_programs_system" by auto
  have calls: "schema_call_formed scope_programs_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{160,161,164,165,166}" for d t
    using scope_programs_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF scope_programs_formed selected calls scope_operations_exact])
qed

text \<open>
  Each local reader already owns an exact presentation and correspondence
  contract. Complete-definition agreement composes their actual programs and
  preserves both meanings. Their union does not identify judgment contexts
  with closed program scopes or change either class's independent subject.

  Compilation fixes all five entries and one closed finite program before
  any future formed input. Every actual extension retains that entire program,
  its artifacts and bindings, and the exact operation result. The chosen
  natural coordinates specify this construction and add no semantic names.
\<close>

end
