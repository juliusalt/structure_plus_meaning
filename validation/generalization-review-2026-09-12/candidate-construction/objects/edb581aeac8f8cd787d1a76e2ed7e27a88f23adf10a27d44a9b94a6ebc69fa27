theory Factor_Judgment_Scope_Reading
  imports Factor_Scope_Reading_Base Factor_Transported_Readings Factor_Reader_Clauses
begin

section \<open>A complete judgment artifact presents an independently formed context\<close>

abbreviation judgment_artifact_presents where
  "judgment_artifact_presents \<equiv>
    composed_presentation judgment_context_presents quoted_artifact_presents"

theorem judgment_artifact_presentation_class:
  "presentation_class judgment_artifact_presents judgment_context_formed
    (\<lambda>c. \<exists>j. judgment_artifact_presents j c)"
proof -
  have result: "presentation_class judgment_artifact_presents judgment_context_formed
      (\<lambda>c. \<exists>t. (\<exists>j. judgment_context_presents j t) \<and> quoted_artifact_presents t c)"
    by (rule quoted_artifact_presentation_class[OF judgment_context_presentation_class])
      (use judgment_context_formed_value in blast)
  have admission: "(\<lambda>c. \<exists>t. (\<exists>j. judgment_context_presents j t) \<and> quoted_artifact_presents t c)=
      (\<lambda>c. \<exists>j. judgment_artifact_presents j c)"
    by (intro ext) (simp only: composed_presentation_def; blast)
  show ?thesis using result by (simp only: admission)
qed

interpretation judgment_artifacts: presentation_class judgment_artifact_presents judgment_context_formed
  "\<lambda>c. \<exists>j. judgment_artifact_presents j c"
  by (rule judgment_artifact_presentation_class)

lemma judgment_artifact_at_source:
  assumes material: "artifact_value_presents C c"
  shows "judgment_artifact_presents j c \<longleftrightarrow> (\<exists>r. judgment_quotation_presents j (C,r))"
  by (simp only: composed_presentation_def quoted_artifact_at_source[OF material])
    (auto simp: judgment_value_quoted_at_def)

section \<open>Only quotation and judgment correspondence are retained\<close>

definition judgment_scope_base_system :: "(nat,nat,nat,nat) schema_system" where
  "judgment_scope_base_system=rooted_system scope_reading_components_system {123,159}"

lemma judgment_scope_base_formed [simp]: "schema_system_formed judgment_scope_base_system"
  unfolding judgment_scope_base_system_def by (rule rooted_system_formed[OF scope_reading_components_formed])

lemma judgment_scope_base_subdomain:
  "system_definitions judgment_scope_base_system\<subseteq>system_definitions scope_reading_components_system"
  unfolding judgment_scope_base_system_def by (rule rooted_system_subdomain)

lemma judgment_scope_base_roots:
  "{123,159}\<subseteq>system_definitions judgment_scope_base_system"
  unfolding judgment_scope_base_system_def by (rule rooted_system_roots[OF scope_reading_components_formed]) auto

lemma judgment_scope_base_call:
  "schema_call_formed judgment_scope_base_system d t \<longleftrightarrow>
    d\<in>system_definitions judgment_scope_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="{123,159}" and d=d and t=t, OF scope_reading_components_formed]
  by (simp only: judgment_scope_base_system_def rooted_system_def system_restriction_definitions
    scope_reading_components_call; blast)

lemma judgment_scope_base_meaning:
  assumes "d\<in>system_definitions judgment_scope_base_system"
  shows "(d,t)\<in>positive_meaning judgment_scope_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning scope_reading_components_system"
  using rooted_system_meaning[where roots="{123,159}" and d=d and t=t, OF scope_reading_components_formed] assms
  by (simp only: judgment_scope_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma judgment_scope_base_agreement:
  "systems_agree_on scope_reading_components_system judgment_scope_base_system
    (system_definitions judgment_scope_base_system)"
  unfolding judgment_scope_base_system_def by (rule rooted_system_agreement)

lemma judgment_scope_base_boundary:
  "system_definitions judgment_scope_base_system\<subseteq>
    insert 123 (system_definitions quotation_admission_system)\<union>system_definitions context_admission_system"
  unfolding judgment_scope_base_system_def
  by (rule rooted_system_least[OF scope_reading_components_formed _ _ scope_judgment_dependency_boundary]) auto

lemma judgment_scope_fresh:
  "160\<notin>system_definitions judgment_scope_base_system"
  "161\<notin>system_definitions judgment_scope_base_system"
proof -
  let ?B="system_definitions complete_data_admission_system\<union>system_definitions artifact_lookup_system\<union>{156,157,158,159}"
  have bound: "system_definitions judgment_scope_base_system\<subseteq>?B"
    using judgment_scope_base_subdomain context_base_subdomain
    unfolding scope_reading_components_definitions context_admission_definitions by blast
  have separate: "?B\<inter>{160,161}={}"
    by auto
  show "160\<notin>system_definitions judgment_scope_base_system" using bound separate by blast
  show "161\<notin>system_definitions judgment_scope_base_system" using bound separate by blast
qed

definition judgment_scope_report_system :: "(nat,nat,nat,nat) schema_system" where
  "judgment_scope_report_system=add_view_definition judgment_scope_base_system 160 data_x
    {(0,transported_reading_schema 123 159)}"

interpretation judgment_scope_report_view: positive_view judgment_scope_base_system 160 data_x
  "{(0,transported_reading_schema 123 159)}"
  by (rule transported_reading_view[OF judgment_scope_base_formed judgment_scope_fresh(1)])
    (use judgment_scope_base_roots in auto)

lemma judgment_scope_report_formed [simp]: "schema_system_formed judgment_scope_report_system"
  unfolding judgment_scope_report_system_def by (rule judgment_scope_report_view.formed)

definition judgment_scope_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "judgment_scope_reading_system=add_view_definition judgment_scope_report_system 161 data_x
    {(0,reader_projection_clause 0 1 0 160)}"

interpretation judgment_scope_projection_view: positive_view judgment_scope_report_system 161 data_x
  "{(0,reader_projection_clause 0 1 0 160)}"
  by (rule reader_projection_view[OF judgment_scope_report_formed])
    (use judgment_scope_fresh(2) in \<open>auto simp: judgment_scope_report_system_def\<close>)

lemma judgment_scope_reading_formed [simp]: "schema_system_formed judgment_scope_reading_system"
  unfolding judgment_scope_reading_system_def by (rule judgment_scope_projection_view.formed)

lemma judgment_scope_reading_definitions [simp]:
  "system_definitions judgment_scope_reading_system={160,161}\<union>system_definitions judgment_scope_base_system"
  by (auto simp: judgment_scope_reading_system_def judgment_scope_report_system_def)

lemma judgment_scope_report_call:
  "schema_call_formed judgment_scope_report_system d t \<longleftrightarrow>
    d\<in>system_definitions judgment_scope_report_system \<and> term_formed t"
  using added_variable_calls[OF judgment_scope_base_formed judgment_scope_report_view.formed judgment_scope_base_call]
  by (simp only: judgment_scope_report_system_def[symmetric])

lemma judgment_scope_reading_call:
  "schema_call_formed judgment_scope_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions judgment_scope_reading_system \<and> term_formed t"
  using added_variable_calls[OF judgment_scope_report_formed judgment_scope_projection_view.formed judgment_scope_report_call]
  by (simp only: judgment_scope_reading_system_def[symmetric])

lemma judgment_scope_reading_old_agreement:
  "systems_agree_on judgment_scope_base_system judgment_scope_reading_system
    (system_definitions judgment_scope_base_system)"
  by (simp add: judgment_scope_reading_system_def judgment_scope_report_system_def
    systems_agree_on_added judgment_scope_fresh)

lemma judgment_scope_reading_old_meaning:
  assumes "d\<in>system_definitions judgment_scope_base_system"
  shows "(d,t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning judgment_scope_base_system"
  using judgment_scope_projection_view.old_meaning[of d t] judgment_scope_report_view.old_meaning[OF assms, of t] assms
  by (auto simp: judgment_scope_reading_system_def judgment_scope_report_system_def)

lemma judgment_scope_reading_agreement:
  "systems_agree_on scope_reading_components_system judgment_scope_reading_system
    (system_definitions judgment_scope_base_system)"
  by (rule systems_agree_on_transitive[OF judgment_scope_base_agreement judgment_scope_reading_old_agreement])

lemma judgment_scope_reading_components:
  "(123,t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  "(159,t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (159,t)\<in>positive_meaning context_admission_system"
proof -
  have member_123: "123\<in>system_definitions judgment_scope_base_system"
    by (rule subsetD[OF judgment_scope_base_roots]) simp
  show "(123,t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
      (123,t)\<in>positive_meaning complete_data_admission_system"
    by (simp only: judgment_scope_reading_old_meaning[OF member_123] judgment_scope_base_meaning[OF member_123] scope_reading_components)
  have member_159: "159\<in>system_definitions judgment_scope_base_system"
    by (rule subsetD[OF judgment_scope_base_roots]) simp
  show "(159,t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
      (159,t)\<in>positive_meaning context_admission_system"
    by (simp only: judgment_scope_reading_old_meaning[OF member_159] judgment_scope_base_meaning[OF member_159] scope_reading_components)
qed

interpretation judgment_scope_transport: transported_reading_profile judgment_scope_reading_system 160 123 159
proof (unfold_locales)
  show "schema_system_formed judgment_scope_reading_system" by (rule judgment_scope_reading_formed)
next
  fix c S
  show "((160,c),S)\<in>system_clauses judgment_scope_reading_system \<longleftrightarrow>
      (c,S)\<in>{(0,transported_reading_schema 123 159)}"
    using judgment_scope_report_view.no_old_clause
    by (auto simp: judgment_scope_reading_system_def judgment_scope_report_system_def)
next
  fix t
  show "schema_call_formed judgment_scope_reading_system 160 t \<longleftrightarrow> term_formed t"
    by (simp add: judgment_scope_reading_call)
qed

interpretation judgment_scope_projection: reader_projection_profile judgment_scope_reading_system 161 160 0 1 0 0
proof (unfold_locales)
  show "schema_system_formed judgment_scope_reading_system" by (rule judgment_scope_reading_formed)
  show "(0::nat)\<noteq>1" by simp
next
  fix c S
  show "((161,c),S)\<in>system_clauses judgment_scope_reading_system \<longleftrightarrow>
      c=0 \<and> S=reader_projection_clause 0 1 0 160"
    using judgment_scope_projection_view.no_old_clause by (auto simp: judgment_scope_reading_system_def)
next
  fix t
  show "schema_call_formed judgment_scope_reading_system 161 t \<longleftrightarrow> term_formed t"
    by (simp add: judgment_scope_reading_call)
qed

lemma judgment_scope_quotation_component:
  "(\<exists>q. (123,Pair_Term c (Pair_Term q t))\<in>positive_meaning judgment_scope_reading_system)
    \<longleftrightarrow> quoted_artifact_presents t c"
  by (auto simp: judgment_scope_reading_components complete_data_admission_exact quoted_artifact_presents_def)

lemma judgment_scope_comparison_component:
  "(159,Pair_Term p q)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    presentation_transport judgment_context_presents judgment_context_presents p q"
  by (simp only: judgment_scope_reading_components judgment_context_identity_transport)

theorem judgment_scope_report_transport:
  "(160,Pair_Term c t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    presentation_transport judgment_artifact_presents judgment_context_presents c t"
  by (rule judgment_scope_transport.composition_transport[OF judgment_scope_quotation_component
    judgment_scope_comparison_component])

theorem judgment_scope_report_exact:
  "(160,z)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (\<exists>c t. z=Pair_Term c t \<and>
      presentation_transport judgment_artifact_presents judgment_context_presents c t)"
proof
  assume native: "(160,z)\<in>positive_meaning judgment_scope_reading_system"
  obtain c t where shape: "z=Pair_Term c t"
    using judgment_scope_transport.exact[of z] native by blast
  have transported: "presentation_transport judgment_artifact_presents judgment_context_presents c t"
    using native by (simp only: shape judgment_scope_report_transport)
  show "\<exists>c t. z=Pair_Term c t \<and> presentation_transport judgment_artifact_presents judgment_context_presents c t"
    using shape transported by blast
next
  assume "\<exists>c t. z=Pair_Term c t \<and> presentation_transport judgment_artifact_presents judgment_context_presents c t"
  then obtain c t where shape: "z=Pair_Term c t" and transported: "presentation_transport judgment_artifact_presents judgment_context_presents c t" by blast
  show "(160,z)\<in>positive_meaning judgment_scope_reading_system"
    by (simp only: shape judgment_scope_report_transport) (rule transported)
qed

theorem judgment_scope_reading_exact:
  "(161,c)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (\<exists>j. judgment_artifact_presents j c)"
  by (simp only: judgment_scope_projection.exact judgment_scope_report_transport presentation_transport_def)
    (use judgment_artifacts.subject_boundary judgments.total in blast)

theorem judgment_artifact_native_class:
  "presentation_class judgment_artifact_presents judgment_context_formed
    (\<lambda>c. (161,c)\<in>positive_meaning judgment_scope_reading_system)"
  using judgment_artifact_presentation_class by (simp only: judgment_scope_reading_exact)

interpretation judgment_scope_reading: presented_function_contract
  judgment_artifact_presents judgment_context_formed "\<lambda>c. (161,c)\<in>positive_meaning judgment_scope_reading_system"
  judgment_context_presents judgment_context_formed "\<lambda>t. (157,t)\<in>positive_meaning context_admission_system"
  id "\<lambda>c t. (160,Pair_Term c t)\<in>positive_meaning judgment_scope_reading_system"
  by (rule judgment_scope_transport.identity_function_contract[OF judgment_artifact_native_class
    judgment_context_native_class judgment_scope_quotation_component judgment_scope_comparison_component])

theorem judgment_scope_report_at_artifact:
  assumes material: "artifact_value_presents C c"
  shows "(160,Pair_Term c t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (\<exists>j r. judgment_quotation_presents j (C,r) \<and> judgment_context_presents j t)"
  by (simp only: judgment_scope_report_transport presentation_transport_def judgment_artifact_at_source[OF material]) blast

corollary judgment_scope_report_preserves_actual_body:
  assumes material: "artifact_value_presents C c"
  shows "(160,Pair_Term c t)\<in>positive_meaning judgment_scope_reading_system \<longleftrightarrow>
    (\<exists>r b j. complete_data_quoted_at C r b \<and> judgment_context_presents j b \<and>
      judgment_context_presents j t)"
  by (simp only: judgment_scope_report_at_artifact[OF material] judgment_value_quoted_at_def fst_conv snd_conv; blast)

theorem judgment_scope_reading_has_no_judgment_checker:
  "system_definitions judgment_scope_reading_system\<inter>{80,85,109,115,122}={}"
proof -
  let ?B="insert 123 (system_definitions quotation_admission_system)\<union>
    system_definitions artifact_lookup_system\<union>{156,157,158,159}"
  have bound: "system_definitions judgment_scope_base_system\<subseteq>?B"
    using judgment_scope_base_boundary context_base_subdomain unfolding context_admission_definitions by blast
  have separate: "(?B\<union>{160,161})\<inter>{80,85,109,115,122}={}"
    by auto
  show ?thesis using bound separate unfolding judgment_scope_reading_definitions by blast
qed

text \<open>
  The independent subject remains every formed judgment context. A complete
  quotation presents that subject through its actual body; the report may
  use any other presentation of the same subject. The transported-reader
  contract owns this correspondence and both presentation invariances.

  The two native entries use exactly the least closure of quotation and
  context identity, followed by ordinary composition and projection. Their
  retained definitions exclude package admission, application admission,
  replay admission, positive judgment, and package retention. A recorded
  context therefore imposes none of those separate conditions.
\<close>

end
