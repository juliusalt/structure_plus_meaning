theory Factor_Program_Scope_Reports
  imports Factor_Scope_Reading_Base Factor_Transported_Readings Factor_Program_Scope_Reading Factor_Reader_Clauses
begin

section \<open>The complete artifact determines its closed program scope\<close>

abbreviation program_artifact_presents where
  "program_artifact_presents \<equiv>
    composed_presentation program_scope_value_presents quoted_artifact_presents"

theorem program_artifact_presentation_class:
  "presentation_class program_artifact_presents program_scope_subject
    (\<lambda>c. \<exists>k. program_artifact_presents k c)"
proof -
  have result: "presentation_class program_artifact_presents program_scope_subject
      (\<lambda>c. \<exists>t. (122,t)\<in>positive_meaning package_retention_admission_system \<and> quoted_artifact_presents t c)"
    by (rule quoted_artifact_presentation_class[OF program_scope_value_presentation_class])
      (use site_value_presents_formed in \<open>auto simp: package_retention_admission_exact; blast\<close>)
  interpret scopes: presentation_class program_scope_value_presents program_scope_subject
    "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
    by (rule program_scope_value_presentation_class)
  have admission: "(\<lambda>c. \<exists>t. (122,t)\<in>positive_meaning package_retention_admission_system \<and> quoted_artifact_presents t c)=
      (\<lambda>c. \<exists>k. program_artifact_presents k c)"
    by (intro ext) (simp only: scopes.admissible_iff composed_presentation_def; blast)
  show ?thesis using result by (simp only: admission)
qed

interpretation program_artifacts: presentation_class program_artifact_presents program_scope_subject
  "\<lambda>c. \<exists>k. program_artifact_presents k c"
  by (rule program_artifact_presentation_class)

lemma program_artifact_at_source:
  assumes material: "artifact_value_presents C c"
  shows "program_artifact_presents ((E,(u,r)),P) c \<longleftrightarrow>
    (\<exists>q. program_scope_quoted_at C q E u r P)"
  by (simp only: composed_presentation_def quoted_artifact_at_source[OF material] fst_conv snd_conv)
    (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)

section \<open>Program scope comparison adds its own intrinsic admission\<close>

definition program_report_base_system :: "(nat,nat,nat,nat) schema_system" where
  "program_report_base_system=rooted_system scope_reading_components_system {122,123,158}"

lemma program_report_base_formed [simp]: "schema_system_formed program_report_base_system"
  unfolding program_report_base_system_def by (rule rooted_system_formed[OF scope_reading_components_formed])

lemma program_report_base_subdomain:
  "system_definitions program_report_base_system\<subseteq>system_definitions scope_reading_components_system"
  unfolding program_report_base_system_def by (rule rooted_system_subdomain)

lemma program_report_base_roots:
  "{122,123,158}\<subseteq>system_definitions program_report_base_system"
  unfolding program_report_base_system_def by (rule rooted_system_roots[OF scope_reading_components_formed]) auto

lemma program_report_base_call:
  "schema_call_formed program_report_base_system d t \<longleftrightarrow>
    d\<in>system_definitions program_report_base_system \<and> term_formed t"
  using rooted_system_calls[where roots="{122,123,158}" and d=d and t=t, OF scope_reading_components_formed]
  by (simp only: program_report_base_system_def rooted_system_def system_restriction_definitions
    scope_reading_components_call; blast)

lemma program_report_base_meaning:
  assumes "d\<in>system_definitions program_report_base_system"
  shows "(d,t)\<in>positive_meaning program_report_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning scope_reading_components_system"
  using rooted_system_meaning[where roots="{122,123,158}" and d=d and t=t, OF scope_reading_components_formed] assms
  by (simp only: program_report_base_system_def rooted_system_def system_restriction_definitions; blast)

lemma program_report_base_agreement:
  "systems_agree_on scope_reading_components_system program_report_base_system
    (system_definitions program_report_base_system)"
  unfolding program_report_base_system_def by (rule rooted_system_agreement)

lemma program_report_base_least:
  assumes "{122,123,158}\<subseteq>U" "system_dependency_closed scope_reading_components_system U"
  shows "system_definitions program_report_base_system\<subseteq>U"
  unfolding program_report_base_system_def
  by (rule rooted_system_least[OF scope_reading_components_formed _ assms]) auto

lemma program_report_fresh:
  "164\<notin>system_definitions program_report_base_system"
  "165\<notin>system_definitions program_report_base_system"
  "166\<notin>system_definitions program_report_base_system"
proof -
  let ?B="system_definitions complete_data_admission_system\<union>system_definitions artifact_lookup_system\<union>{156,157,158,159}"
  have bound: "system_definitions program_report_base_system\<subseteq>?B"
    using program_report_base_subdomain context_base_subdomain
    unfolding scope_reading_components_definitions context_admission_definitions by blast
  have separate: "?B\<inter>{164,165,166}={}"
    by auto
  show "164\<notin>system_definitions program_report_base_system" using bound separate by blast
  show "165\<notin>system_definitions program_report_base_system" using bound separate by blast
  show "166\<notin>system_definitions program_report_base_system" using bound separate by blast
qed

definition program_scope_identity_schema :: "(nat,nat,nat) factor_schema" where
  "program_scope_identity_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,122,data_x),(1,158,Pattern_Pair data_x data_y)}"

definition program_scope_identity_system :: "(nat,nat,nat,nat) schema_system" where
  "program_scope_identity_system=add_view_definition program_report_base_system 164 data_x
    {(0,program_scope_identity_schema)}"

interpretation program_scope_identity_view: positive_view program_report_base_system 164 data_x
  "{(0,program_scope_identity_schema)}"
  by (rule positive_view.intro[OF program_report_base_formed program_report_fresh(1)])
    (use program_report_base_roots in \<open>auto simp: program_scope_identity_schema_def schema_formed_def
      schema_dependencies_def single_valued_def rel_ran_def\<close>)

lemma program_scope_identity_formed [simp]: "schema_system_formed program_scope_identity_system"
  unfolding program_scope_identity_system_def by (rule program_scope_identity_view.formed)

definition program_scope_report_system :: "(nat,nat,nat,nat) schema_system" where
  "program_scope_report_system=add_view_definition program_scope_identity_system 165 data_x
    {(0,transported_reading_schema 123 164)}"

interpretation program_scope_report_view: positive_view program_scope_identity_system 165 data_x
  "{(0,transported_reading_schema 123 164)}"
  by (rule transported_reading_view[OF program_scope_identity_formed])
    (use program_report_fresh(2) program_report_base_roots in \<open>auto simp: program_scope_identity_system_def\<close>)

lemma program_scope_report_formed [simp]: "schema_system_formed program_scope_report_system"
  unfolding program_scope_report_system_def by (rule program_scope_report_view.formed)

definition program_scope_reports_system :: "(nat,nat,nat,nat) schema_system" where
  "program_scope_reports_system=add_view_definition program_scope_report_system 166 data_x
    {(0,reader_projection_clause 0 1 0 165)}"

interpretation program_scope_projection_view: positive_view program_scope_report_system 166 data_x
  "{(0,reader_projection_clause 0 1 0 165)}"
  by (rule reader_projection_view[OF program_scope_report_formed])
    (use program_report_fresh(3) in \<open>auto simp: program_scope_report_system_def program_scope_identity_system_def\<close>)

lemma program_scope_reports_formed [simp]: "schema_system_formed program_scope_reports_system"
  unfolding program_scope_reports_system_def by (rule program_scope_projection_view.formed)

lemma program_scope_reports_definitions [simp]:
  "system_definitions program_scope_reports_system={164,165,166}\<union>system_definitions program_report_base_system"
  by (auto simp: program_scope_reports_system_def program_scope_report_system_def program_scope_identity_system_def)

lemma program_scope_identity_call:
  "schema_call_formed program_scope_identity_system d t \<longleftrightarrow>
    d\<in>system_definitions program_scope_identity_system \<and> term_formed t"
  using added_variable_calls[OF program_report_base_formed program_scope_identity_view.formed program_report_base_call]
  by (simp only: program_scope_identity_system_def[symmetric])

lemma program_scope_report_call:
  "schema_call_formed program_scope_report_system d t \<longleftrightarrow>
    d\<in>system_definitions program_scope_report_system \<and> term_formed t"
  using added_variable_calls[OF program_scope_identity_formed program_scope_report_view.formed program_scope_identity_call]
  by (simp only: program_scope_report_system_def[symmetric])

lemma program_scope_reports_call:
  "schema_call_formed program_scope_reports_system d t \<longleftrightarrow>
    d\<in>system_definitions program_scope_reports_system \<and> term_formed t"
  using added_variable_calls[OF program_scope_report_formed program_scope_projection_view.formed program_scope_report_call]
  by (simp only: program_scope_reports_system_def[symmetric])

lemma program_scope_reports_old_agreement:
  "systems_agree_on program_report_base_system program_scope_reports_system
    (system_definitions program_report_base_system)"
  by (simp add: program_scope_reports_system_def program_scope_report_system_def program_scope_identity_system_def
    systems_agree_on_added program_report_fresh)

lemma program_scope_reports_old_meaning:
  assumes "d\<in>system_definitions program_report_base_system"
  shows "(d,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning program_report_base_system"
  using program_scope_projection_view.old_meaning[of d t] program_scope_report_view.old_meaning[of d t]
    program_scope_identity_view.old_meaning[OF assms, of t] assms
  by (auto simp: program_scope_reports_system_def program_scope_report_system_def program_scope_identity_system_def)

lemma program_scope_reports_agreement:
  "systems_agree_on scope_reading_components_system program_scope_reports_system
    (system_definitions program_report_base_system)"
  by (rule systems_agree_on_transitive[OF program_report_base_agreement program_scope_reports_old_agreement])

lemma program_scope_reports_components:
  "(122,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (122,t)\<in>positive_meaning package_retention_admission_system"
  "(123,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  "(158,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (158,t)\<in>positive_meaning context_admission_system"
proof -
  have member_122: "122\<in>system_definitions program_report_base_system"
    by (rule subsetD[OF program_report_base_roots]) simp
  show "(122,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
      (122,t)\<in>positive_meaning package_retention_admission_system"
    by (simp only: program_scope_reports_old_meaning[OF member_122] program_report_base_meaning[OF member_122] scope_reading_components)
  have member_123: "123\<in>system_definitions program_report_base_system"
    by (rule subsetD[OF program_report_base_roots]) simp
  show "(123,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
      (123,t)\<in>positive_meaning complete_data_admission_system"
    by (simp only: program_scope_reports_old_meaning[OF member_123] program_report_base_meaning[OF member_123] scope_reading_components)
  have member_158: "158\<in>system_definitions program_report_base_system"
    by (rule subsetD[OF program_report_base_roots]) simp
  show "(158,t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
      (158,t)\<in>positive_meaning context_admission_system"
    by (simp only: program_scope_reports_old_meaning[OF member_158] program_report_base_meaning[OF member_158] scope_reading_components)
qed

lemma program_scope_reports_identity_family [simp]:
  "((164,c),S)\<in>system_clauses program_scope_reports_system \<longleftrightarrow>
    c=0 \<and> S=program_scope_identity_schema"
  using program_scope_identity_view.no_old_clause
  by (auto simp: program_scope_reports_system_def program_scope_report_system_def program_scope_identity_system_def)

lemma program_scope_identity_valuation:
  "(164,z)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      z=Pair_Term (h 0) (h 1) \<and>
      (122,h 0)\<in>positive_meaning program_scope_reports_system \<and>
      (158,Pair_Term (h 0) (h 1))\<in>positive_meaning program_scope_reports_system)"
proof -
  have ordinary: "schema_material_premises program_scope_identity_schema={}"
    by (simp add: program_scope_identity_schema_def)
  have accepts: "schema_call_formed program_scope_reports_system 164
      (evaluate_pattern h (schema_conclusion program_scope_identity_schema))"
    if "\<forall>a\<in>schema_variables program_scope_identity_schema. term_formed (h a)" for h
    using that by (auto simp: program_scope_reports_call program_scope_identity_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF program_scope_reports_identity_family ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: program_scope_identity_schema_def schema_variables_def conj_ac all_conj_distrib imp_conjL)
    done
qed

lemma program_scope_identity_calls:
  "(164,z)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>p q. z=Pair_Term p q \<and>
      (122,p)\<in>positive_meaning package_retention_admission_system \<and>
      (158,Pair_Term p q)\<in>positive_meaning context_admission_system)"
proof
  assume "(164,z)\<in>positive_meaning program_scope_reports_system"
  then show "\<exists>p q. z=Pair_Term p q \<and>
      (122,p)\<in>positive_meaning package_retention_admission_system \<and>
      (158,Pair_Term p q)\<in>positive_meaning context_admission_system"
    by (simp only: program_scope_identity_valuation program_scope_reports_components) blast
next
  assume "\<exists>p q. z=Pair_Term p q \<and>
      (122,p)\<in>positive_meaning package_retention_admission_system \<and>
      (158,Pair_Term p q)\<in>positive_meaning context_admission_system"
  then obtain p q where parts: "z=Pair_Term p q"
    "(122,p)\<in>positive_meaning package_retention_admission_system"
    "(158,Pair_Term p q)\<in>positive_meaning context_admission_system" by blast
  have formed: "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
  show "(164,z)\<in>positive_meaning program_scope_reports_system"
    by (simp only: program_scope_identity_valuation program_scope_reports_components;
      rule exI[of _ "\<lambda>a::nat. if a=0 then p else q"])
      (use parts formed in auto)
qed

theorem program_scope_identity_transport:
  "(164,Pair_Term p q)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    presentation_transport program_scope_value_presents program_scope_value_presents p q"
proof -
  interpret scopes: presentation_class program_scope_value_presents program_scope_subject
    "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
    by (rule program_scope_value_presentation_class)
  have retained: "((122,p)\<in>positive_meaning package_retention_admission_system \<and>
      presentation_transport site_context_presents site_context_presents p q) \<longleftrightarrow>
      presentation_transport program_scope_value_presents program_scope_value_presents p q"
    using site_presentations.recovery
    by (auto simp: scopes.admissible_iff presentation_transport_def; metis fst_conv snd_conv)
  show ?thesis by (simp only: program_scope_identity_calls site_context_identity_transport)
    (use retained in auto)
qed

theorem program_scope_identity_exact:
  "(164,z)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>p q. z=Pair_Term p q \<and>
      presentation_transport program_scope_value_presents program_scope_value_presents p q)"
  using program_scope_identity_calls program_scope_identity_transport by blast

interpretation program_scope_identity: presented_function_contract
  program_scope_value_presents program_scope_subject "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
  program_scope_value_presents program_scope_subject "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
  id "\<lambda>p q. (164,Pair_Term p q)\<in>positive_meaning program_scope_reports_system"
proof -
  have operation: "(\<lambda>p q. (164,Pair_Term p q)\<in>positive_meaning program_scope_reports_system)=
      presentation_transport program_scope_value_presents program_scope_value_presents"
    by (intro ext; rule program_scope_identity_transport)
  show "presented_function_contract program_scope_value_presents program_scope_subject
      (\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system)
      program_scope_value_presents program_scope_subject
      (\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system) id
      (\<lambda>p q. (164,Pair_Term p q)\<in>positive_meaning program_scope_reports_system)"
    by (simp only: operation; rule presentation_identity_function[OF program_scope_value_presentation_class
      program_scope_value_presentation_class])
qed

interpretation program_scope_transport: transported_reading_profile program_scope_reports_system 165 123 164
proof (unfold_locales)
  show "schema_system_formed program_scope_reports_system" by (rule program_scope_reports_formed)
next
  fix c S
  show "((165,c),S)\<in>system_clauses program_scope_reports_system \<longleftrightarrow>
      (c,S)\<in>{(0,transported_reading_schema 123 164)}"
    using program_scope_report_view.no_old_clause
    by (auto simp: program_scope_reports_system_def program_scope_report_system_def)
next
  fix t
  show "schema_call_formed program_scope_reports_system 165 t \<longleftrightarrow> term_formed t"
    by (simp add: program_scope_reports_call)
qed

interpretation program_scope_projection: reader_projection_profile program_scope_reports_system 166 165 0 1 0 0
proof (unfold_locales)
  show "schema_system_formed program_scope_reports_system" by (rule program_scope_reports_formed)
  show "(0::nat)\<noteq>1" by simp
next
  fix c S
  show "((166,c),S)\<in>system_clauses program_scope_reports_system \<longleftrightarrow>
      c=0 \<and> S=reader_projection_clause 0 1 0 165"
    using program_scope_projection_view.no_old_clause by (auto simp: program_scope_reports_system_def)
next
  fix t
  show "schema_call_formed program_scope_reports_system 166 t \<longleftrightarrow> term_formed t"
    by (simp add: program_scope_reports_call)
qed

lemma program_scope_quotation_component:
  "(\<exists>q. (123,Pair_Term c (Pair_Term q t))\<in>positive_meaning program_scope_reports_system)
    \<longleftrightarrow> quoted_artifact_presents t c"
  by (auto simp: program_scope_reports_components complete_data_admission_exact quoted_artifact_presents_def)

theorem program_scope_report_transport:
  "(165,Pair_Term c t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    presentation_transport program_artifact_presents program_scope_value_presents c t"
  by (rule program_scope_transport.composition_transport[OF program_scope_quotation_component
    program_scope_identity_transport])

theorem program_scope_report_exact:
  "(165,z)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>c t. z=Pair_Term c t \<and>
      presentation_transport program_artifact_presents program_scope_value_presents c t)"
proof
  assume native: "(165,z)\<in>positive_meaning program_scope_reports_system"
  obtain c t where shape: "z=Pair_Term c t"
    using program_scope_transport.exact[of z] native by blast
  have transported: "presentation_transport program_artifact_presents program_scope_value_presents c t"
    using native by (simp only: shape program_scope_report_transport)
  show "\<exists>c t. z=Pair_Term c t \<and> presentation_transport program_artifact_presents program_scope_value_presents c t"
    using shape transported by blast
next
  assume "\<exists>c t. z=Pair_Term c t \<and> presentation_transport program_artifact_presents program_scope_value_presents c t"
  then obtain c t where shape: "z=Pair_Term c t" and transported: "presentation_transport program_artifact_presents program_scope_value_presents c t" by blast
  show "(165,z)\<in>positive_meaning program_scope_reports_system"
    by (simp only: shape program_scope_report_transport) (rule transported)
qed

theorem program_scope_artifact_exact:
  "(166,c)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>k. program_artifact_presents k c)"
  by (simp only: program_scope_projection.exact program_scope_report_transport presentation_transport_def)
    (use program_artifacts.subject_boundary program_scope_identity.left.total in blast)

theorem program_artifact_native_class:
  "presentation_class program_artifact_presents program_scope_subject
    (\<lambda>c. (166,c)\<in>positive_meaning program_scope_reports_system)"
  using program_artifact_presentation_class by (simp only: program_scope_artifact_exact)

interpretation program_scope_reports: presented_function_contract
  program_artifact_presents program_scope_subject "\<lambda>c. (166,c)\<in>positive_meaning program_scope_reports_system"
  program_scope_value_presents program_scope_subject "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
  id "\<lambda>c t. (165,Pair_Term c t)\<in>positive_meaning program_scope_reports_system"
  by (rule program_scope_transport.identity_function_contract[OF program_artifact_native_class
    program_scope_value_presentation_class program_scope_quotation_component program_scope_identity_transport])

theorem program_scope_report_at_artifact:
  assumes material: "artifact_value_presents C c"
  shows "(165,Pair_Term c t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>q E u r P. program_scope_quoted_at C q E u r P \<and> program_scope_value_presents ((E,(u,r)),P) t)"
  by (simp only: program_scope_report_transport presentation_transport_def)
    (use program_artifact_at_source[OF material] in \<open>auto; metis prod.exhaust_sel\<close>)

corollary program_scope_report_preserves_actual_body:
  assumes material: "artifact_value_presents C c"
  shows "(165,Pair_Term c t)\<in>positive_meaning program_scope_reports_system \<longleftrightarrow>
    (\<exists>q b k. complete_data_quoted_at C q b \<and> program_scope_value_presents k b \<and>
      program_scope_value_presents k t)"
  by (simp only: program_scope_report_transport presentation_transport_def composed_presentation_def
    quoted_artifact_at_source[OF material]) blast

text \<open>
  This class keeps the complete closed package subject already specified by
  the program-scope owner. Its identity clause admits the actual source scope
  and compares the whole site context. The second scope and its unique
  program are thereby determined; a duplicate admission premise is unnecessary.

  Complete quotation composes with this independent class. The same generic
  transported reader used for judgment contexts compares the actual stored
  body with every compatible report. The owned function contract supplies
  invariance in both presentations. Existing minimal-scope and future-call
  theorems continue to describe the recovered program.
\<close>

end
