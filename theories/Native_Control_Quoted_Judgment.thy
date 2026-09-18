theory Native_Control_Quoted_Judgment
  imports Native_Control_Literal_Boundary Factor_Requirement_Artifact_Admission
    Factor_System_Relocation
begin

section \<open>Ground body meaning with natural occurrence coordinates\<close>

definition judgment_ground_clauses :: "finite_factor_term list \<Rightarrow>
    (nat \<times> (nat,nat,nat) factor_schema) set" where
  "judgment_ground_clauses xs=(\<lambda>i. (i,recognizer_schema
    (exact_term_pattern (decode_finite_term (xs!i))))) ` {0..<length xs}"

lemma judgment_ground_view:
  assumes source: "schema_system_formed P" and fresh: "e\<notin>system_definitions P"
    and formed: "list_all finite_term_formed xs"
  shows "positive_view P e data_x (judgment_ground_clauses xs)"
  by (rule positive_view.intro[OF source fresh])
    (use formed in \<open>auto simp: judgment_ground_clauses_def list_all_iff
      finite_term_formed_correct recognizer_schema_def schema_formed_def single_valued_def
      schema_dependencies_def rel_ran_def\<close>)

lemma judgment_ground_rules:
  assumes formed: "list_all finite_term_formed xs"
  shows "(\<exists>c S. (c,S)\<in>judgment_ground_clauses xs \<and> schema_rule_instance S X t)
    \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof
  assume holds: "\<exists>c S. (c,S)\<in>judgment_ground_clauses xs \<and> schema_rule_instance S X t"
  then obtain i where index: "i<length xs" and same: "t=decode_finite_term (xs!i)"
    by (auto simp: judgment_ground_clauses_def exact_recognizer_rule)
  show "t\<in>decode_finite_term ` set xs"
    unfolding same by (rule imageI, rule nth_mem[OF index])
next
  assume "t\<in>decode_finite_term ` set xs"
  then obtain x where member: "x\<in>set xs" and same: "t=decode_finite_term x" by blast
  obtain i where index: "i<length xs" "x=xs!i"
    using member by (auto simp: in_set_conv_nth; blast)
  let ?S="recognizer_schema (exact_term_pattern (decode_finite_term (xs!i))) :: (nat,nat,nat) factor_schema"
  have clause: "(i,?S)\<in>judgment_ground_clauses xs"
    unfolding judgment_ground_clauses_def by (rule imageI) (use index in auto)
  have tf: "term_formed (decode_finite_term x)"
    using formed member by (auto simp: list_all_iff finite_term_formed_correct)
  have actual: "schema_rule_instance ?S X t"
    using tf same by (simp only: exact_recognizer_rule index(2); blast)
  show "\<exists>c S. (c,S)\<in>judgment_ground_clauses xs \<and> schema_rule_instance S X t"
    by (rule exI[of _ i], rule exI[of _ ?S], rule conjI[OF clause actual])
qed

locale quoted_judgment_rows =
  fixes xs :: "finite_factor_term list"
  assumes rows_formed: "list_all finite_term_formed xs"
begin

sublocale rows: positive_view "request_quotation_system {}" 368 data_x "judgment_ground_clauses xs"
  by (rule judgment_ground_view[OF request_quotation_formed _ rows_formed]) simp

definition body_system :: "(nat,nat,nat,nat) schema_system" where
  "body_system=add_view_definition (request_quotation_system {}) 368 data_x (judgment_ground_clauses xs)"

lemma body_formed: "schema_system_formed body_system"
  by (simp only: body_system_def rows.formed)

lemma body_definitions [simp]:
  "system_definitions body_system=insert 368 (system_definitions (request_quotation_system {}))"
  by (simp add: body_system_def)

lemma body_meaning:
  "(368,t)\<in>positive_meaning body_system \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
  using rows_formed
  by (simp only: body_system_def rows.view_meaning judgment_ground_rules[OF rows_formed];
    auto simp: list_all_iff finite_term_formed_correct)

sublocale quoted: quoted_body_guard_extension body_system 369 10 123 368
proof (rule quoted_body_guard_extension.intro[OF body_formed])
  show "369\<notin>system_definitions body_system" by simp
  show "{10,123,368}\<subseteq>system_definitions body_system" by auto
  show "(10,t)\<in>positive_meaning body_system \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system" for t
    using rows.old_meaning[of 10 t] request_quotation_components(1)[where D="{}" and t=t]
    by (auto simp only: body_system_def; auto)
  show "(123,t)\<in>positive_meaning body_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system" for t
    using rows.old_meaning[of 123 t] request_quotation_components(2)[where D="{}" and t=t]
    by (auto simp only: body_system_def; auto)
qed

definition artifact_system where
  "artifact_system=add_view_definition body_system 369 data_x {(0,quoted_body_guard_schema 10 123 368)}"

lemma artifact_formed: "schema_system_formed artifact_system"
  by (simp only: artifact_system_def quoted.installed.formed)

lemma artifact_entry: "369\<in>system_definitions artifact_system"
  by (simp add: artifact_system_def)

theorem artifact_exact:
  "(369,z)\<in>positive_meaning artifact_system \<longleftrightarrow>
    (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
      t\<in>decode_finite_term ` set xs)"
  by (simp only: artifact_system_def quoted.exact body_meaning)

theorem artifact_on_complete_body:
  assumes quote: "complete_data_quoted_at R r t"
  shows "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning artifact_system
    \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
  by (simp only: artifact_system_def quoted.on_complete_body[OF quote] body_meaning)

text \<open>All complete formed readdressings are covered by the original quotation
  contract. No enumeration of preferred artifact copies defines this guard.\<close>

end

section \<open>The installed source supplies the body predicate's exact meaning\<close>

locale installed_quoted_judgment =
  fixes present :: "'a \<Rightarrow> finite_factor_term" and subjects :: "'a list"
    and condition :: "'a \<Rightarrow> bool"
    and d :: "local_address option definition_site"
    and F :: "local_address option finite_artifact_environment" and u :: "local_address option"
    and P :: "local_address option native_system"
  assumes formed: "\<And>x. x\<in>set subjects \<Longrightarrow> finite_term_formed (present x)"
    and source: "filtered_judgment_source present subjects condition=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] P"
begin

sublocale artifact: quoted_judgment_rows "filtered_judgment_rows present subjects condition"
  by (rule quoted_judgment_rows.intro)
    (use formed in \<open>auto simp: filtered_judgment_rows_def list_all_iff\<close>)

lemma installed_body_meaning:
  "(d,t)\<in>positive_meaning P \<longleftrightarrow>
    t\<in>decode_finite_term ` set (filtered_judgment_rows present subjects condition)"
proof -
  obtain Q where q: "native_package_at (decode_finite_environment F) u [] Q"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning Q \<longleftrightarrow>
      t\<in>decode_finite_term ` set (filtered_judgment_rows present subjects condition)"
    by (rule finite_ground_source_meaning[OF source[unfolded filtered_judgment_source_def]]) blast
  have same: "P=Q" by (rule native_package_unique[OF package q])
  show ?thesis using meaning by (simp only: same; blast)
qed

theorem installed_artifact_meaning:
  "(369,z)\<in>positive_meaning artifact.artifact_system \<longleftrightarrow>
    (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
      (d,t)\<in>positive_meaning P)"
  by (simp only: artifact.artifact_exact installed_body_meaning)

theorem installed_artifact_body:
  assumes quote: "complete_data_quoted_at R r t"
  shows "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning artifact.artifact_system
    \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  by (simp only: artifact.artifact_on_complete_body[OF quote] installed_body_meaning)

theorem policy_cause_body:
  assumes injective: "inj_on g (system_definitions artifact.artifact_system)"
    and variant: "system_alpha_variant (rename_system g artifact.artifact_system) T"
    and policy: "native_package_at K pu pr T"
    and cause: "certified_policy_cause_at K pu pr (g 369) E gu gr G H root R"
  shows "\<exists>r t. complete_data_quoted_at R r t \<and> (d,t)\<in>positive_meaning P"
proof -
  have called: "(g 369,Target_Term (Whole_Artifact R))\<in>positive_meaning T"
    by (rule certified_policy_cause_sound[OF policy cause])
  have original: "(369,Target_Term (Whole_Artifact R))\<in>positive_meaning artifact.artifact_system"
    using called system_variant_renamed_meaning_at[OF artifact.artifact_formed injective variant
      artifact.artifact_entry, of "Target_Term (Whole_Artifact R)"] by blast
  show ?thesis using original by (simp only: installed_artifact_meaning factor_term.inject exact_target.inject; blast)
qed

text \<open>This consumes the actual original body package and the exact relocated
  guard package, including the original certified policy cause. It supplies no
  witness, governing owner policy, scope alignment, or authority by assumption.
  Those premises remain mandatory, and an unrelated accepting package does not
  satisfy the proved meaning transport.\<close>

end

end
