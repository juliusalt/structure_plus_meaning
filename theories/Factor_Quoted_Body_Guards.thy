theory Factor_Quoted_Body_Guards
  imports Factor_Complete_Data_Admission Factor_Rule_Instances
begin

section \<open>A predicate is applied to the actual complete body of a literal artifact\<close>

definition quoted_body_guard_schema :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat) factor_schema" where
  "quoted_body_guard_schema projection quotation predicate=data_rule data_x
    {(0,projection,Pattern_Pair data_x data_y),
     (1,quotation,complete_data_quotation_pattern data_y data_z data_w),
     (2,predicate,data_w)}"

lemma quoted_body_guard_formed [simp]: "schema_formed (quoted_body_guard_schema a b c)"
  by (auto simp: quoted_body_guard_schema_def schema_formed_def single_valued_def)

lemma quoted_body_guard_dependencies [simp]:
  "schema_dependencies (quoted_body_guard_schema a b c)={a,b,c}"
  by (auto simp: quoted_body_guard_schema_def schema_dependencies_def rel_ran_image)

locale quoted_body_guard_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry projection quotation predicate :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=quoted_body_guard_schema projection quotation predicate"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
    and projection_meaning: "\<And>t. (projection,t)\<in>positive_meaning P \<longleftrightarrow>
      (10,t)\<in>positive_meaning artifact_projection_system"
    and quotation_meaning: "\<And>t. (quotation,t)\<in>positive_meaning P \<longleftrightarrow>
      (123,t)\<in>positive_meaning complete_data_admission_system"
begin

lemma valuation:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and> z=h 0 \<and>
      (10,Pair_Term (h 0) (h 1))\<in>positive_meaning artifact_projection_system \<and>
      (123,complete_data_quotation_argument (h 1) (h 2) (h 3))\<in>positive_meaning complete_data_admission_system \<and>
      (predicate,h 3)\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family quoted_body_guard_schema_def schema_variables_def call projection_meaning quotation_meaning)

theorem exact:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
      (predicate,t)\<in>positive_meaning P)"
proof
  assume holds: "(entry,z)\<in>positive_meaning P"
  then obtain h :: "nat\<Rightarrow>factor_term" where shape: "z=h 0"
    and projected: "(10,Pair_Term (h 0) (h 1))\<in>positive_meaning artifact_projection_system"
    and quoted: "(123,complete_data_quotation_argument (h 1) (h 2) (h 3))
      \<in>positive_meaning complete_data_admission_system"
    and checked: "(predicate,h 3)\<in>positive_meaning P"
    by (auto simp: valuation)
  obtain R where literal: "h 0=Target_Term (Whole_Artifact R)"
    and material: "artifact_value_presents R (h 1)"
    using projected by (auto simp: artifact_projection_exact)
  obtain r where body: "complete_data_quoted_at R r (h 3)"
    using quoted by (simp only: complete_data_admission_at_artifact[OF material]) blast
  show "\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
      (predicate,t)\<in>positive_meaning P"
    using shape literal body checked by blast
next
  assume "\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
    (predicate,t)\<in>positive_meaning P"
  then obtain R r t where literal: "z=Target_Term (Whole_Artifact R)"
    and body: "complete_data_quoted_at R r t" and checked: "(predicate,t)\<in>positive_meaning P" by blast
  have formed: "exact_formed R" using complete_data_quotation_formed[OF body] by blast
  obtain c where material: "artifact_value_presents R c"
    using artifact_value_presents_total[OF formed] by blast
  have projected: "(10,Pair_Term z c)\<in>positive_meaning artifact_projection_system"
    by (simp only: literal artifact_projection_at_source material)
  have quoted: "(123,complete_data_quotation_argument c (Payload_Term r) t)
      \<in>positive_meaning complete_data_admission_system"
    by (simp only: complete_data_admission_on_values[OF material] body)
  have terms: "term_formed z" "term_formed c" "term_formed (Payload_Term r)" "term_formed t"
    using schema_call_formed_target[OF positive_meaning_formed[OF projected]]
      schema_call_formed_target[OF positive_meaning_formed[OF quoted]] by auto
  let ?h="\<lambda>i::nat. if i=0 then z else if i=1 then c else if i=2 then Payload_Term r else t"
  show "(entry,z)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h])
      (use terms projected quoted checked in auto)
qed

theorem on_complete_body:
  assumes quoted: "complete_data_quoted_at R r t"
  shows "(entry,Target_Term (Whole_Artifact R))\<in>positive_meaning P \<longleftrightarrow>
    (predicate,t)\<in>positive_meaning P"
  using complete_data_quotation_whole_unique[OF quoted]
  by (simp only: exact factor_term.inject exact_target.inject; use quoted in blast)

corollary on_data_syntax:
  assumes "term_formed t" "self_contained_term t"
  shows "(entry,Target_Term (Whole_Artifact (term_syntax t)))\<in>positive_meaning P \<longleftrightarrow>
    (predicate,t)\<in>positive_meaning P"
  by (rule on_complete_body[OF complete_data_quotation_total[OF assms]])

text \<open>
  The literal artifact supplies its own complete material presentation. Its
  actual whole quotation supplies the body on which the predicate is checked.
  A different body's successful judgment cannot satisfy these linked premises.
  Complete quotation also excludes ignored attachments and determines the
  body independently of its admitted address presentation.

  Installation must retain the actual projection and quotation meanings and
  an already justified body predicate. This reusable clause does not validate
  a supplied description, assert historical permission, or authorize itself.
\<close>

end

locale quoted_body_guard_extension =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry projection quotation predicate :: nat
  assumes source: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and supported: "{projection,quotation,predicate}\<subseteq>system_definitions P"
    and projection_meaning: "\<And>t. (projection,t)\<in>positive_meaning P \<longleftrightarrow>
      (10,t)\<in>positive_meaning artifact_projection_system"
    and quotation_meaning: "\<And>t. (quotation,t)\<in>positive_meaning P \<longleftrightarrow>
      (123,t)\<in>positive_meaning complete_data_admission_system"
begin

sublocale installed: positive_view P entry data_x "{(0,quoted_body_guard_schema projection quotation predicate)}"
  by (rule positive_view.intro[OF source fresh])
    (use supported in \<open>auto simp: single_valued_def\<close>)

abbreviation guarded where "guarded \<equiv> add_view_definition P entry data_x
  {(0,quoted_body_guard_schema projection quotation predicate)}"

lemma family:
  "((entry,c),S)\<in>system_clauses guarded \<longleftrightarrow>
    c=0 \<and> S=quoted_body_guard_schema projection quotation predicate"
  using installed.no_old_clause by auto

sublocale body: quoted_body_guard_profile guarded entry projection quotation predicate
proof (rule quoted_body_guard_profile.intro[OF installed.formed family])
  show "schema_call_formed guarded entry t \<longleftrightarrow> term_formed t" for t
    by (simp only: installed.view_call; simp)
  show "(projection,t)\<in>positive_meaning guarded \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system" for t
    using installed.old_meaning[of projection t] supported projection_meaning[of t] by blast
  show "(quotation,t)\<in>positive_meaning guarded \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system" for t
    using installed.old_meaning[of quotation t] supported quotation_meaning[of t] by blast
qed

theorem exact:
  "(entry,z)\<in>positive_meaning guarded \<longleftrightarrow>
    (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
      (predicate,t)\<in>positive_meaning P)"
  using body.exact[of z] installed.old_meaning[of predicate] supported by blast

theorem on_complete_body:
  assumes "complete_data_quoted_at R r t"
  shows "(entry,Target_Term (Whole_Artifact R))\<in>positive_meaning guarded \<longleftrightarrow>
    (predicate,t)\<in>positive_meaning P"
  using body.on_complete_body[OF assms] installed.old_meaning[of predicate t] supported by blast

end

end
