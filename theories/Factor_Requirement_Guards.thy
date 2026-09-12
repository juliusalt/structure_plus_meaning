theory Factor_Requirement_Guards
  imports Factor_Data_Term_Presentations
begin

section \<open>Every required predicate receives the same complete subject\<close>

definition requirement_guard_schema ::
  "(nat\<times>nat) set \<Rightarrow> (nat,nat,nat) factor_schema" where
  "requirement_guard_schema R=data_rule data_x ((\<lambda>(s,d). (s,d,data_x)) ` R)"

lemma requirement_guard_conclusion [simp]:
  "schema_conclusion (requirement_guard_schema R)=data_x"
  by (simp add: requirement_guard_schema_def)

lemma requirement_guard_ordinary [simp]:
  "schema_material_premises (requirement_guard_schema R)={}"
  by (simp add: requirement_guard_schema_def)

lemma requirement_guard_premise [simp]:
  "(s,d,p)\<in>schema_premises (requirement_guard_schema R) \<longleftrightarrow>
    (s,d)\<in>R \<and> p=data_x"
  by (auto simp: requirement_guard_schema_def)

lemma requirement_guard_variables [simp]:
  "schema_variables (requirement_guard_schema R)={0}"
  by (auto simp: requirement_guard_schema_def schema_variables_def)

lemma requirement_guard_dependencies [simp]:
  "schema_dependencies (requirement_guard_schema R)=rel_ran R"
  by (auto simp: requirement_guard_schema_def schema_dependencies_def rel_ran_def image_iff; force)

lemma requirement_guard_formed:
  assumes "finite R" "single_valued R"
  shows "schema_formed (requirement_guard_schema R)"
  using assms by (auto simp: requirement_guard_schema_def schema_formed_def single_valued_def)

locale requirement_guard_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry :: nat
    and requirements :: "(nat\<times>nat) set"
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=requirement_guard_schema requirements"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=h 0 \<and>
      (\<forall>(s,d)\<in>requirements. (d,h 0)\<in>positive_meaning P))"
proof -
  have support:
    "(\<forall>s d p. (s,d,p)\<in>schema_premises (requirement_guard_schema requirements) \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning P) \<longleftrightarrow>
      (\<forall>(s,d)\<in>requirements. (d,h 0)\<in>positive_meaning P)" for h
    by (auto simp: case_prod_unfold; force)
  have reduction:
    "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>h. (\<forall>a\<in>schema_variables (requirement_guard_schema requirements).
          term_formed (h a)) \<and>
        t=evaluate_pattern h (schema_conclusion (requirement_guard_schema requirements)) \<and>
        (\<forall>s d p. (s,d,p)\<in>schema_premises (requirement_guard_schema requirements) \<longrightarrow>
          (d,evaluate_pattern h p)\<in>positive_meaning P))"
    by (rule ordinary_single_clause_valuation[OF family]) (simp_all add: call)
  show ?thesis
    by (simp only: reduction support requirement_guard_variables requirement_guard_conclusion)
      simp
qed

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    term_formed t \<and> (\<forall>(s,d)\<in>requirements. (d,t)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "term_formed t \<and> (\<forall>(s,d)\<in>requirements. (d,t)\<in>positive_meaning P)"
    by (simp only: valuation) blast
next
  assume actual: "term_formed t \<and> (\<forall>(s,d)\<in>requirements. (d,t)\<in>positive_meaning P)"
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>_. t"]) (use actual in auto)
qed

corollary failed_requirement:
  assumes "(s,d)\<in>requirements" "(d,t)\<notin>positive_meaning P"
  shows "(entry,t)\<notin>positive_meaning P"
  using assms by (auto simp: exact)

theorem on_presented_subject:
  assumes subject: "R x t" and formed: "term_formed t"
    and meaning: "\<And>s d y u. (s,d)\<in>requirements \<Longrightarrow> R y u \<Longrightarrow>
      (d,u)\<in>positive_meaning P \<longleftrightarrow> condition d y"
  shows "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>(s,d)\<in>requirements. condition d x)"
  using meaning[OF _ subject] by (simp only: exact formed; blast)

end

text \<open>
  Requirement sockets remain separate occurrences even when they call the
  same predicate. Each premise receives the entire original subject. A check
  of another candidate or a supplied table of satisfaction flags cannot supply
  these premise calls. Empty requirements still retain term formation.

  The guard's clients must establish what each actual predicate means on the
  independently presented subject. The guard does not interpret descriptions,
  certify an arbitrary requirement list, or supply missing evidence.
\<close>

end
