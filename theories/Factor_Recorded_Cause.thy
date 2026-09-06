theory Factor_Recorded_Cause
  imports Factor_Cause Factor_Generation_Scopes
begin

section \<open>Recorded construction validity fixes the minimal scope\<close>

definition recorded_construction_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "recorded_construction_cause_at E gu gr G xs B W R \<longleftrightarrow>
    (\<exists>F pu pr au ar. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      F=native_judgment_environment F pu pr au ar \<and>
      generation_payload G=Whole_Artifact R \<and> construction_judgment_at F pu pr au ar xs B W R)"

theorem recorded_construction_cause_with_scope:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
  shows "recorded_construction_cause_at E gu gr G xs B W R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and>
    generation_payload G=Whole_Artifact R \<and> construction_judgment_at F pu pr au ar xs B W R"
proof
  assume valid: "recorded_construction_cause_at E gu gr G xs B W R"
  obtain F' qu qr bu br where other: "generation_judgment_scope_at E gu gr G F' qu qr bu br"
    "F'=native_judgment_environment F' qu qr bu br" "generation_payload G=Whole_Artifact R"
    "construction_judgment_at F' qu qr bu br xs B W R"
    using valid unfolding recorded_construction_cause_at_def by blast
  have same: "F'=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
    by (rule generation_judgment_scope_unique[OF other(1) scope refl])
  show "F=native_judgment_environment F pu pr au ar \<and>
    generation_payload G=Whole_Artifact R \<and> construction_judgment_at F pu pr au ar xs B W R"
    using other(2-4) same by simp
next
  assume "F=native_judgment_environment F pu pr au ar \<and>
    generation_payload G=Whole_Artifact R \<and> construction_judgment_at F pu pr au ar xs B W R"
  then show "recorded_construction_cause_at E gu gr G xs B W R"
    using scope unfolding recorded_construction_cause_at_def by blast
qed

theorem recorded_construction_account_unique:
  assumes first: "recorded_construction_cause_at E gu gr G xs B W R"
    and second: "recorded_construction_cause_at E' hu hr H ys C X S"
    and cause: "generation_cause G=generation_cause H"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S"
proof -
  obtain F pu pr au ar where left: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    "construction_judgment_at F pu pr au ar xs B W R"
    using first unfolding recorded_construction_cause_at_def by blast
  obtain F' qu qr bu br where right: "generation_judgment_scope_at E' hu hr H F' qu qr bu br"
    "construction_judgment_at F' qu qr bu br ys C X S"
    using second unfolding recorded_construction_cause_at_def by blast
  have same: "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    by (rule generation_judgment_scope_unique[OF left(1) right(1) cause])
  have other: "construction_judgment_at F pu pr au ar ys C X S" using right(2) same by simp
  show ?thesis by (rule construction_judgment_account_unique[OF left(2) other])
qed

theorem different_recorded_accounts_have_different_causes:
  assumes first: "recorded_construction_cause_at E gu gr G xs B W R"
    and second: "recorded_construction_cause_at E' hu hr H ys C X S"
    and different: "xs\<noteq>ys \<or> B\<noteq>C \<or> W\<noteq>X \<or> R\<noteq>S"
  shows "generation_cause G\<noteq>generation_cause H"
  using recorded_construction_account_unique[OF first second] different by blast

theorem recorded_construction_outer_transfer:
  assumes valid: "recorded_construction_cause_at E gu gr G xs B W R"
    and target: "generation_at E' hu hr G"
  shows "recorded_construction_cause_at E' hu hr G xs B W R"
proof -
  obtain F pu pr au ar where parts: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    "F=native_judgment_environment F pu pr au ar" "generation_payload G=Whole_Artifact R"
    "construction_judgment_at F pu pr au ar xs B W R"
    using valid unfolding recorded_construction_cause_at_def by blast
  have scope: "generation_judgment_scope_at E' hu hr G F pu pr au ar"
    by (rule generation_judgment_scope_outer_transfer[OF parts(1) target])
  show ?thesis using scope parts(2-4) unfolding recorded_construction_cause_at_def by blast
qed

theorem recorded_construction_accounts_for_payload:
  assumes valid: "recorded_construction_cause_at E gu gr G xs B W R"
  shows "source_constructs xs B W R" "construction_coordinates_formed B W"
    "generation_payload G=Whole_Artifact R"
    "K2 (construction_assembly xs B W) \<and> R=assembly_output (construction_assembly xs B W)"
proof -
  have parts: "source_constructs xs B W R" "construction_coordinates_formed B W"
    "generation_payload G=Whole_Artifact R"
    using valid by (auto simp: recorded_construction_cause_at_def construction_judgment_at_def factor_constructs_def)
  show "source_constructs xs B W R" "construction_coordinates_formed B W"
    "generation_payload G=Whole_Artifact R" using parts by blast+
  show "K2 (construction_assembly xs B W) \<and> R=assembly_output (construction_assembly xs B W)"
    using parts(1) by (simp add: source_constructs_iff_K2)
qed

theorem recorded_construction_scope_closed:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and valid: "recorded_construction_cause_at E gu gr G xs B W R"
  shows "environment_closed F {pu,au} (native_judgment_demands F pu pr au ar)"
proof -
  have canonical: "F=native_judgment_environment F pu pr au ar"
    and judged: "construction_judgment_at F pu pr au ar xs B W R"
    using recorded_construction_cause_with_scope[OF scope] valid by blast+
  obtain P d t I K where package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d t I K"
    using judged unfolding construction_judgment_at_def by blast
  show ?thesis using native_judgment_environment_closed[OF package app]
    by (simp only: canonical[symmetric])
qed

section \<open>Every existing construction judgment has a complete recordable scope\<close>

theorem construction_judgment_recordable:
  fixes E :: "local_address option artifact_environment"
  assumes judged: "construction_judgment_at E pu pr au ar xs B W R"
  shows "\<exists>F C. judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    construction_judgment_at F pu pr au ar xs B W R \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  obtain P d t I K where package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and claim: "construction_claim_presents xs B W R t" "factor_constructs P d xs B W R"
    using judged unfolding construction_judgment_at_def by blast
  obtain F C where quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and kept: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_judgment_recordable[OF package app] by blast
  have valid: "construction_judgment_at F pu pr au ar xs B W R"
    using construction_judgment_with_reads[OF kept(1,2)] claim by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ C]) (use quote canonical valid program in blast)
qed

text \<open>
  The bare scoped application join in Factor_Cause is insufficient to fix cause
  identity across outer environments. This recorded profile cites a complete
  self-contained value of the program-and-call scope. That scope must equal its
  grammar-derived least restriction. No evidence boundary is folded into it.

  Equal recorded cause targets determine equal scopes and complete construction
  accounts, even under different outer environments. Every presentation of the
  same generation core recovers the same cause validity. Different accounts
  therefore require different recorded cause targets. Every native construction
  judgment has such a recordable scope with unchanged program environment.
  Its generation presentation and proof certificate are constructed by
  separate joins.
\<close>

end
