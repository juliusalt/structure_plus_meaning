theory Factor_Schema_Code
  imports Factor_Syntax_Copy Factor_Reference_Forests
begin

section \<open>Construction facts for complete schema code blocks\<close>

definition schema_code ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> 'u native_schema \<Rightarrow>
    (local_address \<times> exact_artifact) set \<Rightarrow> (local_address \<times> 'u definition_site) set \<Rightarrow> bool" where
  "schema_code R r A L C \<longleftrightarrow> exact_formed R \<and>
    bag_count (object_data R) = (\<lambda>_. 0) \<and> r \<in> rra_carrier (object_structure R) \<and>
    reference_table_formed L C \<and> rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R) \<and>
    rel_ran C = schema_dependencies A \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u L C \<longrightarrow> native_schema_at E u r A)"

lemma schema_code_properties:
  assumes "schema_code R r A L C"
  shows "exact_formed R" "bag_count (object_data R) = (\<lambda>_. 0)"
    "r \<in> rra_carrier (object_structure R)" "reference_table_formed L C"
    "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    "rel_ran C = schema_dependencies A"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u L C \<longrightarrow> native_schema_at E u r A"
  using assms by (auto simp: schema_code_def)

theorem schema_code_total:
  fixes S :: "('a,'s,local_address option definition_site) factor_schema"
  assumes formed: "schema_formed S"
    and addresses: "\<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
  shows "\<exists>R r A L C. schema_alpha_variant S A \<and> schema_code R r A L C"
proof -
  obtain R :: exact_artifact and r :: local_address and f :: "'a \<Rightarrow> local_address"
    and h :: "'s \<Rightarrow> local_address" and L :: "(local_address \<times> exact_artifact) set"
    and C :: "(local_address \<times> local_address option definition_site) set" where built:
    "exact_formed R" "inj_on f (schema_variables S)" "inj_on h (schema_sockets S)"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      syntax_references E u L C \<longrightarrow> native_schema_at E u r (rename_schema f h id S)"
    "reference_table_formed L C" "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    "rel_ran C = schema_dependencies S" "bag_count (object_data R) = (\<lambda>_. 0)"
    "r \<in> rra_carrier (object_structure R)"
    using schema_compilation_total[OF formed addresses] by metis
  have alpha: "schema_alpha_variant S (rename_schema f h id S)"
    unfolding schema_alpha_variant_def
    by (rule exI[of _ f], rule exI[of _ h]) (use built(2,3) in simp)
  have code: "schema_code R r (rename_schema f h id S) L C"
    using built by (simp add: schema_code_def renamed_schema_dependencies)
  show ?thesis using alpha code by blast
qed

theorem schema_code_list_total:
  fixes Ss :: "('a,'s,local_address option definition_site) factor_schema list"
  assumes formed: "\<forall>S\<in>set Ss. schema_formed S"
    and addresses: "\<forall>S\<in>set Ss. \<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
  shows "\<exists>Rs rs As Ls Cs. length Rs = length Ss \<and> length rs = length Ss \<and>
    length As = length Ss \<and> length Ls = length Ss \<and> length Cs = length Ss \<and>
    (\<forall>i<length Ss. schema_alpha_variant (Ss!i) (As!i) \<and> schema_code (Rs!i) (rs!i) (As!i) (Ls!i) (Cs!i))"
  using formed addresses
proof (induction Ss)
  case Nil
  show ?case by (rule exI[of _ "[]"])+ simp
next
  case (Cons S Ss)
  have sf: "schema_formed S" and sa: "\<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
    and tf: "\<forall>T\<in>set Ss. schema_formed T"
    and ta: "\<forall>T\<in>set Ss. \<forall>d\<in>schema_dependencies T. octets_formed (snd d)"
    using Cons.prems by simp_all
  obtain R r A L C where head: "schema_alpha_variant S A" "schema_code R r A L C"
    using schema_code_total[OF sf sa] by metis
  obtain Rs :: "exact_artifact list" and rs :: "local_address list"
    and As :: "local_address option native_schema list"
    and Ls :: "(local_address \<times> exact_artifact) set list"
    and Cs :: "(local_address \<times> local_address option definition_site) set list" where tail:
    "length Rs = length Ss" "length rs = length Ss" "length As = length Ss"
    "length Ls = length Ss" "length Cs = length Ss"
    "\<forall>i<length Ss. schema_alpha_variant (Ss!i) (As!i) \<and> schema_code (Rs!i) (rs!i) (As!i) (Ls!i) (Cs!i)"
    using Cons.IH[OF tf ta] by metis
  have each: "\<forall>i<length (S#Ss). schema_alpha_variant ((S#Ss)!i) ((A#As)!i) \<and>
    schema_code ((R#Rs)!i) ((r#rs)!i) ((A#As)!i) ((L#Ls)!i) ((C#Cs)!i)"
  proof (intro allI impI)
    fix i assume index: "i < length (S#Ss)"
    show "schema_alpha_variant ((S#Ss)!i) ((A#As)!i) \<and>
      schema_code ((R#Rs)!i) ((r#rs)!i) ((A#As)!i) ((L#Ls)!i) ((C#Cs)!i)"
      using index head tail(6) by (cases i) auto
  qed
  show ?case by (rule exI[of _ "R#Rs"], rule exI[of _ "r#rs"], rule exI[of _ "A#As"],
      rule exI[of _ "L#Ls"], rule exI[of _ "C#Cs"])
    (use tail(1-5) each in auto)
qed

text \<open>
  The code predicate collects facts proved by the finite compiler: formation,
  source boundaries, complete references, and recovery by the existing native
  reader. It is a theorem interface for construction. Arbitrary finite source
  lists receive blocks with independent binder and socket assignments; each
  resulting projection is an injective renaming of its corresponding source.
\<close>

end
