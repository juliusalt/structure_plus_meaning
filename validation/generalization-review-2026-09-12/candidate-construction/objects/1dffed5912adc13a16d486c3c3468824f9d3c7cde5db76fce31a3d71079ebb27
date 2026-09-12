theory Factor_Reader_Contracts
  imports Factor_Single_Clause_Reading
begin

section \<open>Complete native definition admission transfers the reader contracts\<close>

theorem admitted_reader_projection_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and source: "site_value_presents E (fst d) (snd d) p"
    and reference: "schema_reference_presents (reader_projection_clause x y s reader) v"
    and admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "x\<noteq>y"
  shows "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and "reader\<in>system_definitions P"
    and "(d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>q. (reader,Pair_Term t q)\<in>positive_meaning P)"
proof -
  let ?S="reader_projection_clause x y s reader"
  have read: "native_single_clause_at E (fst d) (snd d) ?S"
    using admitted by (simp only: single_clause_reading_at_reference[OF source reference])
  show "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    by (rule native_single_clause_call[OF package member read])
  show "reader\<in>system_definitions P"
    using native_single_clause_dependencies[OF package member read] by simp
  have formed: "term_formed t \<and> term_formed q"
    if "(reader,Pair_Term t q)\<in>positive_meaning P" for q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show "(d,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>q. (reader,Pair_Term t q)\<in>positive_meaning P)"
    by (simp only: native_single_clause_meaning[OF package member read] reader_projection_rule[OF variables])
      (use formed in blast)
qed

theorem admitted_fixed_result_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and source: "site_value_presents E (fst d) (snd d) p"
    and reference: "schema_reference_presents (fixed_result_clause x s reader result) v"
    and admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
  shows "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and "reader\<in>system_definitions P"
    and "(d,t)\<in>positive_meaning P \<longleftrightarrow> (reader,Pair_Term t result)\<in>positive_meaning P"
proof -
  let ?S="fixed_result_clause x s reader result"
  have read: "native_single_clause_at E (fst d) (snd d) ?S"
    using admitted by (simp only: single_clause_reading_at_reference[OF source reference])
  show "schema_call_formed P d t \<longleftrightarrow> term_formed t"
    by (rule native_single_clause_call[OF package member read])
  show "reader\<in>system_definitions P"
    using native_single_clause_dependencies[OF package member read] by simp
  have formed: "term_formed t \<and> term_formed result"
    if "(reader,Pair_Term t result)\<in>positive_meaning P"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show "(d,t)\<in>positive_meaning P \<longleftrightarrow> (reader,Pair_Term t result)\<in>positive_meaning P"
    by (simp only: native_single_clause_meaning[OF package member read] fixed_result_rule)
      (use formed in blast)
qed

theorem reader_projection_definition_total:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E"
    and callee: "\<exists>R. artifact_at E (fst reader) R \<and> anchor_formed (R,snd reader)"
  shows "\<exists>F u T p v. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and>
    schema_alpha_variant (reader_projection_clause (0::nat) 1 (0::nat) reader) T \<and>
    site_value_presents F u [] p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow>
      term_formed t \<and> (\<exists>q. term_formed q \<and> (reader,Pair_Term t q)\<in>X)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  let ?S="reader_projection_clause (0::nat) 1 (0::nat) reader"
  have formed: "schema_formed ?S" by simp
  have targets: "\<forall>d\<in>schema_dependencies ?S. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
    using callee by simp
  have rule: "schema_rule_instance ?S X t \<longleftrightarrow>
      term_formed t \<and> (\<exists>q. term_formed q \<and> (reader,Pair_Term t q)\<in>X)" for X t
    by (rule reader_projection_rule) simp
  show ?thesis using single_clause_reading_compilation[OF formed environment targets]
    by (simp only: rule)
qed

theorem fixed_result_definition_total:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E"
    and callee: "\<exists>R. artifact_at E (fst reader) R \<and> anchor_formed (R,snd reader)"
    and result: "term_formed result"
  shows "\<exists>F u T p v. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and>
    schema_alpha_variant (fixed_result_clause (0::nat) (0::nat) reader result) T \<and>
    site_value_presents F u [] p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow>
      term_formed t \<and> (reader,Pair_Term t result)\<in>X) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  let ?S="fixed_result_clause (0::nat) (0::nat) reader result"
  have formed: "schema_formed ?S" using result by simp
  have targets: "\<forall>d\<in>schema_dependencies ?S. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
    using callee by simp
  have rule: "schema_rule_instance ?S X t \<longleftrightarrow>
      term_formed t \<and> (reader,Pair_Term t result)\<in>X" for X t
    using result by (simp only: fixed_result_rule) blast
  show ?thesis using single_clause_reading_compilation[OF formed environment targets]
    by (simp only: rule)
qed

theorem compiled_single_clause_reading:
  assumes source: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and variant: "system_alpha_variant (rename_system g P) Q"
    and package: "native_package_at E pu pr Q" and member: "d\<in>system_definitions P"
    and interface: "system_interface P d=Pattern_Variable i" and family: "system_clause_family P d={(c,S)}"
  shows "\<exists>T p v. native_single_clause_at E (fst (g d)) (snd (g d)) T \<and>
    schema_alpha_variant (rename_schema id id g S) T \<and>
    site_value_presents E (fst (g d)) (snd (g d)) p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance (rename_schema id id g S) X t)"
proof -
  let ?R="rename_system g P"
  have rf: "schema_system_formed ?R" by (rule renamed_system_formed[OF source injective])
  have target: "g d\<in>system_definitions ?R"
    using member by (simp only: renamed_system_definitions) blast
  have actual: "(d,Pattern_Variable i)\<in>system_interfaces P"
    using system_interface_member[OF source member] interface by simp
  have moved: "(g d,Pattern_Variable i)\<in>system_interfaces ?R"
    by (simp only: renamed_system_interface_at[OF source injective member]) (rule actual)
  have ri: "system_interface ?R (g d)=Pattern_Variable i"
    by (rule system_interface_unique[OF rf moved])
  have rc: "system_clause_family ?R (g d)={(c,rename_schema id id g S)}"
    by (rule set_eqI; rename_tac z; case_tac z)
      (simp only: renamed_system_clause_at[OF source injective member] family; auto)
  obtain f h where fields: "system_interface Q (g d)=rename_pattern f (system_interface ?R (g d))"
    "schema_family_variant h (system_clause_family ?R (g d)) (system_clause_family Q (g d))"
    using variant target by (auto simp: system_alpha_variant_def; blast)
  have related: "schema_family_variant h {(c,rename_schema id id g S)} (system_clause_family Q (g d))"
    using fields(2) rc by simp
  obtain T where one: "system_clause_family Q (g d)={(h c,T)}"
    and equivalent: "schema_alpha_variant (rename_schema id id g S) T"
    using schema_family_variant_singleton[OF related] by blast
  have qi: "system_interface Q (g d)=Pattern_Variable (f i)" using fields(1) ri by simp
  have qf: "schema_system_formed Q" by (rule native_package_system_formed[OF package])
  have inside: "g d\<in>system_definitions Q"
    using variant target by (simp add: system_alpha_variant_def)
  obtain q D where read: "native_definition_at E (fst (g d)) (snd (g d)) q D"
    using native_package_definition_exists[OF package inside] by blast
  have head: "q=Pattern_Variable (f i)"
    using system_interface_member[OF qf inside] qi
    by (simp only: native_package_complete_at(1)[OF package inside read])
  have clauses: "D=system_clause_family Q (g d)"
    by (rule set_eqI; rename_tac z; case_tac z)
      (simp only: system_clause_member native_package_complete_at(2)[OF package inside read])
  have single: "native_single_clause_at E (fst (g d)) (snd (g d)) T"
    using read head clauses one by (auto simp: native_single_clause_at_def)
  obtain p v where presented: "site_value_presents E (fst (g d)) (snd (g d)) p"
    "schema_reference_presents T v"
    "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    using single_clause_reading_total[OF single] by blast
  show ?thesis by (rule exI[of _ T], rule exI[of _ p], rule exI[of _ v])
    (use single equivalent presented schema_alpha_rule_instance[OF equivalent] in blast)
qed

text \<open>
  The source presentation identifies the actual definition in its package.
  Admission checks its whole variable interface and singleton clause family
  against a complete reference report. The report transfers the generic
  rule equation to that actual definition and its actual reader dependency.

  Every formed environment with an anchored callee supports a compiled
  instance. Binder and socket coordinates may change under compilation;
  the callee and the rule equation are retained. Both constructions preserve
  every existing artifact and outgoing binding. Fixed-result construction
  requires a formed literal result; the admitted meaning equation also
  derives its formation from any successful call.

  These are sufficient native syntax contracts for the two ordinary rule
  profiles. The mathematical proofs of the contracts remain Isabelle
  proofs; the definitions below can themselves be read by the native reader.
\<close>

end
