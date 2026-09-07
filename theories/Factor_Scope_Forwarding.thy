theory Factor_Scope_Forwarding
  imports Factor_Package_Membership Factor_Pattern_Determination
    Factor_Definition_Environments Factor_Root_Environments
begin

section \<open>A fixed scope and one arbitrary future operand\<close>

definition scope_call_schema ::
  "'a \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    ('a,'s,'d) factor_schema" where
  "scope_call_schema b s k e u r=data_rule (Pattern_Variable b)
    {(s,k,package_subject_pattern (exact_term_pattern e) (exact_term_pattern u)
      (exact_term_pattern r) (Pattern_Variable b))}"

lemma scope_call_schema_formed [simp]:
  "schema_formed (scope_call_schema b s k e u r) \<longleftrightarrow>
    term_formed e \<and> term_formed u \<and> term_formed r"
  by (simp add: scope_call_schema_def schema_formed_def single_valued_def)

lemma scope_call_schema_variables [simp]:
  "schema_variables (scope_call_schema b s k e u r)={b}"
  by (simp add: scope_call_schema_def schema_variables_def)

lemma scope_call_schema_dependencies [simp]:
  "schema_dependencies (scope_call_schema b s k e u r)={k}"
  by (auto simp: scope_call_schema_def schema_dependencies_def rel_ran_def)

lemma scope_call_schema_instance:
  assumes fields: "term_formed e" "term_formed u" "term_formed r" "term_formed z"
  shows "schema_instance (scope_call_schema b s k e u r) {(b,z)} z
    {(s,k,package_subject_argument e u r z)}"
  using fields
  by (auto simp: schema_instance_def scope_call_schema_def schema_variables_def schema_formed_def
      term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)

lemma scope_call_schema_rule:
  "schema_rule_instance (scope_call_schema b s k e u r) X z \<longleftrightarrow>
    term_formed e \<and> term_formed u \<and> term_formed r \<and> term_formed z \<and>
    (k,package_subject_argument e u r z)\<in>X"
proof
  assume rule: "schema_rule_instance (scope_call_schema b s k e u r) X z"
  obtain V Q where inst: "schema_instance (scope_call_schema b s k e u r) V z Q"
    and support: "\<forall>s d t. (s,d,t)\<in>Q \<longrightarrow> (d,t)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  have fields: "term_formed e" "term_formed u" "term_formed r"
    and bindings: "term_bindings_formed {b} V" and bound: "(b,z)\<in>V"
    using inst by (auto simp: schema_instance_def scope_call_schema_def schema_formed_def schema_variables_def)
  have argument: "term_formed z" using bindings bound by (auto simp: term_bindings_formed_def)
  have premise: "(s,k,package_subject_argument e u r z)\<in>Q"
    using schema_instance_premise_iff[OF inst, of s k "package_subject_argument e u r z"]
    by (simp add: scope_call_schema_def fields bound)
  show "term_formed e \<and> term_formed u \<and> term_formed r \<and> term_formed z \<and>
    (k,package_subject_argument e u r z)\<in>X"
    using fields argument support premise by blast
next
  assume parts: "term_formed e \<and> term_formed u \<and> term_formed r \<and> term_formed z \<and>
    (k,package_subject_argument e u r z)\<in>X"
  have inst: "schema_instance (scope_call_schema b s k e u r) {(b,z)} z
      {(s,k,package_subject_argument e u r z)}"
    by (rule scope_call_schema_instance) (use parts in auto)
  have material: "schema_material_satisfied (scope_call_schema b s k e u r) {(b,z)}"
    by (simp add: schema_material_satisfied_def scope_call_schema_def)
  show "schema_rule_instance (scope_call_schema b s k e u r) X z"
    using inst material parts unfolding schema_rule_instance_def by blast
qed

lemma rename_exact_term_pattern [simp]:
  "rename_pattern f (exact_term_pattern t)=exact_term_pattern t"
  by (induction t) auto

lemma rename_scope_call_schema [simp]:
  "rename_schema f h g (scope_call_schema b s k e u r)=scope_call_schema (f b) (h s) (g k) e u r"
  by (simp add: scope_call_schema_def rename_schema_def map_socket_graph_def)

section \<open>The actual definition has exactly one forwarding clause\<close>

definition native_scope_forwarding_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "native_scope_forwarding_at E u r k e v a \<longleftrightarrow>
    (\<exists>i c b s. native_definition_at E u r (Pattern_Variable i)
      {(c,scope_call_schema b s k e v a)})"

lemma native_scope_forwarding_fields:
  assumes "native_scope_forwarding_at E u r k e v a"
  shows "term_formed e" "term_formed v" "term_formed a"
proof -
  obtain i c b s where raw: "native_definition_at E u r (Pattern_Variable i)
    {(c,scope_call_schema b s k e v a)}"
    using assms by (auto simp: native_scope_forwarding_at_def)
  have formed: "schema_formed (scope_call_schema b s k e v a)"
    using native_definition_formed[OF raw] by auto
  show "term_formed e" "term_formed v" "term_formed a" using formed by simp_all
qed

lemma native_scope_forwarding_included:
  assumes read: "native_scope_forwarding_at E u r k e v a"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_scope_forwarding_at F u r k e v a"
proof -
  obtain i c b s where raw: "native_definition_at E u r (Pattern_Variable i)
    {(c,scope_call_schema b s k e v a)}"
    using read by (auto simp: native_scope_forwarding_at_def)
  have copied: "native_definition_at F u r (Pattern_Variable i)
    {(c,scope_call_schema b s k e v a)}"
    by (rule native_definition_included[OF raw included formed])
  show ?thesis using copied by (auto simp: native_scope_forwarding_at_def)
qed

lemma native_scope_forwarding_callee_unique:
  assumes first: "native_scope_forwarding_at E u r k e v a"
    and second: "native_scope_forwarding_at E u r l f w b"
  shows "k=l"
proof -
  obtain i c x s where left: "native_definition_at E u r (Pattern_Variable i)
    {(c,scope_call_schema x s k e v a)}"
    using first by (auto simp: native_scope_forwarding_at_def)
  obtain j d y t where right: "native_definition_at E u r (Pattern_Variable j)
    {(d,scope_call_schema y t l f w b)}"
    using second by (auto simp: native_scope_forwarding_at_def)
  have same: "scope_call_schema x s k e v a=scope_call_schema y t l f w b"
    using native_definition_unique[OF left right] by auto
  have "{k}={l}"
    using arg_cong[OF same, where f=schema_dependencies] by simp
  then show ?thesis by simp
qed

lemma native_scope_forwarding_call:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_scope_forwarding_at E (fst d) (snd d) k e u r"
  shows "schema_call_formed P d z \<longleftrightarrow> term_formed z"
proof -
  obtain i c b s where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i)
      {(c,scope_call_schema b s k e u r)}"
    using read by (auto simp: native_scope_forwarding_at_def)
  show ?thesis
    by (simp only: schema_call_formed_def native_package_system_formed[OF package]
        native_package_complete_at(1)[OF package member raw]) auto
qed

lemma native_scope_forwarding_callee:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_scope_forwarding_at E (fst d) (snd d) k e u r"
  shows "k\<in>system_definitions P"
proof -
  obtain i c b s where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i)
      {(c,scope_call_schema b s k e u r)}"
    using read by (auto simp: native_scope_forwarding_at_def)
  have clause: "((d,c),scope_call_schema b s k e u r)\<in>system_clauses P"
    by (simp only: native_package_complete_at(2)[OF package member raw]) simp
  have dependencies: "schema_dependencies (scope_call_schema b s k e u r)\<subseteq>system_definitions P"
    using native_package_system_formed[OF package] clause
    unfolding schema_system_formed_def by blast
  show ?thesis using dependencies by simp
qed

theorem native_scope_forwarding_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and read: "native_scope_forwarding_at E (fst d) (snd d) k e u r"
  shows "(d,z)\<in>positive_meaning P \<longleftrightarrow>
    (k,package_subject_argument e u r z)\<in>positive_meaning P"
proof -
  obtain i c b s where raw: "native_definition_at E (fst d) (snd d) (Pattern_Variable i)
      {(c,scope_call_schema b s k e u r)}"
    using read by (auto simp: native_scope_forwarding_at_def)
  let ?S="scope_call_schema b s k e u r"
  have family: "((d,n),T)\<in>system_clauses P \<longleftrightarrow> n=c \<and> T=?S" for n T
    by (simp only: native_package_complete_at(2)[OF package member raw]) simp
  have equation: "(d,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h. term_formed (h b) \<and> z=h b \<and>
      (k,package_subject_argument e u r (h b))\<in>positive_meaning P)"
    by (subst ordinary_single_clause_valuation[OF family])
      (auto simp: scope_call_schema_def schema_variables_def
        native_scope_forwarding_call[OF package member read])
  have argument: "term_formed z"
    if "(k,package_subject_argument e u r z)\<in>positive_meaning P"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by auto
  show ?thesis
  proof
    assume "(d,z)\<in>positive_meaning P"
    then show "(k,package_subject_argument e u r z)\<in>positive_meaning P"
      using equation by blast
  next
    assume holds: "(k,package_subject_argument e u r z)\<in>positive_meaning P"
    have witness: "\<exists>h. term_formed (h b) \<and> z=h b \<and>
      (k,package_subject_argument e u r (h b))\<in>positive_meaning P"
      by (rule exI[of _ "\<lambda>_. z"]) (use holds argument[OF holds] in simp)
    show "(d,z)\<in>positive_meaning P" using equation witness by blast
  qed
qed

theorem native_scope_forwarding_shared_meaning:
  assumes package: "native_package_at E pu pr P" and reference: "native_package_at E qu qr Q"
    and member: "d\<in>system_definitions P" "k\<in>system_definitions Q"
    and read: "native_scope_forwarding_at E (fst d) (snd d) k e u r"
  shows "(d,z)\<in>positive_meaning P \<longleftrightarrow>
    (k,package_subject_argument e u r z)\<in>positive_meaning Q"
  by (simp only: native_scope_forwarding_meaning[OF package member(1) read]
      native_packages_shared_meaning[OF package reference
        native_scope_forwarding_callee[OF package member(1) read] member(2)])

section \<open>Every supplied scope has an actual forwarding definition\<close>

theorem native_scope_forwarding_total:
  fixes E :: "local_address option artifact_environment"
  assumes formed: "environment_formed E"
    and callee: "\<exists>R. artifact_at E (fst k) R \<and> anchor_formed (R,snd k)"
    and fields: "term_formed e" "term_formed v" "term_formed a"
  shows "\<exists>F u. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_scope_forwarding_at F u [] k e v a \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  let ?p="Pattern_Variable ()"
  let ?S="scope_call_schema () () k e v a"
  let ?C="{((),?S)}"
  have sf: "\<forall>S\<in>rel_ran ?C. schema_formed S"
    using fields by (auto simp: rel_ran_def)
  have targets: "\<forall>d\<in>(\<Union>S\<in>rel_ran ?C. schema_dependencies S).
    \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
    using callee by (auto simp: rel_ran_def)
  have pf: "pattern_formed ?p" and fin: "finite ?C" by simp_all
  have functional: "single_valued ?C" by (simp add: single_valued_def)
  obtain F u f h D where compiled:
    "environment_formed F" "environment_included E F" "u\<notin>environment_uses E"
    "native_definition_at F u [] (rename_pattern f ?p) D" "schema_family_variant h ?C D"
    "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R"
    "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x"
    using definition_environment_compilation[OF pf fin functional sf formed targets] by blast
  obtain T where entry: "(h (),T)\<in>D" "schema_alpha_variant ?S T"
    using schema_family_variant_entry[OF compiled(5), of "()" ?S] by auto
  obtain f' h' where variant: "T=rename_schema f' h' id ?S"
    using entry(2) by (auto simp: schema_alpha_variant_def)
  have singleton: "D={(h (),T)}"
  proof
    show "D\<subseteq>{(h (),T)}"
    proof
      fix q assume member: "q\<in>D"
      obtain c U where shape: "q=(c,U)" by (cases q)
      have row: "(c,U)\<in>D" using member shape by simp
      have range: "range h={h ()}"
      proof
        show "range h\<subseteq>{h ()}"
        proof
          fix x assume "x\<in>range h"
          then obtain v where x: "x=h v" by blast
          have unit: "v=()" by (cases v) simp
          show "x\<in>{h ()}" using x unit by simp
        qed
        show "{h ()}\<subseteq>range h" by auto
      qed
      have domain: "rel_dom D={h ()}"
        using compiled(5) by (simp add: schema_family_variant_def rel_dom_def range)
      have key: "c=h ()" using rel_domI[OF row] domain by simp
      have functional: "single_valued D" using compiled(5) by (simp add: schema_family_variant_def)
      have same_output: "U=T" using single_valued_outputs[OF functional row] entry(1) key by blast
      show "q\<in>{(h (),T)}" using shape key same_output by simp
    qed
    show "{(h (),T)}\<subseteq>D" using entry(1) by auto
  qed
  have read: "native_scope_forwarding_at F u [] k e v a"
    unfolding native_scope_forwarding_at_def
    by (rule exI[of _ "f ()"], rule exI[of _ "h ()"],
        rule exI[of _ "f' ()"], rule exI[of _ "h' ()"])
       (use compiled(4) singleton variant in simp)
  show ?thesis by (rule exI[of _ F], rule exI[of _ u])
    (use compiled(1-3,6,7) read in blast)
qed

text \<open>
  The scope clause is the existing literal specialization with explicit,
  independent binder and socket parameters. The profile has a variable interface,
  one prospective call, and no material premise. In any formed package containing
  the entry, every formed argument is accepted and its meaning is exactly the
  callee's meaning at that fixed scope. Other definitions may retain arbitrary
  ordinary or material clauses.

  If the callee also belongs to another package in the same environment, shared
  definition agreement supplies that package's exact meaning. The callee is an
  actual syntax dependency. No sampled execution, supplied truth predicate, or
  candidate-selected semantic rule establishes the equation.

  Compilation supplies an actual finite definition over an existing anchored
  callee while preserving every prior artifact and binding. Native binder,
  interface, clause, and socket coordinates are witnesses of that construction.
\<close>

end
