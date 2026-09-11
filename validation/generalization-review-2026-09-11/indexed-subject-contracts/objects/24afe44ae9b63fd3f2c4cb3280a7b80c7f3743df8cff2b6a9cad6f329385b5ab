theory Factor_Related_Test_Clauses
  imports Factor_Reader_Contracts Presentation_Completion
begin

section \<open>Two identified premises share one actual witness\<close>

definition related_test_clause ::
  "'a \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) factor_schema" where
  "related_test_clause x y s t compare test=data_rule (Pattern_Variable x)
    {(s,compare,Pattern_Pair (Pattern_Variable x) (Pattern_Variable y)),
     (t,test,Pattern_Variable y)}"

lemma related_test_clause_formed [simp]:
  "s\<noteq>t \<Longrightarrow> schema_formed (related_test_clause x y s t compare test)"
  by (auto simp: related_test_clause_def schema_formed_def single_valued_def)

lemma related_test_clause_variables [simp]:
  "schema_variables (related_test_clause x y s t compare test)={x,y}"
  by (auto simp: related_test_clause_def schema_variables_def)

lemma related_test_clause_dependencies [simp]:
  "schema_dependencies (related_test_clause x y s t compare test)={compare,test}"
  by (simp add: related_test_clause_def schema_dependencies_def rel_ran_image)

lemma related_test_clause_sockets [simp]:
  "schema_sockets (related_test_clause x y s t compare test)={s,t}"
  by (auto simp: related_test_clause_def schema_sockets_def rel_dom_def)

lemma related_test_clause_ordinary [simp]:
  "schema_material_premises (related_test_clause x y s t compare test)={}"
  by (simp add: related_test_clause_def)

lemma rename_related_test_clause [simp]:
  "rename_schema f h g (related_test_clause x y s t compare test)=
    related_test_clause (f x) (f y) (h s) (h t) (g compare) (g test)"
  by (auto simp: related_test_clause_def rename_schema_def map_socket_graph_def)

lemma related_test_clause_instance:
  assumes "x\<noteq>y" "s\<noteq>t" "term_formed p" "term_formed q"
  shows "schema_instance (related_test_clause x y s t compare test) {(x,p),(y,q)} p
    {(s,compare,Pair_Term p q),(t,test,q)}"
  using assms by (auto simp: schema_instance_def related_test_clause_def schema_formed_def
    schema_variables_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)

theorem related_test_rule:
  assumes variables: "x\<noteq>y" and sockets: "s\<noteq>t"
  shows "schema_rule_instance (related_test_clause x y s t compare test) X p \<longleftrightarrow>
    term_formed p \<and> (\<exists>q. term_formed q \<and> (compare,Pair_Term p q)\<in>X \<and> (test,q)\<in>X)"
proof
  let ?S="related_test_clause x y s t compare test"
  assume "schema_rule_instance ?S X p"
  then obtain V Q where inst: "schema_instance ?S V p Q"
    and support: "\<forall>s d t. (s,d,t)\<in>Q \<longrightarrow> (d,t)\<in>X"
    by (auto simp: schema_rule_instance_def)
  obtain h where assignment: "\<forall>a\<in>schema_variables ?S. (a,h a)\<in>V \<and> term_formed (h a)"
    and head: "p=evaluate_pattern h (schema_conclusion ?S)" and body: "Q=evaluate_schema_premises h ?S"
    using schema_instance_evaluation[OF inst] by blast
  have formed: "term_formed p" using schema_instance_formed[OF inst] by blast
  show "term_formed p \<and> (\<exists>q. term_formed q \<and> (compare,Pair_Term p q)\<in>X \<and> (test,q)\<in>X)"
    by (rule conjI[OF formed], rule exI[of _ "h y"])
      (use assignment head body support in
        \<open>auto simp: related_test_clause_def schema_variables_def evaluate_schema_premises_def\<close>)
next
  let ?S="related_test_clause x y s t compare test"
  assume "term_formed p \<and> (\<exists>q. term_formed q \<and> (compare,Pair_Term p q)\<in>X \<and> (test,q)\<in>X)"
  then obtain q where parts: "term_formed p" "term_formed q" "(compare,Pair_Term p q)\<in>X" "(test,q)\<in>X"
    by blast
  have inst: "schema_instance ?S {(x,p),(y,q)} p {(s,compare,Pair_Term p q),(t,test,q)}"
    by (rule related_test_clause_instance[OF variables sockets parts(1,2)])
  have material: "schema_material_satisfied ?S {(x,p),(y,q)}"
    by (simp add: schema_material_satisfied_def)
  show "schema_rule_instance ?S X p"
    unfolding schema_rule_instance_def
    by (rule exI[of _ "{(x,p),(y,q)}"], rule exI[of _ "{(s,compare,Pair_Term p q),(t,test,q)}"])
      (use inst material parts in auto)
qed

lemma related_test_alpha_profile:
  assumes "schema_alpha_variant (related_test_clause x y s t compare test) T" "x\<noteq>y" "s\<noteq>t"
  shows "\<exists>x' y' s' t'. x'\<noteq>y' \<and> s'\<noteq>t' \<and> T=related_test_clause x' y' s' t' compare test"
  using assms by (auto simp: schema_alpha_variant_def; blast dest: inj_onD)

section \<open>Fresh definitions retain their actual callee meanings\<close>

theorem related_test_view:
  assumes source: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and callees: "compare\<in>system_definitions P" "test\<in>system_definitions P" and sockets: "s\<noteq>t"
  shows "positive_view P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}"
  by (rule positive_view.intro[OF source fresh]) (use callees sockets in \<open>auto simp: single_valued_def\<close>)

theorem related_test_view_meaning:
  assumes view: "positive_view P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
  shows "(entry,p)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}) \<longleftrightarrow>
    (\<exists>q. (compare,Pair_Term p q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
proof -
  interpret view: positive_view P entry "Pattern_Variable i" "{(c,related_test_clause x y s t compare test)}"
    by (rule view)
  have formed: "term_formed p \<and> term_formed q"
    if "(compare,Pair_Term p q)\<in>positive_meaning P" for q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show ?thesis using formed
    by (auto simp: view.view_meaning related_test_rule[OF variables sockets])
qed

theorem related_test_view_saturation:
  assumes view: "positive_view P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
    and compare: "\<And>p q. (compare,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> presentation_transport R R p q"
  shows "(\<lambda>p. (entry,p)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}))=
    saturate_observation R (\<lambda>p. (test,p)\<in>positive_meaning P)"
  by (intro ext) (simp only: related_test_view_meaning[OF view variables sockets] compare saturate_observation_def)

theorem related_test_view_agreement_reduction:
  assumes class_contract: "presentation_class R D A"
    and view: "positive_view P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
    and compare: "\<And>p q. (compare,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> presentation_transport R R p q"
  shows "exact_obligation_reduction UNIV
    (\<lambda>_::unit. (\<lambda>p. (entry,p)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,related_test_clause x y s t compare test)}))=
      (\<lambda>p. A p \<and> (test,p)\<in>positive_meaning P))
    observation_condition (\<lambda>_. observation_obligations (presentation_transport R R)
      (\<lambda>p. (test,p)\<in>positive_meaning P))"
  by (simp only: related_test_view_saturation[OF view variables sockets compare]
      exact_obligation_reduction_def observation_obligations_exact
      presentation_class.saturation_fixed_iff[OF class_contract]; simp)

section \<open>Whole-definition admission transfers the rule to the supplied program\<close>

theorem admitted_related_test_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and source: "site_value_presents E (fst d) (snd d) p"
    and reference: "schema_reference_presents (related_test_clause x y s t compare test) v"
    and admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "x\<noteq>y" and sockets: "s\<noteq>t"
  shows "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "{compare,test}\<subseteq>system_definitions P"
    "(d,z)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>q. (compare,Pair_Term z q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
proof -
  have read: "native_single_clause_at E (fst d) (snd d) (related_test_clause x y s t compare test)"
    using admitted by (simp only: single_clause_reading_at_reference[OF source reference])
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    by (rule native_single_clause_call[OF package member read])
  show "{compare,test}\<subseteq>system_definitions P"
    using native_single_clause_dependencies[OF package member read] by simp
  have formed: "term_formed z \<and> term_formed q"
    if "(compare,Pair_Term z q)\<in>positive_meaning P" for q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show "(d,z)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>q. (compare,Pair_Term z q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
    by (simp only: native_single_clause_meaning[OF package member read] related_test_rule[OF variables sockets])
      (use formed in blast)
qed

theorem related_test_definition_total:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E"
    and callees: "\<forall>d\<in>{compare,test}. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  shows "\<exists>F u T p v. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and>
    schema_alpha_variant (related_test_clause (0::nat) 1 (0::nat) 1 compare test) T \<and>
    site_value_presents F u [] p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X z. schema_rule_instance T X z \<longleftrightarrow>
      term_formed z \<and> (\<exists>q. term_formed q \<and> (compare,Pair_Term z q)\<in>X \<and> (test,q)\<in>X)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  have formed: "schema_formed (related_test_clause (0::nat) 1 (0::nat) 1 compare test)" by simp
  have targets: "\<forall>d\<in>schema_dependencies (related_test_clause (0::nat) 1 (0::nat) 1 compare test).
      \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)" using callees by simp
  show ?thesis using single_clause_reading_compilation[OF formed environment targets]
    by (simp only: related_test_rule[OF zero_neq_one zero_neq_one])
qed

text \<open>
  The two premises have distinct occurrence keys and share the actual witness.
  Distinct variables allow that witness to differ from the submitted argument.
  When the first callee implements complete correspondence, the existing
  saturation construction gives the meaning of this ordinary clause.
  Agreement with the old test enters the same exact observation reduction.

  The native reader checks the entire definition, including its variable
  interface and complete singleton family. Its report transfers the universal
  rule equation to the actual package and actual dependencies. Every formed
  environment with both anchored callees supports a compiled and admitted
  definition. The comparison callee's contract remains independent evidence;
  inspecting this template does not establish an arbitrary callee's semantics.
\<close>

end
