theory Factor_Constrained_Contracts
  imports Factor_Single_Clause_Reading Factor_Constrained_Readings
begin

section \<open>The reading rule has independent native binder and socket coordinates\<close>

definition constrained_reading_clause ::
  "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow>
    ('a,'s,'d) factor_schema" where
  "constrained_reading_clause x y z s t reader constraint =
    data_rule (Pattern_Pair (Pattern_Variable x) (Pattern_Variable z))
      {(s,reader,Pattern_Pair (Pattern_Variable x) (Pattern_Pair (Pattern_Variable y) (Pattern_Variable z))),
       (t,constraint,Pattern_Variable z)}"

lemma constrained_reading_clause_formed [simp]:
  "schema_formed (constrained_reading_clause x y z s t reader constraint) \<longleftrightarrow> s\<noteq>t"
proof
  let ?S="constrained_reading_clause x y z s t reader constraint"
  assume formed: "schema_formed ?S"
  have functional: "single_valued (schema_premises ?S)"
    using formed by (simp add: schema_formed_def)
  show "s\<noteq>t"
  proof
    assume same: "s=t"
    have first: "(s,reader,Pattern_Pair (Pattern_Variable x)
        (Pattern_Pair (Pattern_Variable y) (Pattern_Variable z)))\<in>schema_premises ?S"
      by (simp add: constrained_reading_clause_def)
    have second: "(s,constraint,Pattern_Variable z)\<in>schema_premises ?S"
      using same by (simp add: constrained_reading_clause_def)
    have "(reader,Pattern_Pair (Pattern_Variable x)
        (Pattern_Pair (Pattern_Variable y) (Pattern_Variable z)))=(constraint,Pattern_Variable z)"
      by (rule single_valued_outputs[OF functional first second])
    then show False by simp
  qed
next
  assume "s\<noteq>t"
  then show "schema_formed (constrained_reading_clause x y z s t reader constraint)"
    by (auto simp: constrained_reading_clause_def schema_formed_def single_valued_def)
qed

lemma constrained_reading_clause_variables [simp]:
  "schema_variables (constrained_reading_clause x y z s t reader constraint)={x,y,z}"
  by (auto simp: constrained_reading_clause_def schema_variables_def)

lemma constrained_reading_clause_sockets [simp]:
  "schema_sockets (constrained_reading_clause x y z s t reader constraint)={s,t}"
  by (auto simp: constrained_reading_clause_def schema_sockets_def rel_dom_def)

lemma constrained_reading_clause_dependencies [simp]:
  "schema_dependencies (constrained_reading_clause x y z s t reader constraint)={reader,constraint}"
proof -
  have rows: "rel_ran (schema_premises (constrained_reading_clause x y z s t reader constraint)) =
      {(reader,Pattern_Pair (Pattern_Variable x) (Pattern_Pair (Pattern_Variable y) (Pattern_Variable z))),
       (constraint,Pattern_Variable z)}"
    by (auto simp: constrained_reading_clause_def rel_ran_def)
  show ?thesis by (simp add: schema_dependencies_def rows)
qed

lemma constrained_reading_schema_coordinates:
  "constrained_reading_schema reader constraint =
    constrained_reading_clause (0::nat) 1 2 (0::nat) 1 reader constraint"
  by (simp add: constrained_reading_schema_def constrained_reading_clause_def)

lemma rename_constrained_reading_clause [simp]:
  "rename_schema f h g (constrained_reading_clause x y z s t reader constraint) =
    constrained_reading_clause (f x) (f y) (f z) (h s) (h t) (g reader) (g constraint)"
  by (simp add: constrained_reading_clause_def rename_schema_def map_socket_graph_def)

lemma constrained_reading_clause_instance:
  assumes variables: "distinct [x,y,z]" and sockets: "s\<noteq>t"
    and terms: "term_formed a" "term_formed b" "term_formed c"
  shows "schema_instance (constrained_reading_clause x y z s t reader constraint)
    {(x,a),(y,b),(z,c)} (Pair_Term a c) {(s,reader,Pair_Term a (Pair_Term b c)),(t,constraint,c)}"
  using assms by (auto simp: schema_instance_def constrained_reading_clause_def schema_formed_def
    schema_variables_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)

theorem constrained_reading_clause_rule:
  assumes variables: "distinct [x,y,z]" and sockets: "s\<noteq>t"
  shows "schema_rule_instance (constrained_reading_clause x y z s t reader constraint) X w \<longleftrightarrow>
    (\<exists>a b c. w=Pair_Term a c \<and> term_formed a \<and> term_formed b \<and> term_formed c \<and>
      (reader,Pair_Term a (Pair_Term b c))\<in>X \<and> (constraint,c)\<in>X)"
proof
  let ?S="constrained_reading_clause x y z s t reader constraint"
  assume rule: "schema_rule_instance ?S X w"
  obtain V Q where inst: "schema_instance ?S V w Q"
    and support: "\<forall>p d q. (p,d,q)\<in>Q \<longrightarrow> (d,q)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  obtain h where assignment: "\<forall>a\<in>schema_variables ?S. (a,h a)\<in>V \<and> term_formed (h a)"
    and head: "w=evaluate_pattern h (schema_conclusion ?S)" and body: "Q=evaluate_schema_premises h ?S"
    using schema_instance_evaluation[OF inst] by blast
  show "\<exists>a b c. w=Pair_Term a c \<and> term_formed a \<and> term_formed b \<and> term_formed c \<and>
      (reader,Pair_Term a (Pair_Term b c))\<in>X \<and> (constraint,c)\<in>X"
    by (rule exI[of _ "h x"], rule exI[of _ "h y"], rule exI[of _ "h z"])
      (use assignment head body support in \<open>auto simp: constrained_reading_clause_def
        schema_variables_def evaluate_schema_premises_def\<close>)
next
  let ?S="constrained_reading_clause x y z s t reader constraint"
  assume "\<exists>a b c. w=Pair_Term a c \<and> term_formed a \<and> term_formed b \<and> term_formed c \<and>
      (reader,Pair_Term a (Pair_Term b c))\<in>X \<and> (constraint,c)\<in>X"
  then obtain a b c where parts: "w=Pair_Term a c" "term_formed a" "term_formed b" "term_formed c"
    "(reader,Pair_Term a (Pair_Term b c))\<in>X" "(constraint,c)\<in>X" by blast
  have inst: "schema_instance ?S {(x,a),(y,b),(z,c)} (Pair_Term a c)
      {(s,reader,Pair_Term a (Pair_Term b c)),(t,constraint,c)}"
    by (rule constrained_reading_clause_instance[OF variables sockets parts(2-4)])
  have material: "schema_material_satisfied ?S {(x,a),(y,b),(z,c)}"
    by (simp add: schema_material_satisfied_def constrained_reading_clause_def)
  show "schema_rule_instance ?S X w"
    using inst material parts by (auto simp: schema_rule_instance_def)
qed

section \<open>Native admission gives the complete composition contract\<close>

theorem admitted_constrained_reading_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and source: "site_value_presents E (fst d) (snd d) p"
    and reference: "schema_reference_presents (constrained_reading_clause x y z s t reader constraint) v"
    and admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "distinct [x,y,z]"
  shows "schema_call_formed P d w \<longleftrightarrow> term_formed w"
    and "{reader,constraint}\<subseteq>system_definitions P"
    and "(d,w)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>a b c. w=Pair_Term a c \<and>
        (reader,Pair_Term a (Pair_Term b c))\<in>positive_meaning P \<and>
        (constraint,c)\<in>positive_meaning P)"
proof -
  let ?S="constrained_reading_clause x y z s t reader constraint"
  have read: "native_single_clause_at E (fst d) (snd d) ?S"
    using admitted by (simp only: single_clause_reading_at_reference[OF source reference])
  have sockets: "s\<noteq>t"
    using reference by (simp add: schema_reference_presents_def schema_data_formed_def)
  show "schema_call_formed P d w \<longleftrightarrow> term_formed w"
    by (rule native_single_clause_call[OF package member read])
  show "{reader,constraint}\<subseteq>system_definitions P"
    using native_single_clause_dependencies[OF package member read] by simp
  have formed: "term_formed a \<and> term_formed b \<and> term_formed c"
    if "(reader,Pair_Term a (Pair_Term b c))\<in>positive_meaning P" for a b c
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show "(d,w)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>a b c. w=Pair_Term a c \<and>
        (reader,Pair_Term a (Pair_Term b c))\<in>positive_meaning P \<and>
        (constraint,c)\<in>positive_meaning P)"
    by (simp only: native_single_clause_meaning[OF package member read]
      constrained_reading_clause_rule[OF variables sockets]) (use formed in blast)
qed

corollary admitted_constrained_reading_at_pair:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and source: "site_value_presents E (fst d) (snd d) p"
    and reference: "schema_reference_presents (constrained_reading_clause x y z s t reader constraint) v"
    and admitted: "(127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system"
    and variables: "distinct [x,y,z]"
  shows "(d,Pair_Term a c)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>b. (reader,Pair_Term a (Pair_Term b c))\<in>positive_meaning P \<and>
      (constraint,c)\<in>positive_meaning P)"
  by (simp only: admitted_constrained_reading_meaning(3)[OF assms]) auto

theorem constrained_reading_definition_total:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E"
    and callees: "\<forall>d\<in>{reader,constraint}. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
  shows "\<exists>F u T p v. environment_formed F \<and> environment_included E F \<and> u\<notin>environment_uses E \<and>
    native_single_clause_at F u [] T \<and>
    schema_alpha_variant (constrained_reading_clause (0::nat) 1 2 (0::nat) 1 reader constraint) T \<and>
    site_value_presents F u [] p \<and> schema_reference_presents T v \<and>
    (127,Pair_Term p v)\<in>positive_meaning single_clause_reading_system \<and>
    (\<forall>X w. schema_rule_instance T X w \<longleftrightarrow>
      (\<exists>a b c. w=Pair_Term a c \<and> term_formed a \<and> term_formed b \<and> term_formed c \<and>
        (reader,Pair_Term a (Pair_Term b c))\<in>X \<and> (constraint,c)\<in>X)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R \<longleftrightarrow> artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  let ?S="constrained_reading_clause (0::nat) 1 2 (0::nat) 1 reader constraint"
  have formed: "schema_formed ?S" by simp
  have targets: "\<forall>d\<in>schema_dependencies ?S. \<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
    using callees by simp
  have rule: "schema_rule_instance ?S X w \<longleftrightarrow>
      (\<exists>a b c. w=Pair_Term a c \<and> term_formed a \<and> term_formed b \<and> term_formed c \<and>
        (reader,Pair_Term a (Pair_Term b c))\<in>X \<and> (constraint,c)\<in>X)" for X w
    by (rule constrained_reading_clause_rule) simp_all
  show ?thesis using single_clause_reading_compilation[OF formed environment targets]
    by (simp only: rule)
qed

text \<open>
  This is the earlier constrained-reading schema with explicit independent
  binder and socket parameters. The coordinate theorem identifies that
  concrete instance; it adds no second semantic operation. The three
  variable roles are distinct, as are the two premise occurrences. The
  actual reader and constraint callees may coincide.

  Admission uses the generic complete-definition reader and an exact
  reference report. It recovers the whole singleton clause family and the
  variable interface. In any formed package containing that definition, its
  actual callee dependencies are members of the package and its meaning is
  exactly the two linked calls on the same returned body. The equation
  concerns the independently fixed least positive meaning, including
  programs with cycles.

  Arbitrary supplied callee anchors also give an actual compiled definition
  and admitted reports. The construction preserves all existing artifacts
  and bindings, and its rule equation holds for every future supporting
  relation and term. A fixed report can be stored in the ordinary reference
  checker constructed by the preceding theory. Neither a program label nor
  sampled executions stand in for the syntax and dependency checks.

  These results check this sufficient rule profile. Exact native checking
  of further presentation constructions, their full mathematical contracts,
  and proof records remains a separate part of the presentation theory.
\<close>

end
