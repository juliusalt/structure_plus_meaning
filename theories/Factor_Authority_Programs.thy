theory Factor_Authority_Programs
  imports Factor_Native_Authority Factor_Pattern_Programs
begin

section \<open>Ordinary pattern programs admitted over complete subject data\<close>

lemma adoption_recognizer_program:
  assumes pf: "pattern_formed p"
    and recognizes: "\<And>A G purpose t. adoption_value_presents A G purpose t \<Longrightarrow>
      (pattern_accepts p t\<longleftrightarrow>M A G purpose)"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    d\<in>system_definitions Q \<and> adoption_permission_invariant Q d \<and>
    (\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M A G purpose))"
proof -
  let ?P="recognizer_system a p"
  have formed: "schema_system_formed ?P" by (rule recognizer_system_formed[OF pf])
  have member: "()\<in>system_definitions ?P"
    by (simp add: system_definitions_def recognizer_system_def rel_dom_def)
  have observed: "\<And>A G purpose t. adoption_value_presents A G purpose t \<Longrightarrow>
      (((),t)\<in>positive_meaning ?P\<longleftrightarrow>M A G purpose)"
    using recognizer_positive_meaning[OF pf, where a=a] recognizes by blast
  have boundary: "\<And>A G purpose t. adoption_value_presents A G purpose t \<Longrightarrow>
      schema_call_formed ?P () t"
    using adoption_value_presents_formed recognizer_call_formed[OF pf, where a=a] by blast
  have invariant: "adoption_permission_invariant ?P ()"
    unfolding adoption_permission_invariant_def
  proof (intro allI impI)
    fix A G purpose t v assume first: "adoption_value_presents A G purpose t"
      and second: "adoption_value_presents A G purpose v"
    show "(schema_call_formed ?P () t\<longleftrightarrow>schema_call_formed ?P () v) \<and>
      (((),t)\<in>positive_meaning ?P\<longleftrightarrow>((),v)\<in>positive_meaning ?P)"
      using boundary[OF first] boundary[OF second] observed[OF first] observed[OF second] by blast
  qed
  obtain E :: "local_address option artifact_environment" and pu Q d where compiled:
    "closed_native_package_at E pu [] Q" "native_package_environment E pu []=E"
    "d\<in>system_definitions Q" "adoption_permission_invariant Q d"
    "\<forall>t. (schema_call_formed Q d t\<longleftrightarrow>schema_call_formed ?P () t) \<and>
      ((d,t)\<in>positive_meaning Q\<longleftrightarrow>((),t)\<in>positive_meaning ?P)"
    using native_adoption_program_compilation[OF formed member invariant] by blast
  have every: "\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M A G purpose)"
  proof (intro allI impI)
    fix A G purpose t assume present: "adoption_value_presents A G purpose t"
    show "schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>M A G purpose)"
      using compiled(5)[rule_format, of t] boundary[OF present] observed[OF present] by blast
  qed
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ d])
       (use compiled(1-4) every in blast)
qed

theorem constant_adoption_program:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    d\<in>system_definitions Q \<and> adoption_permission_invariant Q d \<and>
    (\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>b))"
proof -
  let ?p="if b then Pattern_Variable (0::nat) else Pattern_Payload []"
  have pf: "pattern_formed ?p" by (simp add: octets_formed_def)
  have recognizes: "\<And>A G purpose t. adoption_value_presents A G purpose t \<Longrightarrow>
      (pattern_accepts ?p t\<longleftrightarrow>b)"
  proof -
    fix A G purpose t assume present: "adoption_value_presents A G purpose t"
    have tf: "term_formed t" using adoption_value_presents_formed[OF present] by blast
    have pair: "\<exists>a v. t=Pair_Term a v" by (rule adoption_value_is_pair[OF present])
    show "pattern_accepts ?p t\<longleftrightarrow>b"
    proof (cases b)
      case True then show ?thesis using tf by simp
    next
      case False then show ?thesis using pair by (auto simp: pattern_accepts_def)
    qed
  qed
  show ?thesis by (rule adoption_recognizer_program[OF pf recognizes])
qed

corollary constant_native_adoption_application:
  assumes authority: "target_formed A" and core: "generation_formed G"
    and purpose: "target_formed p"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>pu au Q d t I K.
    environment_formed F \<and> native_package_at F pu [] Q \<and>
    native_application_at F au [] d t I K \<and> adoption_permission_invariant Q d \<and>
    adoption_value_presents A G p t \<and> native_application_formed F pu [] au [] \<and>
    (native_adoption_judgment_at F pu [] au [] A G p\<longleftrightarrow>b)"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d where policy:
    "closed_native_package_at E pu [] Q" "d\<in>system_definitions Q"
    "adoption_permission_invariant Q d"
    "\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q\<longleftrightarrow>b)"
    using constant_adoption_program[of b] by blast
  have package: "native_package_at E pu [] Q" using policy(1) by (simp add: closed_native_package_at_def)
  obtain t where present: "adoption_value_presents A G p t"
    using adoption_value_presents_total[OF authority core purpose] by blast
  have observed: "schema_call_formed Q d t" "(d,t)\<in>positive_meaning Q\<longleftrightarrow>b"
    using policy(4)[rule_format, OF present] by auto
  have permission: "factor_adopts Q d A G p\<longleftrightarrow>b"
    using factor_adoption_at_presentation[OF policy(3) present] observed(2) by blast
  obtain F au I K where future: "environment_formed F" "native_package_at F pu [] Q"
    "native_application_at F au [] d t I K"
    "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed Q d t"
    "native_adoption_judgment_at F pu [] au [] A G p\<longleftrightarrow>factor_adopts Q d A G p"
    using native_adoption_application_total[OF package policy(2,3) present] by blast
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ pu], rule exI[of _ au], rule exI[of _ Q],
        rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
       (use future policy(3) present observed(1) permission in blast)
qed

section \<open>A nonconstant policy can inspect an exact purpose coordinate\<close>

definition adoption_occurrence_pattern :: "local_address option \<Rightarrow> nat term_pattern" where
  "adoption_occurrence_pattern s=
    Pattern_Pair (Pattern_Variable 0)
      (Pattern_Pair (Pattern_Variable 1)
        (Pattern_Pair (Pattern_Variable 2) (exact_term_pattern (use_data_term s))))"

lemma adoption_occurrence_pattern_formed [simp]:
  "pattern_formed (adoption_occurrence_pattern s)"
  by (simp add: adoption_occurrence_pattern_def)

lemma adoption_occurrence_pattern_accepts:
  "pattern_accepts (adoption_occurrence_pattern s) t\<longleftrightarrow>
    (\<exists>a g p. term_formed a \<and> term_formed g \<and> term_formed p \<and>
      t=Pair_Term a (Pair_Term g (Pair_Term p (use_data_term s))))"
proof
  assume "pattern_accepts (adoption_occurrence_pattern s) t"
  then obtain V where inst: "pattern_instance V (adoption_occurrence_pattern s) t"
    and formed: "term_formed t" by (auto simp: pattern_accepts_def)
  show "\<exists>a g p. term_formed a \<and> term_formed g \<and> term_formed p \<and>
      t=Pair_Term a (Pair_Term g (Pair_Term p (use_data_term s)))"
    using inst formed by (auto simp: adoption_occurrence_pattern_def)
next
  assume "\<exists>a g p. term_formed a \<and> term_formed g \<and> term_formed p \<and>
      t=Pair_Term a (Pair_Term g (Pair_Term p (use_data_term s)))"
  then obtain a g p where fields: "term_formed a" "term_formed g" "term_formed p"
    and shape: "t=Pair_Term a (Pair_Term g (Pair_Term p (use_data_term s)))" by blast
  let ?V="{(0,a),(1,g),(2,p)}"
  have bindings: "term_bindings_formed (pattern_variables (adoption_occurrence_pattern s)) ?V"
    using fields by (auto simp: term_bindings_formed_def adoption_occurrence_pattern_def
      single_valued_def rel_dom_def)
  have inst: "pattern_instance ?V (adoption_occurrence_pattern s) t"
    using shape by (auto simp: adoption_occurrence_pattern_def)
  have tf: "term_formed t" using fields shape by simp
  show "pattern_accepts (adoption_occurrence_pattern s) t"
    using bindings inst tf unfolding pattern_accepts_def by blast
qed

lemma adoption_occurrence_observation:
  assumes present: "adoption_value_presents A G purpose t"
  shows "pattern_accepts (adoption_occurrence_pattern s) t\<longleftrightarrow>target_occurrence purpose=s"
proof -
  obtain a g p where fields: "target_value_presents A a" "generation_value_presents G g"
    "target_value_presents purpose p" "t=Pair_Term a (Pair_Term g p)"
    using present unfolding adoption_value_presents_def by blast
  obtain v where purpose: "artifact_value_presents (target_artifact purpose) v"
    "p=Pair_Term v (use_data_term (target_occurrence purpose))"
    using fields(3) unfolding target_value_presents_def by blast
  have af: "term_formed a" using target_value_presents_formed[OF fields(1)] by blast
  have gf: "term_formed g" using generation_value_presents_formed[OF fields(2)] by blast
  have vf: "term_formed v" using artifact_value_presents_formed[OF purpose(1)] by blast
  show ?thesis
    using fields(4) purpose(2) af gf vf
    by (auto simp: adoption_occurrence_pattern_accepts dest: injD[OF use_data_term_injective])
qed

theorem occurrence_adoption_program:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    d\<in>system_definitions Q \<and> adoption_permission_invariant Q d \<and>
    (\<forall>A G purpose t. adoption_value_presents A G purpose t \<longrightarrow>
      schema_call_formed Q d t \<and>
      ((d,t)\<in>positive_meaning Q\<longleftrightarrow>target_occurrence purpose=s))"
  by (rule adoption_recognizer_program[
    OF adoption_occurrence_pattern_formed adoption_occurrence_observation])

text \<open>
  The constant policies are two actual premise-free pattern programs: one has
  a variable conclusion, the other an empty-payload conclusion. Their broad
  interfaces form every complete adoption argument; their clauses respectively
  accept every such argument and refuse every such argument. The Boolean in
  the existence theorem chooses the source program to compile.

  The third program observes the exact optional occurrence coordinate in the
  purpose data. It leaves all complete artifact and generation presentations
  unconstrained, so collection order cannot alter formation or truth. The
  selected coordinate is an explicit policy parameter with no intrinsic
  authority. All three use only the existing pattern and positive-meaning rules.
\<close>

end
