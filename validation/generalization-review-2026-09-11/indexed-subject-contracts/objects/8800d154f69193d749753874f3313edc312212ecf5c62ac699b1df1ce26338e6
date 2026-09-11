theory Factor_Seeded_Closure
  imports Factor_Finite_Relations
begin

section \<open>Finite seeds preserve the independently formed application boundary\<close>

definition seed_family_formed ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> (('d \<times> 'k) \<times> factor_term) set \<Rightarrow> bool" where
  "seed_family_formed P T \<longleftrightarrow> finite T \<and> single_valued T \<and>
    (\<forall>d k t. ((d,k),t) \<in> T \<longrightarrow> schema_call_formed P d t)"

definition seed_calls :: "(('d \<times> 'k) \<times> factor_term) set \<Rightarrow> ('d \<times> factor_term) set" where
  "seed_calls T = {q. \<exists>k. ((fst q,k),snd q) \<in> T}"

lemma seed_call_member [simp]: "(d,t) \<in> seed_calls T \<longleftrightarrow> (\<exists>k. ((d,k),t) \<in> T)"
  by (simp add: seed_calls_def)

definition seeded_system ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> (('d \<times> 'k) \<times> factor_term) set \<Rightarrow>
    ('a,'s,'d,'c+'k) schema_system" where
  "seeded_system P T =
    \<lparr>system_interfaces = system_interfaces P,
     system_clauses =
       (\<lambda>((d,c),S). ((d,Inl c),S)) ` system_clauses P \<union>
       (\<lambda>((d,k),t). ((d,Inr k),recognizer_schema (exact_term_pattern t))) ` T\<rparr>"

lemma seeded_interfaces [simp]: "system_interfaces (seeded_system P T) = system_interfaces P"
  by (simp add: seeded_system_def)

lemma seeded_definitions [simp]: "system_definitions (seeded_system P T) = system_definitions P"
  by (simp add: system_definitions_def)

lemma seeded_old_clause [simp]:
  "((d,Inl c),S) \<in> system_clauses (seeded_system P T) \<longleftrightarrow> ((d,c),S) \<in> system_clauses P"
  by (auto simp: seeded_system_def case_prod_unfold image_iff; force)

lemma seeded_new_clause [simp]:
  "((d,Inr k),S) \<in> system_clauses (seeded_system P T) \<longleftrightarrow>
    (\<exists>t. ((d,k),t) \<in> T \<and> S=recognizer_schema (exact_term_pattern t))"
  by (auto simp: seeded_system_def case_prod_unfold image_iff; force)

lemma seeded_system_formed:
  assumes pf: "schema_system_formed P" and seeds: "seed_family_formed P T"
  shows "schema_system_formed (seeded_system P T)"
proof -
  have finite: "finite T" and functional: "single_valued T"
    and calls: "\<forall>d k t. ((d,k),t) \<in> T \<longrightarrow> schema_call_formed P d t"
    using seeds by (auto simp: seed_family_formed_def)
  have targets: "\<forall>d k t. ((d,k),t) \<in> T \<longrightarrow> d \<in> system_definitions P \<and> term_formed t"
  proof (intro allI impI)
    fix d k t assume member: "((d,k),t) \<in> T"
    have call: "schema_call_formed P d t" using calls member by blast
    show "d \<in> system_definitions P \<and> term_formed t"
      by (rule schema_call_formed_target[OF call])
  qed
  have old_finite: "finite (system_clauses P)" and old_functional: "single_valued (system_clauses P)"
    using pf by (auto simp: schema_system_formed_def)
  have clause_finite: "finite (system_clauses (seeded_system P T))"
    using old_finite finite by (simp add: seeded_system_def)
  have clause_functional: "single_valued (system_clauses (seeded_system P T))"
    using old_functional functional by (auto simp: seeded_system_def single_valued_def; metis)
  have clause_formed: "\<forall>d c S. ((d,c),S) \<in> system_clauses (seeded_system P T) \<longrightarrow>
    d \<in> system_definitions P \<and> schema_formed S \<and> schema_dependencies S \<subseteq> system_definitions P"
  proof (intro allI impI)
    fix d c S assume member: "((d,c),S) \<in> system_clauses (seeded_system P T)"
    show "d \<in> system_definitions P \<and> schema_formed S \<and>
      schema_dependencies S \<subseteq> system_definitions P"
    proof (cases c)
      case (Inl k)
      have old: "((d,k),S) \<in> system_clauses P" using member Inl by simp
      show ?thesis using pf old by (auto simp: schema_system_formed_def)
    next
      case (Inr k)
      obtain t where source: "((d,k),t) \<in> T" "S=recognizer_schema (exact_term_pattern t)"
        using member Inr by auto
      have typed: "d \<in> system_definitions P" "term_formed t" using targets source(1) by blast+
      show ?thesis using typed source(2)
        by (simp add: recognizer_schema_def schema_formed_def schema_dependencies_def single_valued_def)
    qed
  qed
  show ?thesis
    using pf clause_finite clause_functional clause_formed
    by (simp only: schema_system_formed_def seeded_interfaces seeded_definitions) blast
qed

lemma seeded_call_formed:
  assumes "schema_system_formed P" "seed_family_formed P T"
  shows "schema_call_formed (seeded_system P T) d t \<longleftrightarrow> schema_call_formed P d t"
  by (simp only: schema_call_formed_def seeded_system_formed[OF assms] assms(1) seeded_interfaces)

section \<open>The actual consequence operator is exactly the seeded operator\<close>

lemma seeded_old_instance:
  assumes "schema_system_formed P" "seed_family_formed P T"
  shows "admitted_schema_instance (seeded_system P T) d (Inl c) V t Q \<longleftrightarrow>
    admitted_schema_instance P d c V t Q"
  by (simp only: admitted_schema_instance_def seeded_call_formed[OF assms] seeded_old_clause)

lemma seeded_new_instance:
  assumes pf: "schema_system_formed P" and seeds: "seed_family_formed P T"
  shows "admitted_schema_instance (seeded_system P T) d (Inr k) V t Q \<longleftrightarrow>
    ((d,k),t) \<in> T \<and> V={} \<and> Q={}"
proof
  assume admitted: "admitted_schema_instance (seeded_system P T) d (Inr k) V t Q"
  show "((d,k),t) \<in> T \<and> V={} \<and> Q={}"
    using admitted
    by (auto simp: admitted_schema_instance_def exact_recognizer_instance)
next
  assume entry: "((d,k),t) \<in> T \<and> V={} \<and> Q={}"
  have old_call: "schema_call_formed P d t"
    using entry seeds by (auto simp: seed_family_formed_def)
  have call: "schema_call_formed (seeded_system P T) d t"
    using old_call by (simp only: seeded_call_formed[OF pf seeds])
  have formed: "term_formed t" using schema_call_formed_target[OF old_call] by blast
  have inst: "schema_instance (recognizer_schema (exact_term_pattern t)) V t Q"
    using entry formed by (simp only: exact_recognizer_instance)
  have clause: "((d,Inr k),recognizer_schema (exact_term_pattern t)) \<in>
    system_clauses (seeded_system P T)"
    using entry by auto
  have material: "schema_material_satisfied (recognizer_schema (exact_term_pattern t)) V"
    by (simp add: schema_material_satisfied_def recognizer_schema_def)
  show "admitted_schema_instance (seeded_system P T) d (Inr k) V t Q"
    using call clause inst material entry unfolding admitted_schema_instance_def by blast
qed

theorem seeded_system_consequences:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes pf: "schema_system_formed P" and seeds: "seed_family_formed P T"
  shows "schema_consequences (seeded_system P T) X = seed_calls T \<union> schema_consequences P X"
proof (rule set_eqI)
  fix q :: "'d \<times> factor_term"
  obtain d t where shape: "q=(d,t)" by (cases q)
  show "q \<in> schema_consequences (seeded_system P T) X \<longleftrightarrow>
    q \<in> seed_calls T \<union> schema_consequences P X"
  proof
    assume member: "q \<in> schema_consequences (seeded_system P T) X"
    obtain c V Q where inst: "admitted_schema_instance (seeded_system P T) d c V t Q"
      and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> X"
      using member shape by (auto simp: schema_consequences_def)
    show "q \<in> seed_calls T \<union> schema_consequences P X"
    proof (cases c)
      case (Inl k)
      have old: "admitted_schema_instance P d k V t Q"
        using inst Inl by (simp only: seeded_old_instance[OF pf seeds])
      have "(d,t) \<in> schema_consequences P X"
        using old support unfolding schema_consequences_def by blast
      then show ?thesis using shape by blast
    next
      case (Inr k)
      have seed: "((d,k),t) \<in> T"
        using inst Inr by (simp only: seeded_new_instance[OF pf seeds])
      show ?thesis using seed shape by auto
    qed
  next
    assume member: "q \<in> seed_calls T \<union> schema_consequences P X"
    show "q \<in> schema_consequences (seeded_system P T) X"
    proof (cases "q \<in> seed_calls T")
      case True
      obtain k where seed: "((d,k),t) \<in> T" using True shape by auto
      have inst: "admitted_schema_instance (seeded_system P T) d (Inr k) {} t {}"
        using seed by (simp add: seeded_new_instance[OF pf seeds])
      show ?thesis using inst shape by (auto simp: schema_consequences_def)
    next
      case False
      obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
        and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> X"
        using member False shape by (auto simp: schema_consequences_def)
      have copied: "admitted_schema_instance (seeded_system P T) d (Inl c) V t Q"
        using inst by (simp only: seeded_old_instance[OF pf seeds])
      show ?thesis using copied support shape unfolding schema_consequences_def by blast
    qed
  qed
qed

theorem seeded_system_meaning:
  assumes "schema_system_formed P" "seed_family_formed P T"
  shows "positive_meaning (seeded_system P T) =
    lfp (\<lambda>X. seed_calls T \<union> schema_consequences P X)"
  unfolding positive_meaning_def
  by (rule arg_cong[where f=lfp]) (rule ext; rule seeded_system_consequences[OF assms])

theorem seeded_system_unfold:
  assumes "schema_system_formed P" "seed_family_formed P T"
  shows "positive_meaning (seeded_system P T) =
    seed_calls T \<union> schema_consequences P (positive_meaning (seeded_system P T))"
  by (subst positive_meaning_unfold) (rule seeded_system_consequences[OF assms])

theorem seeded_system_least:
  assumes "schema_system_formed P" "seed_family_formed P T"
    "seed_calls T \<subseteq> X" "schema_consequences P X \<subseteq> X"
  shows "positive_meaning (seeded_system P T) \<subseteq> X"
  by (rule positive_meaning_least)
     (use assms(3,4) in \<open>simp only: seeded_system_consequences[OF assms(1,2)]; blast\<close>)

corollary already_true_seeds_preserve_meaning:
  assumes pf: "schema_system_formed P" and seeds: "seed_family_formed P T"
    and true_seeds: "seed_calls T \<subseteq> positive_meaning P"
  shows "positive_meaning (seeded_system P T) = positive_meaning P"
proof (rule equalityI)
  show "positive_meaning (seeded_system P T) \<subseteq> positive_meaning P"
    by (rule seeded_system_least[OF pf seeds true_seeds])
       (subst positive_meaning_unfold[symmetric]; rule subset_refl)
  show "positive_meaning P \<subseteq> positive_meaning (seeded_system P T)"
    by (rule positive_meaning_least)
       (use seeded_system_unfold[OF pf seeds] in blast)
qed

theorem seeded_closure_native_total:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes pf: "schema_system_formed P" and seeds: "seed_family_formed P T"
  shows "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E u Q.
    inj_on g (system_definitions P) \<and> closed_native_package_at E u [] Q \<and>
    native_package_environment E u [] = E \<and>
    system_alpha_variant (rename_system g (seeded_system P T)) Q \<and>
    positive_meaning Q = map_prod g id `
      lfp (\<lambda>X. seed_calls T \<union> schema_consequences P X)"
proof -
  have formed: "schema_system_formed (seeded_system P T)"
    by (rule seeded_system_formed[OF pf seeds])
  show ?thesis using program_compilation_total[OF formed]
    by (simp only: seeded_definitions seeded_system_meaning[OF pf seeds])
qed

text \<open>
  The seed family and old clause family have disjoint occurrence coordinates.
  Their sum injections are construction correspondences, erased by native
  compilation into ordinary clause occurrences. The application interface is
  exactly the old one. Every seed must already satisfy that formation boundary.

  The result is a new program whose independently defined meaning is the least
  set containing the supplied seeds and closed under the old positive rules.
  A seed is a clause of that new program; it asserts no fact about the truth of
  the old program. No step can test the absence of a result from this closure.
\<close>

end
