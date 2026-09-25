theory Factor_Parametric_Causes
  imports Factor_Placeholder_Packages Factor_System_Payloads
begin

section \<open>A family of certified causes certified once at a placeholder\<close>

text \<open>
  A family of judgments that differ in one literal is certified once, at a placeholder no reader reads as
  syntax: the empty artifact, whose carrier is empty, so that at a use holding it no syntax, binding source or
  occurrence stands. At the fill of every use holding it (@{const placeholder_fill}) each reading the certified
  cause makes is the placeholder's reading mapped by the placeholder's leaf map (@{text Factor_Placeholder_Packages}),
  and positive meaning follows that map at an observation-free program
  (@{thm [source] positive_meaning_mapped}), so the placeholder's certified call carries to every payload. The
  replay at the fill is not transported: it is supplied for the positive call by
  @{thm [source] native_positive_replay_total}.
\<close>

section \<open>A call at an observation-free rooting holds in the mapped program\<close>

text \<open>
  A call whose entry roots an observation-free program holds in the whole program mapped: the rooted program
  holds it, the leaf map carries it there, and the mapped rooted program is the rooting of the mapped program
  (@{thm [source] rooted_system_leaf_map}). The whole program may hold material premises outside the entry's
  closure.
\<close>

theorem positive_meaning_rooted_mapped:
  assumes holds: "(d,t)\<in>positive_meaning P"
    and preserve: "leaf_map_formed h" and free: "system_observation_free (rooted_system P {d})"
  shows "(d,map_term_leaves h t)\<in>positive_meaning (map_system_leaves h P)"
proof -
  have formed: "schema_system_formed P" by (rule positive_meaning_has_formed_system[OF holds])
  have member: "d\<in>system_definition_closure P {d}"
    by (rule subsetD[OF system_definition_closure_roots], simp)
  have rooted: "(d,t)\<in>positive_meaning (rooted_system P {d})"
    by (simp only: rooted_system_meaning[OF formed]) (rule conjI[OF member holds])
  have "(d,map_term_leaves h t)\<in>positive_meaning (map_system_leaves h (rooted_system P {d}))"
    by (rule positive_meaning_mapped[OF rooted preserve free])
  then have "(d,map_term_leaves h t)\<in>positive_meaning (rooted_system (map_system_leaves h P) {d})"
    by (simp only: rooted_system_leaf_map)
  then have "d\<in>system_definition_closure (map_system_leaves h P) {d} \<and>
      (d,map_term_leaves h t)\<in>positive_meaning (map_system_leaves h P)"
    by (simp only: rooted_system_meaning[OF map_system_leaves_formed[OF formed preserve]])
  then show ?thesis by (rule conjunct2)
qed

section \<open>The placeholder's facts\<close>

text \<open>
  The placeholder's judgment: the package at the program site of its least judgment environment J0 and the
  application of the entry d to the whole empty artifact there, J0 its own least environment, a closed native
  replay in an environment including J0, J0's package environment the policy K0's, the program rooted at the
  entry observation-free, and the bounded quotation C0 of J0 at its sites with boundary V0, the uses of J0
  holding the empty artifact. These are what the bounded judgment at the empty artifact establishes.
\<close>

locale placeholder_policy_certificate =
  fixes K0 J0 H0 :: "local_address option artifact_environment"
    and pu :: "local_address option" and pr :: local_address
    and au :: "local_address option" and ar :: local_address
    and d root0 :: "local_address option definition_site"
    and P0 Pk :: "local_address option native_system" and I A :: "local_address set"
    and C0 :: exact_artifact and cr :: local_address and V0 :: "local_address option set"
  assumes package: "native_package_at J0 pu pr P0"
    and application: "native_application_at J0 au ar d (Target_Term (Whole_Artifact empty_artifact)) I A"
    and least: "native_judgment_environment J0 pu pr au ar=J0"
    and included: "environment_included J0 H0"
    and replay: "native_replay_at H0 pu pr au ar root0 {}"
    and policy: "native_package_at K0 pu pr Pk"
    and aligned: "native_package_environment J0 pu pr=native_package_environment K0 pu pr"
    and free: "system_observation_free (rooted_system P0 {d})"
    and quoted: "bounded_scope_quoted_at C0 cr J0 pu pr au ar V0"
    and placeholders: "V0={u. artifact_at J0 u empty_artifact}"
begin

text \<open>The placeholder's call holds: its closed replay is sound, read at the replay's inclusion of J0.\<close>

lemma placeholder_holds: "(d,Target_Term (Whole_Artifact empty_artifact))\<in>positive_meaning P0"
  by (rule native_replay_closed_meaning[OF replay included package application])

lemma placeholder_term:
  "map_term_leaves (placeholder_leaf R) (Target_Term (Whole_Artifact empty_artifact))=Target_Term (Whole_Artifact R)"
  by (simp add: placeholder_artifact_def)

text \<open>At the fill of J0 by a formed payload each reading the cause makes is the placeholder's, mapped.\<close>

lemma fill_holds:
  assumes R_formed: "exact_formed R"
  shows "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning (map_system_leaves (placeholder_leaf R) P0)"
  using positive_meaning_rooted_mapped[OF placeholder_holds placeholder_leaf_formed[OF R_formed] free]
  by (simp only: placeholder_term)

lemma fill_package: "exact_formed R \<Longrightarrow>
    native_package_at (placeholder_fill J0 R) pu pr (map_system_leaves (placeholder_leaf R) P0)"
  by (rule native_package_placeholder_fill[OF _ package])

lemma fill_application: "exact_formed R \<Longrightarrow>
    native_application_at (placeholder_fill J0 R) au ar d (Target_Term (Whole_Artifact R)) I A"
  using native_application_placeholder_fill[OF _ application, of R] by (simp only: placeholder_term)

lemma fill_least: "exact_formed R \<Longrightarrow>
    native_judgment_environment (placeholder_fill J0 R) pu pr au ar=placeholder_fill J0 R"
  using native_judgment_environment_placeholder_fill[OF _ package application, of R] by (simp only: least)

lemma fill_policy: "exact_formed R \<Longrightarrow>
    native_package_environment (placeholder_fill J0 R) pu pr=native_package_environment (placeholder_fill K0 R) pu pr"
  by (simp only: native_package_environment_placeholder_fill[OF _ package]
      native_package_environment_placeholder_fill[OF _ policy] aligned)

lemma fill_positive:
  assumes R_formed: "exact_formed R"
  shows "native_positive_holds (placeholder_fill J0 R) pu pr au ar"
  by (simp only: native_positive_holds_with_reads[OF fill_package[OF R_formed] fill_application[OF R_formed]])
    (rule fill_holds[OF R_formed])

text \<open>
  The bounded scope of a generation whose cause is C0 and whose payload is R is the fill of J0 by R, whatever R
  is: the cause and the payload determine it (@{thm [source] generation_bounded_scope_unique}).
\<close>

lemma fill_scope:
  assumes gen: "generation_at E gu gr G" and cause: "generation_cause G=Whole_Artifact C0"
    and payload: "generation_payload G=Whole_Artifact R"
  shows "generation_bounded_scope_at E gu gr G (placeholder_fill J0 R) pu pr au ar"
proof -
  have held: "\<forall>u\<in>V0. artifact_at J0 u empty_artifact" by (simp add: placeholders)
  have "generation_bounded_scope_at E gu gr G (payload_fill J0 V0 R) pu pr au ar"
    by (rule generation_bounded_scope_from_core[OF gen cause quoted payload held])
  then show ?thesis by (simp only: placeholder_fill_def placeholders)
qed

section \<open>The parametric certified cause\<close>

text \<open>
  Every generation read with the cause C0 and a formed payload R has the bounded certified policy cause at the
  fill of the policy by R: the scope is the fill of J0, the package reads the placeholder's program mapped and
  the call reads the whole payload, the call holds there, a closed replay including the scope exists, and the
  scope's package environment is the filled policy's. No premise on R is taken beyond its formation: R may be
  an artifact J0 holds at another use, or the empty artifact itself.
\<close>

theorem parametric_certified_policy_cause:
  assumes gen: "generation_at E gu gr G" and cause: "generation_cause G=Whole_Artifact C0"
    and payload: "generation_payload G=Whole_Artifact R" and R_formed: "exact_formed R"
  shows "\<exists>H root. bounded_certified_policy_cause_at (placeholder_fill K0 R) pu pr d E gu gr G H root R"
proof -
  let ?F="placeholder_fill J0 R"
  have scope: "generation_bounded_scope_at E gu gr G ?F pu pr au ar" by (rule fill_scope[OF gen cause payload])
  have pkg: "native_package_at ?F pu pr (map_system_leaves (placeholder_leaf R) P0)" by (rule fill_package[OF R_formed])
  have app: "native_application_at ?F au ar d (Target_Term (Whole_Artifact R)) I A"
    by (rule fill_application[OF R_formed])
  have canonical: "?F=native_judgment_environment ?F pu pr au ar" by (simp only: fill_least[OF R_formed])
  obtain H root where replay_F: "native_replay_at H pu pr au ar root {}"
    and inc: "environment_included (native_judgment_environment ?F pu pr au ar) H"
    by (insert native_positive_replay_total[OF fill_positive[OF R_formed]], elim conjE exE) (rule that; assumption)
  have included_F: "environment_included ?F H" using inc by (simp only: fill_least[OF R_formed])
  have base: "scope_certified_base_cause_at generation_bounded_scope_at E gu gr G H root R"
    unfolding scope_certified_base_cause_at_def
    by (intro exI conjI) (rule scope, rule canonical, rule payload, rule pkg, rule app, rule included_F, rule replay_F)
  have policy_F: "native_package_at (placeholder_fill K0 R) pu pr (map_system_leaves (placeholder_leaf R) Pk)"
    by (rule native_package_placeholder_fill[OF R_formed policy])
  have "bounded_certified_policy_cause_at (placeholder_fill K0 R) pu pr d E gu gr G H root R"
    unfolding bounded_certified_policy_cause_at_def scope_certified_policy_cause_at_def
  proof (intro conjI)
    show "\<exists>P. native_package_at (placeholder_fill K0 R) pu pr P" by (rule exI, rule policy_F)
    show "scope_certified_base_cause_at generation_bounded_scope_at E gu gr G H root R" by (rule base)
    show "\<exists>F au ar I A. generation_bounded_scope_at E gu gr G F pu pr au ar \<and>
        native_package_environment F pu pr=native_package_environment (placeholder_fill K0 R) pu pr \<and>
        native_application_at F au ar d (Target_Term (Whole_Artifact R)) I A"
      by (intro exI conjI) (rule scope, rule fill_policy[OF R_formed], rule app)
  qed
  then show ?thesis by (intro exI)
qed

end

end
