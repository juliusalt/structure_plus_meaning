theory Development_Given_Extensions
  imports Development_Given_Installation
begin

text \<open>
  A program that extends the given's readers (DECISIONS.md "Every distinction a native program relies on comes from
  a native notion", "The native request at a package"): it agrees with the readers the given carries on all their
  definitions, and it is installed over their package by the mapped extension, every artifact and binding of the
  given's environment kept, the readers at their installed sites and its own definitions at fresh uses, each meaning
  at its placed site what it means in the program (\<open>given_readers_extension\<close>). The first problem's asked relation
  (\<open>Development_First_Problem_Asked\<close>) and the first request's program (\<open>Development_First_Request_Program\<close>) are
  its instances: the installation stated first for the guard alone (task 393) is stated here once (task 545).
\<close>

section \<open>General facts: closures and rooted programs under agreement, views over agreeing programs\<close>

text \<open>A program agreeing with another on its whole domain reaches, from any roots, no more than the other does.\<close>

lemma definition_closure_agreement:
  assumes formed: "schema_system_formed P" and agreement: "systems_agree_on P J (system_definitions P)"
  shows "system_definition_closure P R\<subseteq>system_definition_closure J R"
proof -
  have edges: "system_dependency_edges P\<subseteq>system_dependency_edges J"
  proof
    fix x assume "x\<in>system_dependency_edges P"
    then obtain d e c S where x: "x=(d,e)" and cl: "((d,c),S)\<in>system_clauses P"
      and dep: "e\<in>schema_dependencies S"
      by (auto simp only: system_dependency_edges_def mem_Collect_eq split: prod.splits)
    have "d\<in>system_definitions P" using formed cl unfolding schema_system_formed_def by blast
    then have "((d,c),S)\<in>system_clauses J" using cl agreement unfolding systems_agree_on_def by blast
    then show "x\<in>system_dependency_edges J" using dep unfolding x system_dependency_edges_def by auto
  qed
  have "id ` system_definition_closure P R\<subseteq>system_definition_closure J (id ` R)"
    by (rule definition_closure_map) (use edges in auto)
  then show ?thesis by simp
qed

text \<open>
  A program rooted at roots inside a larger root set of a program it agrees with on its whole domain stands inside the
  larger rooted program and agrees with it there.
\<close>

lemma rooted_system_agreement_inside:
  assumes formed: "schema_system_formed P" "schema_system_formed J"
    and agreement: "systems_agree_on P J (system_definitions P)"
    and roots: "A\<subseteq>system_definitions P" "A\<subseteq>R"
  shows "system_definitions (rooted_system P A)\<subseteq>system_definitions (rooted_system J R)"
    and "systems_agree_on (rooted_system P A) (rooted_system J R) (system_definitions (rooted_system P A))"
proof -
  have mono: "system_definition_closure J A\<subseteq>system_definition_closure J R"
    by (rule system_definition_closure_least[OF subset_trans[OF roots(2) system_definition_closure_roots]
      system_definition_closure_closed])
  have closure: "system_definition_closure P A\<subseteq>system_definition_closure J R"
    using definition_closure_agreement[OF formed(1) agreement, of A] mono by blast
  have inside_J: "system_definitions P\<subseteq>system_definitions J" by (rule whole_agreement_definitions[OF agreement])
  show inside: "system_definitions (rooted_system P A)\<subseteq>system_definitions (rooted_system J R)"
    using closure inside_J unfolding rooted_system_def by auto
  have right: "systems_agree_on J (rooted_system J R) (system_definitions (rooted_system P A))"
    by (rule systems_agree_on_subdomain[OF rooted_system_agreement inside])
  show "systems_agree_on (rooted_system P A) (rooted_system J R) (system_definitions (rooted_system P A))"
    by (rule systems_agree_on_transitive[OF rooted_agreement_transfer[OF agreement] right])
qed

text \<open>The same view added at a definition fresh in two programs keeps their agreement, and extends it to the view.\<close>

lemma view_extension_agreement:
  assumes agreement: "systems_agree_on P Q (U-{d})"
    and fresh: "d\<notin>system_definitions P" "d\<notin>system_definitions Q"
    and formed: "schema_system_formed P" "schema_system_formed Q"
  shows "systems_agree_on (add_view_definition P d p C) (add_view_definition Q d p C) U"
proof -
  have ownerP: "e\<in>system_definitions P" if "((e,c),S)\<in>system_clauses P" for e c S
    using formed(1) that unfolding schema_system_formed_def by blast
  have ownerQ: "e\<in>system_definitions Q" if "((e,c),S)\<in>system_clauses Q" for e c S
    using formed(2) that unfolding schema_system_formed_def by blast
  have ifaceP: "e\<in>system_definitions P" if "(e,q)\<in>system_interfaces P" for e q
    using that unfolding system_definitions_def rel_dom_def by blast
  have ifaceQ: "e\<in>system_definitions Q" if "(e,q)\<in>system_interfaces Q" for e q
    using that unfolding system_definitions_def rel_dom_def by blast
  show ?thesis unfolding systems_agree_on_def
  proof (intro conjI ballI allI)
    fix e q assume e: "e\<in>U"
    show "(e,q)\<in>system_interfaces (add_view_definition P d p C) \<longleftrightarrow>
        (e,q)\<in>system_interfaces (add_view_definition Q d p C)"
    proof (cases "e=d")
      case True then show ?thesis using fresh by (auto dest: ifaceP ifaceQ)
    next
      case False then show ?thesis using agreement e unfolding systems_agree_on_def by auto
    qed
  next
    fix e c S assume e: "e\<in>U"
    show "((e,c),S)\<in>system_clauses (add_view_definition P d p C) \<longleftrightarrow>
        ((e,c),S)\<in>system_clauses (add_view_definition Q d p C)"
    proof (cases "e=d")
      case True then show ?thesis using fresh by (auto dest: ownerP ownerQ)
    next
      case False then show ?thesis using agreement e unfolding systems_agree_on_def by auto
    qed
  qed
qed

section \<open>A program extending the given's readers, installed over their package\<close>

text \<open>
  The program is finite and formed, and agrees with the readers the given carries on all their definitions. The
  mapped extension's premises at the readers' own package (@{thm [source] given_readers_extensible}) then install
  it: the given's environment kept, the readers at their installed sites, its own definitions at uses fresh in the
  given's environment, the installed package an alpha variant of the program at its placement.
\<close>

locale given_readers_extension =
  fixes Q :: "(nat,nat,nat,nat) finite_schema_system"
  assumes target: "finite_system_formed Q"
    and agreement: "systems_agree_on given_rooted_readers_system (decode_finite_system Q)
      (system_definitions given_rooted_readers_system)"
begin

sublocale install: finite_mapped_native_extension given_environment finite_rooted_given_readers Q
    "snd given_readers_installed" "[]" given_readers_program given_readers_placement
  by (rule finite_mapped_native_extension.intro[OF given_readers_extensible(1,2) target
    agreement[folded finite_rooted_given_readers_exact] given_readers_extensible(3,4)])

lemma target_formed: "schema_system_formed (decode_finite_system Q)"
  using target by (simp only: finite_system_formed_correct)

definition installed_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "installed_placement=finite_program_coordinates given_environment (finite_system_definitions finite_rooted_given_readers)
    (finite_system_definitions Q) given_readers_placement"

definition installed :: "local_address option finite_artifact_environment\<times>local_address option" where
  "installed=the (finite_extend_mapped_native given_environment finite_rooted_given_readers Q given_readers_placement)"

lemma built:
  "finite_extend_mapped_native given_environment finite_rooted_given_readers Q given_readers_placement=Some installed"
  using install.total unfolding installed_def by auto

definition installed_environment :: "local_address option finite_artifact_environment" where
  "installed_environment=fst installed"

definition installed_use :: "local_address option" where
  "installed_use=snd installed"

lemma correct:
  "finite_environment_formed installed_environment \<and>
    environment_included (decode_finite_environment given_environment) (decode_finite_environment installed_environment) \<and>
    native_package_at (decode_finite_environment installed_environment) (snd given_readers_installed) [] given_readers_program \<and>
    inj_on installed_placement (system_definitions (decode_finite_system Q)) \<and>
    (\<forall>d\<in>system_definitions given_rooted_readers_system. installed_placement d=given_readers_placement d) \<and>
    (\<exists>T. native_package_at (decode_finite_environment installed_environment) installed_use [] T \<and>
      system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) T \<and>
      system_definitions T=installed_placement ` system_definitions (decode_finite_system Q) \<and>
      positive_meaning T=map_prod installed_placement id ` positive_meaning (decode_finite_system Q) \<and>
      (\<forall>d\<in>system_definitions (decode_finite_system Q). \<forall>t.
        schema_call_formed T (installed_placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t)) \<and>
    (\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
      artifact_at (decode_finite_environment installed_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
      binds_slot (decode_finite_environment installed_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v)"
proof -
  have built': "finite_extend_mapped_native given_environment finite_rooted_given_readers Q
      given_readers_placement=Some (fst installed,snd installed)"
    using built by simp
  show ?thesis
  using install.correct[OF built']
  unfolding installed_placement_def[symmetric] installed_environment_def[symmetric] installed_use_def[symmetric]
    finite_system_definitions_correct finite_rooted_given_readers_exact .
qed

definition installed_program :: "local_address option native_system" where
  "installed_program=(THE T. native_package_at (decode_finite_environment installed_environment) installed_use [] T)"

theorem installation:
  "finite_environment_formed installed_environment"
  "environment_included (decode_finite_environment given_environment) (decode_finite_environment installed_environment)"
  "native_package_at (decode_finite_environment installed_environment) (snd given_readers_installed) [] given_readers_program"
  "\<forall>d\<in>system_definitions given_rooted_readers_system. installed_placement d=given_readers_placement d"
  "inj_on installed_placement (system_definitions (decode_finite_system Q))"
  "native_package_at (decode_finite_environment installed_environment) installed_use [] installed_program"
  "system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) installed_program"
  "system_definitions installed_program=installed_placement ` system_definitions (decode_finite_system Q)"
  "positive_meaning installed_program=map_prod installed_placement id ` positive_meaning (decode_finite_system Q)"
  "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
    artifact_at (decode_finite_environment installed_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A"
  "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
    binds_slot (decode_finite_environment installed_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v"
proof -
  note c=correct
  have ex: "\<exists>T. native_package_at (decode_finite_environment installed_environment) installed_use [] T \<and>
      system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) T \<and>
      system_definitions T=installed_placement ` system_definitions (decode_finite_system Q) \<and>
      positive_meaning T=map_prod installed_placement id ` positive_meaning (decode_finite_system Q) \<and>
      (\<forall>d\<in>system_definitions (decode_finite_system Q). \<forall>t.
        schema_call_formed T (installed_placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]])
  have program: "native_package_at (decode_finite_environment installed_environment) installed_use [] installed_program \<and>
      system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) installed_program \<and>
      system_definitions installed_program=installed_placement ` system_definitions (decode_finite_system Q) \<and>
      positive_meaning installed_program=map_prod installed_placement id ` positive_meaning (decode_finite_system Q)"
    using ex
  proof (rule exE)
    fix T assume T0: "native_package_at (decode_finite_environment installed_environment) installed_use [] T \<and>
      system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) T \<and>
      system_definitions T=installed_placement ` system_definitions (decode_finite_system Q) \<and>
      positive_meaning T=map_prod installed_placement id ` positive_meaning (decode_finite_system Q) \<and>
      (\<forall>d\<in>system_definitions (decode_finite_system Q). \<forall>t.
        schema_call_formed T (installed_placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t)"
    have package: "native_package_at (decode_finite_environment installed_environment) installed_use [] T"
      by (rule conjunct1[OF T0])
    have same: "installed_program=T" unfolding installed_program_def
      by (rule the_equality[where P="\<lambda>T. native_package_at (decode_finite_environment installed_environment) installed_use [] T",
        OF package]) (rule native_package_unique[OF _ package])
    show ?thesis unfolding same
      by (intro conjI conjunct1[OF T0] conjunct1[OF conjunct2[OF T0]] conjunct1[OF conjunct2[OF conjunct2[OF T0]]]
        conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF T0]]]])
  qed
  show "finite_environment_formed installed_environment" by (rule conjunct1[OF c])
  show "environment_included (decode_finite_environment given_environment) (decode_finite_environment installed_environment)"
    by (rule conjunct1[OF conjunct2[OF c]])
  show "native_package_at (decode_finite_environment installed_environment) (snd given_readers_installed) [] given_readers_program"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF c]]])
  show "inj_on installed_placement (system_definitions (decode_finite_system Q))"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]])
  show "\<forall>d\<in>system_definitions given_rooted_readers_system. installed_placement d=given_readers_placement d"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]])
  show "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
      artifact_at (decode_finite_environment installed_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]]])
  show "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
      binds_slot (decode_finite_environment installed_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]]])
  show "native_package_at (decode_finite_environment installed_environment) installed_use [] installed_program"
    "system_alpha_variant (rename_system installed_placement (decode_finite_system Q)) installed_program"
    "system_definitions installed_program=installed_placement ` system_definitions (decode_finite_system Q)"
    "positive_meaning installed_program=map_prod installed_placement id ` positive_meaning (decode_finite_system Q)"
    by (rule conjunct1[OF program], rule conjunct1[OF conjunct2[OF program]],
      rule conjunct1[OF conjunct2[OF conjunct2[OF program]]], rule conjunct2[OF conjunct2[OF conjunct2[OF program]]])
qed

text \<open>The program's definitions stand at uses fresh in the given's environment, each at an artifact root.\<close>

lemmas fresh=install.coordinates(3,4)[folded installed_placement_def,
  unfolded finite_system_definitions_correct finite_rooted_given_readers_exact]

text \<open>Each definition means at its placed site what it means in the program.\<close>

lemma installed_meaning:
  assumes "d\<in>system_definitions (decode_finite_system Q)"
  shows "(installed_placement d,t)\<in>positive_meaning installed_program \<longleftrightarrow> (d,t)\<in>positive_meaning (decode_finite_system Q)"
  by (rule system_variant_renamed_meaning_at[OF target_formed installation(5,7) assms])

text \<open>The installed package's site and every placed definition are positions of the installed environment.\<close>

lemma installed_positions:
  "(installed_use,[])\<in>environment_positions (decode_finite_environment installed_environment)"
  "\<And>d. d\<in>system_definitions (decode_finite_system Q) \<Longrightarrow>
    installed_placement d\<in>environment_positions (decode_finite_environment installed_environment)"
proof -
  show "(installed_use,[])\<in>environment_positions (decode_finite_environment installed_environment)"
    by (rule native_package_site_position[OF installation(6)])
  have image: "installed_placement ` system_definitions (decode_finite_system Q)\<subseteq>
      environment_positions (decode_finite_environment installed_environment)"
    by (rule native_renamed_source_positions[OF installation(6,7)])
  show "\<And>d. d\<in>system_definitions (decode_finite_system Q) \<Longrightarrow>
      installed_placement d\<in>environment_positions (decode_finite_environment installed_environment)"
    using image by blast
qed

end

text \<open>
  Installing an extension over the given's readers is a choice made outside the native process, a residual as the
  given's installation is. The given is unchanged: the installed program stands in an environment that includes the
  given's, and two extensions installed so stand in two environments, neither in the other's.
\<close>

end
