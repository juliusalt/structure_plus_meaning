theory Factor_Related_Test_Profiles
  imports Factor_Related_Test_Clauses Factor_Single_Clause_Packages
    Factor_Program_Entry_Presentations
begin

section \<open>The complete native profile leaves private coordinates free\<close>

definition native_related_test_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow> bool" where
  "native_related_test_at E u r k test \<longleftrightarrow>
    (\<exists>x y s t. x\<noteq>y \<and> s\<noteq>t \<and>
      native_single_clause_at E u r (related_test_clause x y s t k test))"

lemma native_related_test_included:
  assumes "native_related_test_at E u r k test" "environment_included E F" "environment_formed F"
  shows "native_related_test_at F u r k test"
proof -
  obtain x y s t where roles: "x\<noteq>y" "s\<noteq>t"
    and read: "native_single_clause_at E u r (related_test_clause x y s t k test)"
    using assms(1) by (auto simp: native_related_test_at_def)
  have copied: "native_single_clause_at F u r (related_test_clause x y s t k test)"
    by (rule native_single_clause_included[OF read assms(2,3)])
  show ?thesis unfolding native_related_test_at_def
    by (rule exI[of _ x], rule exI[of _ y], rule exI[of _ s], rule exI[of _ t])
      (use roles copied in blast)
qed

theorem native_related_test_meaning:
  assumes package: "native_package_at E pu pr P" and member: "d\<in>system_definitions P"
    and profile: "native_related_test_at E (fst d) (snd d) k test"
  shows "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "{k,test}\<subseteq>system_definitions P"
    "(d,z)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>q. (k,Pair_Term z q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
proof -
  obtain x y s t where roles: "x\<noteq>y" "s\<noteq>t"
    and read: "native_single_clause_at E (fst d) (snd d) (related_test_clause x y s t k test)"
    using profile by (auto simp: native_related_test_at_def)
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    by (rule native_single_clause_call[OF package member read])
  show "{k,test}\<subseteq>system_definitions P"
    using native_single_clause_dependencies[OF package member read] by simp
  have formed: "term_formed z \<and> term_formed q"
    if "(k,Pair_Term z q)\<in>positive_meaning P" for q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show "(d,z)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>q. (k,Pair_Term z q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
    by (simp only: native_single_clause_meaning[OF package member read] related_test_rule[OF roles])
      (use formed in blast)
qed

section \<open>A common environment retains the reference and the actual candidate\<close>

definition native_related_test_package ::
  "local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site \<Rightarrow> bool" where
  "native_related_test_package C k E pu pr d \<longleftrightarrow>
    environment_formed C \<and> (\<exists>P H test. native_package_at E pu pr P \<and>
      d\<in>system_definitions P \<and> environment_formed H \<and>
      environment_included C H \<and> environment_included E H \<and>
      native_related_test_at H (fst d) (snd d) k test)"

abbreviation related_test_package_domain ::
  "local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    program_entry_context \<Rightarrow> bool" where
  "related_test_package_domain C k z \<equiv> native_related_test_package C k (fst (fst z))
    (fst (snd (fst z))) (snd (snd (fst z))) (snd z)"

lemma related_test_package_boundary:
  assumes "related_test_package_domain C k z"
  shows "program_entry_context_formed z"
proof -
  obtain P where package: "native_package_at (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) P"
    and member: "snd z\<in>system_definitions P"
    using assms unfolding native_related_test_package_def by blast
  have formed: "environment_formed (fst (fst z))"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have root: "snd (fst z)\<in>environment_positions (fst (fst z))"
    using native_package_root_position[OF package] by simp
  have entry: "snd z\<in>environment_positions (fst (fst z))"
    by (rule native_package_entry_position[OF package member])
  show ?thesis using formed root entry by (simp add: program_entry_context_formed_def)
qed

theorem related_test_package_presentation_class:
  "presentation_class (\<lambda>z p. related_test_package_domain C k z \<and> program_entry_presents z p)
    (related_test_package_domain C k)
    (\<lambda>p. \<exists>z. related_test_package_domain C k z \<and> program_entry_presents z p)"
  by (rule presentation_class_subdomain[OF program_entry_presentation_class related_test_package_boundary])

lemma native_related_test_package_witnesses:
  assumes profile: "native_related_test_package C k E pu pr d" and package: "native_package_at E pu pr P"
  obtains H test where "d\<in>system_definitions P" "environment_formed H"
    "environment_included C H" "environment_included E H"
    "native_related_test_at H (fst d) (snd d) k test"
proof -
  obtain Q H test where parts: "native_package_at E pu pr Q" "d\<in>system_definitions Q"
    "environment_formed H" "environment_included C H" "environment_included E H"
    "native_related_test_at H (fst d) (snd d) k test"
    using profile unfolding native_related_test_package_def by blast
  have "Q=P" by (rule native_package_unique[OF parts(1) package])
  then show thesis using that parts(2-6) by blast
qed

theorem native_related_test_package_saturation:
  assumes reference: "native_package_at C cu cr R" and comparison_entry: "k\<in>system_definitions R"
    and comparison: "\<And>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow> presentation_transport A A p q"
    and package: "native_package_at E pu pr P" and profile: "native_related_test_package C k E pu pr d"
  shows "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation A (\<lambda>z. (test,z)\<in>positive_meaning P)"
proof -
  obtain H test where data: "d\<in>system_definitions P" "environment_formed H"
    "environment_included C H" "environment_included E H"
    "native_related_test_at H (fst d) (snd d) k test"
    using native_related_test_package_witnesses[OF profile package] by blast
  have original: "native_package_at H pu pr P" by (rule native_package_included[OF package data(4,2)])
  have fixed: "native_package_at H cu cr R" by (rule native_package_included[OF reference data(3,2)])
  have dependencies: "{k,test}\<subseteq>system_definitions P"
    by (rule native_related_test_meaning(2)[OF original data(1,5)])
  have local_entry: "k\<in>system_definitions P" using dependencies by blast
  have shared: "(k,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow> presentation_transport A A p q" for p q
    by (simp only: native_packages_shared_meaning[OF original fixed local_entry comparison_entry] comparison)
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    by (rule native_related_test_meaning(1)[OF original data(1,5)])
  have equation: "(\<lambda>z. (d,z)\<in>positive_meaning P)=saturate_observation A (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (intro ext; simp only: native_related_test_meaning(3)[OF original data(1,5)] shared saturate_observation_def)
  show "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation A (\<lambda>z. (test,z)\<in>positive_meaning P)"
    using dependencies equation by blast
qed

section \<open>Every compatible pair of actual callees supports a closed candidate\<close>

theorem native_related_test_package_total:
  assumes reference: "environment_formed C" "environment_included C E"
    and package: "native_package_at E pu pr P" and callees: "k\<in>system_definitions P" "test\<in>system_definitions P"
  shows "\<exists>F u Q d. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    d\<notin>system_definitions P \<and> system_definitions Q=insert d (system_definitions P) \<and>
    native_related_test_package C k F u [] d \<and>
    (\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P))"
proof -
  let ?S="related_test_clause (0::nat) 1 (0::nat) 1 k test"
  have formed: "schema_formed ?S" by simp
  have dependencies: "schema_dependencies ?S\<subseteq>system_definitions P" using callees by simp
  obtain H v u Q T where built: "environment_formed H" "environment_included E H"
    "(v,[])\<notin>system_definitions P" "native_package_at H u [] Q"
    "system_definitions Q=insert (v,[]) (system_definitions P)"
    "native_single_clause_at H v [] T" "schema_alpha_variant ?S T"
    "\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P)"
    using native_single_clause_package_total[OF package formed dependencies] by blast
  have roles: "native_related_test_at H v [] k test"
    using built(6) related_test_alpha_profile[OF built(7) zero_neq_one zero_neq_one]
    by (auto simp: native_related_test_at_def)
  let ?F="native_package_environment H u []"
  have closed: "closed_native_package_at ?F u [] Q" by (rule native_package_closed_restriction[OF built(4)])
  have candidate: "native_package_at ?F u [] Q" using closed by (simp add: closed_native_package_at_def)
  have included: "environment_included C H" by (rule environment_included_trans[OF reference(2) built(2)])
  have profile: "native_related_test_package C k ?F u [] (v,[])"
    unfolding native_related_test_package_def
    by (rule conjI[OF reference(1)], rule exI[of _ Q], rule exI[of _ H], rule exI[of _ test])
      (use candidate built(1,5) included roles native_package_environment_included[of H u "[]"] in auto)
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ "(v,[])"])
    (use closed native_package_closed_environment_fixed[OF closed] built(3,5,8) profile in blast)
qed

text \<open>
  This independent finite profile requires membership in the actual complete
  candidate package and the complete two-premise definition. A formed common
  environment retains both the candidate and the fixed reference. It may keep
  a reference root selector omitted by the candidate's closed restriction.

  The existing program-entry class supplies every complete source presentation.
  Restriction adds the actual profile. A proved comparison meaning then yields
  exactly the existing saturation, using the candidate's actual test callee.
  Every compatible package containing both callees has a constructed closed
  candidate. No existing policy or scope is replaced by this construction.
\<close>

end
