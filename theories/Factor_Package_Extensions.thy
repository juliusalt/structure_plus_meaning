theory Factor_Package_Extensions
  imports Factor_Root_Environments
begin

section \<open>Complete definition readings determine their outgoing edges\<close>

lemma native_definition_edges_at:
  assumes read: "native_definition_at E (fst d) (snd d) p C"
  shows "(d,e)\<in>native_definition_edges E \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>C \<and> e\<in>schema_dependencies S)"
proof -
  have unique: "q=p \<and> B=C" if "native_definition_at E (fst d) (snd d) q B" for q B
    by (rule native_definition_unique[OF that read])
  show ?thesis unfolding native_definition_edges_def using read unique by blast
qed

lemma native_package_edge_closed:
  assumes package: "native_package_at E u r P" and member: "d\<in>system_definitions P"
    and edge: "(d,e)\<in>native_definition_edges E"
  shows "e\<in>system_definitions P"
proof -
  have domain: "system_definitions P=native_definition_sites E (native_package_roots E u r)"
    using native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  have reached: "d\<in>native_definition_sites E (native_package_roots E u r)"
    using member domain by simp
  show ?thesis using native_definition_step[OF reached edge] domain by simp
qed

section \<open>A complete closed finite family receives an exact root selector\<close>

theorem native_definition_family_selection:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E"
    and readings: "\<And>d. d\<in>D \<Longrightarrow> \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    and closed: "\<And>d e. d\<in>D \<Longrightarrow> (d,e)\<in>native_definition_edges E \<Longrightarrow> e\<in>D"
  shows "\<exists>F u Q. environment_formed F \<and> environment_included E F \<and>
    native_package_at F u [] Q \<and> system_definitions Q=D \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
proof -
  have sites: "native_definition_sites E D=D"
    by (rule subset_antisym[OF native_definition_sites_least[OF subset_refl closed]
      native_definition_roots])
  have dependency: "native_package_formed E D"
    unfolding native_package_formed_def sites using environment readings by blast
  have targets: "\<forall>d\<in>D. \<exists>A. artifact_at E (fst d) A \<and> anchor_formed (A,snd d)"
  proof (intro ballI)
    fix d assume member: "d\<in>D"
    obtain p C where read: "native_definition_at E (fst d) (snd d) p C"
      using readings[OF member] by blast
    show "\<exists>A. artifact_at E (fst d) A \<and> anchor_formed (A,snd d)"
      by (rule native_definition_has_anchor[OF read])
  qed
  obtain F u L where selected: "environment_formed F" "environment_included E F"
    "native_root_family_at F u [] L" "rel_ran L=D"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x"
    using root_family_environment_extension[OF environment targets] by blast
  have kept: "native_package_formed F D \<and> native_program F D=native_program E D"
    by (rule native_dependency_package_included[OF dependency selected(2,1)])
  have package: "native_package_at F u [] (native_program E D)"
    unfolding native_package_at_def by (rule exI[of _ L]) (use selected(3,4) kept in auto)
  have definitions: "system_definitions (native_program E D)=D"
    by (simp only: native_program_definitions[OF dependency] sites)
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ "native_program E D"])
    (use selected(1,2,5,6) package definitions in blast)
qed

theorem native_definition_family_selectable:
  fixes E :: "local_address option artifact_environment"
  assumes environment: "environment_formed E" and finite: "finite D"
    and readings: "\<And>d. d\<in>D \<Longrightarrow> \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    and closed: "\<And>d e. d\<in>D \<Longrightarrow> (d,e)\<in>native_definition_edges E \<Longrightarrow> e\<in>D"
  shows "\<exists>F u Q. environment_formed F \<and> environment_included E F \<and>
    native_package_at F u [] Q \<and> system_definitions Q=D \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s x. binds_slot F w s x \<longleftrightarrow> binds_slot E w s x)"
  by (rule native_definition_family_selection[OF environment readings closed])

text \<open>
  Selection consumes the actual complete definition readings and closure under
  their actual dependencies. The finite family may be empty or recursive.
  Its constructed root selector recovers precisely those definitions, with
  every previous artifact and outgoing binding preserved. Forwarding and
  single-clause extensions use this same selection theorem.
\<close>

end
