theory Factor_Finite_Relations
  imports Factor_Pattern_Programs Factor_Compiled_Applications
begin

section \<open>Finite extensional families as ordinary positive clauses\<close>

definition extensional_family_formed :: "('c \<times> factor_term) set \<Rightarrow> bool" where
  "extensional_family_formed T \<longleftrightarrow>
    finite T \<and> single_valued T \<and> (\<forall>c t. (c,t) \<in> T \<longrightarrow> term_formed t)"

definition finite_relation_system ::
  "'a \<Rightarrow> ('c \<times> factor_term) set \<Rightarrow> ('a,unit,unit,'c) schema_system" where
  "finite_relation_system a T =
    \<lparr>system_interfaces = {((),Pattern_Variable a)},
     system_clauses = (\<lambda>(c,t). (((),c),recognizer_schema (exact_term_pattern t))) ` T\<rparr>"

lemma finite_relation_clause:
  "((d,c),S) \<in> system_clauses (finite_relation_system a T) \<longleftrightarrow>
    d=() \<and> (\<exists>t. (c,t) \<in> T \<and> S=recognizer_schema (exact_term_pattern t))"
  by (auto simp: finite_relation_system_def)

lemma finite_relation_formed:
  assumes family: "extensional_family_formed T"
  shows "schema_system_formed (finite_relation_system a T)"
  using family
  by (auto simp: schema_system_formed_def finite_relation_system_def
      extensional_family_formed_def recognizer_schema_def schema_formed_def
      schema_dependencies_def system_definitions_def single_valued_def rel_dom_def rel_ran_def)

lemma finite_relation_definitions [simp]:
  "system_definitions (finite_relation_system a T) = {()}"
  by (auto simp: system_definitions_def finite_relation_system_def rel_dom_def)

lemma finite_relation_call:
  assumes "extensional_family_formed T"
  shows "schema_call_formed (finite_relation_system a T) () t \<longleftrightarrow> term_formed t"
  by (simp only: schema_call_formed_def finite_relation_formed[OF assms])
     (simp add: finite_relation_system_def)

lemma exact_recognizer_instance:
  "schema_instance (recognizer_schema (exact_term_pattern x)) V t Q \<longleftrightarrow>
    term_formed x \<and> V={} \<and> t=x \<and> Q={}"
  by (auto simp: schema_instance_def recognizer_schema_def schema_formed_def
      schema_variables_def term_bindings_formed_def schema_premise_instance_def
      single_valued_def rel_dom_def)

lemma finite_relation_instance:
  assumes family: "extensional_family_formed T"
  shows "admitted_schema_instance (finite_relation_system a T) () c V t Q \<longleftrightarrow>
    (c,t) \<in> T \<and> V={} \<and> Q={}"
proof
  assume admitted: "admitted_schema_instance (finite_relation_system a T) () c V t Q"
  show "(c,t) \<in> T \<and> V={} \<and> Q={}"
    using admitted
    by (auto simp: admitted_schema_instance_def finite_relation_clause exact_recognizer_instance)
next
  assume entry: "(c,t) \<in> T \<and> V={} \<and> Q={}"
  have formed: "term_formed t"
    using family entry by (auto simp: extensional_family_formed_def)
  have inst: "schema_instance (recognizer_schema (exact_term_pattern t)) V t Q"
    using entry formed by (simp only: exact_recognizer_instance)
  have clause: "(((),c),recognizer_schema (exact_term_pattern t)) \<in>
    system_clauses (finite_relation_system a T)"
    using entry by (auto simp only: finite_relation_clause)
  have call: "schema_call_formed (finite_relation_system a T) () t"
    using formed by (simp only: finite_relation_call[OF family])
  have material: "schema_material_satisfied (recognizer_schema (exact_term_pattern t)) V"
    by (simp add: schema_material_satisfied_def recognizer_schema_def)
  show "admitted_schema_instance (finite_relation_system a T) () c V t Q"
    using entry inst clause call material unfolding admitted_schema_instance_def by blast
qed

theorem finite_relation_consequences:
  assumes family: "extensional_family_formed T"
  shows "schema_consequences (finite_relation_system a T) X = {()} \<times> rel_ran T"
  by (auto simp: schema_consequences_def finite_relation_instance[OF family] rel_ran_def)

theorem finite_relation_meaning:
  assumes family: "extensional_family_formed T"
  shows "positive_meaning (finite_relation_system a T) = {()} \<times> rel_ran T"
  by (subst positive_meaning_unfold) (rule finite_relation_consequences[OF family])

corollary finite_relation_holds:
  assumes "extensional_family_formed T"
  shows "((),t) \<in> positive_meaning (finite_relation_system a T) \<longleftrightarrow> t \<in> rel_ran T"
  by (simp only: finite_relation_meaning[OF assms]) simp

lemma empty_extensional_family [simp]: "extensional_family_formed {}"
  by (simp add: extensional_family_formed_def single_valued_def)

corollary empty_finite_relation:
  "schema_call_formed (finite_relation_system a {}) () t \<longleftrightarrow> term_formed t"
  "positive_meaning (finite_relation_system a {}) = {}"
  using finite_relation_call[OF empty_extensional_family]
    finite_relation_meaning[OF empty_extensional_family] by simp_all

lemma finite_relation_occurrences:
  "rel_dom (system_clauses (finite_relation_system a T)) = (\<lambda>c. ((),c)) ` rel_dom T"
  by (auto simp: finite_relation_system_def rel_dom_def image_iff; force)

theorem finite_relation_native_total:
  assumes family: "extensional_family_formed T"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au \<notin> environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] d t I K \<and>
      native_package_environment F pu [] = E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> t \<in> rel_ran T)))"
proof -
  let ?P = "finite_relation_system () T"
  have formed: "schema_system_formed ?P" by (rule finite_relation_formed[OF family])
  obtain g :: "unit \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q where compiled:
    "closed_native_package_at E pu [] Q"
    "\<forall>d\<in>system_definitions ?P. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
        au \<notin> environment_uses E \<and> native_package_at F pu [] Q \<and>
        native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu [] = E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed ?P d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t) \<in> positive_meaning ?P))"
    using compiled_program_future_applications[OF formed] by metis
  have calls: "\<forall>t. term_formed t \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au \<notin> environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g ()) t I K \<and>
      native_package_environment F pu [] = E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> t \<in> rel_ran T))"
    using compiled(2)
    by (auto simp: finite_relation_call[OF family] finite_relation_holds[OF family]; blast)
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g ()"])
    (use compiled(1) calls in blast)
qed

text \<open>
  This is a construction in the existing language. Each supplied tuple
  occurrence becomes one ordinary clause occurrence, including distinct
  occurrences with equal tuples. No extensional truth branch or comparison
  callback is added. The comparison is exact term equality; permitted
  renaming of code positions is handled by native compilation.

  An empty family still has a formed interface and has no true calls.
  One closed compiled program receives every future formed term with exactly
  the supplied family's membership relation.
\<close>

end
