theory Factor_Native_Definition_Extensions
  imports Factor_Native_Program_Variants Factor_Positive_Locality Factor_Definition_Code Factor_Closed_Native_Definitions
    Factor_Package_Locality
begin

section \<open>Actual old readings and complete new code determine the whole extension\<close>

locale native_definition_extension =
  fixes E :: "local_address option artifact_environment"
    and P Q :: "('a,'s,local_address option definition_site,'c) schema_system"
    and pu :: "local_address option" and pr :: local_address
    and N :: "local_address option native_system"
    and K :: "local_address option definition_site\<Rightarrow>definition_code"
  assumes native: "native_package_at E pu pr N"
    and source_variant: "system_alpha_variant P N"
    and formed: "schema_system_formed Q"
    and agreement: "systems_agree_on P Q (system_definitions P)"
    and codes: "\<forall>d\<in>system_definitions Q-system_definitions P.
      definition_code_for (system_interface Q d) (system_clause_family Q d) (K d)"
    and compiled: "\<forall>d\<in>system_definitions Q-system_definitions P.
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
begin

lemma environment: "environment_formed E"
  using native_package_projection(1)[OF native] by (simp add: native_package_formed_def)

lemma source_formed: "schema_system_formed P" using source_variant by (simp add: system_alpha_variant_def)
lemma source_definitions: "system_definitions P=system_definitions N"
  using source_variant by (simp add: system_alpha_variant_def)
lemma source_inside: "system_definitions P\<subseteq>system_definitions Q"
  by (rule whole_agreement_definitions[OF agreement])

lemma source_site:
  assumes "d\<in>system_definitions P"
  shows "d\<in>system_definitions N"
  using assms by (simp only: source_definitions)

lemma readings:
  assumes member: "d\<in>system_definitions Q"
  shows "\<exists>p C. native_definition_at E (fst d) (snd d) p C"
proof (cases "d\<in>system_definitions P")
  case True
  show ?thesis by (rule native_package_definition_exists[OF native source_site[OF True]])
next
  case False
  show ?thesis using compiled member False by blast
qed

lemma variants:
  assumes member: "d\<in>system_definitions Q"
  shows "\<exists>p C f h. native_definition_at E (fst d) (snd d) p C \<and>
    inj_on f (pattern_variables (system_interface Q d)) \<and>
    p=rename_pattern f (system_interface Q d) \<and>
    schema_family_variant h (system_clause_family Q d) C"
proof (cases "d\<in>system_definitions P")
  case True
  obtain p C where read: "native_definition_at E (fst d) (snd d) p C" using readings[OF member] by blast
  obtain f h where maps: "inj_on f (pattern_variables (system_interface P d))"
    "system_interface N d=rename_pattern f (system_interface P d)"
    "schema_family_variant h (system_clause_family P d) (system_clause_family N d)"
    using source_variant True unfolding system_alpha_variant_def by blast
  have fields: "system_interface N d=p" "system_clause_family N d=C"
    by (rule native_package_fields_at[OF native source_site[OF True] read])+
  have agree: "system_interface Q d=system_interface P d" "system_clause_family Q d=system_clause_family P d"
    by (rule systems_agree_on_fields[OF source_formed formed agreement True True])+
  show ?thesis by (rule exI[of _ p], rule exI[of _ C], rule exI[of _ f], rule exI[of _ h])
    (use read maps fields agree in simp)
next
  case False
  have new: "d\<in>system_definitions Q-system_definitions P" using member False by blast
  have code: "definition_code_for (system_interface Q d) (system_clause_family Q d) (K d)"
    using codes new by blast
  have read: "native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
    using compiled new by blast
  show ?thesis using definition_code_properties(4)[OF code] read by blast
qed

lemma closed:
  assumes member: "d\<in>system_definitions Q" and edge: "(d,e)\<in>native_definition_edges E"
  shows "e\<in>system_definitions Q"
proof -
  obtain p C f h where read: "native_definition_at E (fst d) (snd d) p C"
    and family: "schema_family_variant h (system_clause_family Q d) C"
    using variants[OF member] by blast
  have dependency: "e\<in>(\<Union>S\<in>rel_ran C. schema_dependencies S)"
    using native_definition_edges_at[OF read, of e] edge by (auto simp: rel_ran_def)
  show ?thesis using system_clause_family_dependencies[OF formed, of d] dependency
    by (simp only: schema_family_variant_dependencies[OF family]; blast)
qed

lemma sites: "native_definition_sites E (system_definitions Q)=system_definitions Q"
  by (rule native_definition_family_closed(1)[OF environment]) (use readings closed in blast)+

lemma package_formed: "native_package_formed E (system_definitions Q)"
  by (rule native_definition_family_closed(2)[OF environment]) (use readings closed in blast)+

theorem program_variant: "system_alpha_variant Q (native_program E (system_definitions Q))"
  by (rule native_program_variant_from_readings[OF formed package_formed sites[symmetric] variants])

theorem package_variant:
  assumes target: "native_package_at E u r T" and definitions: "system_definitions T=system_definitions Q"
  shows "system_alpha_variant Q T"
  by (rule native_package_variant_from_readings[OF formed target definitions[symmetric] variants])

end

text \<open>
  The source premise relates the whole old program to its actual native
  reading. Every new definition has a complete compilation contract and an
  actual reading in the same environment. The resulting complete family is
  closed under every original and new callee, including recursive cycles.
  This contract is independent of the environment constructor and root
  selector that supplied those readings.
\<close>

end
