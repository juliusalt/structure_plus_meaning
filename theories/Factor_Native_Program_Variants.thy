theory Factor_Native_Program_Variants
  imports Factor_System_Alpha Factor_Packages
begin

section \<open>Complete native definition readings determine the program fields\<close>

lemma native_program_fields_at:
  assumes package: "native_package_formed E U" and site: "d\<in>native_definition_sites E U"
    and read: "native_definition_at E (fst d) (snd d) p C"
  shows "system_interface (native_program E U) d=p"
    and "system_clause_family (native_program E U) d=C"
proof -
  have formed: "schema_system_formed (native_program E U)" by (rule native_program_formed[OF package])
  have interface: "(d,p)\<in>system_interfaces (native_program E U)"
    by (simp only: native_program_complete_at(1)[OF site read])
  show "system_interface (native_program E U) d=p" by (rule system_interface_unique[OF formed interface])
  have clauses: "(c,S)\<in>system_clause_family (native_program E U) d \<longleftrightarrow> (c,S)\<in>C" for c S
    by (simp only: system_clause_member native_program_complete_at(2)[OF site read])
  show "system_clause_family (native_program E U) d=C" using clauses by auto
qed

lemma native_package_fields_at:
  assumes package: "native_package_at E u r P" and member: "d\<in>system_definitions P"
    and read: "native_definition_at E (fst d) (snd d) p C"
  shows "system_interface P d=p" and "system_clause_family P d=C"
proof -
  obtain L where target: "native_package_formed E (rel_ran L)" "P=native_program E (rel_ran L)"
    "native_root_family_at E u r L"
    using package unfolding native_package_at_def by blast
  have site: "d\<in>native_definition_sites E (rel_ran L)"
    using member target(2) by (simp only: native_program_definitions[OF target(1)])
  show "system_interface P d=p" "system_clause_family P d=C"
    using native_program_fields_at[OF target(1) site read] target(2) by simp_all
qed

theorem native_program_variant_from_readings:
  assumes source: "schema_system_formed P" and target: "native_package_formed E U"
    and definitions: "system_definitions P=native_definition_sites E U"
    and readings: "\<And>d. d\<in>system_definitions P \<Longrightarrow> \<exists>p C f h.
      native_definition_at E (fst d) (snd d) p C \<and>
      inj_on f (pattern_variables (system_interface P d)) \<and>
      p=rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) C"
  shows "system_alpha_variant P (native_program E U)"
proof -
  have formed: "schema_system_formed (native_program E U)" by (rule native_program_formed[OF target])
  have domains: "system_definitions P=system_definitions (native_program E U)"
    by (simp only: native_program_definitions[OF target] definitions)
  have fields: "\<exists>f h. inj_on f (pattern_variables (system_interface P d)) \<and>
    system_interface (native_program E U) d=rename_pattern f (system_interface P d) \<and>
    schema_family_variant h (system_clause_family P d) (system_clause_family (native_program E U) d)"
    if member: "d\<in>system_definitions P" for d
  proof -
    obtain p C f h where actual: "native_definition_at E (fst d) (snd d) p C"
      "inj_on f (pattern_variables (system_interface P d))" "p=rename_pattern f (system_interface P d)"
      "schema_family_variant h (system_clause_family P d) C" using readings[OF member] by blast
    have site: "d\<in>native_definition_sites E U" using member definitions by simp
    show ?thesis using native_program_fields_at[OF target site actual(1)] actual(2-4) by blast
  qed
  show ?thesis using source formed domains fields by (simp add: system_alpha_variant_def)
qed

theorem native_package_variant_from_readings:
  assumes source: "schema_system_formed P" and target: "native_package_at E u r T"
    and definitions: "system_definitions P=system_definitions T"
    and readings: "\<And>d. d\<in>system_definitions P \<Longrightarrow> \<exists>p C f h.
      native_definition_at E (fst d) (snd d) p C \<and>
      inj_on f (pattern_variables (system_interface P d)) \<and>
      p=rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) C"
  shows "system_alpha_variant P T"
proof -
  obtain L where package: "native_package_formed E (rel_ran L)" "T=native_program E (rel_ran L)"
    "native_root_family_at E u r L"
    using target unfolding native_package_at_def by blast
  have sites: "system_definitions P=native_definition_sites E (rel_ran L)"
    using definitions package(2) by (simp only: native_program_definitions[OF package(1)])
  show ?thesis using native_program_variant_from_readings[OF source package(1) sites readings] package(2) by simp
qed

text \<open>
  The witnesses are actual complete definition readings in the target
  environment. Their interface and clause-family correspondences determine
  the whole program variant. This applies independently of the constructor
  that produced those readings.
\<close>

end
