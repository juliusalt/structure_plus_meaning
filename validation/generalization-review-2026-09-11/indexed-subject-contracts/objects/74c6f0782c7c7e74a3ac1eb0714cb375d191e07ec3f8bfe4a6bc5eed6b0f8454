theory Factor_Generation_Scope_Base
  imports Factor_Generation_Source_Contracts Factor_Scope_Programs
begin

section \<open>Generation source and scope readers share their lower definitions\<close>

lemma generation_scope_shared_boundary:
  "system_definitions generation_source_system\<inter>system_definitions scope_programs_system
    \<subseteq>system_definitions located_admission_system"
  "system_definitions generation_source_system\<inter>system_definitions scope_programs_system
    \<subseteq>system_definitions generation_source_base_system"
  "system_definitions generation_source_system\<inter>system_definitions scope_programs_system
    \<subseteq>system_definitions judgment_scope_base_system\<union>system_definitions program_report_base_system"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions scope_programs_system"
  let ?G="{147,148,149,150,151,152,153,154,155}"
  let ?S="{160,161,164,165,166}"
  have source_bound: "system_definitions generation_source_system\<subseteq>
      system_definitions generation_source_components_system\<union>?G"
    using generation_source_base_subdomain unfolding generation_source_definitions by blast
  have new_source_absent: "?G\<inter>(system_definitions scope_reading_components_system\<union>?S)={}"
    using context_base_subdomain by (auto dest: subsetD)
  have new_scope_absent: "?S\<inter>(system_definitions generation_source_components_system\<union>?G)={}"
    using generation_target_subdomain by (auto dest: subsetD)
  have retained_source: "?U\<subseteq>system_definitions generation_source_base_system"
    using scope_programs_boundary new_source_absent
    unfolding generation_source_definitions by blast
  have retained_scope: "?U\<subseteq>
      system_definitions judgment_scope_base_system\<union>system_definitions program_report_base_system"
    using source_bound new_scope_absent
    unfolding scope_programs_definitions judgment_scope_reading_definitions program_scope_reports_definitions by blast
  have context_lower: "system_definitions context_base_system\<subseteq>system_definitions located_admission_system"
    by (rule subset_trans[OF context_base_subdomain]) auto
  have target_lower: "system_definitions target_difference_system\<inter>system_definitions complete_data_admission_system
      \<subseteq>system_definitions located_admission_system" by auto
  have target_separate: "system_definitions target_difference_system\<inter>{156,157,158,159}={}"
    by auto
  have target_overlap: "system_definitions target_difference_system\<inter>system_definitions scope_reading_components_system
      \<subseteq>system_definitions located_admission_system"
    using target_lower context_lower target_separate
    unfolding scope_reading_components_definitions context_admission_definitions by blast
  have value_separate: "{139,140,141,142,143,144,145,146}\<inter>system_definitions scope_reading_components_system={}"
    using context_base_subdomain by (auto dest: subsetD)
  have value_overlap: "system_definitions generation_value_system\<inter>system_definitions scope_reading_components_system
      \<subseteq>system_definitions located_admission_system"
    using generation_target_subdomain target_overlap value_separate unfolding generation_value_definitions by blast
  have component_overlap: "system_definitions generation_source_components_system\<inter>system_definitions scope_reading_components_system
      \<subseteq>system_definitions located_admission_system"
    using value_overlap unfolding generation_source_components_definitions by blast
  show "?U\<subseteq>system_definitions located_admission_system"
    using retained_source retained_scope generation_source_base_subdomain judgment_scope_base_subdomain
      program_report_base_subdomain component_overlap by blast
  show "?U\<subseteq>system_definitions generation_source_base_system" by (rule retained_source)
  show "?U\<subseteq>system_definitions judgment_scope_base_system\<union>system_definitions program_report_base_system"
    by (rule retained_scope)
qed

lemma generation_source_located_agreement:
  "systems_agree_on located_admission_system generation_source_components_system
    (system_definitions located_admission_system)"
  using system_union_agree_left[OF generation_value_system_formed generation_located_agreement]
  by (simp only: generation_source_components_system_def)

lemma generation_source_retained_agreement:
  "systems_agree_on generation_source_base_system generation_source_system
    (system_definitions generation_source_base_system)"
  using generation_source_group.old_agreement by (simp only: generation_source_system_def)

lemma generation_scope_program_agreement:
  "systems_agree_on generation_source_system scope_programs_system
    (system_definitions generation_source_system\<inter>system_definitions scope_programs_system)"
proof -
  let ?U="system_definitions generation_source_system\<inter>system_definitions scope_programs_system"
  have one: "systems_agree_on located_admission_system generation_source_components_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_located_agreement generation_scope_shared_boundary(1)])
  have two: "systems_agree_on generation_source_components_system generation_source_base_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_base_agreement generation_scope_shared_boundary(2)])
  have three: "systems_agree_on generation_source_base_system generation_source_system ?U"
    by (rule systems_agree_on_subdomain[OF generation_source_retained_agreement generation_scope_shared_boundary(2)])
  have first: "systems_agree_on located_admission_system generation_source_system ?U"
    by (rule systems_agree_on_transitive[OF one systems_agree_on_transitive[OF two three]])
  have four: "systems_agree_on located_admission_system complete_data_admission_system ?U"
    by (rule systems_agree_on_subdomain[OF complete_data_located_agreement generation_scope_shared_boundary(1)])
  have contained: "?U\<subseteq>system_definitions complete_data_admission_system"
    by (rule subset_trans[OF generation_scope_shared_boundary(1)]) auto
  have five: "systems_agree_on complete_data_admission_system scope_reading_components_system ?U"
    by (rule systems_agree_on_subdomain[OF scope_reading_complete_agreement contained])
  have six: "systems_agree_on scope_reading_components_system scope_programs_system ?U"
    by (rule systems_agree_on_subdomain[OF scope_programs_base_agreement generation_scope_shared_boundary(3)])
  have second: "systems_agree_on located_admission_system scope_programs_system ?U"
    by (rule systems_agree_on_transitive[OF four systems_agree_on_transitive[OF five six]])
  show ?thesis by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF first] second])
qed

definition generation_scope_components_system :: "(nat,nat,nat,nat) schema_system" where
  "generation_scope_components_system=system_union generation_source_system scope_programs_system"

lemma generation_scope_components_formed [simp]: "schema_system_formed generation_scope_components_system"
  unfolding generation_scope_components_system_def
  by (rule system_union_agree_formed[OF generation_source_system_formed scope_programs_formed generation_scope_program_agreement])

lemma generation_scope_components_definitions [simp]:
  "system_definitions generation_scope_components_system=
    system_definitions generation_source_system\<union>system_definitions scope_programs_system"
  by (simp add: generation_scope_components_system_def)

lemma generation_scope_components_call:
  "schema_call_formed generation_scope_components_system d t \<longleftrightarrow>
    d\<in>system_definitions generation_scope_components_system \<and> term_formed t"
  using system_union_agree_call[OF generation_source_system_formed scope_programs_formed
    generation_scope_program_agreement, of d t]
  by (simp only: generation_scope_components_system_def system_union_definitions generation_source_call
    scope_programs_call Un_iff; blast)

theorem generation_scope_source_locality:
  assumes "d\<in>system_definitions generation_source_system"
  shows "schema_call_formed generation_scope_components_system d t \<longleftrightarrow>
      schema_call_formed generation_source_system d t"
    and "(d,t)\<in>positive_meaning generation_scope_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning generation_source_system"
  using system_union_agree_left_locality[OF generation_source_system_formed scope_programs_formed
    generation_scope_program_agreement assms, of t]
  by (simp_all only: generation_scope_components_system_def)

theorem generation_scope_reader_locality:
  assumes "d\<in>system_definitions scope_programs_system"
  shows "schema_call_formed generation_scope_components_system d t \<longleftrightarrow>
      schema_call_formed scope_programs_system d t"
    and "(d,t)\<in>positive_meaning generation_scope_components_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning scope_programs_system"
  using system_union_agree_right_locality[OF generation_source_system_formed scope_programs_formed
    generation_scope_program_agreement assms, of t]
  by (simp_all only: generation_scope_components_system_def)

lemma generation_scope_component_meanings:
  "(151,t)\<in>positive_meaning generation_scope_components_system \<longleftrightarrow>
    (151,t)\<in>positive_meaning generation_source_system"
  "(160,t)\<in>positive_meaning generation_scope_components_system \<longleftrightarrow>
    (160,t)\<in>positive_meaning judgment_scope_reading_system"
  "(165,t)\<in>positive_meaning generation_scope_components_system \<longleftrightarrow>
    (165,t)\<in>positive_meaning program_scope_reports_system"
  using generation_scope_source_locality(2)[of 151 t] generation_scope_reader_locality(2)[of 160 t]
    generation_scope_reader_locality(2)[of 165 t] scope_programs_components[of t] by auto

text \<open>
  Complete shared definitions connect the actual generation reader to the two
  local scope readers. The intersection lies in their ordinary citation and
  data infrastructure, whose full interfaces and clause families agree.
  Formation and every positive call of both programs are preserved.

  The following group retains only the least closure of its actual external
  callees in this source program. The combination itself changes no quoted
  program, adopted scope, or independent generation relation.
\<close>

end
