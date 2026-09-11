theory Factor_Inference_Specialization_Base
  imports Factor_Specialization_Binding_Clauses Factor_Proof_Node_Reading
begin

section \<open>The node and specialization programs agree on the common package readers\<close>

lemma specialization_report_package_agreement:
  "systems_agree_on program_call_list_system specialization_report_system
    (system_definitions program_call_list_system)"
proof -
  have reverse: "systems_agree_on program_call_list_system pattern_call_reading_system
      (system_definitions program_call_list_system\<inter>system_definitions pattern_call_reading_system)"
    using systems_agree_on_sym[OF schema_pattern_call_list_agreement] by (simp only: Int_commute)
  have calls: "systems_agree_on program_call_list_system schema_pattern_call_base_system
      (system_definitions program_call_list_system)"
    using system_union_agree_left[OF pattern_call_reading_system_formed reverse]
    by (simp only: schema_pattern_call_base_system_def system_union_commute)
  have whole: "systems_agree_on schema_pattern_call_base_system schema_pattern_base_system
      (system_definitions schema_pattern_call_base_system)"
    using system_union_agree_left[OF schema_reading_system_formed schema_pattern_report_agreement]
    by (simp only: schema_pattern_base_system_def)
  have restricted: "systems_agree_on schema_pattern_call_base_system schema_pattern_base_system
      (system_definitions program_call_list_system)"
    by (rule systems_agree_on_subdomain[OF whole]) auto
  have base: "systems_agree_on program_call_list_system schema_pattern_base_system
      (system_definitions program_call_list_system)"
    by (rule systems_agree_on_transitive[OF calls restricted])
  show ?thesis using base
    by (simp add: specialization_report_system_def clause_specialization_reading_system_def
      schema_pattern_reading_system_def systems_agree_on_added)
qed

lemma specialization_binding_package_agreement:
  "systems_agree_on program_call_list_system specialization_binding_system
    (system_definitions program_call_list_system)"
proof -
  have whole: "systems_agree_on specialization_report_system specialization_binding_base_system
      (system_definitions specialization_report_system)"
    using system_union_agree_left[OF binding_record_formed specialization_binding_agreement]
    by (simp only: specialization_binding_base_system_def)
  have restricted: "systems_agree_on specialization_report_system specialization_binding_base_system
      (system_definitions program_call_list_system)"
    by (rule systems_agree_on_subdomain[OF whole]) auto
  have base: "systems_agree_on program_call_list_system specialization_binding_base_system
      (system_definitions program_call_list_system)"
    by (rule systems_agree_on_transitive[OF specialization_report_package_agreement restricted])
  show ?thesis using base by (simp add: specialization_binding_system_def systems_agree_on_added)
qed

lemma proof_node_package_agreement:
  "systems_agree_on program_call_list_system proof_node_reading_system
    (system_definitions program_call_list_system)"
  by (simp add: proof_node_reading_system_def discharge_table_reading_system_def binding_table_reading_system_def
    site_link_vector_system_def application_vector_system_def site_link_reading_system_def
    site_citation_reading_system_def admitted_instantiation_system_def systems_agree_on_added)

lemma inference_specialization_agreement:
  "systems_agree_on specialization_binding_system proof_node_reading_system
    (system_definitions specialization_binding_system\<inter>system_definitions proof_node_reading_system)"
proof -
  have shared: "systems_agree_on specialization_binding_system proof_node_reading_system
      (system_definitions program_call_list_system)"
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF specialization_binding_package_agreement]
      proof_node_package_agreement])
  have overlap: "system_definitions specialization_binding_system\<inter>system_definitions proof_node_reading_system=
      system_definitions program_call_list_system" by auto
  show ?thesis using shared by (simp only: overlap)
qed

definition inference_specialization_base_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_specialization_base_system=system_union specialization_binding_system proof_node_reading_system"

lemma inference_specialization_base_formed [simp]: "schema_system_formed inference_specialization_base_system"
  unfolding inference_specialization_base_system_def
  by (rule system_union_agree_formed[OF specialization_binding_formed proof_node_reading_system_formed
    inference_specialization_agreement])

lemma inference_specialization_base_definitions [simp]:
  "system_definitions inference_specialization_base_system=
    system_definitions specialization_binding_system\<union>system_definitions proof_node_reading_system"
  by (simp add: inference_specialization_base_system_def)

lemma inference_specialization_base_call:
  "schema_call_formed inference_specialization_base_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_specialization_base_system \<and> term_formed t"
  using system_union_agree_call[OF specialization_binding_formed proof_node_reading_system_formed
    inference_specialization_agreement, of d t]
  by (simp only: inference_specialization_base_system_def system_union_definitions
    specialization_binding_call proof_node_reading_call; blast)

lemma inference_specialization_base_binding:
  assumes "d\<in>system_definitions specialization_binding_system"
  shows "(d,t)\<in>positive_meaning inference_specialization_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning specialization_binding_system"
  using system_union_agree_left_locality(2)[OF specialization_binding_formed proof_node_reading_system_formed
    inference_specialization_agreement assms, of t]
  by (simp only: inference_specialization_base_system_def)

lemma inference_specialization_base_node:
  assumes "d\<in>system_definitions proof_node_reading_system"
  shows "(d,t)\<in>positive_meaning inference_specialization_base_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning proof_node_reading_system"
  using system_union_agree_right_locality(2)[OF specialization_binding_formed proof_node_reading_system_formed
    inference_specialization_agreement assms, of t]
  by (simp only: inference_specialization_base_system_def)

end
