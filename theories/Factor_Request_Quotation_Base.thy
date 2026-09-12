theory Factor_Request_Quotation_Base
  imports Factor_Checked_Requirement_Plans Factor_Scope_Reading_Base
begin

section \<open>Request construction and complete quotation share their actual lower source\<close>

lemma quotation_data_agreement:
  "systems_agree_on data_append_system quotation_admission_system
    (system_definitions data_append_system)"
  by (simp add: systems_agree_on_added quotation_admission_system_def
    payload_disjoint_system_def data_union_system_def data_subset_system_def)

lemma complete_data_append_agreement:
  "systems_agree_on data_append_system complete_data_admission_system
    (system_definitions data_append_system)"
proof -
  have sub: "system_definitions data_append_system\<subseteq>system_definitions quotation_admission_system"
    by auto
  have later: "systems_agree_on quotation_admission_system complete_data_admission_system
      (system_definitions data_append_system)"
    by (rule systems_agree_on_subdomain[OF complete_data_quotation_agreement sub])
  show ?thesis by (rule systems_agree_on_transitive[OF quotation_data_agreement later])
qed

lemma request_data_agreement:
  "systems_agree_on data_append_system (admission_request_system D)
    (system_definitions data_append_system)"
proof -
  have first: "systems_agree_on data_append_system admission_sequence_system
      (system_definitions data_append_system)"
    using admission_sequence_data_extension unfolding admission_extension_def by blast
  have sub: "system_definitions data_append_system\<subseteq>system_definitions admission_sequence_system"
    by auto
  have later: "systems_agree_on admission_sequence_system (admission_request_system D)
      (system_definitions data_append_system)"
    unfolding admission_request_system_def
    by (rule systems_agree_on_subdomain[OF admission_request_group.old_agreement sub])
  show ?thesis by (rule systems_agree_on_transitive[OF first later])
qed

lemma request_quotation_agreement:
  "systems_agree_on complete_data_admission_system (admission_request_system D)
    (system_definitions complete_data_admission_system\<inter>system_definitions (admission_request_system D))"
proof -
  have overlap: "system_definitions complete_data_admission_system\<inter>
      system_definitions (admission_request_system D)=system_definitions data_append_system"
    by auto
  show ?thesis by (simp only: overlap;
    rule systems_agree_on_transitive[OF systems_agree_on_sym[OF complete_data_append_agreement]
      request_data_agreement])
qed

definition request_quotation_system :: "nat set \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "request_quotation_system D=system_union complete_data_admission_system (admission_request_system D)"

lemma request_quotation_formed [simp]: "schema_system_formed (request_quotation_system D)"
  unfolding request_quotation_system_def
  by (rule system_union_agree_formed[OF complete_data_admission_system_formed
    admission_request_system_formed request_quotation_agreement])

lemma request_quotation_definitions [simp]:
  "system_definitions (request_quotation_system D)=
    system_definitions complete_data_admission_system\<union>system_definitions (admission_request_system D)"
  by (simp add: request_quotation_system_def)

lemma request_quotation_call:
  "schema_call_formed (request_quotation_system D) d t \<longleftrightarrow>
    d\<in>system_definitions (request_quotation_system D) \<and> term_formed t"
  by (simp only: request_quotation_system_def system_union_agree_call[OF complete_data_admission_system_formed
    admission_request_system_formed request_quotation_agreement] system_union_definitions
    complete_data_admission_call admission_request_call Un_iff; blast)

lemma request_quotation_complete_meaning:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "(d,t)\<in>positive_meaning (request_quotation_system D) \<longleftrightarrow>
    (d,t)\<in>positive_meaning complete_data_admission_system"
  unfolding request_quotation_system_def
  by (rule system_union_agree_left_locality(2)[OF complete_data_admission_system_formed
    admission_request_system_formed request_quotation_agreement assms])

lemma request_quotation_request_meaning:
  assumes "d\<in>system_definitions (admission_request_system D)"
  shows "(d,t)\<in>positive_meaning (request_quotation_system D) \<longleftrightarrow>
    (d,t)\<in>positive_meaning (admission_request_system D)"
  unfolding request_quotation_system_def
  by (rule system_union_agree_right_locality(2)[OF complete_data_admission_system_formed
    admission_request_system_formed request_quotation_agreement assms])

lemma request_quotation_components:
  "(10,t)\<in>positive_meaning (request_quotation_system D) \<longleftrightarrow>
    (10,t)\<in>positive_meaning artifact_projection_system"
  "(123,t)\<in>positive_meaning (request_quotation_system D) \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  "(367,t)\<in>positive_meaning (request_quotation_system D) \<longleftrightarrow>
    (367,t)\<in>positive_meaning (admission_request_system D)"
  using request_quotation_request_meaning[where d=10 and t=t and D=D]
    admission_request_old_meaning[where d=10 and t=t and D=D]
    admission_sequence_data_meaning[where d=10 and t=t]
    data_append_old_meaning[where d=10 and t=t] target_projection_components(1)[where t=t]
    request_quotation_complete_meaning[where d=123 and t=t and D=D]
    request_quotation_request_meaning[where d=367 and t=t and D=D]
  by auto

text \<open>
  The intersection consists of the actual complete data-append source. Both
  branches preserve its interfaces and whole clause families. Their union
  consequently preserves all original meanings, including literal artifact
  projection, whole quotation, and checked request construction.
\<close>

end
