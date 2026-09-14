theory Factor_Required_History_Construction
  imports Factor_Required_History_Steps Factor_Requirement_Source_Examples Optional_Result_Invariants
begin

lemma finite_required_histories_nonempty:
  "\<exists>q. finite_required_history_valid q"
proof -
  have source: "finite_native_source (finite_guard_source True) None [0]=
    Some (finite_guard_source_program True)"
    by (simp only: finite_native_source_correct; rule finite_guard_source_package)
  obtain d K pu where built: "finite_construct_source_requirements (finite_guard_source True) None [0] []=Some (d,K,pu)"
    using finite_construct_source_requirements_total[of "finite_guard_source True" None "[0]" "[]"] source by auto
  obtain q where prepared: "finite_prepare_required_history (finite_guard_source True) None [0] []=Some q"
    by (simp only: finite_prepare_required_history_def built option.map; blast)
  show ?thesis using finite_prepare_required_history_valid[OF prepared] by blast
qed

typedef required_history = "{q. finite_required_history_valid q}"
  morphisms raw_required_history Required_History
  using finite_required_histories_nonempty by blast

setup_lifting type_definition_required_history

lift_definition (code_dt) prepare_required_history ::
  "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option definition_site admission_goal list \<Rightarrow> required_history option"
  is finite_prepare_required_history
  by (auto intro: optional_result_invariant finite_prepare_required_history_valid)

lift_definition (code_dt) required_history_step ::
  "required_history \<Rightarrow> finite_exact_target \<Rightarrow>
    (local_address option definition_site\<times>finite_generation) list \<Rightarrow>
    local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option definition_site \<Rightarrow>
    finite_exact_artifact \<Rightarrow> required_history option"
  is finite_required_history_step
  by (auto intro: optional_result_invariant finite_required_history_step_valid)

theorem required_history_valid:
  "finite_required_history_valid (raw_required_history q)"
  using raw_required_history[of q] by simp

export_code prepare_required_history required_history_step raw_required_history checking SML

text \<open>
  The exposed type carries the proved state invariant. Only checked preparation
  and checked insertion construct its optional results. Its invariant concerns
  the original policy, every recorded generation reading and payload requirement
  truth. It does not identify all such states with a complete historical
  authority account or certify arbitrary host actions. Those requirements
  remain explicit even though this transition is enforced by construction.
\<close>

end
