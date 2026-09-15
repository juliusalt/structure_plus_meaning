theory Factor_Known_Replay_Policy
  imports Factor_Finite_Known_Judgment_Scopes Factor_Parametric_Policy_Attempts Optional_Known_Checks
begin

definition replay_policy_condition where
  "replay_policy_condition K ku kr entry R J pu pr au ar=(
    finite_native_package_readings K ku kr\<noteq>{||} \<and>
    finite_policy_cause_alignment K ku kr entry R (J,pu,pr,au,ar))"

definition policy_record_replay_from_source where
  "policy_record_replay_from_source construct K ku entry H l rows E pu pr au ar root R=(
    if finite_literal_replay_ready E pu pr au ar root R then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> if replay_policy_condition K ku [] entry R J pu pr au ar then
          construct H l (Finite_Whole R) (Finite_Whole C) rows else None)
    else None)"

context generation_record_backend
begin

theorem record_replay_known_scopes:
  assumes result: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "finite_generation_judgment_readings (read_environment A) u [] G={|(J,pu,pr,au,ar)|}"
proof -
  have generated: "construct H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    and quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
    using result by (simp only: record_native_replay_with_result; blast)+
  have actual: "finite_check_generation G (read_environment A) u []" by (rule generation[OF generated])
  have cause: "generation_cause G=Finite_Whole C"
    by (simp add: core[OF generated] finite_generation_record_core_def)
  show ?thesis by (rule finite_generation_judgment_readings_known[OF actual cause
    finite_native_judgment_quote_correct(1)[OF quoted]])
qed

theorem record_replay_known_policy:
  assumes result: "record_native_replay_with construct H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "finite_certified_policy_cause K ku kr entry (read_environment A) u [] G E root R=
    replay_policy_condition K ku kr entry R J pu pr au ar"
proof -
  have certified: "finite_certified_base_cause (read_environment A) u [] G E root R"
    using record_replay_certified[OF result] by (simp only: finite_certified_base_cause_exact)
  show ?thesis by (simp only: finite_certified_policy_cause_def replay_policy_condition_def
    certified record_replay_known_scopes[OF result]; simp)
qed

theorem policy_record_replay_from_source_exact:
  "policy_record_replay_from_source construct K ku entry H l rows E pu pr au ar root R=
    policy_record_replay_with read_environment construct K ku entry H l rows E pu pr au ar root R"
proof (cases "finite_literal_replay_ready E pu pr au ar root R")
  case False then show ?thesis by (simp add: policy_record_replay_from_source_def
    policy_record_replay_with_def record_native_replay_with_def optional_checked_result_case)
next
  case ready: True
  show ?thesis
  proof (cases "finite_native_judgment_quote E pu pr au ar")
    case None then show ?thesis by (simp add: policy_record_replay_from_source_def
      policy_record_replay_with_def record_native_replay_with_def optional_checked_result_case ready)
  next
    case (Some pair)
    obtain J C where pair: "pair=(J,C)" by (cases pair) auto
    have quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)" using Some pair by simp
    let ?input = "record_native_replay_with construct H l rows E pu pr au ar root R"
    let ?check = "\<lambda>(A,u,G,J,C). finite_certified_policy_cause K ku [] entry (read_environment A) u [] G E root R"
    let ?extract = "\<lambda>(A,u,G,J,C). (A,u,G)"
    let ?known = "replay_policy_condition K ku [] entry R J pu pr au ar"
    have every: "?check result_value=?known" if result: "?input=Some result_value" for result_value
    proof -
      obtain A u G F D where shape: "result_value=(A,u,G,F,D)" by (cases result_value) auto
      have returned: "?input=Some (A,u,G,F,D)" using result shape by simp
      have other: "finite_native_judgment_quote E pu pr au ar=Some (F,D)"
        using returned by (simp only: record_native_replay_with_result; blast)
      have same: "F=J" using quoted other by simp
      show ?thesis using record_replay_known_policy[OF returned, of K ku "[]" entry]
        by (simp only: shape case_prod_conv same)
    qed
    have checked: "policy_record_replay_with read_environment construct K ku entry H l rows E pu pr au ar root R=
      (if ?known then map_option ?extract ?input else None)"
      unfolding policy_record_replay_with_def
      by (rule optional_checked_result_known_check) (rule every)
    show ?thesis by (simp add: checked policy_record_replay_from_source_def record_native_replay_with_def
      ready quoted option.map_comp option.map_id[unfolded id_def] comp_def case_prod_unfold split: option.splits prod.splits)
  qed
qed

end

export_code policy_record_replay_from_source checking SML

text \<open>
  The actual replay result establishes the generation and its uniquely quoted
  scope. Its existing certification theorem supplies the original base-cause
  condition. The remaining package and policy-alignment check is still computed
  from that complete scope. The optional-result contract permits checking it
  before construction while retaining every refusal and complete success.
  No arbitrary cause or generation is admitted by this result-specific equation.
\<close>

end
