theory Factor_Generation_History_Append
  imports Factor_Required_History_Transitions RRA_Complete_Environment_Agreement
begin

theorem finite_required_history_append_valid:
  assumes previous: "finite_required_history_valid q"
    and formed: "finite_environment_formed A"
    and included: "finite_environment_included (required_history_material q) A"
    and generation: "finite_check_generation G A u []"
    and payload: "generation_payload G=Finite_Whole R"
    and admitted: "finite_certified_policy_cause (required_history_policy q) (required_history_policy_use q) []
      (required_history_entry q) A u [] G E root R"
  shows "finite_required_history_valid (finite_required_history_append q A u G)"
proof -
  obtain P where source: "finite_native_source (required_history_source q) (required_history_source_use q)
      (required_history_source_root q)=Some P"
    and built: "finite_construct_source_requirements (required_history_source q) (required_history_source_use q)
      (required_history_source_root q) (required_history_goals q)=
        Some (required_history_entry q,required_history_policy q,required_history_policy_use q)"
    and old: "\<forall>d H. (d,H)\<in>set (required_history_members q) \<longrightarrow>
      finite_check_generation H (required_history_material q) (fst d) (snd d) \<and>
      required_generation_payload P (required_history_goals q) H"
    using previous unfolding finite_required_history_valid_def by blast
  have required: "finite_required_cause (required_history_source q) (required_history_source_use q)
    (required_history_source_root q) (required_history_goals q) A u [] G E root R"
    by (simp only: finite_required_cause_def built option.case case_prod_conv admitted)
  have truth: "admission_requirements_hold (positive_meaning (decode_finite_system P))
      (required_history_goals q) (Target_Term (Whole_Artifact (decode_finite_object R)))"
    by (rule finite_required_cause_all_requirements[OF source required])
  have new_payload: "required_generation_payload P (required_history_goals q) G"
    using payload truth by (auto simp: required_generation_payload_def)
  have kept: "finite_check_generation H A (fst d) (snd d) \<and>
    required_generation_payload P (required_history_goals q) H"
    if member: "(d,H)\<in>set (required_history_members q)" for d H
    using old member finite_check_generation_included[OF _ included formed] by blast
  show ?thesis unfolding finite_required_history_valid_def
    by (rule exI[of _ P]) (use source built formed generation new_payload kept in
      \<open>auto simp: finite_required_history_append_def\<close>)
qed

theorem finite_required_history_append_preserved:
  assumes agreement: "finite_environment_agrees_on (required_history_material q) A
    (finite_environment_uses (required_history_material q))"
  shows "finite_environment_agrees_on (required_history_material q)
      (required_history_material (finite_required_history_append q A u G))
      (finite_environment_uses (required_history_material q))"
    "required_history_members (finite_required_history_append q A u G)=((u,[]),G)#required_history_members q"
    "(required_history_source (finite_required_history_append q A u G),
       required_history_source_use (finite_required_history_append q A u G),
       required_history_source_root (finite_required_history_append q A u G),
       required_history_goals (finite_required_history_append q A u G),
       required_history_entry (finite_required_history_append q A u G),
       required_history_policy (finite_required_history_append q A u G),
       required_history_policy_use (finite_required_history_append q A u G))=
      (required_history_source q,required_history_source_use q,required_history_source_root q,
       required_history_goals q,required_history_entry q,required_history_policy q,required_history_policy_use q)"
  by (simp_all add: finite_required_history_append_def agreement)

text \<open>
  Original history validity depends on actual preserved material, the new
  generation, its payload and the actual original policy check. It does not
  depend on one generation allocator or replay wrapper. Ledger order and every
  original source, requirement and policy field remain explicit. Membership
  admission and historical reachability are separate obligations.
\<close>

end
