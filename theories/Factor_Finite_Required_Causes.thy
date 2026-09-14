theory Factor_Finite_Required_Causes
  imports Factor_Finite_Policy_Causes Factor_Finite_Native_Requirements
begin

definition finite_required_cause where
  "finite_required_cause S su sr gs E gu gr G H root R=(case finite_construct_source_requirements S su sr gs of
    None \<Rightarrow> False | Some (d,K,pu) \<Rightarrow> finite_certified_policy_cause K pu [] d E gu gr G H root R)"

theorem finite_required_cause_all_requirements:
  assumes original: "finite_native_source S su sr=Some P"
    and accepted: "finite_required_cause S su sr gs E gu gr G H root R"
  shows "admission_requirements_hold (positive_meaning (decode_finite_system P)) gs
    (Target_Term (Whole_Artifact (decode_finite_object R)))"
proof -
  obtain d K pu where built: "finite_construct_source_requirements S su sr gs=Some (d,K,pu)"
    and certified: "finite_certified_policy_cause K pu [] d E gu gr G H root R"
    using accepted by (auto simp: finite_required_cause_def split: option.splits prod.splits)
  obtain P' Q e T where source: "native_package_at (decode_finite_environment S) su sr (decode_finite_system P')"
    and policy: "native_package_at (decode_finite_environment K) pu [] T"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P')) gs t"
    using finite_construct_source_requirements_correct[OF built] by blast
  have same: "P'=P" using source original by (simp only: finite_native_source_correct[symmetric]; simp)
  have truth: "(d,Target_Term (Whole_Artifact (decode_finite_object R)))\<in>positive_meaning T"
    by (rule certified_policy_cause_sound[OF policy certified[unfolded finite_certified_policy_cause_exact]])
  show ?thesis using meaning truth by (simp only: same; blast)
qed

corollary finite_required_cause_failed_requirement:
  assumes "finite_native_source S su sr=Some P" "g\<in>set gs"
    "\<not>admission_goal_holds (positive_meaning (decode_finite_system P)) g
      (Target_Term (Whole_Artifact (decode_finite_object R)))"
  shows "\<not>finite_required_cause S su sr gs E gu gr G H root R"
proof
  assume accepted: "finite_required_cause S su sr gs E gu gr G H root R"
  have "admission_requirements_hold (positive_meaning (decode_finite_system P)) gs
    (Target_Term (Whole_Artifact (decode_finite_object R)))"
    by (rule finite_required_cause_all_requirements[OF assms(1) accepted])
  then show False using assms(2,3) unfolding admission_requirements_hold_def by blast
qed

text \<open>
  The original complete source and requirement family construct the policy
  before the candidate record is admitted. Cause validity cannot substitute a
  different accepting entry or scope. Failure of any original requirement
  excludes the record under the original source meaning. Adequacy of the full
  development requirement family, historical permission and enforcement of
  every workflow transition remain separate obligations.
\<close>

end
