theory RRA_Complete_Environment_Agreement
  imports RRA_Finite_Environment_Preservation
begin

theorem environment_agreement_included:
  assumes formed: "environment_formed E"
    and agreement: "environment_agrees_on E F (environment_uses E)"
  shows "environment_included E F"
proof -
  have artifacts: "artifact_at E u R \<Longrightarrow> artifact_at F u R" for u R
    using agreement by (auto simp: environment_agrees_on_def environment_uses_def rel_dom_def artifact_at_def)
  have bindings: "binds_slot E u k v \<Longrightarrow> binds_slot F u k v" for u k v
    using agreement environment_binding_uses(1)[OF formed]
    by (auto simp: environment_agrees_on_def)
  show ?thesis using artifacts bindings
    by (auto simp: environment_included_def artifact_at_def binds_slot_def)
qed

lemma finite_environment_agreement_original:
  "finite_environment_agrees_on E F U=environment_agrees_on
    (decode_finite_environment E) (decode_finite_environment F) (fset U)"
  by (simp only: finite_environment_agrees_on_correct environment_agrees_on_def; blast)

theorem finite_environment_agreement_included:
  assumes formed: "finite_environment_formed E"
    and agreement: "finite_environment_agrees_on E F (finite_environment_uses E)"
  shows "finite_environment_included E F"
  by (simp only: finite_environment_included_correct;
    rule environment_agreement_included)
    (use formed agreement in \<open>simp_all only: finite_environment_formed_correct
      finite_environment_agreement_original finite_environment_uses_correct\<close>)

text \<open>
  Complete agreement on every original use already entails original inclusion
  when the source environment is formed. Constructor contracts can derive this
  judgment instead of assuming a second primitive preservation condition.
\<close>

end
