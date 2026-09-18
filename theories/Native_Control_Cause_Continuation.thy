theory Native_Control_Cause_Continuation
  imports Native_Control_Reviewed_Receiving Factor_Certificate_Policy_Continuation
begin

definition admitted_guard_certificate_records where
  "admitted_guard_certificate_records body adapter target witness R H l predecessors =
    map_option (Parallel.map (\<lambda>(i,source). (i,case source of None \<Rightarrow> None
      | Some (d,K,v) \<Rightarrow> certificate_policy_attempt K v d witness R H l predecessors)))
      (admitted_guard_install body adapter target)"

lemma admitted_guard_certificate_fields:
  assumes result: "admitted_guard_certificate_records body adapter target witness R H l predecessors=Some results"
    and member: "(i,Some ((A,M,root,G,au,I,W,B),(F,fu,g)))\<in>set results"
  obtains installed d K v p where "admitted_guard_install body adapter target=Some installed"
    "(i,Some (d,K,v))\<in>set installed" "witness=Some p"
    "certificate_policy_record K v d p R H l predecessors=Some ((A,M,root,G,au,I,W,B),(F,fu,g))"
  using result member
  by (auto simp: admitted_guard_certificate_records_def
    certificate_policy_attempt_def split: option.splits)

theorem admitted_guard_certificate_truth:
  assumes result: "admitted_guard_certificate_records body adapter target witness R H l predecessors=Some results"
    and member: "(i,Some ((A,M,root,G,au,I,W,B),(F,fu,g)))\<in>set results"
  shows "\<exists>r s. complete_data_quoted_at (decode_finite_object R) r
    (decode_finite_term (syntax_judgment_data s)) \<and> syntax_judgment_truth s"
proof (rule admitted_guard_certificate_fields[OF result member])
  fix installed d K v p
  assume installed: "admitted_guard_install body adapter target=Some installed"
    and original: "(i,Some (d,K,v))\<in>set installed"
    and witness: "witness=Some p"
    and certified: "certificate_policy_record K v d p R H l predecessors=
      Some ((A,M,root,G,au,I,W,B),(F,fu,g))"
  show ?thesis by (rule admitted_guard_original_policy_cause[OF installed original
    certificate_policy_record_original_cause[OF certified]])
qed

lemma admitted_guard_certificate_refusals:
  "admitted_guard_certificate_records absent_development_report adapter target witness R H l rows=None"
  "admitted_guard_certificate_records body absent_development_report target witness R H l rows=None"
  "admitted_guard_certificate_records body adapter absent_development_report witness R H l rows=None"
  by (simp_all add: admitted_guard_certificate_records_def)

lemma admitted_guard_missing_certificate:
  "admitted_guard_certificate_records body adapter target None R H l rows=
    map_option (map (\<lambda>(i,source). (i,None))) (admitted_guard_install body adapter target)"
proof -
  have mapped: "map (\<lambda>(i,source). (i,case source of None \<Rightarrow> None
      | Some (d,K,v) \<Rightarrow> certificate_policy_attempt K v d None R H l rows)) xs =
    map (\<lambda>(i,source). (i,None)) xs" for xs :: "(nat \<times>
      (local_address option definition_site \<times> local_address option finite_artifact_environment \<times>
        local_address option) option) list"
    by (induction xs) (auto simp: certificate_policy_attempt_def split: option.splits prod.splits)
  show ?thesis by (cases "admitted_guard_install body adapter target")
    (simp_all only: admitted_guard_certificate_records_def Parallel.map_def option.simps mapped)
qed

text \<open>This candidate continuation binds every successful cause to the
  actual installed guard obtained from all three original native reports.
  The complete source/certificate/replay requirements and original history
  prerequisites are unchanged. This theory supplies no actual certificate,
  executed cause, governing policy authorization or normative handoff.\<close>

end
