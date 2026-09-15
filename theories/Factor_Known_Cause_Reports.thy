theory Factor_Known_Cause_Reports
  imports Factor_Certified_Cause_Assessment Factor_Finite_Known_Judgment_Scopes
begin

definition certified_quoted_judgment_report where
  "certified_quoted_judgment_report J pu pr au ar H root R=(
    let programs=finite_native_package_readings J pu pr;
        apps=finite_application_readings J au ar;
        replays=finite_native_replay_readings H pu pr au ar root
    in ((J,pu,pr,au,ar),J,programs,apps,replays,
      fBex apps (\<lambda>((d,t),I,K). t=Finite_Target (Finite_Whole R)),True,True,
      fBall (finite_environment_uses J) (\<lambda>u. case u of None \<Rightarrow> True | Some a \<Rightarrow> octets_formed a)))"

theorem certified_quoted_judgment_report_exact:
  assumes quoted: "finite_native_judgment_quote H pu pr au ar=Some (J,C)"
    and cause: "generation_cause G=Finite_Whole C"
  shows "certified_cause_judgment_report (E,gu,gr,G,H,root,R) (J,pu,pr,au,ar)=
    certified_quoted_judgment_report J pu pr au ar H root R"
proof -
  have least: "finite_native_judgment_environment J pu pr au ar=J"
    using finite_native_judgment_quote_correct(3)[OF quoted]
    by (simp only: finite_native_judgment_environment_correct[symmetric]
        decode_finite_environment_injective)
  have included: "finite_environment_included J H"
    using finite_native_judgment_quote_correct(4)[OF quoted]
    by (simp only: finite_environment_included_correct)
  have built: "finite_data_syntax (finite_judgment_term J pu pr au ar)=Some C"
    using quoted by (simp only: finite_native_judgment_quote_result; blast)
  show ?thesis by (simp add: certified_cause_judgment_report_def
    certified_quoted_judgment_report_def least included built cause)
qed

definition certified_cause_report_at_source where
  "certified_cause_report_at_source pu pr au ar X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    case finite_native_judgment_quote H pu pr au ar of None \<Rightarrow> certified_cause_report X
    | Some (J,C) \<Rightarrow> if generation_cause G=Finite_Whole C then
        (finite_check_generation G E gu gr,generation_payload G=Finite_Whole R,
          {|certified_quoted_judgment_report J pu pr au ar H root R|})
      else certified_cause_report X)"

theorem certified_cause_report_at_source_exact:
  "certified_cause_report_at_source pu pr au ar X=certified_cause_report X"
proof -
  obtain E gu gr G H root R where shape: "X=(E,gu,gr,G,H,root,R)" by (cases X) auto
  show ?thesis
  proof (cases "finite_native_judgment_quote H pu pr au ar")
    case None
    then show ?thesis by (simp add: shape certified_cause_report_at_source_def)
  next
    case (Some pair)
    obtain J C where pair: "pair=(J,C)" by (cases pair) auto
    have quoted: "finite_native_judgment_quote H pu pr au ar=Some (J,C)" using Some pair by simp
    show ?thesis
    proof (cases "generation_cause G=Finite_Whole C")
      case False
      then show ?thesis by (simp add: shape certified_cause_report_at_source_def quoted)
    next
      case True
      have scopes: "finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
        by (rule finite_native_judgment_quote_scopes[OF quoted])
      show ?thesis by (simp add: shape certified_cause_report_at_source_def quoted True
        certified_cause_report_def certified_cause_core_scopes_def scopes
        certified_quoted_judgment_report_exact[OF quoted True])
    qed
  qed
qed

text \<open>The shortcut is conditional on an actual successful native quotation
  and equality with the generation's actual cause. Whole-quotation uniqueness
  establishes the complete scope family. The quotation contracts also establish
  its least environment, inclusion and canonical syntax. Generation presence,
  payload equality, every program, application and replay reading, literal
  target and byte-word condition remain the original computed fields. Other
  causes use their original complete reader. The equation holds for arbitrary
  subjects and sites, including altered environments and absent generations.\<close>

end
