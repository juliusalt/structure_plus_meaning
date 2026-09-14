theory Factor_Certified_Cause_Assessment
  imports Factor_Certified_Cause_Variants Boolean_Decision_Assessments
begin

definition certified_cause_core_scopes where
  "certified_cause_core_scopes G=(case generation_cause G of Finite_Whole C \<Rightarrow>
    finite_whole_judgment_readings C | _ \<Rightarrow> {||})"

definition certified_cause_judgment_report where
  "certified_cause_judgment_report X q=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    case q of (F,pu,pr,au,ar) \<Rightarrow>
      let programs=finite_native_package_readings F pu pr;
          apps=finite_application_readings F au ar;
          replays=finite_native_replay_readings H pu pr au ar root
      in (q,finite_native_judgment_environment F pu pr au ar,programs,apps,replays,
        fBex apps (\<lambda>((d,t),I,K). t=Finite_Target (Finite_Whole R)),
        finite_environment_included F H,
        map_option Finite_Whole (finite_data_syntax (finite_judgment_term F pu pr au ar))=Some (generation_cause G),
        fBall (finite_environment_uses F) (\<lambda>u. case u of None \<Rightarrow> True | Some a \<Rightarrow> octets_formed a)))"

definition certified_cause_judgment_decide where
  "certified_cause_judgment_decide (m::nat) payload report=(case report of
    (q,least,programs,apps,replays,literal,included,canonical,words) \<Rightarrow>
    case q of (F,pu,pr,au,ar) \<Rightarrow>
      if m=3 then {||} |\<in>| replays
      else (if m=8 then True else least=F) \<and> payload \<and> programs\<noteq>{||} \<and>
        (if m=9 then True else literal) \<and> (if m=10 then True else included) \<and>
        {||} |\<in>| replays \<and> (if m=6 then canonical else True) \<and>
        (if m=7 then words else True))"

lemma certified_cause_judgment_report_exact:
  "certified_cause_judgment_decide 0 (generation_payload G=Finite_Whole R)
    (certified_cause_judgment_report (E,gu,gr,G,H,root,R) (F,pu,pr,au,ar))=
    finite_certified_judgment_context F pu pr au ar G H root R"
proof -
  have literal_nonempty: "finite_literal_application_ready F au ar R \<Longrightarrow>
    finite_application_readings F au ar\<noteq>{||}"
    by (auto simp: finite_literal_application_ready_def)
  show ?thesis
    using literal_nonempty by (auto simp: certified_cause_judgment_decide_def certified_cause_judgment_report_def
      finite_certified_judgment_context_def finite_native_judgment_ready_def
      finite_literal_application_ready_def[symmetric] finite_native_replay_proves_def Let_def)
qed

definition certified_cause_report :: "certified_cause_subject \<Rightarrow> _" where
  "certified_cause_report X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    (finite_check_generation G E gu gr,generation_payload G=Finite_Whole R,
      fimage (certified_cause_judgment_report X) (certified_cause_core_scopes G)))"

definition certified_cause_decide where
  "certified_cause_decide (m::nat) report=(case report of (present,payload,rows) \<Rightarrow>
    if m=1 then present else if m=2 then rows\<noteq>{||}
    else if m=4 then False else if m=5 then True
    else (if m=3 \<or> m=11 then True else present) \<and>
      fBex rows (certified_cause_judgment_decide m payload))"

definition certified_cause_method where
  "certified_cause_method (m::nat) X=certified_cause_decide m (certified_cause_report X)"

lemma certified_cause_method_original:
  "certified_cause_method 0 X=certified_cause_direct X"
proof -
  have rows: "fBex (fimage (certified_cause_judgment_report (E,gu,gr,G,H,root,R)) Q)
      (certified_cause_judgment_decide 0 (generation_payload G=Finite_Whole R))=
    fBex Q (\<lambda>(F,pu,pr,au,ar). finite_certified_judgment_context F pu pr au ar G H root R)"
    for E gu gr G H root R Q
  proof -
    have each: "certified_cause_judgment_decide 0 (generation_payload G=Finite_Whole R)
        (certified_cause_judgment_report (E,gu,gr,G,H,root,R) q)=
      (case q of (F,pu,pr,au,ar) \<Rightarrow> finite_certified_judgment_context F pu pr au ar G H root R)" for q
    proof -
      obtain F pu pr au ar where q: "q=(F,pu,pr,au,ar)" by (cases q) auto
      show ?thesis by (simp only: q case_prod_conv certified_cause_judgment_report_exact)
    qed
    show ?thesis by (simp only: FSet.bex_simps(5) each)
  qed
  have calculated: "certified_cause_method 0 (E,gu,gr,G,H,root,R)=
      (finite_check_generation G E gu gr \<and> fBex (certified_cause_core_scopes G)
        (\<lambda>(F,pu,pr,au,ar). finite_certified_judgment_context F pu pr au ar G H root R))"
    for E gu gr G H root R
    by (simp only: certified_cause_method_def certified_cause_report_def certified_cause_decide_def
      case_prod_conv rows; simp)
  have direct: "certified_cause_direct (E,gu,gr,G,H,root,R)=
      (finite_check_generation G E gu gr \<and> fBex (certified_cause_core_scopes G)
        (\<lambda>(F,pu,pr,au,ar). finite_certified_judgment_context F pu pr au ar G H root R))"
    for E gu gr G H root R
    by (cases "finite_check_generation G E gu gr")
      (simp add: certified_cause_direct_def finite_certified_base_cause_def
        finite_generation_judgment_readings_def certified_cause_core_scopes_def)+
  obtain E gu gr G H root R where X: "X=(E,gu,gr,G,H,root,R)" by (cases X) auto
  show ?thesis by (simp only: X calculated direct)
qed

lemma certified_cause_original_exact:
  "certified_cause_method 0 X=certified_cause_holds X"
  by (simp only: certified_cause_method_original certified_cause_direct_exact)

definition certified_cause_condition where
  "certified_cause_condition f method X=boolean_decision_condition f certified_cause_holds method X"

definition certified_cause_family_condition where
  "certified_cause_family_condition f method problem=(case problem of (seed,w) \<Rightarrow>
    (\<exists>c X. (c,Some X) |\<in>| certified_cause_family seed 0 \<and> certified_cause_holds X) \<and>
    (\<forall>(c,X)\<in>fset (certified_cause_family seed w).
      optional_decision_condition f certified_cause_holds method X))"

definition certified_cause_family_assessment where
  "certified_cause_family_assessment m problem=(case problem of (seed,w) \<Rightarrow>
    decision_family_assessment certified_cause_report (certified_cause_decide 0) (certified_cause_decide m)
      (certified_cause_covered seed,certified_cause_family seed w))"

lemma certified_cause_read_decisions:
  "certified_cause_decide 0 \<circ> certified_cause_report=certified_cause_holds"
  "certified_cause_decide m \<circ> certified_cause_report=certified_cause_method m"
  by (rule ext; simp only: comp_apply certified_cause_method_def[symmetric] certified_cause_original_exact)+

lemma certified_cause_reference_function:
  "certified_cause_method 0=certified_cause_holds"
  by (rule ext) (rule certified_cause_original_exact)

theorem certified_cause_family_assessment_exact:
  "decision_family_inspect (certified_cause_family_assessment m X) f=
    certified_cause_family_condition f (certified_cause_method m) X"
  by (cases X) (simp only: certified_cause_family_assessment_def case_prod_conv
    decision_family_assessment_exact certified_cause_read_decisions certified_cause_reference_function
    decision_family_condition_def certified_cause_family_condition_def certified_cause_covered_exact)

text \<open>
  Complete scope, least environment, native package, application and replay
  readings precede every method decision. The original certified-cause relation
  determines soundness and completeness through the shared assessment contract.
  Controls omit particular checks or restrict admitted presentations. Missing
  distinctions remain visible in the native comparison and its repair report.
\<close>

end
