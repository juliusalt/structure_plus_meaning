theory Factor_Prepared_Cause_Scope_Reports
  imports Factor_Constructed_Cause_Cache Optional_Constructed_Caches
begin

definition complete_cause_scope_report where
  "complete_cause_scope_report H root R target q=(case q of (F,pu,pr,au,ar) \<Rightarrow>
    let programs=finite_native_package_readings F pu pr;
        apps=finite_application_readings F au ar;
        replays=finite_native_replay_readings H pu pr au ar root
    in (q,finite_native_judgment_environment F pu pr au ar,programs,apps,replays,
      fBex apps (\<lambda>((d,t),I,K). t=Finite_Target (Finite_Whole R)),
      finite_environment_included F H,
      map_option Finite_Whole (finite_data_syntax (finite_judgment_term F pu pr au ar))=Some target,
      fBall (finite_environment_uses F) (\<lambda>u. case u of None \<Rightarrow> True | Some a \<Rightarrow> octets_formed a)))"

lemma complete_cause_scope_report_exact:
  "complete_cause_scope_report H root R (generation_cause G) q=
    certified_cause_judgment_report (E,gu,gr,G,H,root,R) q"
  by (simp only: complete_cause_scope_report_def certified_cause_judgment_report_def case_prod_conv)

definition complete_cause_scope_reports where
  "complete_cause_scope_reports H root R target=
    fimage (complete_cause_scope_report H root R target) (target_judgment_scopes target)"

lemma complete_cause_scope_reports_exact:
  "complete_cause_scope_reports H root R (generation_cause G)=
    fimage (certified_cause_judgment_report (E,gu,gr,G,H,root,R)) (certified_cause_core_scopes G)"
proof -
  have report: "complete_cause_scope_report H root R (generation_cause G)=
      certified_cause_judgment_report (E,gu,gr,G,H,root,R)"
    by (rule ext; rule complete_cause_scope_report_exact)
  have scopes: "target_judgment_scopes (generation_cause G)=certified_cause_core_scopes G"
    by (cases "generation_cause G") (simp_all add: certified_cause_core_scopes_def)
  show ?thesis by (simp only: complete_cause_scope_reports_def report scopes)
qed

definition constructed_scope_report_key where
  "constructed_scope_report_key entry=Finite_Whole (snd entry)"

definition constructed_scope_report_value where
  "constructed_scope_report_value H pu pr au ar root R entry=(case entry of (J,C) \<Rightarrow>
    {|complete_cause_scope_report H root R (Finite_Whole C) (J,pu,pr,au,ar)|})"

lemma constructed_scope_report_entry_exact:
  "Some entry\<in>set (constructed_judgment_sources H pu pr au ar) \<Longrightarrow>
    constructed_scope_report_value H pu pr au ar root R entry=
      complete_cause_scope_reports H root R (constructed_scope_report_key entry)"
  by (cases entry)
    (simp add: constructed_scope_report_key_def constructed_scope_report_value_def
      complete_cause_scope_reports_def constructed_judgment_sources_scopes)

definition prepared_complete_cause_scopes where
  "prepared_complete_cause_scopes H pu pr au ar root R=(let cache=optional_constructed_cache
      constructed_scope_report_key (constructed_scope_report_value H pu pr au ar root R)
      (constructed_judgment_sources H pu pr au ar)
    in exact_cache_read (complete_cause_scope_reports H root R) (map_of cache))"

theorem prepared_complete_cause_scopes_exact:
  "prepared_complete_cause_scopes H pu pr au ar root R target=
    complete_cause_scope_reports H root R target"
  unfolding prepared_complete_cause_scopes_def Let_def
  by (rule optional_constructed_cache_exact; rule constructed_scope_report_entry_exact; assumption)

definition cause_report_with_scopes :: "_ \<Rightarrow> certified_cause_subject \<Rightarrow> _" where
  "cause_report_with_scopes read_scopes X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    (finite_check_generation G E gu gr,generation_payload G=Finite_Whole R,read_scopes (generation_cause G)))"

lemma cause_report_with_scopes_exact:
  "cause_report_with_scopes (complete_cause_scope_reports H root R) (E,gu,gr,G,H,root,R)=
    certified_cause_report (E,gu,gr,G,H,root,R)"
  by (simp only: cause_report_with_scopes_def certified_cause_report_def case_prod_conv
      complete_cause_scope_reports_exact[where E=E and gu=gu and gr=gr])

definition replay_cause_with_scopes where
  "replay_cause_with_scopes read_scopes X result=map_option (\<lambda>Y.
    let readings=cause_report_with_scopes read_scopes Y
    in (Y,readings,certified_cause_decide 0 readings)) (digit_replay_cause_subject X result)"

lemma replay_cause_with_scopes_exact:
  "replay_cause_with_scopes (complete_cause_scope_reports E root R)
      (input,l,rows,E,pu,pr,au,ar,root,R) result=
    digit_replay_cause_report (input,l,rows,E,pu,pr,au,ar,root,R) result"
  by (cases result)
    (simp_all add: replay_cause_with_scopes_def digit_replay_cause_report_shared_code
      digit_replay_cause_subject_def cause_report_with_scopes_exact split: prod.splits)

definition prepared_replay_cause_reader where
  "prepared_replay_cause_reader X=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    replay_cause_with_scopes (prepared_complete_cause_scopes E pu pr au ar root R) X)"

theorem prepared_replay_cause_reader_exact:
  "prepared_replay_cause_reader X=digit_replay_cause_report X"
proof -
  have scopes: "prepared_complete_cause_scopes E pu pr au ar root R=complete_cause_scope_reports E root R"
    for E pu pr au ar root R
    by (rule ext; rule prepared_complete_cause_scopes_exact)
  show ?thesis by (rule ext; cases X)
    (simp add: prepared_replay_cause_reader_def scopes replay_cause_with_scopes_exact split: prod.splits)
qed

text \<open>The three actual constructed quotation subjects prepare their
  complete source readings once. Each cached scope row includes its actual
  least environment, package, application and replay readings, target match,
  inclusion, canonical quotation comparison and word condition. Every changed
  generation still supplies its own presence and payload checks. Other cause
  targets execute the original complete scope reader.\<close>

end
