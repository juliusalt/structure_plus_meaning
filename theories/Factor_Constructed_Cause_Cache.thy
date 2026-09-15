theory Factor_Constructed_Cause_Cache
  imports Factor_Constructed_Judgment_Sources Factor_Digit_Replay_Known_Reports Exact_Cache_Readings
begin

fun target_judgment_scopes where
  "target_judgment_scopes (Finite_Whole C)=finite_whole_judgment_readings C"
| "target_judgment_scopes (Finite_Anchor C r)={||}"

definition constructed_cause_scope_cache where
  "constructed_cause_scope_cache E pu pr au ar=concat (map (\<lambda>entry. case entry of None \<Rightarrow> []
    | Some (J,C) \<Rightarrow> [(Finite_Whole C,{|(J,pu,pr,au,ar)|})])
      (constructed_judgment_sources E pu pr au ar))"

theorem constructed_cause_scope_cache_lookup:
  assumes lookup: "map_of (constructed_cause_scope_cache E pu pr au ar) target=Some scopes"
  shows "scopes=target_judgment_scopes target"
proof -
  have member: "(target,scopes)\<in>set (constructed_cause_scope_cache E pu pr au ar)"
    by (rule map_of_SomeD[OF lookup])
  obtain J C where source: "Some (J,C)\<in>set (constructed_judgment_sources E pu pr au ar)"
    and fields: "target=Finite_Whole C" "scopes={|(J,pu,pr,au,ar)|}"
    using member by (auto simp: constructed_cause_scope_cache_def split: option.splits prod.splits)
  show ?thesis using constructed_judgment_sources_scopes[OF source]
    by (simp only: fields target_judgment_scopes.simps)
qed

definition constructed_cause_scopes where
  "constructed_cause_scopes E pu pr au ar target=exact_cache_read target_judgment_scopes
    (map_of (constructed_cause_scope_cache E pu pr au ar)) target"

theorem constructed_cause_scopes_exact:
  "constructed_cause_scopes E pu pr au ar target=target_judgment_scopes target"
  unfolding constructed_cause_scopes_def
  by (rule exact_cache_read_correct; rule constructed_cause_scope_cache_lookup; assumption)

definition constructed_source_cause_report ::
  "local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> certified_cause_subject \<Rightarrow> _" where
  "constructed_source_cause_report pu pr au ar X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    (finite_check_generation G E gu gr,generation_payload G=Finite_Whole R,
      fimage (certified_cause_judgment_report X)
        (constructed_cause_scopes H pu pr au ar (generation_cause G))))"

theorem constructed_source_cause_report_exact:
  "constructed_source_cause_report pu pr au ar X=certified_cause_report X"
  by (cases X) (simp add: constructed_source_cause_report_def certified_cause_report_def
      constructed_cause_scopes_exact certified_cause_core_scopes_def split: finite_exact_target.splits)

declare digit_replay_cause_report_known_code[code del]

theorem digit_replay_constructed_cause_code [code]:
  "digit_replay_cause_report X result=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    map_option (\<lambda>Y. let readings=constructed_source_cause_report pu pr au ar Y
      in (Y,readings,certified_cause_decide 0 readings)) (digit_replay_cause_subject X result))"
  by (cases X) (simp add: digit_replay_cause_report_shared_code constructed_source_cause_report_exact)

text \<open>The existing exact-cache contract is instantiated by actual complete
  quotations. A cache entry applies only to an equal actual cause target; a
  miss executes the original reader. Every original judgment-report field,
  including least-environment, canonical-order and byte-word conditions, is
  still computed. The whole report equation holds for arbitrary source sites,
  altered generations, unavailable inputs and malformed complete subjects.\<close>

end
