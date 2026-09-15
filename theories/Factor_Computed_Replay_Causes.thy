theory Factor_Computed_Replay_Causes
  imports Factor_Prepared_Replay_Assessments Prepared_Computed_Functions
begin

definition replay_cause_value_key where
  "replay_cause_value_key result=(case result of ((n,A),u,G,J,C) \<Rightarrow> (u,G,A))"

definition replay_cause_preparation_keys where
  "replay_cause_preparation_keys variants=concat (map (\<lambda>(method,results).
    case Option.bind (finite_singleton_option results) (map_option replay_cause_value_key) of
      None \<Rightarrow> [] | Some key \<Rightarrow> [key]) variants)"

definition replay_cause_cache_keys where
  "replay_cause_cache_keys (mode::nat) variants=(let keys=replay_cause_preparation_keys variants
    in if mode=0 then rev keys else take 1 keys)"

definition replay_cause_components where
  "replay_cause_components read_scopes X key=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    case key of (u,G,A) \<Rightarrow>
      let readings=cause_report_with_scopes read_scopes (A,u,[],G,E,root,R)
      in (readings,certified_cause_decide 0 readings))"

definition replay_cause_from_components where
  "replay_cause_from_components evaluate X result=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    map_option (\<lambda>value. case value of ((n,A),u,G,J,C) \<Rightarrow>
      let components=evaluate (replay_cause_value_key value)
      in ((A,u,[],G,E,root,R),fst components,snd components)) result)"

lemma replay_cause_components_exact:
  "replay_cause_from_components (replay_cause_components read_scopes X) X result=
    replay_cause_with_scopes read_scopes X result"
  by (cases X; cases result)
    (simp_all add: replay_cause_from_components_def replay_cause_components_def
      replay_cause_value_key_def replay_cause_with_scopes_def digit_replay_cause_subject_def
      Let_def split: prod.splits)

definition prepared_computed_replay_cause_reader where
  "prepared_computed_replay_cause_reader mode variants X=(case X of (input,l,rows,E,pu,pr,au,ar,root,R) \<Rightarrow>
    let scopes=prepared_complete_cause_scopes E pu pr au ar root R;
      evaluate=prepared_computed_function (replay_cause_components scopes X) (replay_cause_cache_keys mode variants)
    in replay_cause_from_components evaluate X)"

theorem prepared_computed_replay_cause_reader_exact:
  "prepared_computed_replay_cause_reader mode variants X=prepared_replay_cause_reader X"
  by (rule ext; cases X)
    (simp add: prepared_computed_replay_cause_reader_def prepared_computed_function_exact
      prepared_replay_cause_reader_def replay_cause_components_exact Let_def split: prod.splits)

definition computed_replay_assessor where
  "computed_replay_assessor mode context=(case context of (X,reference,variants) \<Rightarrow>
    replay_assessment_with_reader (prepared_computed_replay_cause_reader mode variants X) context)"

theorem computed_replay_assessor_exact:
  "computed_replay_assessor mode context=prepared_replay_assessor context"
  by (cases "context")
    (simp add: computed_replay_assessor_def prepared_replay_assessor_def
      prepared_computed_replay_cause_reader_exact split: prod.splits)

text \<open>The key contains exactly the returned use, generation and material
  read by the original cause computation. Allocation counters, supplied
  judgment fields and supplied quotation fields remain in every original
  candidate result; the original cause subject does not read them. The full
  cause subject is rebuilt from the actual result, while its complete readings
  and decision can be reused. Both preparation choices evaluate actual keys,
  retain full results and execute the original function on every cache miss.
  Singleton selection only chooses preparation keys and imposes no assumption
  that an arbitrary supplied context contains singleton result families.\<close>

end
