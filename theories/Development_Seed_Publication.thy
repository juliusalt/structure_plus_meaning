theory Development_Seed_Publication
  imports Development_Seed_Verification Development_Decision_Generations RRA_Formed_Snapshot_Transactions
    Parallel_Computed_Preparation
begin

section \<open>The seeded development publishes certified generations by transactions\<close>

text \<open>
  The published state of the seeded development starts from its incumbents: one base generation
  for each problem, at the problem's locus, recorded with its cause certified under the policy of
  its family's acceptance by the checked context. The round's decisions are published beside them: the
  selection of the next problems at the development's selection locus, and the issue of every issued
  request at its problem's issue locus, each certified under the policy that lists its payload. An issue
  is recorded beside the incumbent its request was made against and cites that incumbent and the
  selection. For every issued request, the unchanged answer is recorded beside the issue, cites the
  issue, whose predecessor the incumbent is, is certified in the same way and is published by the
  transaction that expects the incumbent; it replaces it. The answer with the reversed table, admitted against the same incumbent,
  is then published by the same kind of transaction and conflicts, because the locus now holds the first
  answer. The two answers present the same payload, because a payload carries the names it uses and the
  reversal is a correspondence of tables. Publishing the selection, every issue and the unchanged answers
  of all issued requests one after another applies every transaction, since each writes only its own
  locus.
\<close>

type_synonym development_seed_incumbent = "development_problem\<times>
  (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option"

definition development_seed_incumbents_with ::
    "development_payload_judge \<Rightarrow> development_problem list \<Rightarrow> development_seed_incumbent list" where
  "development_seed_incumbents_with judge ps=
    Parallel.map (\<lambda>p. (p,development_incumbent_with judge development_seed_state p)) ps"

definition development_seed_snapshot :: "development_seed_incumbent list \<Rightarrow> finite_snapshot option" where
  "development_seed_snapshot xs=map_option fset_of_list (those (map (\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) xs))"

definition development_seed_incumbent_of :: "development_seed_incumbent list \<Rightarrow> development_request \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_seed_incumbent_of xs r=Option.bind (find (\<lambda>(p,x). p=fst r) xs) snd"

section \<open>The decisions of the round\<close>

text \<open>
  The round's decisions are the ones the loop makes on the seeded development: its native selection of
  the ready problems and the requests it issues for the selected leaves of the seeded library, each with
  the library reading it rested on (\<open>development_loop_decisions_made\<close>).
\<close>

type_synonym development_seed_decisions =
  "development_problem list\<times>(development_request\<times>(nat\<times>development_problem) fset fset) list"

definition development_seed_decisions :: "development_problem fset \<Rightarrow> development_seed_decisions option" where
  "development_seed_decisions answered=map_option (\<lambda>(loop,xs,issues). (xs,issues))
     (development_loop_decisions development_seed_library development_seed_request_of (development_seed_loop_state answered))"

definition development_seed_issue_using :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow>
    development_seed_incumbent list \<Rightarrow> development_problem list \<Rightarrow> development_request \<Rightarrow>
    (nat\<times>development_problem) fset fset \<Rightarrow>
    (local_address option finite_artifact_environment\<times>development_generation_row list\<times>finite_generation) option" where
  "development_seed_issue_using construct judge xs selected r reading=Option.bind (development_seed_incumbent_of xs r)
     (development_recorded_issue_using construct judge (fst (snd development_seed_state)) (Some selected) r reading)"

definition development_seed_answer_using :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow>
    isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow>
    (local_address option finite_artifact_environment\<times>development_generation_row list\<times>finite_generation) option \<Rightarrow>
    finite_generation option" where
  "development_seed_answer_using construct judge S' r issued=Option.bind issued (\<lambda>(B,rows,Q).
     map_option (\<lambda>(B',u',G). G) (development_answer_using construct judge development_seed_state r S' B rows))"

type_synonym development_seed_publication_row = "finite_generation option\<times>finite_generation option\<times>
  finite_generation option\<times>finite_transaction_result option list\<times>bool"

text \<open>
  A row admits the issue of one request and publishes its two answers in turn over the incumbent both
  were judged against, starting from the published incumbents.
\<close>

definition development_seed_publication_row :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow>
    development_seed_incumbent list \<Rightarrow> development_problem list \<Rightarrow> finite_snapshot option \<Rightarrow>
    development_request\<times>(nat\<times>development_problem) fset fset \<Rightarrow> development_seed_publication_row" where
  "development_seed_publication_row construct judge xs selected S0 issue=(case issue of (r,reading) \<Rightarrow>
     let I=map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r);
       issued=development_seed_issue_using construct judge xs selected r reading;
       Q=map_option (\<lambda>(B,rows,Q). Q) issued;
       G=development_seed_answer_using construct judge development_seed_state r issued;
       H=development_seed_answer_using construct judge development_seed_renamed r issued
     in (Q,G,H,(case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S [(None,Q),(I,G),(I,H)]),
       map_option generation_payload G=map_option generation_payload H))"

type_synonym development_seed_publication = "finite_snapshot option\<times>finite_generation option\<times>
  development_seed_publication_row list\<times>finite_transaction_result option list"

definition development_seed_publication_from :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow>
    development_seed_decisions option \<Rightarrow> development_seed_publication" where
  "development_seed_publication_from construct judge decisions=(let
     xs=development_seed_incumbents_with judge development_seed_problems;
     S0=development_seed_snapshot xs in
     case decisions of None \<Rightarrow> (S0,None,[],[])
     | Some (selected,issues) \<Rightarrow> (let
         Sel=map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge (fst (snd development_seed_state))
           selected (finite_enumerated_environment [] []) []);
         rows=Parallel.map (development_seed_publication_row construct judge xs selected S0) issues;
         incumbents=map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)) issues in
       (S0,Sel,rows,case S0 of None \<Rightarrow> []
         | Some S \<Rightarrow> finite_locus_publications S ((None,Sel)#map (\<lambda>(Q,G,H,results,equal). (None,Q)) rows@
             map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip incumbents rows)))))"

definition development_seed_publication :: "development_problem fset \<Rightarrow> development_seed_publication" where
  "development_seed_publication answered=development_seed_publication_from finite_construct_generation_record
    development_payload_judgment (development_seed_decisions answered)"

section \<open>The chain of a round records with known readings\<close>

text \<open>
  Every incumbent of the report is recorded in an environment of its own, every issue in its incumbent's
  environment after the selection, and every answer in its issue's environment. Every reading a recording
  cites is one the report has just recorded, so the report records with the known constructor and reads
  no predecessor back (\<open>development_recorded_issue_using_known\<close>, \<open>development_answer_using_known\<close>).
\<close>

lemma development_seed_incumbent_of_recorded:
  assumes found: "development_seed_incumbent_of (development_seed_incumbents_with judge ps) r=Some (B,u,I)"
  shows "finite_environment_formed B" "finite_check_generation I B u []"
proof -
  obtain y where located: "find (\<lambda>(p,x). p=fst r) (development_seed_incumbents_with judge ps)=Some y"
    and present: "snd y=Some (B,u,I)"
    using found by (auto simp: development_seed_incumbent_of_def bind_eq_Some_conv)
  obtain i where index: "i<length (development_seed_incumbents_with judge ps)"
    and at: "y=development_seed_incumbents_with judge ps!i"
    using located by (auto simp: find_Some_iff)
  have "y\<in>set (development_seed_incumbents_with judge ps)" using index at by simp
  then obtain p where "y=(p,development_incumbent_with judge development_seed_state p)"
    by (auto simp: development_seed_incumbents_with_def)
  then have built: "development_incumbent_with judge development_seed_state p=Some (B,u,I)" using present by simp
  show "finite_environment_formed B" "finite_check_generation I B u []"
    by (rule development_incumbent_with_recorded[OF built])+
qed

lemma development_seed_publication_row_known:
  "development_seed_publication_row finite_construct_known_original_generation judge
      (development_seed_incumbents_with judge ps) selected S0=
    development_seed_publication_row finite_construct_generation_record judge
      (development_seed_incumbents_with judge ps) selected S0"
proof (rule ext)
  fix issue :: "development_request\<times>(nat\<times>development_problem) fset fset"
  let ?xs="development_seed_incumbents_with judge ps"
  obtain r reading where shape: "issue=(r,reading)" by (cases issue) auto
  have issued: "development_seed_issue_using finite_construct_known_original_generation judge ?xs selected r reading=
      development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading"
  proof (cases "development_seed_incumbent_of ?xs r")
    case None
    then show ?thesis by (simp add: development_seed_issue_using_def)
  next
    case (Some incumbent)
    obtain B u I where found: "development_seed_incumbent_of ?xs r=Some (B,u,I)" using Some by (cases incumbent) auto
    note recorded=development_seed_incumbent_of_recorded[OF found]
    show ?thesis
      by (simp add: development_seed_issue_using_def found development_recorded_issue_using_known[OF recorded]
        development_recorded_issue_with_def)
  qed
  have answered: "development_seed_answer_using finite_construct_known_original_generation judge S' r
      (development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading)=
    development_seed_answer_using finite_construct_generation_record judge S' r
      (development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading)" for S'
  proof (cases "development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading")
    case None
    then show ?thesis by (simp add: development_seed_answer_using_def)
  next
    case (Some result)
    obtain B2 rows Q where recorded: "development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading=
        Some (B2,rows,Q)" using Some by (cases result) auto
    obtain incumbent where found: "development_seed_incumbent_of ?xs r=Some incumbent"
      and issue: "development_recorded_issue_with judge (fst (snd development_seed_state)) (Some selected) r reading incumbent=
        Some (B2,rows,Q)"
      using recorded by (auto simp: development_seed_issue_using_def development_recorded_issue_with_def bind_eq_Some_conv)
    obtain B u I where shape: "incumbent=(B,u,I)" by (cases incumbent) auto
    note known=development_recorded_issue_recorded[OF issue[unfolded shape]]
    show ?thesis
      by (simp add: recorded development_seed_answer_using_def development_answer_using_known[OF known]
        development_answer_with_def)
  qed
  show "development_seed_publication_row finite_construct_known_original_generation judge ?xs selected S0 issue=
      development_seed_publication_row finite_construct_generation_record judge ?xs selected S0 issue"
    by (simp add: shape development_seed_publication_row_def issued answered Let_def split: option.split)
qed

lemma development_seed_publication_from_known:
  "development_seed_publication_from finite_construct_known_original_generation judge decisions=
    development_seed_publication_from finite_construct_generation_record judge decisions"
  by (simp add: development_seed_publication_from_def development_seed_publication_row_known Let_def
    split: option.splits prod.splits)

section \<open>Each payload is judged once\<close>

text \<open>
  The judgment of a payload is a function of its presentation, so the report judges each family of a
  problem and each decision's payload once, in parallel, and every generation whose payload has that
  presentation is recorded with the one judgment. An answer whose family differs is judged when it is
  recorded. The report is unchanged, because the prepared function is the judgment itself; the decisions
  are made once and read by both.
\<close>

definition development_seed_family_keys :: "finite_factor_term list" where
  "development_seed_family_keys=List.map_filter (\<lambda>p. map_option snd (development_incumbent_key development_seed_state p))
    development_seed_problems"

definition development_seed_decision_keys :: "development_seed_decisions option \<Rightarrow> finite_factor_term list" where
  "development_seed_decision_keys decisions=(case decisions of None \<Rightarrow> []
     | Some (selected,issues) \<Rightarrow> development_selection_payload (fst (snd development_seed_state)) selected#
         map (\<lambda>(r,reading). development_issue_payload (fst (snd development_seed_state)) r reading) issues)"

declare development_seed_publication_def [code del]

lemma development_seed_publication_prepared [code]:
  "development_seed_publication answered=(let decisions=development_seed_decisions answered in
     development_seed_publication_from finite_construct_known_original_generation
       (parallel_computed_function development_payload_judgment
         (development_seed_family_keys@development_seed_decision_keys decisions)) decisions)"
  by (simp only: development_seed_publication_def development_seed_publication_from_known
    parallel_computed_function_exact Let_def)

section \<open>The report is presented through the presentations of its notions\<close>

definition development_seed_publication_data :: "development_seed_publication \<Rightarrow> finite_factor_term" where
  "development_seed_publication_data=finite_pair_presentation (finite_option_presentation finite_snapshot_value)
    (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
      (finite_pair_presentation (finite_sequence_presentation
        (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
          (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
            (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
              (finite_pair_presentation (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value))
                finite_boolean_data)))))
        (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value))))"

lemma development_seed_publication_data_injective [intro]: "inj development_seed_publication_data"
  unfolding development_seed_publication_data_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective) blast+

definition development_seed_publication_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_publication_value answered=
    development_seed_publication_data (development_seed_publication answered)"

text \<open>
  The expected outcomes follow from the kinds of transaction, not from the seeded values: in every
  row the issue is admitted, the first publication applies and the second conflicts with its complete
  observation, the two payloads of a request are equal, and the sequential publication applies all of
  them. Every generation's cause is a certified call of the policy that lists its payload; an incumbent's
  and an answer's policy is constructed only for a family of entities of its checked context, and a
  decision's only for the decision the loop made. The verdict that admitted an answer and the packet
  that admitted the selection are recorded in the development's history, not in the published
  generations.
\<close>

end
