theory Development_Seed_Publication
  imports Development_Seed_Verification Development_Publication
begin

section \<open>The seeded development publishes admitted answers by transactions\<close>

text \<open>
  The published state of the seeded development starts from its incumbents: one base generation
  for each problem, at the problem's locus. For every issued request, the unchanged answer is
  published by the transaction that expects the incumbent the request was issued against, and it
  replaces that incumbent. The answer with the reversed table, admitted against the same
  incumbent, is then published by the same kind of transaction and conflicts, because the locus
  now holds the first answer: both answers are admitted generations of the history, and one is
  selected. The two answers present the same payload, because a payload carries the names it uses
  and the reversal is a correspondence of tables. Publishing the unchanged answers of all issued
  requests one after another applies every transaction, since each writes only its own locus.
\<close>

definition development_seed_incumbents :: "finite_snapshot option" where
  "development_seed_incumbents=development_incumbent_snapshot development_seed_state development_seed_problems"

definition development_seed_expected :: "development_request \<Rightarrow> finite_generation option" where
  "development_seed_expected r=Option.bind development_seed_incumbents (\<lambda>S0.
     Option.bind (development_data_target (development_problem_locus (fst (snd development_seed_state)) (fst r)))
       (finite_snapshot_lookup S0))"

type_synonym development_seed_publication_row = "finite_generation option\<times>finite_generation option\<times>
  finite_transaction_result option\<times>finite_transaction_result option\<times>bool"

definition development_seed_publication_row :: "development_request \<Rightarrow> development_seed_publication_row" where
  "development_seed_publication_row r=(let I=development_seed_expected r;
     G=development_answer_publication development_seed_state r development_seed_state I;
     H=development_answer_publication development_seed_state r development_seed_renamed I;
     first=(case (development_seed_incumbents,G) of
       (Some S0,Some G') \<Rightarrow> finite_transact S0 (finite_locus_transaction I G') | _ \<Rightarrow> None);
     second=(case (first,H) of
       (Some (Finite_Applied U),Some H') \<Rightarrow> finite_transact U (finite_locus_transaction I H') | _ \<Rightarrow> None)
   in (G,H,first,second,map_option generation_payload G=map_option generation_payload H))"

fun development_seed_publish_all ::
    "finite_snapshot \<Rightarrow> development_request list \<Rightarrow> finite_transaction_result option list" where
  "development_seed_publish_all S []=[]"
| "development_seed_publish_all S (r#rs)=(let I=development_seed_expected r in
    case development_answer_publication development_seed_state r development_seed_state I of
      None \<Rightarrow> None#development_seed_publish_all S rs
    | Some G \<Rightarrow> (let result=finite_transact S (finite_locus_transaction I G) in
        result#(case result of Some (Finite_Applied U) \<Rightarrow> development_seed_publish_all U rs
          | _ \<Rightarrow> development_seed_publish_all S rs)))"

type_synonym development_seed_publication = "finite_snapshot option\<times>development_seed_publication_row list\<times>
  finite_transaction_result option list"

definition development_seed_publication :: "development_problem fset \<Rightarrow> development_seed_publication" where
  "development_seed_publication answered=(let rs=development_seed_requests answered in
     (development_seed_incumbents,Parallel.map development_seed_publication_row rs,
      case development_seed_incumbents of None \<Rightarrow> [] | Some S0 \<Rightarrow> development_seed_publish_all S0 rs))"

definition development_seed_publication_data :: "development_seed_publication \<Rightarrow> finite_factor_term" where
  "development_seed_publication_data=finite_pair_presentation (finite_option_presentation finite_snapshot_value)
    (finite_pair_presentation (finite_sequence_presentation
      (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
        (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
          (finite_pair_presentation (finite_option_presentation finite_transaction_result_value)
            (finite_pair_presentation (finite_option_presentation finite_transaction_result_value)
              finite_boolean_data)))))
      (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value)))"

lemma development_seed_publication_data_injective [intro]: "inj development_seed_publication_data"
  unfolding development_seed_publication_data_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective) blast+

definition development_seed_publication_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_publication_value answered=
    development_seed_publication_data (development_seed_publication answered)"

text \<open>
  The expected outcomes follow from the kinds of transaction, not from the seeded values: every
  first publication applies, every second one conflicts with its complete observation, the two
  payloads of a request are equal, and the sequential publication applies all of them. The
  incumbents' causes are the acceptance of their equations by the checked context and the
  answers' causes are their verdicts; whether these recorded causes are valid under the first
  loop's policy is a separate judgment this report does not make.
\<close>

end
