theory Development_Seed_Publication
  imports Development_Seed_Verification Development_Certified_Generations RRA_Formed_Snapshot_Transactions
    Parallel_Computed_Preparation
begin

section \<open>The seeded development publishes certified generations by transactions\<close>

text \<open>
  The published state of the seeded development starts from its incumbents: one base generation
  for each problem, at the problem's locus, recorded with its cause certified under the policy of
  its family's acceptance by the checked context. For every issued request, the unchanged answer is
  recorded beside the incumbent it was judged against, cites it, is certified in the same way and is
  published by the transaction that expects that incumbent; it replaces it. The answer with the
  reversed table, admitted against the same incumbent, is then published by the same kind of
  transaction and conflicts, because the locus now holds the first answer. The two answers present
  the same payload, because a payload carries the names it uses and the reversal is a correspondence
  of tables. Publishing the unchanged answers of all issued requests one after another applies every
  transaction, since each writes only its own locus.
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

definition development_seed_answer_with :: "development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> finite_generation option" where
  "development_seed_answer_with judge xs r S'=Option.bind (development_seed_incumbent_of xs r) (\<lambda>(B,u,I).
     map_option (\<lambda>(B',u',G). G) (development_answer_with judge development_seed_state r S' B [((u,[]),I)]))"

type_synonym development_seed_publication_row = "finite_generation option\<times>finite_generation option\<times>
  finite_transaction_result option list\<times>bool"

text \<open>
  A row publishes the two answers of one request in turn over the incumbent both were judged against,
  starting from the published incumbents.
\<close>

definition development_seed_publication_row_with :: "development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    finite_snapshot option \<Rightarrow> development_request \<Rightarrow> development_seed_publication_row" where
  "development_seed_publication_row_with judge xs S0 r=(let I=map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r);
     G=development_seed_answer_with judge xs r development_seed_state;
     H=development_seed_answer_with judge xs r development_seed_renamed
   in (G,H,(case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S [(I,G),(I,H)]),
     map_option generation_payload G=map_option generation_payload H))"

type_synonym development_seed_publication = "finite_snapshot option\<times>development_seed_publication_row list\<times>
  finite_transaction_result option list"

definition development_seed_publication_with ::
    "development_payload_judge \<Rightarrow> development_problem fset \<Rightarrow> development_seed_publication" where
  "development_seed_publication_with judge answered=(let rs=development_seed_requests answered;
     xs=development_seed_incumbents_with judge development_seed_problems;
     S0=development_seed_snapshot xs;
     rows=Parallel.map (development_seed_publication_row_with judge xs S0) rs in
     (S0,rows,case S0 of None \<Rightarrow> []
       | Some S \<Rightarrow> finite_locus_publications S (map (\<lambda>(r,(G,H,results,equal)).
           (map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),G)) (zip rs rows))))"

definition development_seed_publication :: "development_problem fset \<Rightarrow> development_seed_publication" where
  "development_seed_publication answered=development_seed_publication_with development_payload_judgment answered"

section \<open>Each family is judged once\<close>

text \<open>
  The judgment of a family is a function of the family's presentation with its names, so the report
  judges each family of a problem once, in parallel, and every incumbent and answer whose family has
  that presentation is recorded with the one judgment. An answer whose family differs is judged when it
  is recorded. The report is unchanged, because the prepared function is the judgment itself.
\<close>

definition development_seed_family_keys :: "finite_factor_term list" where
  "development_seed_family_keys=List.map_filter (\<lambda>p. map_option snd (development_incumbent_key development_seed_state p))
    development_seed_problems"

declare development_seed_publication_def [code del]

lemma development_seed_publication_prepared [code]:
  "development_seed_publication answered=development_seed_publication_with
     (parallel_computed_function development_payload_judgment development_seed_family_keys) answered"
  by (simp only: development_seed_publication_def parallel_computed_function_exact)

section \<open>The report is presented through the presentations of its notions\<close>

definition development_seed_publication_data :: "development_seed_publication \<Rightarrow> finite_factor_term" where
  "development_seed_publication_data=finite_pair_presentation (finite_option_presentation finite_snapshot_value)
    (finite_pair_presentation (finite_sequence_presentation
      (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
        (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
          (finite_pair_presentation (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value))
            finite_boolean_data))))
      (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value)))"

lemma development_seed_publication_data_injective [intro]: "inj development_seed_publication_data"
  unfolding development_seed_publication_data_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective) blast+

definition development_seed_publication_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_publication_value answered=
    development_seed_publication_data (development_seed_publication answered)"

text \<open>
  The expected outcomes follow from the kinds of transaction, not from the seeded values: in every
  row the first publication applies and the second conflicts with its complete observation, the two
  payloads of a request are equal, and the sequential publication applies all of them. Every
  generation's cause is a certified call of the policy that lists its family's quotation, whose
  constructor requires the family to be entities of the checked context; the verdict that admitted
  an answer is recorded in the development's history, not in the published generation.
\<close>

end
