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

section \<open>A snapshot's formation is read once for all its publications\<close>

text \<open>
  Every row publishes over the same published incumbents, and so does the sequential publication of the
  whole round: publishing over a snapshot checks its formation. The publisher of the incumbents is the
  publication over their snapshot applied to the snapshot alone, whose code equation
  (\<open>finite_locus_publications_code\<close>) reads the formation once, where the publisher is made; every row and
  the round's own publication use that publisher. The report is unchanged.
\<close>

definition development_seed_publication_row_with ::
    "((finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
    development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    development_problem list \<Rightarrow> development_request\<times>(nat\<times>development_problem) fset fset \<Rightarrow>
    development_seed_publication_row" where
  "development_seed_publication_row_with publish construct judge xs selected issue=(case issue of (r,reading) \<Rightarrow>
     let I=map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r);
       issued=development_seed_issue_using construct judge xs selected r reading;
       Q=map_option (\<lambda>(B,rows,Q). Q) issued;
       G=development_seed_answer_using construct judge development_seed_state r issued;
       H=development_seed_answer_using construct judge development_seed_renamed r issued
     in (Q,G,H,publish [(None,Q),(I,G),(I,H)],
       map_option generation_payload G=map_option generation_payload H))"

lemma development_seed_publication_row_published:
  "development_seed_publication_row construct judge xs selected S0=
    development_seed_publication_row_with (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)
      construct judge xs selected"
proof (rule ext)
  fix issue
  show "development_seed_publication_row construct judge xs selected S0 issue=
    development_seed_publication_row_with (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)
      construct judge xs selected issue"
    by (cases issue) (simp only: development_seed_publication_row_def development_seed_publication_row_with_def
      prod.case Let_def)
qed

text \<open>
  The publications of a round are the same over any publisher of a snapshot; the publisher the round
  starts from is the publication over the incumbents' snapshot.
\<close>

definition development_seed_publication_among ::
    "(finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
      development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
      development_seed_decisions option \<Rightarrow> development_seed_publication" where
  "development_seed_publication_among P construct judge xs decisions=(let
     S0=development_seed_snapshot xs;
     publish=(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> P S) in
     case decisions of None \<Rightarrow> (S0,None,[],[])
     | Some (selected,issues) \<Rightarrow> (let
         Sel=map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge (fst (snd development_seed_state))
           selected (finite_enumerated_environment [] []) []);
         rows=Parallel.map (development_seed_publication_row_with publish construct judge xs selected) issues;
         incumbents=map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)) issues in
       (S0,Sel,rows,publish ((None,Sel)#map (\<lambda>(Q,G,H,results,equal). (None,Q)) rows@
             map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip incumbents rows)))))"

definition development_seed_publication_over ::
    "(finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
      development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_decisions option \<Rightarrow>
      development_seed_publication" where
  "development_seed_publication_over P construct judge decisions=development_seed_publication_among P construct judge
     (development_seed_incumbents_with judge development_seed_problems) decisions"

lemma development_seed_publication_from_published [code]:
  "development_seed_publication_from construct judge decisions=
    development_seed_publication_over finite_locus_publications construct judge decisions"
proof -
  have publish: "(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> finite_locus_publications S)=
      (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)" for S0 :: "finite_snapshot option"
    by (cases S0) simp_all
  show ?thesis
    by (simp only: development_seed_publication_from_def development_seed_publication_over_def
      development_seed_publication_among_def development_seed_publication_row_published publish Let_def)
qed

section \<open>A published generation's formation is established by its recording constructor\<close>

text \<open>
  Every generation the round compares or writes, the incumbents, the selection, the issues and the
  answers, was made by the recording constructor, whose contract states it formed
  (\<open>development_payload_generation_fields\<close>, \<open>development_recorded_issue_fields\<close>,
  \<open>development_incumbent_with_recorded\<close>). So each publication the round makes satisfies the premise of
  the body publications (\<open>finite_locus_publications_body_established\<close>), and the round publishes by the
  body, the transactions checking only their loci. The premise is established here, for the recording
  constructor; a round over another constructor has no contract to establish it.
\<close>

lemma development_seed_incumbent_of_formed:
  "pred_option finite_generation_formed (map_option (\<lambda>(B,u,G). G)
     (development_seed_incumbent_of (development_seed_incumbents_with judge ps) r))"
proof (cases "development_seed_incumbent_of (development_seed_incumbents_with judge ps) r")
  case None
  then show ?thesis by simp
next
  case (Some incumbent)
  obtain B u I where found: "development_seed_incumbent_of (development_seed_incumbents_with judge ps) r=Some (B,u,I)"
    using Some by (cases incumbent) auto
  have "finite_generation_formed I"
    by (rule finite_check_generation_formed[OF development_seed_incumbent_of_recorded(2)[OF found]])
  then show ?thesis by (simp add: found)
qed

lemma development_seed_selection_formed:
  "pred_option finite_generation_formed (map_option (\<lambda>(B,u,G). G)
     (development_selection_generation_with judge names selected H rows))"
proof (cases "development_selection_generation_with judge names selected H rows")
  case None
  then show ?thesis by simp
next
  case (Some selection)
  obtain B u G where built: "development_selection_generation_with judge names selected H rows=Some (B,u,G)"
    using Some by (cases selection) auto
  have "finite_generation_formed G" by (rule development_selection_generation_fields(2)[OF built])
  then show ?thesis by (simp add: built)
qed

lemma development_seed_issue_formed:
  "pred_option finite_generation_formed (map_option (\<lambda>(B,rows,Q). Q)
     (development_seed_issue_using finite_construct_generation_record judge xs selected r reading))"
proof (cases "development_seed_issue_using finite_construct_generation_record judge xs selected r reading")
  case None
  then show ?thesis by simp
next
  case (Some result)
  obtain B2 rows Q where issued: "development_seed_issue_using finite_construct_generation_record judge xs selected r reading=
      Some (B2,rows,Q)" using Some by (cases result) auto
  obtain incumbent where issue: "development_recorded_issue_with judge (fst (snd development_seed_state)) (Some selected)
      r reading incumbent=Some (B2,rows,Q)"
    using issued by (auto simp: development_seed_issue_using_def development_recorded_issue_with_def bind_eq_Some_conv)
  obtain B u I where shape: "incumbent=(B,u,I)" by (cases incumbent) auto
  have "finite_generation_formed Q"
    by (rule development_recorded_issue_fields[OF issue[unfolded shape]])
  then show ?thesis by (simp add: issued)
qed

lemma development_seed_answer_formed:
  "pred_option finite_generation_formed
     (development_seed_answer_using finite_construct_generation_record judge S' r issued)"
proof (cases issued)
  case None
  then show ?thesis by (simp add: development_seed_answer_using_def)
next
  case (Some result)
  obtain B rows Q where shape: "issued=Some (B,rows,Q)" using Some by (cases result) auto
  show ?thesis
  proof (cases "development_answer_using finite_construct_generation_record judge development_seed_state r S' B rows")
    case None
    then show ?thesis by (simp add: development_seed_answer_using_def shape)
  next
    case (Some answer)
    obtain B' u' G where answered: "development_answer_using finite_construct_generation_record judge
        development_seed_state r S' B rows=Some (B',u',G)"
      using Some by (cases answer) auto
    have "finite_generation_formed G"
      by (rule development_answer_with_fields(2)[OF answered[folded development_answer_with_def]])
    then show ?thesis by (simp add: development_seed_answer_using_def shape answered)
  qed
qed

lemma development_seed_publication_row_with_formed:
  assumes row: "development_seed_publication_row_with P finite_construct_generation_record judge xs selected issue=
      (Q,G,H,results,equal)"
  shows "pred_option finite_generation_formed Q" "pred_option finite_generation_formed G"
    "pred_option finite_generation_formed H"
proof -
  obtain r reading where shape: "issue=(r,reading)" by (cases issue) auto
  show "pred_option finite_generation_formed Q" "pred_option finite_generation_formed G"
    "pred_option finite_generation_formed H"
    using row by (auto simp: shape development_seed_publication_row_with_def Let_def
      development_seed_issue_formed development_seed_answer_formed)
qed

lemma development_seed_publication_row_with_agree:
  assumes agree: "\<And>ps. finite_publications_formed_generations ps \<Longrightarrow> P ps=P' ps"
  shows "development_seed_publication_row_with P finite_construct_generation_record judge
      (development_seed_incumbents_with judge qs) selected=
    development_seed_publication_row_with P' finite_construct_generation_record judge
      (development_seed_incumbents_with judge qs) selected"
proof (rule ext)
  fix issue :: "development_request\<times>(nat\<times>development_problem) fset fset"
  obtain r reading where shape: "issue=(r,reading)" by (cases issue) auto
  let ?xs="development_seed_incumbents_with judge qs"
  let ?I="map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of ?xs r)"
  let ?issued="development_seed_issue_using finite_construct_generation_record judge ?xs selected r reading"
  let ?Q="map_option (\<lambda>(B,rows,Q). Q) ?issued"
  let ?G="development_seed_answer_using finite_construct_generation_record judge development_seed_state r ?issued"
  let ?H="development_seed_answer_using finite_construct_generation_record judge development_seed_renamed r ?issued"
  have formed: "finite_publications_formed_generations [(None,?Q),(?I,?G),(?I,?H)]"
    by (simp add: finite_publications_formed_generations_def development_seed_incumbent_of_formed
      development_seed_issue_formed development_seed_answer_formed)
  show "development_seed_publication_row_with P finite_construct_generation_record judge ?xs selected issue=
      development_seed_publication_row_with P' finite_construct_generation_record judge ?xs selected issue"
    by (simp only: shape development_seed_publication_row_with_def prod.case Let_def agree[OF formed])
qed

lemma development_seed_publication_round_formed:
  "finite_publications_formed_generations
     ((None,map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge names selected H0 []))#
       map (\<lambda>(Q,G,H,results,equal). (None,Q))
         (Parallel.map (development_seed_publication_row_with P finite_construct_generation_record judge
           (development_seed_incumbents_with judge qs) selected) issues)@
       map (\<lambda>(I,(Q,G,H,results,equal)). (I,G))
         (zip (map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G)
             (development_seed_incumbent_of (development_seed_incumbents_with judge qs) r)) issues)
           (Parallel.map (development_seed_publication_row_with P finite_construct_generation_record judge
             (development_seed_incumbents_with judge qs) selected) issues)))"
proof -
  let ?rows="Parallel.map (development_seed_publication_row_with P finite_construct_generation_record judge
      (development_seed_incumbents_with judge qs) selected) issues"
  let ?incs="map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G)
      (development_seed_incumbent_of (development_seed_incumbents_with judge qs) r)) issues"
  have row: "pred_option finite_generation_formed Q \<and> pred_option finite_generation_formed G"
    if member: "(Q,G,H,results,equal)\<in>set ?rows" for Q G H results equal
  proof -
    obtain issue where "development_seed_publication_row_with P finite_construct_generation_record judge
        (development_seed_incumbents_with judge qs) selected issue=(Q,G,H,results,equal)"
      using member by (auto simp: Parallel.map_def)
    note formed=development_seed_publication_row_with_formed[OF this]
    show ?thesis using formed(1,2) by simp
  qed
  have incumbent: "pred_option finite_generation_formed I" if "I\<in>set ?incs" for I
    using that by (auto simp: development_seed_incumbent_of_formed)
  have first: "\<forall>(I,A)\<in>set (map (\<lambda>(Q,G,H,results,equal). (None,Q)) ?rows).
      pred_option finite_generation_formed I \<and> pred_option finite_generation_formed A"
  proof
    fix x :: "finite_generation option\<times>finite_generation option"
    assume "x\<in>set (map (\<lambda>(Q,G,H,results,equal). (None,Q)) ?rows)"
    then obtain y where y: "y\<in>set ?rows" and mapped: "x=(case y of (Q,G,H,results,equal) \<Rightarrow> (None,Q))"
      unfolding set_map by blast
    obtain Q G H results equal where shape: "y=(Q,G,H,results,equal)" by (rule prod_cases5)
    have x: "x=(None,Q)" using mapped by (simp add: shape)
    have member: "(Q,G,H,results,equal)\<in>set ?rows" using y by (simp add: shape)
    show "case x of (I,A) \<Rightarrow> pred_option finite_generation_formed I \<and> pred_option finite_generation_formed A"
      using row[OF member] by (simp add: x)
  qed
  have second: "\<forall>(I,A)\<in>set (map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip ?incs ?rows)).
      pred_option finite_generation_formed I \<and> pred_option finite_generation_formed A"
  proof
    fix x :: "finite_generation option\<times>finite_generation option"
    assume "x\<in>set (map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip ?incs ?rows))"
    then obtain y where y: "y\<in>set (zip ?incs ?rows)"
      and mapped: "x=(case y of (I,(Q,G,H,results,equal)) \<Rightarrow> (I,G))"
      unfolding set_map by blast
    obtain I Q G H results equal where shape: "y=(I,(Q,G,H,results,equal))" by (rule prod_cases6)
    have x: "x=(I,G)" using mapped by (simp add: shape)
    have zipped: "(I,(Q,G,H,results,equal))\<in>set (zip ?incs ?rows)" using y by (simp add: shape)
    have "pred_option finite_generation_formed I" by (rule incumbent[OF set_zip_leftD[OF zipped]])
    moreover have "pred_option finite_generation_formed G" using row[OF set_zip_rightD[OF zipped]] by simp
    ultimately show "case x of (I,A) \<Rightarrow> pred_option finite_generation_formed I \<and> pred_option finite_generation_formed A"
      by (simp add: x)
  qed
  show ?thesis
    using first second by (auto simp: finite_publications_formed_generations_def development_seed_selection_formed)
qed

lemma development_seed_publication_over_formed:
  "development_seed_publication_over finite_locus_publications finite_construct_generation_record judge decisions=
    development_seed_publication_over (\<lambda>S. if finite_snapshot_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) finite_construct_generation_record judge decisions"
proof -
  have agree: "(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> finite_locus_publications S) ps=
      (case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> (if finite_snapshot_formed S then finite_locus_publications_body S
        else map (\<lambda>q. None))) ps"
    if formed: "finite_publications_formed_generations ps" for S0 ps
    by (cases S0) (simp_all add: checked_premise.checked_at_entry[OF finite_locus_publications_checked]
      established_premise.exact[OF finite_locus_publications_body_established formed])
  have rows: "development_seed_publication_row_with (case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> finite_locus_publications S)
      finite_construct_generation_record judge (development_seed_incumbents_with judge qs) selected=
    development_seed_publication_row_with (case S0 of None \<Rightarrow> (\<lambda>ps. [])
        | Some S \<Rightarrow> (if finite_snapshot_formed S then finite_locus_publications_body S else map (\<lambda>q. None)))
      finite_construct_generation_record judge (development_seed_incumbents_with judge qs) selected" for S0 qs selected
    by (rule development_seed_publication_row_with_agree) (rule agree)
  show ?thesis
  proof (cases decisions)
    case None
    then show ?thesis by (simp add: development_seed_publication_over_def development_seed_publication_among_def)
  next
    case (Some d)
    obtain selected issues where d: "d=(selected,issues)" by (cases d) auto
    show ?thesis
      by (simp only: development_seed_publication_over_def development_seed_publication_among_def Let_def Some d
        prod.case option.case rows
        agree[OF development_seed_publication_round_formed])
  qed
qed

lemma development_seed_publication_row_with_publisher:
  "development_seed_publication_row_with P construct judge xs selected (r,reading)=
    (case development_seed_publication_row_with P' construct judge xs selected (r,reading) of (Q,G,H,results,equal) \<Rightarrow>
      (Q,G,H,P [(None,Q),(map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),G),
        (map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),H)],equal))"
  by (simp add: development_seed_publication_row_with_def Let_def)

lemma development_seed_publication_row_with_known:
  "development_seed_publication_row_with P finite_construct_known_original_generation judge
      (development_seed_incumbents_with judge ps) selected=
    development_seed_publication_row_with P finite_construct_generation_record judge
      (development_seed_incumbents_with judge ps) selected"
proof (rule ext)
  fix issue :: "development_request\<times>(nat\<times>development_problem) fset fset"
  obtain r reading where shape: "issue=(r,reading)" by (cases issue) auto
  have none: "development_seed_publication_row_with (\<lambda>ps. []) finite_construct_known_original_generation judge
      (development_seed_incumbents_with judge ps) selected (r,reading)=
    development_seed_publication_row_with (\<lambda>ps. []) finite_construct_generation_record judge
      (development_seed_incumbents_with judge ps) selected (r,reading)"
    using fun_cong[OF development_seed_publication_row_known[of judge ps selected None], of "(r,reading)"]
    by (simp only: development_seed_publication_row_published option.case)
  show "development_seed_publication_row_with P finite_construct_known_original_generation judge
      (development_seed_incumbents_with judge ps) selected issue=
    development_seed_publication_row_with P finite_construct_generation_record judge
      (development_seed_incumbents_with judge ps) selected issue"
    by (simp only: shape development_seed_publication_row_with_publisher[where P=P and P'="\<lambda>ps. []"] none)
qed

lemma development_seed_publication_over_known:
  "development_seed_publication_over P finite_construct_known_original_generation judge decisions=
    development_seed_publication_over P finite_construct_generation_record judge decisions"
  by (simp add: development_seed_publication_over_def development_seed_publication_among_def
    development_seed_publication_row_with_known Let_def split: option.splits prod.splits)

declare development_seed_publication_prepared [code del]

text \<open>
  The code equation publishes the round by the body publications, the premise discharged above for the
  recording constructor; the known constructor and the prepared judgment are the same round.
\<close>

lemma development_seed_publication_formed [code]:
  "development_seed_publication answered=(let decisions=development_seed_decisions answered in
     development_seed_publication_over (\<lambda>S. if finite_snapshot_formed S then finite_locus_publications_body S
       else map (\<lambda>q. None)) finite_construct_known_original_generation
       (parallel_computed_function development_payload_judgment
         (development_seed_family_keys@development_seed_decision_keys decisions)) decisions)"
  by (simp only: development_seed_publication_def development_seed_publication_from_published
    development_seed_publication_over_formed development_seed_publication_over_known
    parallel_computed_function_exact Let_def)

section \<open>The cause's formation is established by the judgment, the snapshot's generations by the constructor\<close>

text \<open>
  The round records every incumbent, issue and answer with a cause its judgment quoted, so the cause is
  formed by the judgment's contract (\<open>development_payload_judgment_formed_causes\<close>) and each recording checks
  only the rest of its readiness (\<open>development_payload_generation_using_formed_causes\<close>). The incumbents'
  snapshot holds generations the recording constructor made, formed by its contract
  (\<open>development_incumbent_with_recorded\<close>), so its formation is the distinctness of its loci
  (\<open>finite_snapshot_loci_established\<close>). Both premises are established here, for the round's own judge and
  incumbents; the report is unchanged.
\<close>

definition development_seed_incumbents_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_problem list \<Rightarrow> development_seed_incumbent list" where
  "development_seed_incumbents_using construct judge ps=Parallel.map (\<lambda>p. (p,
     Option.bind (development_incumbent_key development_seed_state p)
       (\<lambda>(l,t). development_payload_generation_using construct judge t (finite_enumerated_environment [] []) l []))) ps"

lemma development_seed_incumbents_using_formed_causes:
  assumes judge: "development_judge_formed_causes judge"
  shows "development_seed_incumbents_using finite_construct_formed_cause_generation judge ps=
    development_seed_incumbents_with judge ps"
proof -
  have formed: "finite_environment_formed (finite_enumerated_environment [] [])"
    by (simp add: finite_environment_formed_def finite_enumerated_environment_def finite_relation_functional_def)
  have rows: "list_all (\<lambda>(d,G). finite_check_generation G (finite_enumerated_environment [] []) (fst d) (snd d)) []"
    by simp
  show ?thesis
    by (simp only: development_seed_incumbents_using_def development_seed_incumbents_with_def
      development_incumbent_with_def development_payload_generation_using_formed_causes[OF judge]
      development_payload_generation_using_known[OF formed rows])
qed

lemma development_recorded_issue_using_formed_causes:
  assumes judge: "development_judge_formed_causes judge"
  shows "development_recorded_issue_using finite_construct_formed_cause_generation judge=
    development_recorded_issue_using finite_construct_known_original_generation judge"
  by (intro ext) (simp only: development_recorded_issue_using_def development_selection_generation_using_def
    development_issue_generation_using_def development_payload_generation_using_formed_causes[OF judge])

lemma development_seed_publication_row_with_formed_causes:
  assumes judge: "development_judge_formed_causes judge"
  shows "development_seed_publication_row_with P finite_construct_formed_cause_generation judge xs selected=
    development_seed_publication_row_with P finite_construct_known_original_generation judge xs selected"
  by (intro ext) (simp only: development_seed_publication_row_with_def development_seed_issue_using_def
    development_seed_answer_using_def development_recorded_issue_using_formed_causes[OF judge]
    development_answer_using_formed_causes[OF judge])

lemma development_seed_publication_among_formed_causes:
  assumes judge: "development_judge_formed_causes judge"
  shows "development_seed_publication_among P finite_construct_formed_cause_generation judge xs decisions=
    development_seed_publication_among P finite_construct_known_original_generation judge xs decisions"
  by (simp only: development_seed_publication_among_def development_seed_publication_row_with_formed_causes[OF judge])

lemma development_seed_snapshot_formed:
  assumes snapshot: "development_seed_snapshot (development_seed_incumbents_with judge ps)=Some S"
  shows "fBall S finite_generation_formed"
proof -
  obtain gs where listed: "those (map (\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) (development_seed_incumbents_with judge ps))=
      Some gs" and whole: "S=fset_of_list gs"
    using snapshot by (auto simp: development_seed_snapshot_def)
  have origin: "\<exists>y\<in>set ys. f y=Some g" if "those (map f ys)=Some hs" "g\<in>set hs"
    for f :: "'x \<Rightarrow> 'y option" and ys hs g
    using that by (induction ys arbitrary: hs) (auto split: option.splits)
  show ?thesis
  proof (rule fBallI)
    fix g
    assume "g |\<in>| S"
    then have "g\<in>set gs" by (simp add: whole fset_of_list_elem)
    then obtain y where y: "y\<in>set (development_seed_incumbents_with judge ps)"
      and found: "(\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) y=Some g"
      using origin[OF listed] by blast
    obtain p where shape: "y=(p,development_incumbent_with judge development_seed_state p)"
      using y by (auto simp: development_seed_incumbents_with_def Parallel.map_def)
    obtain B u where built: "development_incumbent_with judge development_seed_state p=Some (B,u,g)"
      using found shape by (auto simp: map_option_eq_Some split: prod.splits)
    show "finite_generation_formed g"
      by (rule finite_check_generation_formed[OF development_incumbent_with_recorded(2)[OF built]])
  qed
qed

lemma development_seed_publication_among_loci:
  "development_seed_publication_among (\<lambda>S. if finite_snapshot_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) construct judge (development_seed_incumbents_with judge ps) decisions=
    development_seed_publication_among (\<lambda>S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) construct judge (development_seed_incumbents_with judge ps) decisions"
proof -
  let ?S0="development_seed_snapshot (development_seed_incumbents_with judge ps)"
  have publish: "(case ?S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> (if finite_snapshot_formed S then
        finite_locus_publications_body S else map (\<lambda>q. None)))=
      (case ?S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> (if finite_snapshot_loci_formed S then
        finite_locus_publications_body S else map (\<lambda>q. None)))"
  proof (cases ?S0)
    case None
    then show ?thesis by simp
  next
    case (Some S)
    have "finite_snapshot_formed S=finite_snapshot_loci_formed S"
      by (rule established_premise.exact[OF finite_snapshot_loci_established development_seed_snapshot_formed[OF Some]])
    then show ?thesis by (simp add: Some)
  qed
  show ?thesis by (simp only: development_seed_publication_among_def Let_def publish)
qed

declare development_seed_publication_formed [code del]

text \<open>
  The code equation records the round with the constructor that does not check the quoted cause and publishes
  it over the incumbents' snapshot checking only its loci.
\<close>

lemma development_seed_publication_formed_causes [code]:
  "development_seed_publication answered=(let decisions=development_seed_decisions answered;
     judge=parallel_computed_function development_payload_judgment
       (development_seed_family_keys@development_seed_decision_keys decisions) in
     development_seed_publication_among (\<lambda>S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
       else map (\<lambda>q. None)) finite_construct_formed_cause_generation judge
       (development_seed_incumbents_using finite_construct_formed_cause_generation judge development_seed_problems)
       decisions)"
  by (simp only: development_seed_publication_formed parallel_computed_function_exact Let_def
    development_seed_publication_over_def development_seed_publication_among_loci
    development_seed_incumbents_using_formed_causes[OF development_payload_judgment_formed_causes]
    development_seed_publication_among_formed_causes[OF development_payload_judgment_formed_causes])

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
