theory Development_Seed_Publication
  imports Development_Seed_Verification Development_Decision_Generations Represented_Snapshot_Transactions
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

section \<open>The round over a representation\<close>

text \<open>
  The round is stated once over how a recorded generation is represented and how the represented
  generations are published: the incumbents are recorded with a constructor of their own, the selection with
  the recording constructor and every row with the rows' constructor, each recording retaining the judgment
  it was made with. At the plain representation a generation is itself, and the older statement of the round
  below is that instance, its incumbents recorded with the recording constructor. Every row publishes over the
  same published incumbents, and so does the sequential publication of the whole round: the publisher of the
  incumbents is the publication over their snapshot applied to the snapshot alone, whose code equation
  (\<open>finite_locus_publications_code\<close>) reads the formation once, where the publisher is made.
\<close>

type_synonym seed_judged = "(finite_exact_artifact\<times>development_policy_judgment) option"
type_synonym seed_recorded =
  "(local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option"
type_synonym 'k seed_made = "seed_recorded\<times>'k option"

definition seed_record :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    (finite_exact_target\<times>finite_factor_term) option \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow>
    development_generation_row list \<Rightarrow> 'k seed_made" where
  "seed_record L construct key H rows=(case key of None \<Rightarrow> (None,None)
     | Some (l,t) \<Rightarrow> (case L t of (j,k) \<Rightarrow>
         (development_payload_generation_using construct (\<lambda>s. j) t H l rows,Some k)))"

definition seed_made_generation :: "'k seed_made \<Rightarrow> finite_generation option" where
  "seed_made_generation m=map_option (\<lambda>(B,u,G). G) (fst m)"

lemma seed_made_generation_none [simp]: "seed_made_generation (None,k)=None"
  by (simp add: seed_made_generation_def)

type_synonym 'k seed_row_made = "finite_generation option\<times>'k seed_made\<times>'k seed_made\<times>
  development_generation_row list\<times>'k seed_made\<times>development_generation_row list\<times>'k seed_made"

definition seed_row_selection :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_problem list \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> 'k seed_made" where
  "seed_row_selection L construct selected B=seed_record L construct
     (map_option (\<lambda>l. (l,development_selection_payload (fst (snd development_seed_state)) selected))
       (development_data_target development_selection_locus)) B []"

definition seed_row_issue :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_request \<Rightarrow> (nat\<times>development_problem) fset fset \<Rightarrow> local_address option \<Rightarrow> finite_generation \<Rightarrow>
    'k seed_made \<Rightarrow> 'k seed_made" where
  "seed_row_issue L construct r reading u I S=(case fst S of None \<Rightarrow> (None,None) | Some (B1,us,Sel) \<Rightarrow>
     seed_record L construct (map_option (\<lambda>l. (l,development_issue_payload (fst (snd development_seed_state)) r reading))
       (development_locus_target Development_Issue_Role (fst r))) B1 [((u,[]),I),((us,[]),Sel)])"

definition seed_row_answer :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> 'k seed_made \<Rightarrow> development_generation_row list\<times>'k seed_made" where
  "seed_row_answer L construct r S' Q=(case fst Q of None \<Rightarrow> ([],(None,None)) | Some (B2,uq,Qg) \<Rightarrow>
     (case development_answer_key development_seed_state r S' of None \<Rightarrow> ([],(None,None))
      | Some (l,t) \<Rightarrow> (development_answer_citations (fst (snd development_seed_state)) (fst r) l [((uq,[]),Qg)],
          seed_record L construct (Some (l,t)) B2
            (development_answer_citations (fst (snd development_seed_state)) (fst r) l [((uq,[]),Qg)]))))"

definition seed_row_made :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_seed_incumbent list \<Rightarrow> development_problem list \<Rightarrow>
    development_request\<times>(nat\<times>development_problem) fset fset \<Rightarrow> development_problem\<times>'k seed_row_made" where
  "seed_row_made L construct xs selected issue=(case issue of (r,reading) \<Rightarrow> (fst r,
     case development_seed_incumbent_of xs r of
       None \<Rightarrow> (None,(None,None),(None,None),[],(None,None),[],(None,None))
     | Some (B,u,I) \<Rightarrow> (let S=seed_row_selection L construct selected B; Q=seed_row_issue L construct r reading u I S;
         G=seed_row_answer L construct r development_seed_state Q; H=seed_row_answer L construct r development_seed_renamed Q
       in (Some I,S,Q,fst G,snd G,fst H,snd H))))"

lemma seed_record_result:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "fst (seed_record L construct key H rows)=
    Option.bind key (\<lambda>(l,t). development_payload_generation_using construct judge t H l rows)"
proof (cases key)
  case None
  then show ?thesis by (simp add: seed_record_def)
next
  case (Some lt)
  obtain l t where lt: "lt=(l,t)" by (cases lt)
  obtain j k where Lt: "L t=(j,k)" by (cases "L t")
  have j: "j=judge t" using judged[of t] Lt by simp
  show ?thesis by (simp add: seed_record_def Some lt Lt j development_payload_generation_using_def)
qed

lemma seed_row_selection_result:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "fst (seed_row_selection L construct selected B)=
    development_selection_generation_using construct judge (fst (snd development_seed_state)) selected B []"
  by (cases "development_data_target development_selection_locus")
    (simp_all add: seed_row_selection_def seed_record_result[OF judged] development_selection_generation_using_def)

lemma seed_row_issue_result:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "development_recorded_issue_using construct judge (fst (snd development_seed_state)) (Some selected) r reading (B,u,I)=
    map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q))
      (fst (seed_row_issue L construct r reading u I (seed_row_selection L construct selected B)))"
proof (cases "fst (seed_row_selection L construct selected B)")
  case None
  then show ?thesis using seed_row_selection_result[OF judged, where construct=construct and selected=selected and B=B]
    by (simp add: development_recorded_issue_using_def seed_row_issue_def)
next
  case (Some s)
  obtain B1 us Sel where s: "s=(B1,us,Sel)" by (cases s)
  show ?thesis using Some seed_row_selection_result[OF judged, where construct=construct and selected=selected and B=B]
    by (cases "development_locus_target Development_Issue_Role (fst r)")
      (simp_all add: s development_recorded_issue_using_def seed_row_issue_def development_issue_generation_using_def
        seed_record_result[OF judged])
qed

lemma seed_row_answer_result:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "seed_made_generation (snd (seed_row_answer L construct r S' Q))=
    development_seed_answer_using construct judge S' r (map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q)) (fst Q))"
proof (cases "fst Q")
  case None
  then show ?thesis by (simp add: seed_row_answer_def development_seed_answer_using_def seed_made_generation_def)
next
  case (Some q)
  note issued=this
  obtain B2 uq Qg where q: "q=(B2,uq,Qg)" by (cases q)
  show ?thesis
  proof (cases "development_answer_key development_seed_state r S'")
    case None
    then show ?thesis using issued
      by (simp add: q seed_row_answer_def development_seed_answer_using_def development_answer_using_def seed_made_generation_def)
  next
    case (Some lt)
    obtain l t where lt: "lt=(l,t)" by (cases lt)
    show ?thesis using issued Some
      by (simp add: q lt seed_row_answer_def development_seed_answer_using_def development_answer_using_def
        seed_made_generation_def seed_record_result[OF judged])
  qed
qed

definition seed_plain_row :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    development_problem list \<Rightarrow> development_request\<times>(nat\<times>development_problem) fset fset \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option" where
  "seed_plain_row construct judge xs selected issue=(case issue of (r,reading) \<Rightarrow>
     let issued=development_seed_issue_using construct judge xs selected r reading in
     (map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),map_option (\<lambda>(B,rows,Q). Q) issued,
       development_seed_answer_using construct judge development_seed_state r issued,
       development_seed_answer_using construct judge development_seed_renamed r issued))"

definition seed_row_plain_reps :: "development_problem\<times>'k seed_row_made \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option" where
  "seed_row_plain_reps row=(case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow>
     (I,seed_made_generation Q,seed_made_generation G,seed_made_generation H))"

lemma seed_row_made_plain:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "seed_row_plain_reps (seed_row_made L construct xs selected issue)=seed_plain_row construct judge xs selected issue"
proof -
  obtain r reading where issue: "issue=(r,reading)" by (cases issue)
  show ?thesis
  proof (cases "development_seed_incumbent_of xs r")
    case None
    then show ?thesis
      by (simp add: issue seed_row_made_def seed_row_plain_reps_def seed_plain_row_def development_seed_issue_using_def
        development_seed_answer_using_def seed_made_generation_def)
  next
    case (Some inc)
    note found=this
    obtain B u I where inc: "inc=(B,u,I)" by (cases inc)
    have issued: "development_seed_issue_using construct judge xs selected r reading=
        map_option (\<lambda>(B2,uq,Q). (B2,[((uq,[]),Q)],Q))
          (fst (seed_row_issue L construct r reading u I (seed_row_selection L construct selected B)))"
      by (simp add: development_seed_issue_using_def found inc seed_row_issue_result[OF judged])
    have Qgen: "map_option (\<lambda>(B,rows,Q). Q) (development_seed_issue_using construct judge xs selected r reading)=
        seed_made_generation (seed_row_issue L construct r reading u I (seed_row_selection L construct selected B))"
      by (simp add: issued seed_made_generation_def option.map_comp o_def case_prod_unfold)
    have Ggen: "development_seed_answer_using construct judge S' r (development_seed_issue_using construct judge xs selected r reading)=
        seed_made_generation (snd (seed_row_answer L construct r S'
          (seed_row_issue L construct r reading u I (seed_row_selection L construct selected B))))" for S'
      by (simp only: issued seed_row_answer_result[OF judged])
    show ?thesis
      by (simp add: issue seed_row_made_def seed_row_plain_reps_def seed_plain_row_def found inc Let_def Qgen Ggen
        del: prod.collapse)
  qed
qed

type_synonym 'k seed_made_round = "'k seed_made list\<times>'k seed_made\<times>(development_problem\<times>'k seed_row_made) list"
type_synonym 't seed_reps = "'t generation_structure option list\<times>'t generation_structure option\<times>
  ('t generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>
    't generation_structure option) list"
type_synonym ('t,'r) seed_round = "'t represented_snapshot option\<times>'t generation_structure option\<times>
  ('t generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>'r option list\<times>bool) list\<times>
  'r option list"

definition seed_made_round_of :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_constructor \<Rightarrow> development_seed_decisions option \<Rightarrow> 'k seed_made_round" where
  "seed_made_round_of L incumbent construct decisions=(let
     incs=Parallel.map (\<lambda>p. seed_record L incumbent (development_incumbent_key development_seed_state p)
       (finite_enumerated_environment [] []) []) development_seed_problems;
     xs=zip development_seed_problems (map fst incs)
   in (case decisions of None \<Rightarrow> (incs,(None,None),[])
     | Some (selected,issues) \<Rightarrow> (incs,seed_row_selection L finite_construct_generation_record selected
           (finite_enumerated_environment [] []),
         Parallel.map (seed_row_made L construct xs selected) issues)))"

definition seed_round_row :: "(('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 'r option list) \<Rightarrow>
    't generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>
      't generation_structure option \<Rightarrow>
    't generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>'r option list\<times>bool" where
  "seed_round_row publish=(\<lambda>(I,Q,G,H). (Q,G,H,publish [(None,Q),(I,G),(I,H)],
     map_option generation_payload G=map_option generation_payload H))"

definition seed_round_assemble :: "'t seed_reps\<times>'s \<Rightarrow>
    ('s \<Rightarrow> 't represented_snapshot \<Rightarrow> ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 'r option list) \<Rightarrow>
    development_seed_decisions option \<Rightarrow> ('t,'r) seed_round" where
  "seed_round_assemble represented pub decisions=(case represented of ((ireps,sel,rows),s) \<Rightarrow> let
     S0=map_option fset_of_list (those ireps);
     publish=(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> pub s S)
   in (S0,sel,Parallel.map (seed_round_row publish) rows,
     (case decisions of None \<Rightarrow> [] | Some d \<Rightarrow>
       publish ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@map (\<lambda>(I,Q,G,H). (I,G)) rows))))"

definition development_seed_round :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_constructor \<Rightarrow> ('k seed_made_round \<Rightarrow> 't seed_reps\<times>'s) \<Rightarrow>
    ('s \<Rightarrow> 't represented_snapshot \<Rightarrow> ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 'r option list) \<Rightarrow>
    development_seed_decisions option \<Rightarrow> ('t,'r) seed_round\<times>'s" where
  "development_seed_round L incumbent construct represent pub decisions=(let
     represented=represent (seed_made_round_of L incumbent construct decisions)
   in (seed_round_assemble represented pub decisions,snd represented))"

definition seed_plain_reps :: "'k seed_made_round \<Rightarrow> finite_exact_target seed_reps\<times>unit" where
  "seed_plain_reps m=(case m of (incs,sel,rows) \<Rightarrow> ((map seed_made_generation incs,seed_made_generation sel,
     map (\<lambda>(p,I,S,Q,rG,G,rH,H). (I,seed_made_generation Q,seed_made_generation G,seed_made_generation H)) rows),()))"

section \<open>The older statement of the round is its plain instance\<close>

text \<open>
  A row over a publisher is the round's row at the plain row; the round over given incumbents is the
  assembly of their plain representation; the round over a publisher is the round with the recording
  constructor for the incumbents at the plain representation, and the round from a constructor and judgment
  is it over the incumbents' snapshot's publications. Each keeps the equation it was defined by.
\<close>

definition development_seed_publication_row_with ::
    "((finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
    development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    development_problem list \<Rightarrow> development_request\<times>(nat\<times>development_problem) fset fset \<Rightarrow>
    development_seed_publication_row" where
  "development_seed_publication_row_with publish construct judge xs selected issue=
    seed_round_row publish (seed_plain_row construct judge xs selected issue)"

lemma development_seed_publication_row_with_eq:
  "development_seed_publication_row_with publish construct judge xs selected issue=(case issue of (r,reading) \<Rightarrow>
     let I=map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r);
       issued=development_seed_issue_using construct judge xs selected r reading;
       Q=map_option (\<lambda>(B,rows,Q). Q) issued;
       G=development_seed_answer_using construct judge development_seed_state r issued;
       H=development_seed_answer_using construct judge development_seed_renamed r issued
     in (Q,G,H,publish [(None,Q),(I,G),(I,H)],
       map_option generation_payload G=map_option generation_payload H))"
  by (cases issue) (simp add: development_seed_publication_row_with_def seed_round_row_def seed_plain_row_def Let_def)

lemma development_seed_publication_row_published:
  "development_seed_publication_row construct judge xs selected S0=
    development_seed_publication_row_with (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)
      construct judge xs selected"
proof (rule ext)
  fix issue
  show "development_seed_publication_row construct judge xs selected S0 issue=
    development_seed_publication_row_with (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)
      construct judge xs selected issue"
    by (cases issue) (simp only: development_seed_publication_row_def development_seed_publication_row_with_eq
      prod.case Let_def)
qed

definition seed_plain_among :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
    development_seed_decisions option \<Rightarrow> finite_exact_target seed_reps\<times>unit" where
  "seed_plain_among construct judge xs decisions=((map (\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) xs,
     (case decisions of None \<Rightarrow> None | Some (selected,issues) \<Rightarrow> map_option (\<lambda>(B,u,G). G)
       (development_selection_generation_with judge (fst (snd development_seed_state)) selected
         (finite_enumerated_environment [] []) [])),
     (case decisions of None \<Rightarrow> [] | Some (selected,issues) \<Rightarrow>
       Parallel.map (seed_plain_row construct judge xs selected) issues)),())"

definition development_seed_publication_among ::
    "(finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
      development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_incumbent list \<Rightarrow>
      development_seed_decisions option \<Rightarrow> development_seed_publication" where
  "development_seed_publication_among P construct judge xs decisions=
    seed_round_assemble (seed_plain_among construct judge xs decisions) (\<lambda>s. P) decisions"

lemma development_seed_publication_among_eq:
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
proof -
  have S0: "map_option fset_of_list (those (map (\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) xs))=development_seed_snapshot xs"
    by (simp add: development_seed_snapshot_def)
  have rows: "map (seed_round_row publish) (map (seed_plain_row construct judge xs selected) issues)=
      map (development_seed_publication_row_with publish construct judge xs selected) issues" for publish selected issues
    by (induction issues) (simp_all add: development_seed_publication_row_with_def)
  have published: "map (\<lambda>(I,Q,G,H). (None,Q)) (map (seed_plain_row construct judge xs selected) issues)@
      map (\<lambda>(I,Q,G,H). (I,G)) (map (seed_plain_row construct judge xs selected) issues)=
    map (\<lambda>(Q,G,H,results,equal). (None,Q)) (map (development_seed_publication_row_with publish construct judge xs selected) issues)@
      map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip (map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G)
        (development_seed_incumbent_of xs r)) issues) (map (development_seed_publication_row_with publish construct judge xs selected) issues))"
    for publish selected issues
    by (induction issues) (auto simp: seed_plain_row_def development_seed_publication_row_with_def seed_round_row_def Let_def)
  show ?thesis
  proof (cases decisions)
    case None
    then show ?thesis
      by (simp add: development_seed_publication_among_def seed_round_assemble_def seed_plain_among_def Let_def
        Parallel.map_def S0)
  next
    case (Some d)
    obtain selected issues where d: "d=(selected,issues)" by (cases d)
    show ?thesis
      by (simp only: development_seed_publication_among_def seed_round_assemble_def seed_plain_among_def prod.case
        Let_def S0 Parallel.map_def rows Some d option.case
        published[where publish="case development_seed_snapshot xs of None \<Rightarrow> (\<lambda>ps. []) | Some x \<Rightarrow> P x"])
  qed
qed

definition development_seed_incumbents_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_problem list \<Rightarrow> development_seed_incumbent list" where
  "development_seed_incumbents_using construct judge ps=Parallel.map (\<lambda>p. (p,
     Option.bind (development_incumbent_key development_seed_state p)
       (\<lambda>(l,t). development_payload_generation_using construct judge t (finite_enumerated_environment [] []) l []))) ps"

lemma seed_incumbents_record:
  "development_seed_incumbents_using finite_construct_generation_record judge ps=development_seed_incumbents_with judge ps"
  by (simp add: development_seed_incumbents_using_def development_seed_incumbents_with_def development_incumbent_with_def
    development_payload_generation_using_original)

theorem seed_round_assemble_plain:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "seed_round_assemble (seed_plain_reps (seed_made_round_of L incumbent construct decisions)) (\<lambda>s. P) decisions=
    development_seed_publication_among P construct judge
      (development_seed_incumbents_using incumbent judge development_seed_problems) decisions"
proof -
  let ?inc="\<lambda>p. seed_record L incumbent (development_incumbent_key development_seed_state p)
    (finite_enumerated_environment [] []) []"
  let ?xs="development_seed_incumbents_using incumbent judge development_seed_problems"
  have incs: "zip development_seed_problems (map fst (Parallel.map ?inc development_seed_problems))=?xs"
    by (simp add: Parallel.map_def zip_map2 zip_same_conv_map development_seed_incumbents_using_def
      seed_record_result[OF judged])
  have ireps: "map (\<lambda>p. seed_made_generation (?inc p)) development_seed_problems=
      map (\<lambda>(p,x). map_option (\<lambda>(B,u,G). G) x) ?xs"
    by (simp add: development_seed_incumbents_using_def Parallel.map_def seed_made_generation_def
      seed_record_result[OF judged] o_def)
  have rows: "map seed_row_plain_reps (Parallel.map (seed_row_made L construct ?xs selected) issues)=
      map (seed_plain_row construct judge ?xs selected) issues" for selected issues
    by (simp add: Parallel.map_def seed_row_made_plain[OF judged])
  have reps: "seed_plain_reps (seed_made_round_of L incumbent construct decisions)=
      seed_plain_among construct judge ?xs decisions"
  proof (cases decisions)
    case None
    then show ?thesis
      by (simp add: seed_plain_reps_def seed_made_round_of_def seed_plain_among_def Let_def Parallel.map_def o_def
        ireps[symmetric])
  next
    case (Some d)
    obtain selected issues where d: "d=(selected,issues)" by (cases d)
    have selection: "seed_made_generation (seed_row_selection L finite_construct_generation_record selected
        (finite_enumerated_environment [] []))=map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge
          (fst (snd development_seed_state)) selected (finite_enumerated_environment [] []) [])"
      by (simp add: seed_made_generation_def seed_row_selection_result[OF judged] development_selection_generation_with_def)
    have made: "seed_made_round_of L incumbent construct (Some (selected,issues))=(Parallel.map ?inc development_seed_problems,
        seed_row_selection L finite_construct_generation_record selected (finite_enumerated_environment [] []),
        Parallel.map (seed_row_made L construct ?xs selected) issues)"
      by (simp only: seed_made_round_of_def Let_def option.case prod.case incs)
    show ?thesis
      by (simp add: made seed_plain_reps_def selection rows[symmetric] seed_row_plain_reps_def Parallel.map_def o_def
        seed_plain_among_def Some d ireps[symmetric])
  qed
  show ?thesis by (simp only: development_seed_publication_among_def reps)
qed

definition development_seed_publication_over ::
    "(finite_snapshot \<Rightarrow> (finite_generation option\<times>finite_generation option) list \<Rightarrow> finite_transaction_result option list) \<Rightarrow>
      development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> development_seed_decisions option \<Rightarrow>
      development_seed_publication" where
  "development_seed_publication_over P construct judge decisions=fst (development_seed_round (\<lambda>t. (judge t,()))
     finite_construct_generation_record construct seed_plain_reps (\<lambda>s. P) decisions)"

lemma development_seed_publication_over_eq:
  "development_seed_publication_over P construct judge decisions=development_seed_publication_among P construct judge
     (development_seed_incumbents_with judge development_seed_problems) decisions"
  by (simp add: development_seed_publication_over_def development_seed_round_def seed_round_assemble_plain
    seed_incumbents_record)

definition development_seed_publication_from :: "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow>
    development_seed_decisions option \<Rightarrow> development_seed_publication" where
  "development_seed_publication_from construct judge decisions=
    development_seed_publication_over finite_locus_publications construct judge decisions"

lemma development_seed_publication_from_eq:
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
proof -
  have publish: "(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> finite_locus_publications S)=
      (\<lambda>ps. case S0 of None \<Rightarrow> [] | Some S \<Rightarrow> finite_locus_publications S ps)" for S0 :: "finite_snapshot option"
    by (cases S0) simp_all
  show ?thesis
    by (simp only: development_seed_publication_from_def development_seed_publication_over_eq
      development_seed_publication_among_eq development_seed_publication_row_published publish Let_def)
qed

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
  by (simp add: development_seed_publication_from_eq development_seed_publication_row_known Let_def
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
    using row by (auto simp: shape development_seed_publication_row_with_eq Let_def
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
    by (simp only: shape development_seed_publication_row_with_eq prod.case Let_def agree[OF formed])
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
    then show ?thesis by (simp add: development_seed_publication_over_eq development_seed_publication_among_eq)
  next
    case (Some d)
    obtain selected issues where d: "d=(selected,issues)" by (cases d) auto
    show ?thesis
      by (simp only: development_seed_publication_over_eq development_seed_publication_among_eq Let_def Some d
        prod.case option.case rows
        agree[OF development_seed_publication_round_formed])
  qed
qed

lemma development_seed_publication_row_with_publisher:
  "development_seed_publication_row_with P construct judge xs selected (r,reading)=
    (case development_seed_publication_row_with P' construct judge xs selected (r,reading) of (Q,G,H,results,equal) \<Rightarrow>
      (Q,G,H,P [(None,Q),(map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),G),
        (map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r),H)],equal))"
  by (simp add: development_seed_publication_row_with_eq Let_def)

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
  by (simp add: development_seed_publication_over_eq development_seed_publication_among_eq
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
  by (simp only: development_seed_publication_def development_seed_publication_from_def
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
  by (intro ext) (simp only: development_seed_publication_row_with_eq development_seed_issue_using_def
    development_seed_answer_using_def development_recorded_issue_using_formed_causes[OF judge]
    development_answer_using_formed_causes[OF judge])

lemma development_seed_publication_among_formed_causes:
  assumes judge: "development_judge_formed_causes judge"
  shows "development_seed_publication_among P finite_construct_formed_cause_generation judge xs decisions=
    development_seed_publication_among P finite_construct_known_original_generation judge xs decisions"
  by (simp only: development_seed_publication_among_eq development_seed_publication_row_with_formed_causes[OF judge])

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
  show ?thesis by (simp only: development_seed_publication_among_eq Let_def publish)
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
    development_seed_publication_over_eq development_seed_publication_among_loci
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
