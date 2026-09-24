theory Development_Seed_Referenced_Publication
  imports Development_Seed_Publication Represented_Snapshot_Transactions Presented_Publication_Values
    Shared_Term_Words
begin

section \<open>The seed round holds its targets once, where they are made\<close>

text \<open>
  The round is stated once over its representation: how a recorded generation is represented, and how the
  represented generations are published. At the plain representation a generation is itself and the
  round's publications are the existing ones; at the reference representation a generation holds
  references into the round's table, the first-occurrence table of the targets the round makes, each
  entered once where it is made: the loci and the payload and cause of every prepared judgment before the
  parallel rows, and a target made inside a row whose judgment was not prepared after the rows, by value.
\<close>

subsection \<open>A target's key in the round's table\<close>

fun seed_target_occurrence :: "finite_exact_target \<Rightarrow> local_address option" where
  "seed_target_occurrence (Finite_Whole a)=None"
| "seed_target_occurrence (Finite_Anchor a r)=Some r"

definition seed_target_key :: "finite_exact_target \<Rightarrow> compared_artifact_rows\<times>local_address option" where
  "seed_target_key x=(compared_artifact_rows (finite_artifact_rows (finite_target_artifact x)),seed_target_occurrence x)"

lemma seed_target_key_injective: "inj seed_target_key"
proof (rule injI)
  fix x y
  assume same: "seed_target_key x=seed_target_key y"
  show "x=y"
    using same by (cases x; cases y) (simp_all add: seed_target_key_def compared_artifact_rows_def
      finite_artifact_rows_injective)
qed

subsection \<open>A recording retains the judgment it was made with\<close>

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

subsection \<open>The round over a representation\<close>

type_synonym 'k seed_made_round = "'k seed_made list\<times>'k seed_made\<times>(development_problem\<times>'k seed_row_made) list"
type_synonym 't seed_reps = "'t generation_structure option list\<times>'t generation_structure option\<times>
  ('t generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>
    't generation_structure option) list"
type_synonym ('t,'r) seed_round = "'t represented_snapshot option\<times>'t generation_structure option\<times>
  ('t generation_structure option\<times>'t generation_structure option\<times>'t generation_structure option\<times>'r option list\<times>bool) list\<times>
  'r option list"

definition seed_made_round_of :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    development_seed_decisions option \<Rightarrow> 'k seed_made_round" where
  "seed_made_round_of L construct decisions=(let
     incs=Parallel.map (\<lambda>p. seed_record L construct (development_incumbent_key development_seed_state p)
       (finite_enumerated_environment [] []) []) development_seed_problems;
     xs=zip development_seed_problems (map fst incs)
   in (case decisions of None \<Rightarrow> (incs,(None,None),[])
     | Some (selected,issues) \<Rightarrow> (incs,seed_row_selection L finite_construct_generation_record selected
           (finite_enumerated_environment [] []),
         Parallel.map (seed_row_made L construct xs selected) issues)))"

definition seed_round_assemble :: "'t seed_reps\<times>'s \<Rightarrow>
    ('s \<Rightarrow> 't represented_snapshot \<Rightarrow> ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 'r option list) \<Rightarrow>
    development_seed_decisions option \<Rightarrow> ('t,'r) seed_round" where
  "seed_round_assemble represented pub decisions=(case represented of ((ireps,sel,rows),s) \<Rightarrow> let
     S0=map_option fset_of_list (those ireps);
     publish=(case S0 of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> pub s S)
   in (S0,sel,Parallel.map (\<lambda>(I,Q,G,H). (Q,G,H,publish [(None,Q),(I,G),(I,H)],
       map_option generation_payload G=map_option generation_payload H)) rows,
     (case decisions of None \<Rightarrow> [] | Some d \<Rightarrow>
       publish ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@map (\<lambda>(I,Q,G,H). (I,G)) rows))))"

definition development_seed_round :: "(finite_factor_term \<Rightarrow> seed_judged\<times>'k) \<Rightarrow> development_constructor \<Rightarrow>
    ('k seed_made_round \<Rightarrow> 't seed_reps\<times>'s) \<Rightarrow>
    ('s \<Rightarrow> 't represented_snapshot \<Rightarrow> ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 'r option list) \<Rightarrow>
    development_seed_decisions option \<Rightarrow> ('t,'r) seed_round\<times>'s" where
  "development_seed_round L construct represent pub decisions=(let
     represented=represent (seed_made_round_of L construct decisions)
   in (seed_round_assemble represented pub decisions,snd represented))"

subsection \<open>The plain representation\<close>

definition seed_plain_reps :: "'k seed_made_round \<Rightarrow> finite_exact_target seed_reps\<times>unit" where
  "seed_plain_reps m=(case m of (incs,sel,rows) \<Rightarrow> ((map seed_made_generation incs,seed_made_generation sel,
     map (\<lambda>(p,I,S,Q,rG,G,rH,H). (I,seed_made_generation Q,seed_made_generation G,seed_made_generation H)) rows),()))"

definition development_seed_plain_round :: "development_problem fset \<Rightarrow> development_seed_publication" where
  "development_seed_plain_round A=fst (development_seed_round (\<lambda>t. (development_payload_judgment t,()))
     finite_construct_generation_record seed_plain_reps (\<lambda>s S. finite_locus_publications S) (development_seed_decisions A))"

lemma seed_incumbents_record:
  "development_seed_incumbents_using finite_construct_generation_record judge ps=development_seed_incumbents_with judge ps"
  by (simp add: development_seed_incumbents_using_def development_seed_incumbents_with_def development_incumbent_with_def
    development_payload_generation_using_original)

lemma seed_zip_map: "zip xs (map f xs)=map (\<lambda>x. (x,f x)) xs"
  by (induction xs) simp_all

theorem seed_round_assemble_plain:
  assumes judged: "\<And>t. fst (L t)=judge t"
  shows "seed_round_assemble (seed_plain_reps (seed_made_round_of L construct decisions)) (\<lambda>s. P) decisions=
    development_seed_publication_among P construct judge
      (development_seed_incumbents_using construct judge development_seed_problems) decisions"
proof -
  let ?inc="\<lambda>p. seed_record L construct (development_incumbent_key development_seed_state p)
    (finite_enumerated_environment [] []) []"
  let ?xs="development_seed_incumbents_using construct judge development_seed_problems"
  have incs: "zip development_seed_problems (map fst (Parallel.map ?inc development_seed_problems))=?xs"
    by (simp add: Parallel.map_def seed_zip_map development_seed_incumbents_using_def seed_record_result[OF judged])
  have snapshot: "map_option fset_of_list (those (map (\<lambda>p. seed_made_generation (?inc p)) development_seed_problems))=
      development_seed_snapshot ?xs"
    by (simp add: development_seed_snapshot_def development_seed_incumbents_using_def Parallel.map_def seed_made_generation_def
      seed_record_result[OF judged] o_def)
  have rows: "map seed_row_plain_reps (Parallel.map (seed_row_made L construct ?xs selected) issues)=
      map (seed_plain_row construct judge ?xs selected) issues" for selected issues
    by (simp add: Parallel.map_def seed_row_made_plain[OF judged])
  have row: "(\<lambda>(I,Q,G,H). (Q,G,H,publish [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (seed_plain_row construct judge ?xs selected issue)=
      development_seed_publication_row_with publish construct judge ?xs selected issue" for publish selected issue
    by (cases issue) (simp add: seed_plain_row_def development_seed_publication_row_with_def Let_def)
  have published: "map (\<lambda>(I,Q,G,H). (None,Q)) (map (seed_plain_row construct judge ?xs selected) issues)@
      map (\<lambda>(I,Q,G,H). (I,G)) (map (seed_plain_row construct judge ?xs selected) issues)=
    map (\<lambda>(Q,G,H,results,equal). (None,Q)) (map (development_seed_publication_row_with publish construct judge ?xs selected) issues)@
      map (\<lambda>(I,(Q,G,H,results,equal)). (I,G)) (zip (map (\<lambda>(r,reading). map_option (\<lambda>(B,u,G). G)
        (development_seed_incumbent_of ?xs r)) issues) (map (development_seed_publication_row_with publish construct judge ?xs selected) issues))"
    for publish selected issues
    by (induction issues) (auto simp: seed_plain_row_def development_seed_publication_row_with_def Let_def)
  show ?thesis
  proof (cases decisions)
    case None
    then show ?thesis
      by (simp add: seed_round_assemble_def seed_plain_reps_def seed_made_round_of_def development_seed_publication_among_def
        Let_def Parallel.map_def o_def snapshot)
  next
    case (Some d)
    obtain selected issues where d: "d=(selected,issues)" by (cases d)
    have selection: "seed_made_generation (seed_row_selection L finite_construct_generation_record selected
        (finite_enumerated_environment [] []))=map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge
          (fst (snd development_seed_state)) selected (finite_enumerated_environment [] []) [])"
      by (simp add: seed_made_generation_def seed_row_selection_result[OF judged] development_selection_generation_with_def)
    have made: "seed_made_round_of L construct decisions=(Parallel.map ?inc development_seed_problems,
        seed_row_selection L finite_construct_generation_record selected (finite_enumerated_environment [] []),
        Parallel.map (seed_row_made L construct ?xs selected) issues)"
      by (simp only: seed_made_round_of_def Let_def Some d option.case prod.case incs)
    have reps: "seed_plain_reps (seed_made_round_of L construct decisions)=
        ((map (\<lambda>p. seed_made_generation (?inc p)) development_seed_problems,
          map_option (\<lambda>(B,u,G). G) (development_selection_generation_with judge (fst (snd development_seed_state)) selected
            (finite_enumerated_environment [] []) []),
          map (seed_plain_row construct judge ?xs selected) issues),())"
      by (simp add: made seed_plain_reps_def selection rows[symmetric] seed_row_plain_reps_def Parallel.map_def o_def)
    have rowsmap: "map (\<lambda>(I,Q,G,H). (Q,G,H,publish [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (map (seed_plain_row construct judge ?xs selected) issues)=
      map (development_seed_publication_row_with publish construct judge ?xs selected) issues" for publish
      by (induction issues) (simp_all add: row)
    show ?thesis
      by (simp only: reps[unfolded Some d] seed_round_assemble_def prod.case Let_def snapshot Parallel.map_def rowsmap
        published[where publish="case development_seed_snapshot ?xs of None \<Rightarrow> (\<lambda>ps. []) | Some x \<Rightarrow> P x"]
        development_seed_publication_among_def Some d option.case)
  qed
qed

theorem development_seed_plain_round_exact: "development_seed_plain_round A=development_seed_publication A"
proof -
  have "development_seed_plain_round A=development_seed_publication_among finite_locus_publications
      finite_construct_generation_record development_payload_judgment
      (development_seed_incumbents_using finite_construct_generation_record development_payload_judgment development_seed_problems)
      (development_seed_decisions A)"
    by (simp add: development_seed_plain_round_def development_seed_round_def seed_round_assemble_plain)
  also have "\<dots>=development_seed_publication A"
    by (simp add: development_seed_publication_def development_seed_publication_from_published
      development_seed_publication_over_def seed_incumbents_record)
  finally show ?thesis .
qed

subsection \<open>The reference representation\<close>

text \<open>
  The round's table is the first-occurrence table of the targets it makes, built by
  \<open>keyed_reference_step\<close> at a target's rows key. The loci of every problem and of the selection and the
  payload and cause of every prepared judgment are entered before the parallel rows; a recording made with
  a prepared judgment holds that judgment's references. After the rows, the loci of the made generations are
  looked up and the payload and cause of a generation whose judgment was not prepared are entered by value.
\<close>

type_synonym seed_state = "(compared_artifact_rows\<times>local_address option,nat) rbt\<times>nat\<times>finite_exact_target list"

fun seed_keyed_sequence :: "finite_exact_target list \<Rightarrow> seed_state \<Rightarrow> nat list\<times>seed_state" where
  "seed_keyed_sequence [] q=([],q)"
| "seed_keyed_sequence (x#xs) q=(case keyed_reference_step seed_target_key x q of (i,q1) \<Rightarrow>
     (case seed_keyed_sequence xs q1 of (is,q2) \<Rightarrow> (i#is,q2)))"

lemma seed_keyed_sequence_exact:
  "keyed_reference_state seed_target_key q T \<Longrightarrow>
    fst (seed_keyed_sequence xs q)=fst (value_reference_sequence xs T) \<and>
    keyed_reference_state seed_target_key (snd (seed_keyed_sequence xs q)) (snd (value_reference_sequence xs T))"
proof (induction xs arbitrary: q T)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  note step=keyed_reference_step_exact[OF seed_target_key_injective Cons.prems, of x]
  obtain i q1 where q1: "keyed_reference_step seed_target_key x q=(i,q1)" by (cases "keyed_reference_step seed_target_key x q")
  obtain j T1 where T1: "value_reference_step x T=(j,T1)" by (cases "value_reference_step x T")
  have ij: "i=j" and rep: "keyed_reference_state seed_target_key q1 T1" using step by (simp_all add: q1 T1)
  note rest=Cons.IH[OF rep]
  show ?case using rest by (simp add: q1 T1 ij case_prod_unfold Let_def)
qed

lemma seed_state_table: "keyed_reference_state seed_target_key q T \<Longrightarrow> T=rev (snd (snd q))"
  by (cases q) (simp add: keyed_reference_state_def)

lemma seed_state_empty: "keyed_reference_state seed_target_key (RBT.empty,0,[]) []"
  by (simp add: keyed_reference_state_def)

definition seed_cause :: "finite_exact_artifact\<times>development_policy_judgment \<Rightarrow> finite_exact_artifact" where
  "seed_cause v=snd (snd (snd (snd (snd (snd (snd (snd v)))))))"

lemma seed_payload_generation_using:
  "development_payload_generation_using construct judge t H l rows=
    Option.bind (judge t) (\<lambda>v. construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows)"
  by (simp add: development_payload_generation_using_def seed_cause_def case_prod_unfold)

definition seed_judged_targets :: "seed_judged \<Rightarrow> finite_exact_target list" where
  "seed_judged_targets j=(case j of None \<Rightarrow> [] | Some v \<Rightarrow> [Finite_Whole (fst v),Finite_Whole (seed_cause v)])"

fun seed_prepared_refs :: "nat list \<Rightarrow> (finite_factor_term\<times>seed_judged) list \<Rightarrow>
    (finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list" where
  "seed_prepared_refs ns []=[]"
| "seed_prepared_refs ns ((t,None)#cs)=(t,None,None)#seed_prepared_refs ns cs"
| "seed_prepared_refs ns ((t,Some v)#cs)=(t,Some v,Some (ns!0,ns!1))#seed_prepared_refs (drop 2 ns) cs"

definition seed_loci :: "development_problem list \<Rightarrow> finite_exact_target list" where
  "seed_loci ps=List.map_filter id (development_data_target development_selection_locus#
     concat (map (\<lambda>p. [development_locus_target Development_Problem_Role p,
       development_locus_target Development_Issue_Role p]) ps))"

definition seed_prepared :: "finite_factor_term list \<Rightarrow> (finite_factor_term\<times>seed_judged) list" where
  "seed_prepared keys=Parallel.map (\<lambda>t. (t,development_payload_judgment t)) (remdups keys)"

definition seed_lookup :: "(finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list \<Rightarrow> finite_factor_term \<Rightarrow>
    seed_judged\<times>(nat\<times>nat) option" where
  "seed_lookup cs t=(case map_of cs t of Some v \<Rightarrow> v | None \<Rightarrow> (development_payload_judgment t,None))"

definition seed_made_targets :: "(nat\<times>nat) option seed_made \<Rightarrow> finite_exact_target list" where
  "seed_made_targets m=(case fst m of None \<Rightarrow> [] | Some (B,u,G) \<Rightarrow> generation_locus G#
     (case snd m of Some (Some ab) \<Rightarrow> [] | _ \<Rightarrow> [generation_payload G,generation_cause G]))"

definition seed_made_rep :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made \<Rightarrow> nat generation_structure list \<Rightarrow>
    nat generation_structure option" where
  "seed_made_rep ns m ps=(case fst m of None \<Rightarrow> None | Some (B,u,G) \<Rightarrow> Some (case snd m of
     Some (Some (a,b)) \<Rightarrow> Generation (ns!0) (fset_of_list ps) a b
   | _ \<Rightarrow> Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2)))"

fun seed_consume_list :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made list \<Rightarrow> nat generation_structure option list" where
  "seed_consume_list ns []=[]"
| "seed_consume_list ns (m#ms)=seed_made_rep ns m []#seed_consume_list (drop (length (seed_made_targets m)) ns) ms"

definition seed_row_targets :: "development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow> finite_exact_target list" where
  "seed_row_targets row=(case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow>
     seed_made_targets S@seed_made_targets Q@seed_made_targets G@seed_made_targets H)"

definition seed_row_rep :: "nat generation_structure option list \<Rightarrow> nat list \<Rightarrow>
    development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>
      nat generation_structure option" where
  "seed_row_rep ireps ns row=(case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow> let
     Ir=Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd;
     n1=drop (length (seed_made_targets S)) ns; Sr=seed_made_rep ns S [];
     n2=drop (length (seed_made_targets Q)) n1; Qr=seed_made_rep n1 Q (List.map_filter id [Ir,Sr]);
     n3=drop (length (seed_made_targets G)) n2; Gr=seed_made_rep n2 G (map (\<lambda>x. the Qr) rG);
     Hr=seed_made_rep n3 H (map (\<lambda>x. the Qr) rH)
   in (Ir,Qr,Gr,Hr))"

fun seed_rows_rep :: "nat generation_structure option list \<Rightarrow> nat list \<Rightarrow>
    (development_problem\<times>(nat\<times>nat) option seed_row_made) list \<Rightarrow>
    (nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>
      nat generation_structure option) list" where
  "seed_rows_rep ireps ns []=[]"
| "seed_rows_rep ireps ns (row#rows)=seed_row_rep ireps ns row#
     seed_rows_rep ireps (drop (length (seed_row_targets row)) ns) rows"

definition seed_round_targets :: "(nat\<times>nat) option seed_made_round \<Rightarrow> finite_exact_target list" where
  "seed_round_targets m=(case m of (incs,sel,rows) \<Rightarrow>
     concat (map seed_made_targets incs)@seed_made_targets sel@concat (map seed_row_targets rows))"

definition seed_reps_of :: "nat list \<Rightarrow> (nat\<times>nat) option seed_made_round \<Rightarrow> nat seed_reps" where
  "seed_reps_of ns m=(case m of (incs,sel,rows) \<Rightarrow> let
     ireps=seed_consume_list ns incs;
     n1=drop (length (concat (map seed_made_targets incs))) ns;
     n2=drop (length (seed_made_targets sel)) n1
   in (ireps,seed_made_rep n1 sel [],seed_rows_rep ireps n2 rows))"

definition seed_reference_reps :: "seed_state \<Rightarrow> (nat\<times>nat) option seed_made_round \<Rightarrow>
    nat seed_reps\<times>finite_exact_target list" where
  "seed_reference_reps q0 m=(case seed_keyed_sequence (seed_round_targets m) q0 of (ns,q) \<Rightarrow>
     (seed_reps_of ns m,rev (snd (snd q))))"

definition seed_reference_pub :: "finite_exact_target list \<Rightarrow> nat represented_snapshot \<Rightarrow>
    (nat generation_structure option\<times>nat generation_structure option) list \<Rightarrow> nat represented_transaction_result option list" where
  "seed_reference_pub T S=(if represented_snapshot_loci_formed S
     then represented_locus_publications_body (\<lambda>i. finite_target_formed (T!i)) S else map (\<lambda>q. None))"

definition seed_prepared_state :: "development_seed_decisions option \<Rightarrow>
    (finite_factor_term\<times>seed_judged\<times>(nat\<times>nat) option) list\<times>seed_state" where
  "seed_prepared_state decisions=(let
     cache=seed_prepared (development_seed_family_keys@development_seed_decision_keys decisions);
     entered=seed_keyed_sequence (seed_loci development_seed_problems@concat (map (\<lambda>(t,j). seed_judged_targets j) cache))
       (RBT.empty,0,[])
   in (seed_prepared_refs (drop (length (seed_loci development_seed_problems)) (fst entered)) cache,snd entered))"

definition development_seed_reference_round :: "development_problem fset \<Rightarrow>
    (nat,nat represented_transaction_result) seed_round\<times>finite_exact_target list" where
  "development_seed_reference_round A=(let decisions=development_seed_decisions A; prepared=seed_prepared_state decisions
   in development_seed_round (seed_lookup (fst prepared)) finite_construct_formed_cause_generation
     (seed_reference_reps (snd prepared)) seed_reference_pub decisions)"

subsection \<open>Reading references\<close>

definition seed_reads :: "finite_exact_target list \<Rightarrow> nat list \<Rightarrow> finite_exact_target list \<Rightarrow> bool" where
  "seed_reads T ns xs \<longleftrightarrow> length xs\<le>length ns \<and> (\<forall>i<length xs. value_reference_read T (ns!i)=Some (xs!i))"

lemma seed_reads_append:
  "seed_reads T ns (xs@ys) \<longleftrightarrow> seed_reads T ns xs \<and> seed_reads T (drop (length xs) ns) ys"
proof
  assume whole: "seed_reads T ns (xs@ys)"
  show "seed_reads T ns xs \<and> seed_reads T (drop (length xs) ns) ys"
  proof
    show "seed_reads T ns xs" unfolding seed_reads_def
    proof (intro conjI allI impI)
      show "length xs\<le>length ns" using whole by (simp add: seed_reads_def)
      fix i
      assume i: "i<length xs"
      have "value_reference_read T (ns!i)=Some ((xs@ys)!i)" using whole i by (simp add: seed_reads_def)
      then show "value_reference_read T (ns!i)=Some (xs!i)" using i by (simp add: nth_append)
    qed
    show "seed_reads T (drop (length xs) ns) ys" unfolding seed_reads_def
    proof (intro conjI allI impI)
      show "length ys\<le>length (drop (length xs) ns)" using whole by (auto simp: seed_reads_def)
      fix i
      assume i: "i<length ys"
      have bound: "length xs\<le>length ns" using whole by (simp add: seed_reads_def)
      have "value_reference_read T (ns!(length xs+i))=Some ((xs@ys)!(length xs+i))"
        using whole i by (simp add: seed_reads_def)
      then show "value_reference_read T (drop (length xs) ns!i)=Some (ys!i)" using bound by (simp add: nth_append)
    qed
  qed
next
  assume parts: "seed_reads T ns xs \<and> seed_reads T (drop (length xs) ns) ys"
  show "seed_reads T ns (xs@ys)" unfolding seed_reads_def
  proof (intro conjI allI impI)
    show "length (xs@ys)\<le>length ns" using parts by (auto simp: seed_reads_def)
    fix i
    assume i: "i<length (xs@ys)"
    show "value_reference_read T (ns!i)=Some ((xs@ys)!i)"
    proof (cases "i<length xs")
      case True
      then show ?thesis using parts by (simp add: seed_reads_def nth_append)
    next
      case False
      then obtain k where k: "i=length xs+k" by (metis le_add_diff_inverse not_less)
      have "k<length ys" using i k by simp
      then have "value_reference_read T (drop (length xs) ns!k)=Some (ys!k)" using parts unfolding seed_reads_def by blast
      moreover have "length xs\<le>length ns" using parts by (simp add: seed_reads_def)
      ultimately show ?thesis using k by (simp add: nth_append)
    qed
  qed
qed

lemma seed_reads_cons:
  "seed_reads T ns (x#xs) \<longleftrightarrow> ns\<noteq>[] \<and> value_reference_read T (ns!0)=Some x \<and> seed_reads T (drop 1 ns) xs"
proof -
  have "seed_reads T ns ([x]@xs) \<longleftrightarrow> seed_reads T ns [x] \<and> seed_reads T (drop 1 ns) xs"
    by (simp only: seed_reads_append) simp
  moreover have "seed_reads T ns [x] \<longleftrightarrow> ns\<noteq>[] \<and> value_reference_read T (ns!0)=Some x"
    by (cases ns) (auto simp: seed_reads_def)
  ultimately show ?thesis by simp
qed

lemma seed_reads_sequence:
  "seed_reads (snd (value_reference_sequence xs T)) (fst (value_reference_sequence xs T)) xs"
proof -
  have exact: "map (value_reference_read (snd (value_reference_sequence xs T))) (fst (value_reference_sequence xs T))=map Some xs"
    by (rule value_reference_sequence_exact)
  then have length: "length (fst (value_reference_sequence xs T))=length xs" by (metis length_map)
  show ?thesis unfolding seed_reads_def
  proof (intro conjI allI impI)
    show "length xs\<le>length (fst (value_reference_sequence xs T))" using length by simp
    fix i
    assume "i<length xs"
    then show "value_reference_read (snd (value_reference_sequence xs T)) (fst (value_reference_sequence xs T)!i)=Some (xs!i)"
      using arg_cong[OF exact, of "\<lambda>l. l!i"] length by simp
  qed
qed

lemma seed_reads_preserved:
  assumes reads: "seed_reads T ns xs"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "seed_reads T' ns xs"
  using reads kept by (simp add: seed_reads_def)

lemma seed_read_bound: "value_reference_read T i=Some x \<Longrightarrow> i<length T \<and> T!i=x"
  by (simp add: value_reference_read_def split: if_splits)

subsection \<open>Every recorded generation is represented\<close>

definition seed_represents :: "finite_exact_target list \<Rightarrow> nat generation_structure \<Rightarrow> finite_generation \<Rightarrow> bool" where
  "seed_represents T g G \<longleftrightarrow> set_generation_structure g\<subseteq>{..<length T} \<and> map_generation_structure (\<lambda>i. T!i) g=G"

definition seed_made_valid :: "finite_exact_target list \<Rightarrow> development_generation_row list \<Rightarrow>
    (nat\<times>nat) option seed_made \<Rightarrow> bool" where
  "seed_made_valid T rows m \<longleftrightarrow> (\<forall>B u G. fst m=Some (B,u,G) \<longrightarrow>
     generation_predecessors G=fset_of_list (map snd rows) \<and>
     (\<forall>a b. snd m=Some (Some (a,b)) \<longrightarrow>
       value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)))"

lemma seed_made_valid_preserved:
  assumes valid: "seed_made_valid T rows m"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "seed_made_valid T' rows m"
  using valid kept by (auto simp: seed_made_valid_def)

lemma seed_represents_generation:
  assumes bounds: "k<length T" "a<length T" "b<length T"
    and inside: "\<And>g. g\<in>set ps \<Longrightarrow> set_generation_structure g\<subseteq>{..<length T}"
  shows "seed_represents T (Generation k (fset_of_list ps) a b)
    (Generation (T!k) (fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)) (T!a) (T!b))"
  unfolding seed_represents_def
proof
  show "set_generation_structure (Generation k (fset_of_list ps) a b)\<subseteq>{..<length T}"
    using bounds by (auto simp: fset_of_list_elem dest!: inside)
  show "map_generation_structure (\<lambda>i. T!i) (Generation k (fset_of_list ps) a b)=
    Generation (T!k) (fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)) (T!a) (T!b)"
    by simp
qed

lemma seed_represents_list:
  assumes preds: "list_all2 (seed_represents T) ps Gs"
  shows "fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)=fset_of_list Gs"
    and "\<And>g. g\<in>set ps \<Longrightarrow> set_generation_structure g\<subseteq>{..<length T}"
proof -
  have "map (map_generation_structure (\<lambda>i. T!i)) ps=Gs"
  proof (rule nth_equalityI)
    show "length (map (map_generation_structure (\<lambda>i. T!i)) ps)=length Gs" using preds by (simp add: list_all2_lengthD)
    fix i
    assume "i<length (map (map_generation_structure (\<lambda>i. T!i)) ps)"
    then show "map (map_generation_structure (\<lambda>i. T!i)) ps!i=Gs!i"
      using preds by (auto simp: list_all2_conv_all_nth seed_represents_def)
  qed
  then show "fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)=fset_of_list Gs"
    by (metis fset_of_list_map)
  fix g
  assume "g\<in>set ps"
  then obtain i where i: "i<length ps" "g=ps!i" by (auto simp: in_set_conv_nth)
  then show "set_generation_structure g\<subseteq>{..<length T}"
    using preds by (auto simp: list_all2_conv_all_nth seed_represents_def)
qed

lemma seed_made_rep_represents:
  assumes valid: "seed_made_valid T rows m"
    and reads: "seed_reads T ns (seed_made_targets m)"
    and preds: "list_all2 (seed_represents T) ps (map snd rows)"
  shows "rel_option (seed_represents T) (seed_made_rep ns m ps) (seed_made_generation m)"
proof (cases "fst m")
  case None
  then show ?thesis by (simp add: seed_made_rep_def seed_made_generation_def)
next
  case (Some x)
  obtain B u G where x: "x=(B,u,G)" by (cases x)
  have made: "fst m=Some (B,u,G)" using Some x by simp
  have gen: "seed_made_generation m=Some G" by (simp add: seed_made_generation_def made)
  have family: "fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)=generation_predecessors G"
    using valid made seed_represents_list(1)[OF preds] by (simp add: seed_made_valid_def)
  note inside=seed_represents_list(2)[OF preds]
  obtain l Q p c where G: "G=Generation l Q p c" by (cases G)
  have represented: "rel_option (seed_represents T) (Some (Generation k (fset_of_list ps) a b)) (Some G)"
    if k: "value_reference_read T k=Some l" and a: "value_reference_read T a=Some p" and b: "value_reference_read T b=Some c"
    for k a b
  proof -
    have bounds: "k<length T" "T!k=l" "a<length T" "T!a=p" "b<length T" "T!b=c"
      using seed_read_bound[OF k] seed_read_bound[OF a] seed_read_bound[OF b] by simp_all
    have "G=Generation (T!k) (fimage (map_generation_structure (\<lambda>i. T!i)) (fset_of_list ps)) (T!a) (T!b)"
      using bounds family by (simp add: G)
    then show ?thesis using seed_represents_generation[OF bounds(1,3,5) inside] by simp
  qed
  have three: "value_reference_read T (ns!0)=Some l \<and> value_reference_read T (ns!1)=Some p \<and>
      value_reference_read T (ns!2)=Some c" if targets: "seed_made_targets m=[l,p,c]"
    using reads unfolding targets seed_reads_def by (auto simp: less_Suc_eq numeral_eq_Suc)
  show ?thesis
  proof (cases "snd m")
    case (Some k)
    note token=this
    show ?thesis
    proof (cases k)
      case (Some ab)
      obtain a b where ab: "ab=(a,b)" by (cases ab)
      have targets: "seed_made_targets m=[l]" by (simp add: seed_made_targets_def made token Some ab G)
      have locus: "value_reference_read T (ns!0)=Some l"
        using reads by (simp add: targets seed_reads_cons)
      have fields: "value_reference_read T a=Some p" "value_reference_read T b=Some c"
        using valid made token Some ab by (simp_all add: seed_made_valid_def G)
      have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) a b)"
        by (simp add: seed_made_rep_def made token Some ab)
      then show ?thesis using represented[OF locus fields] gen by simp
    next
      case None
      have targets: "seed_made_targets m=[l,p,c]" by (simp add: seed_made_targets_def made token None G)
      have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2))"
        by (simp add: seed_made_rep_def made token None)
      then show ?thesis using three[OF targets] represented gen by simp
    qed
  next
    case None
    have targets: "seed_made_targets m=[l,p,c]" by (simp add: seed_made_targets_def made None G)
    have "seed_made_rep ns m ps=Some (Generation (ns!0) (fset_of_list ps) (ns!1) (ns!2))"
      by (simp add: seed_made_rep_def made None)
    then show ?thesis using three[OF targets] represented gen by simp
  qed
qed

lemma seed_made_rep_none: "fst m=None \<Longrightarrow> rel_option (seed_represents T) (seed_made_rep ns m ps) (seed_made_generation m)"
  by (simp add: seed_made_rep_def seed_made_generation_def)

subsection \<open>Every recording of the reference round is valid\<close>

definition seed_construct_core :: "development_constructor \<Rightarrow> bool" where
  "seed_construct_core construct \<longleftrightarrow> (\<forall>E l p c rows B u G. construct E l p c rows=Some (B,u,G) \<longrightarrow>
     G=Generation l (fset_of_list (map snd rows)) p c)"

lemma seed_construct_core_formed_cause: "seed_construct_core finite_construct_formed_cause_generation"
  by (auto simp: seed_construct_core_def finite_construct_formed_cause_generation_def finite_generation_record_body_def
    finite_generation_record_core_def split: if_splits)

lemma seed_construct_core_record: "seed_construct_core finite_construct_generation_record"
  by (auto simp: seed_construct_core_def finite_construct_generation_record_def finite_generation_record_body_def
    finite_generation_record_core_def split: if_splits)

definition seed_lookup_valid :: "finite_exact_target list \<Rightarrow> (finite_factor_term \<Rightarrow> seed_judged\<times>(nat\<times>nat) option) \<Rightarrow> bool" where
  "seed_lookup_valid T L \<longleftrightarrow> (\<forall>t. fst (L t)=development_payload_judgment t) \<and>
     (\<forall>t a b. snd (L t)=Some (a,b) \<longrightarrow> (\<exists>v. fst (L t)=Some v \<and>
       value_reference_read T a=Some (Finite_Whole (fst v)) \<and> value_reference_read T b=Some (Finite_Whole (seed_cause v))))"

lemma seed_lookup_valid_preserved:
  assumes valid: "seed_lookup_valid T L"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "seed_lookup_valid T' L"
  using valid kept unfolding seed_lookup_valid_def by blast

lemma seed_record_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "seed_made_valid T rows (seed_record L construct key H rows)"
proof (cases key)
  case None
  then show ?thesis by (simp add: seed_record_def seed_made_valid_def)
next
  case (Some lt)
  obtain l t where lt: "lt=(l,t)" by (cases lt)
  obtain j k where Lt: "L t=(j,k)" by (cases "L t")
  show ?thesis unfolding seed_made_valid_def
  proof (intro allI impI)
    fix B u G
    assume made: "fst (seed_record L construct key H rows)=Some (B,u,G)"
    then have bound: "Option.bind j (\<lambda>v. construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows)=Some (B,u,G)"
      by (simp add: seed_record_def Some lt Lt seed_payload_generation_using)
    then obtain v where j: "j=Some v"
      and built: "construct H l (Finite_Whole (fst v)) (Finite_Whole (seed_cause v)) rows=Some (B,u,G)"
      unfolding bind_eq_Some_conv by blast
    have G: "G=Generation l (fset_of_list (map snd rows)) (Finite_Whole (fst v)) (Finite_Whole (seed_cause v))"
      using core built by (simp add: seed_construct_core_def)
    show "generation_predecessors G=fset_of_list (map snd rows) \<and>
      (\<forall>a b. snd (seed_record L construct key H rows)=Some (Some (a,b)) \<longrightarrow>
        value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G))"
    proof
      show "generation_predecessors G=fset_of_list (map snd rows)" by (simp add: G)
      show "\<forall>a b. snd (seed_record L construct key H rows)=Some (Some (a,b)) \<longrightarrow>
        value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)"
      proof (intro allI impI)
        fix a b
        assume "snd (seed_record L construct key H rows)=Some (Some (a,b))"
        then have "snd (L t)=Some (a,b)" by (simp add: seed_record_def Some lt Lt)
        then obtain w where w: "fst (L t)=Some w" "value_reference_read T a=Some (Finite_Whole (fst w))"
          "value_reference_read T b=Some (Finite_Whole (seed_cause w))"
          using lookup unfolding seed_lookup_valid_def by blast
        have "w=v" using w(1) j Lt by simp
        then show "value_reference_read T a=Some (generation_payload G) \<and> value_reference_read T b=Some (generation_cause G)"
          using w by (simp add: G)
      qed
    qed
  qed
qed

definition seed_row_valid :: "finite_exact_target list \<Rightarrow> development_problem\<times>(nat\<times>nat) option seed_row_made \<Rightarrow> bool" where
  "seed_row_valid T row \<longleftrightarrow> (case row of (p,I,S,Q,rG,G,rH,H) \<Rightarrow> seed_made_valid T [] S \<and>
     (\<forall>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<longrightarrow> (\<exists>Ig B1 us Sel u. I=Some Ig \<and> fst S=Some (B1,us,Sel) \<and>
        seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q) \<and>
       seed_made_valid T rG G \<and> (\<forall>x\<in>set rG. snd x=Qg) \<and> seed_made_valid T rH H \<and> (\<forall>x\<in>set rH. snd x=Qg)) \<and>
     (fst Q=None \<longrightarrow> fst G=None \<and> fst H=None))"

lemma seed_row_answer_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "fst Q=Some (B2,uq,Qg) \<Longrightarrow> seed_made_valid T (fst (seed_row_answer L construct r S' Q)) (snd (seed_row_answer L construct r S' Q)) \<and>
      (\<forall>x\<in>set (fst (seed_row_answer L construct r S' Q)). snd x=Qg)"
    and "fst Q=None \<Longrightarrow> fst (snd (seed_row_answer L construct r S' Q))=None"
proof -
  assume issued: "fst Q=Some (B2,uq,Qg)"
  show "seed_made_valid T (fst (seed_row_answer L construct r S' Q)) (snd (seed_row_answer L construct r S' Q)) \<and>
      (\<forall>x\<in>set (fst (seed_row_answer L construct r S' Q)). snd x=Qg)"
  proof (cases "development_answer_key development_seed_state r S'")
    case None
    then show ?thesis using issued by (simp add: seed_row_answer_def seed_made_valid_def)
  next
    case (Some lt)
    obtain l t where lt: "lt=(l,t)" by (cases lt)
    show ?thesis
      using issued Some seed_record_valid[OF core lookup]
      by (simp add: seed_row_answer_def lt development_answer_citations_def)
  qed
next
  assume "fst Q=None"
  then show "fst (snd (seed_row_answer L construct r S' Q))=None" by (simp add: seed_row_answer_def)
qed

lemma seed_row_made_valid:
  assumes core: "seed_construct_core construct" and lookup: "seed_lookup_valid T L"
  shows "seed_row_valid T (seed_row_made L construct xs selected issue)"
proof -
  obtain r reading where issue: "issue=(r,reading)" by (cases issue)
  show ?thesis
  proof (cases "development_seed_incumbent_of xs r")
    case None
    then show ?thesis by (simp add: issue seed_row_made_def seed_row_valid_def seed_made_valid_def)
  next
    case (Some inc)
    note found=this
    obtain B u I where inc: "inc=(B,u,I)" by (cases inc)
    let ?S="seed_row_selection L construct selected B"
    let ?Q="seed_row_issue L construct r reading u I ?S"
    have S: "seed_made_valid T [] ?S" unfolding seed_row_selection_def by (rule seed_record_valid[OF core lookup])
    have Q: "\<exists>Ig B1 us Sel u'. Some I=Some Ig \<and> fst ?S=Some (B1,us,Sel) \<and> seed_made_valid T [((u',[]),Ig),((us,[]),Sel)] ?Q"
      if "fst ?Q=Some q" for q
    proof (cases "fst ?S")
      case None
      then show ?thesis using that by (simp add: seed_row_issue_def)
    next
      case (Some x)
      obtain B1 us Sel where x: "x=(B1,us,Sel)" by (cases x)
      have "seed_made_valid T [((u,[]),I),((us,[]),Sel)] ?Q"
        using Some seed_record_valid[OF core lookup] by (simp add: seed_row_issue_def x)
      then show ?thesis using Some x by blast
    qed
    show ?thesis
      unfolding issue seed_row_made_def seed_row_valid_def prod.case found inc option.case Let_def
      using S Q seed_row_answer_valid[OF core lookup] by (auto simp del: prod.collapse)
  qed
qed

subsection \<open>The prepared references\<close>

lemma seed_prepared_refs_valid:
  "seed_reads T ns (concat (map (\<lambda>(t,j). seed_judged_targets j) cs)) \<Longrightarrow> x\<in>set (seed_prepared_refs ns cs) \<Longrightarrow>
    (fst x,fst (snd x))\<in>set cs \<and> (\<forall>a b. snd (snd x)=Some (a,b) \<longrightarrow> (\<exists>v. fst (snd x)=Some v \<and>
      value_reference_read T a=Some (Finite_Whole (fst v)) \<and> value_reference_read T b=Some (Finite_Whole (seed_cause v))))"
proof (induction ns cs rule: seed_prepared_refs.induct)
  case (1 ns)
  then show ?case by simp
next
  case (2 ns t cs)
  then show ?case by (auto simp: seed_judged_targets_def)
next
  case (3 ns t v cs)
  have reads: "seed_reads T ns ([Finite_Whole (fst v),Finite_Whole (seed_cause v)]@concat (map (\<lambda>(t,j). seed_judged_targets j) cs))"
    using "3.prems"(1) by (simp add: seed_judged_targets_def)
  have head: "seed_reads T ns [Finite_Whole (fst v),Finite_Whole (seed_cause v)]"
    and rest: "seed_reads T (drop 2 ns) (concat (map (\<lambda>(t,j). seed_judged_targets j) cs))"
    using reads[unfolded seed_reads_append] by (simp_all add: numeral_2_eq_2)
  have h: "value_reference_read T (ns!0)=Some (Finite_Whole (fst v))" "value_reference_read T (ns!1)=Some (Finite_Whole (seed_cause v))"
    using head by (auto simp: seed_reads_def less_Suc_eq numeral_eq_Suc)
  show ?case
  proof (cases "x=(t,Some v,Some (ns!0,ns!1))")
    case True
    then show ?thesis using h by simp
  next
    case False
    then have "x\<in>set (seed_prepared_refs (drop 2 ns) cs)" using "3.prems"(2) by simp
    note later="3.IH"[OF rest this]
    then show ?thesis by simp
  qed
qed

lemma seed_prepared_state_valid:
  assumes prepared: "seed_prepared_state decisions=(cs,q0)"
  obtains T0 where "keyed_reference_state seed_target_key q0 T0" "distinct T0" "seed_lookup_valid T0 (seed_lookup cs)"
proof -
  let ?cache="seed_prepared (development_seed_family_keys@development_seed_decision_keys decisions)"
  let ?loci="seed_loci development_seed_problems"
  let ?xs="?loci@concat (map (\<lambda>(t,j). seed_judged_targets j) ?cache)"
  have exact: "fst (seed_keyed_sequence ?xs (RBT.empty,0,[]))=fst (value_reference_sequence ?xs [])"
    "keyed_reference_state seed_target_key (snd (seed_keyed_sequence ?xs (RBT.empty,0,[]))) (snd (value_reference_sequence ?xs []))"
    using seed_keyed_sequence_exact[OF seed_state_empty] by blast+
  let ?T0="snd (value_reference_sequence ?xs [])"
  have q0: "q0=snd (seed_keyed_sequence ?xs (RBT.empty,0,[]))" and
    cs: "cs=seed_prepared_refs (drop (length ?loci) (fst (value_reference_sequence ?xs []))) ?cache"
    using prepared exact(1) by (simp_all add: seed_prepared_state_def Let_def)
  have reads: "seed_reads ?T0 (drop (length ?loci) (fst (value_reference_sequence ?xs []))) (concat (map (\<lambda>(t,j). seed_judged_targets j) ?cache))"
    using seed_reads_sequence[of ?xs "[]"] by (simp add: seed_reads_append)
  have judged: "(t,j)\<in>set ?cache \<Longrightarrow> j=development_payload_judgment t" for t j
    by (auto simp: seed_prepared_def Parallel.map_def)
  have "seed_lookup_valid ?T0 (seed_lookup cs)"
    unfolding seed_lookup_valid_def
  proof (intro conjI allI impI)
    fix t
    show "fst (seed_lookup cs t)=development_payload_judgment t"
    proof (cases "map_of cs t")
      case None
      then show ?thesis by (simp add: seed_lookup_def)
    next
      case (Some w)
      then have "(t,w)\<in>set cs" by (rule map_of_SomeD)
      then have "(t,fst w)\<in>set ?cache" using seed_prepared_refs_valid[OF reads] by (fastforce simp: cs)
      then show ?thesis using Some judged by (simp add: seed_lookup_def)
    qed
  next
    fix t a b
    assume token: "snd (seed_lookup cs t)=Some (a,b)"
    then obtain w where w: "map_of cs t=Some w" by (cases "map_of cs t") (simp_all add: seed_lookup_def)
    then have member: "(t,w)\<in>set cs" by (rule map_of_SomeD)
    show "\<exists>v. fst (seed_lookup cs t)=Some v \<and> value_reference_read ?T0 a=Some (Finite_Whole (fst v)) \<and>
        value_reference_read ?T0 b=Some (Finite_Whole (seed_cause v))"
      using seed_prepared_refs_valid[OF reads, of "(t,w)"] member token w by (simp add: cs seed_lookup_def)
  qed
  moreover have "distinct ?T0" using value_reference_sequence_distinct[of "[]" ?xs] by simp
  ultimately show ?thesis using that exact(2) q0 by blast
qed


subsection \<open>The represented rows\<close>

definition seed_quad_decode :: "finite_exact_target list \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option" where
  "seed_quad_decode T x=(map_option (map_generation_structure (\<lambda>i. T!i)) (fst x),
     map_option (map_generation_structure (\<lambda>i. T!i)) (fst (snd x)),
     map_option (map_generation_structure (\<lambda>i. T!i)) (fst (snd (snd x))),
     map_option (map_generation_structure (\<lambda>i. T!i)) (snd (snd (snd x))))"

definition seed_quad_rel :: "finite_exact_target list \<Rightarrow>
    nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option\<times>nat generation_structure option \<Rightarrow>
    finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_generation option \<Rightarrow> bool" where
  "seed_quad_rel T x y \<longleftrightarrow> rel_option (seed_represents T) (fst x) (fst y) \<and>
     rel_option (seed_represents T) (fst (snd x)) (fst (snd y)) \<and>
     rel_option (seed_represents T) (fst (snd (snd x))) (fst (snd (snd y))) \<and>
     rel_option (seed_represents T) (snd (snd (snd x))) (snd (snd (snd y)))"

lemma seed_decode_option:
  assumes "rel_option (seed_represents T) x y"
  shows "map_option (map_generation_structure (\<lambda>i. T!i)) x=y"
    and "\<And>g. g\<in>set_option x \<Longrightarrow> set_generation_structure g\<subseteq>{..<length T}"
  using assms by (cases x; cases y; auto simp: seed_represents_def)+

lemma seed_row_rep_represents:
  assumes valid: "seed_row_valid T (p,I,S,Q,rG,G,rH,H)" and reads: "seed_reads T ns (seed_row_targets (p,I,S,Q,rG,G,rH,H))"
    and incumbent: "rel_option (seed_represents T)
      (Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd) I"
  shows "seed_quad_rel T (seed_row_rep ireps ns (p,I,S,Q,rG,G,rH,H)) (seed_row_plain_reps (p,I,S,Q,rG,G,rH,H))"
proof -
  let ?Ir="Option.bind (find (\<lambda>(q,g). q=p) (zip development_seed_problems ireps)) snd"
  let ?n1="drop (length (seed_made_targets S)) ns"
  let ?n2="drop (length (seed_made_targets Q)) ?n1"
  let ?n3="drop (length (seed_made_targets G)) ?n2"
  let ?Sr="seed_made_rep ns S []"
  let ?Qr="seed_made_rep ?n1 Q (List.map_filter id [?Ir,?Sr])"
  have parts: "seed_reads T ns (seed_made_targets S)" "seed_reads T ?n1 (seed_made_targets Q)"
    "seed_reads T ?n2 (seed_made_targets G)" "seed_reads T ?n3 (seed_made_targets H)"
    using reads by (simp_all add: seed_row_targets_def seed_reads_append)
  have SV: "seed_made_valid T [] S"
    and QV: "\<And>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<Longrightarrow> (\<exists>Ig B1 us Sel u. I=Some Ig \<and> fst S=Some (B1,us,Sel) \<and>
        seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q) \<and>
       seed_made_valid T rG G \<and> (\<forall>x\<in>set rG. snd x=Qg) \<and> seed_made_valid T rH H \<and> (\<forall>x\<in>set rH. snd x=Qg)"
    and QN: "fst Q=None \<Longrightarrow> fst G=None \<and> fst H=None"
    using valid by (simp_all add: seed_row_valid_def)
  have Sr: "rel_option (seed_represents T) ?Sr (seed_made_generation S)"
    by (rule seed_made_rep_represents[OF SV parts(1)]) simp
  have Qr: "rel_option (seed_represents T) ?Qr (seed_made_generation Q)"
  proof (cases "fst Q")
    case None
    then show ?thesis by (rule seed_made_rep_none)
  next
    case (Some q)
    obtain B2 uq Qg where q: "q=(B2,uq,Qg)" by (cases q)
    obtain Ig B1 us Sel u where Ig: "I=Some Ig" and S1: "fst S=Some (B1,us,Sel)"
      and QV1: "seed_made_valid T [((u,[]),Ig),((us,[]),Sel)] Q"
      using QV[of B2 uq Qg] Some q by blast
    obtain gI where gI: "?Ir=Some gI" "seed_represents T gI Ig"
      using incumbent Ig by (cases ?Ir) simp_all
    have "seed_made_generation S=Some Sel" by (simp add: seed_made_generation_def S1)
    then obtain gS where gS: "?Sr=Some gS" "seed_represents T gS Sel"
      using Sr by (cases ?Sr) simp_all
    have preds: "list_all2 (seed_represents T) (List.map_filter id [?Ir,?Sr]) (map snd [((u,[]),Ig),((us,[]),Sel)])"
      using gI gS by (simp add: List.map_filter_def)
    show ?thesis by (rule seed_made_rep_represents[OF QV1 parts(2) preds])
  qed
  have answer: "rel_option (seed_represents T) (seed_made_rep n A (map (\<lambda>x. the ?Qr) rA)) (seed_made_generation A)"
    if reads_A: "seed_reads T n (seed_made_targets A)"
      and valid_A: "\<And>B2 uq Qg. fst Q=Some (B2,uq,Qg) \<Longrightarrow> seed_made_valid T rA A \<and> (\<forall>x\<in>set rA. snd x=Qg)"
      and none_A: "fst Q=None \<Longrightarrow> fst A=None"
    for n A rA
  proof (cases "fst Q")
    case None
    then show ?thesis using none_A by (simp add: seed_made_rep_none)
  next
    case (Some q)
    obtain B2 uq Qg where q: "q=(B2,uq,Qg)" by (cases q)
    have VA: "seed_made_valid T rA A" and cited: "\<forall>x\<in>set rA. snd x=Qg" using valid_A[of B2 uq Qg] Some q by simp_all
    have "seed_made_generation Q=Some Qg" by (simp add: seed_made_generation_def Some q)
    then obtain gQ where gQ: "?Qr=Some gQ" "seed_represents T gQ Qg" using Qr by (cases ?Qr) simp_all
    have preds: "list_all2 (seed_represents T) (map (\<lambda>x. the ?Qr) rA) (map snd rA)"
      using gQ cited by (simp add: list_all2_conv_all_nth)
    show ?thesis by (rule seed_made_rep_represents[OF VA reads_A preds])
  qed
  have Gr: "rel_option (seed_represents T) (seed_made_rep ?n2 G (map (\<lambda>x. the ?Qr) rG)) (seed_made_generation G)"
    by (rule answer[OF parts(3)]) (use QV QN in simp_all)
  have Hr: "rel_option (seed_represents T) (seed_made_rep ?n3 H (map (\<lambda>x. the ?Qr) rH)) (seed_made_generation H)"
    by (rule answer[OF parts(4)]) (use QV QN in simp_all)
  show ?thesis
    using incumbent Qr Gr Hr by (simp add: seed_row_rep_def seed_row_plain_reps_def seed_quad_rel_def Let_def add.assoc)
qed

lemma seed_consume_list_represents:
  "seed_reads T ns (concat (map seed_made_targets ms)) \<Longrightarrow> \<forall>m\<in>set ms. seed_made_valid T [] m \<Longrightarrow>
    list_all2 (rel_option (seed_represents T)) (seed_consume_list ns ms) (map seed_made_generation ms)"
proof (induction ms arbitrary: ns)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  have reads: "seed_reads T ns (seed_made_targets m)"
    "seed_reads T (drop (length (seed_made_targets m)) ns) (concat (map seed_made_targets ms))"
    using Cons.prems(1) by (simp_all add: seed_reads_append)
  have head: "rel_option (seed_represents T) (seed_made_rep ns m []) (seed_made_generation m)"
    using Cons.prems(2) by (intro seed_made_rep_represents[OF _ reads(1)]) simp_all
  show ?case using head Cons.IH[OF reads(2)] Cons.prems(2) by simp
qed

lemma seed_rows_rep_represents:
  "seed_reads T ns (concat (map seed_row_targets rows)) \<Longrightarrow> \<forall>row\<in>set rows. seed_row_valid T row \<Longrightarrow>
    \<forall>row\<in>set rows. rel_option (seed_represents T)
      (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ireps)) snd) (fst (snd row)) \<Longrightarrow>
    list_all2 (seed_quad_rel T) (seed_rows_rep ireps ns rows) (map seed_row_plain_reps rows)"
proof (induction rows arbitrary: ns)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  have reads: "seed_reads T ns (seed_row_targets row)"
    "seed_reads T (drop (length (seed_row_targets row)) ns) (concat (map seed_row_targets rows))"
    using Cons.prems(1) by (simp_all add: seed_reads_append)
  obtain p I S Q rG G rH H where row: "row=(p,I,S,Q,rG,G,rH,H)" by (metis prod.collapse)
  have head: "seed_quad_rel T (seed_row_rep ireps ns row) (seed_row_plain_reps row)"
    using Cons.prems(2,3) reads(1) by (simp add: row seed_row_rep_represents)
  show ?case using head Cons.IH[OF reads(2)] Cons.prems(2,3) by simp
qed

lemma seed_find_rel:
  assumes "list_all2 (rel_option R) ys (map f zs)" and "length ps=length zs"
  shows "rel_option R (Option.bind (find (\<lambda>(q,g). q=a) (zip ps ys)) snd)
    (Option.bind (find (\<lambda>(q,z). q=a) (zip ps zs)) (\<lambda>(q,z). f z))"
  using assms
proof (induction ps arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain z zs' where zs: "zs=z#zs'" using Cons.prems(2) by (cases zs) auto
  obtain y ys' where ys: "ys=y#ys'" using Cons.prems(1) zs by (cases ys) auto
  have head: "rel_option R y (f z)" and tail: "list_all2 (rel_option R) ys' (map f zs')"
    using Cons.prems(1) ys zs by simp_all
  show ?case using Cons.IH[OF tail] Cons.prems(2) head by (simp add: ys zs)
qed

lemma seed_incumbent_find:
  "map_option (\<lambda>(B,u,G). G) (Option.bind (find (\<lambda>(p,x). p=a) (zip ps (map fst incs))) snd)=
    Option.bind (find (\<lambda>(q,z). q=a) (zip ps incs)) (\<lambda>(q,z). seed_made_generation z)"
proof (induction ps arbitrary: incs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case by (cases incs) (simp_all add: seed_made_generation_def)
qed

lemma seed_row_made_fields:
  shows "fst (seed_row_made L construct xs selected (r,reading))=fst r"
    and "fst (snd (seed_row_made L construct xs selected (r,reading)))=
      map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)"
proof -
  show "fst (seed_row_made L construct xs selected (r,reading))=fst r" by (simp add: seed_row_made_def)
  show "fst (snd (seed_row_made L construct xs selected (r,reading)))=
      map_option (\<lambda>(B,u,G). G) (development_seed_incumbent_of xs r)"
    by (cases "development_seed_incumbent_of xs r") (auto simp: seed_row_made_def Let_def)
qed


subsection \<open>The reference round decodes to the round\<close>

definition seed_round_decode :: "finite_exact_target list \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow>
    development_seed_publication" where
  "seed_round_decode T v=(case v of (S0,Sel,rows,results) \<Rightarrow>
     (map_option (decode_represented_snapshot (\<lambda>i. T!i)) S0,map_option (map_generation_structure (\<lambda>i. T!i)) Sel,
      map (\<lambda>(Q,G,H,rs,e). (map_option (map_generation_structure (\<lambda>i. T!i)) Q,
        map_option (map_generation_structure (\<lambda>i. T!i)) G,map_option (map_generation_structure (\<lambda>i. T!i)) H,
        map (map_option (decode_represented_result (\<lambda>i. T!i))) rs,e)) rows,
      map (map_option (decode_represented_result (\<lambda>i. T!i))) results))"

lemma seed_those_map: "those (map (map_option f) xs)=map_option (map f) (those xs)"
  by (induction xs) (auto split: option.split simp: option.map_comp o_def)

lemma seed_those_member: "those xs=Some gs \<Longrightarrow> g\<in>set gs \<Longrightarrow> Some g\<in>set xs"
  by (induction xs arbitrary: gs) (auto split: option.splits)

lemma seed_payload_map: "generation_payload (map_generation_structure f g)=f (generation_payload g)"
  by (cases g) simp

lemma seed_payload_member: "generation_payload g\<in>set_generation_structure g"
  by (cases g) simp

lemma seed_reference_pub_decoded:
  assumes distinct: "distinct T" and S: "represented_snapshot_targets S\<subseteq>{..<length T}"
    and ps: "represented_publications_targets ps\<subseteq>{..<length T}"
  shows "map (map_option (decode_represented_result (\<lambda>i. T!i))) (seed_reference_pub T S ps)=
    (if finite_snapshot_loci_formed (decode_represented_snapshot (\<lambda>i. T!i) S)
     then finite_locus_publications_body (decode_represented_snapshot (\<lambda>i. T!i) S) else map (\<lambda>q. None))
      (decode_represented_publications (\<lambda>i. T!i) ps)"
proof -
  have inj: "inj_on (\<lambda>i. T!i) {..<length T}" using distinct by (simp add: inj_on_nth)
  show ?thesis
    using represented_snapshot_loci_formed_decoded[OF inj S] represented_locus_publications_body_decoded[OF inj S ps]
    by (simp add: seed_reference_pub_def decode_represented_publications_def)
qed

lemma seed_list_targets:
  assumes rel: "list_all2 (rel_option (seed_represents T)) xs ys" and member: "Some g\<in>set xs"
  shows "set_generation_structure g\<subseteq>{..<length T}"
proof -
  obtain i where i: "i<length xs" "xs!i=Some g" using member in_set_conv_nth[of "Some g" xs] by blast
  have "rel_option (seed_represents T) (xs!i) (ys!i)" using rel i(1) by (simp add: list_all2_conv_all_nth)
  then show ?thesis using seed_decode_option(2) i(2) by fastforce
qed

lemma seed_snapshot_targets:
  assumes rel: "list_all2 (rel_option (seed_represents T)) xs ys" and listed: "those xs=Some gs"
  shows "represented_snapshot_targets (fset_of_list gs)\<subseteq>{..<length T}"
proof
  fix x
  assume "x\<in>represented_snapshot_targets (fset_of_list gs)"
  then obtain G where G: "G\<in>set gs" "x\<in>set_generation_structure G"
    by (auto simp: represented_snapshot_targets_def fset_of_list_elem)
  show "x\<in>{..<length T}" using seed_list_targets[OF rel seed_those_member[OF listed G(1)]] G(2) by blast
qed

lemma seed_quad_targets:
  assumes rows: "list_all2 (seed_quad_rel T) rows rows'" and member: "x\<in>set rows"
  shows "\<forall>g\<in>set_option (fst x)\<union>set_option (fst (snd x))\<union>set_option (fst (snd (snd x)))\<union>set_option (snd (snd (snd x))).
    set_generation_structure g\<subseteq>{..<length T}"
proof -
  obtain i where i: "i<length rows" "rows!i=x" using member in_set_conv_nth[of x rows] by blast
  have "seed_quad_rel T x (rows'!i)" using rows i by (auto simp: list_all2_conv_all_nth)
  then show ?thesis unfolding seed_quad_rel_def using seed_decode_option(2) by blast
qed

lemma seed_publications_targets:
  "\<forall>(I,A)\<in>set ps. (\<forall>g\<in>set_option I. set_generation_structure g\<subseteq>K) \<and> (\<forall>g\<in>set_option A. set_generation_structure g\<subseteq>K) \<Longrightarrow>
    represented_publications_targets ps\<subseteq>K"
  by (fastforce simp: represented_publications_targets_def)

theorem seed_round_assemble_decoded:
  assumes distinct: "distinct T"
    and ireps: "list_all2 (rel_option (seed_represents T)) ireps Is"
    and sel: "rel_option (seed_represents T) sel Sel"
    and rows: "list_all2 (seed_quad_rel T) rows rows'"
  shows "seed_round_decode T (seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub d)=
    seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) d"
proof -
  let ?dec="\<lambda>i::nat. T!i"
  let ?K="{..<length T}"
  let ?D="map_option (map_generation_structure ?dec)"
  let ?P="\<lambda>S. if finite_snapshot_loci_formed S then finite_locus_publications_body S else map (\<lambda>q. None)"
  let ?pubR="case map_option fset_of_list (those ireps) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> seed_reference_pub T S"
  let ?pubP="case map_option fset_of_list (those Is) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> ?P S"
  have inj: "inj_on ?dec ?K" using distinct by (simp add: inj_on_nth)
  have Is: "map ?D ireps=Is"
    using ireps by (induction rule: list_all2_induct) (simp_all add: seed_decode_option(1))
  have Sel: "?D sel=Sel" and Seltargets: "\<And>g. g\<in>set_option sel \<Longrightarrow> set_generation_structure g\<subseteq>?K"
    using seed_decode_option[OF sel] by simp_all
  have quad: "y=seed_quad_decode T x" if related: "seed_quad_rel T x y" for x y
  proof -
    have r: "rel_option (seed_represents T) (fst x) (fst y)" "rel_option (seed_represents T) (fst (snd x)) (fst (snd y))"
      "rel_option (seed_represents T) (fst (snd (snd x))) (fst (snd (snd y)))"
      "rel_option (seed_represents T) (snd (snd (snd x))) (snd (snd (snd y)))"
      using related by (simp_all add: seed_quad_rel_def)
    show ?thesis using seed_decode_option(1)[OF r(1)] seed_decode_option(1)[OF r(2)] seed_decode_option(1)[OF r(3)]
      seed_decode_option(1)[OF r(4)] by (simp add: seed_quad_decode_def prod_eq_iff)
  qed
  have rows': "rows'=map (seed_quad_decode T) rows"
    using rows by (induction rule: list_all2_induct) (simp_all add: quad)
  note Rtargets=seed_quad_targets[OF rows]
  have publish: "map (map_option (decode_represented_result ?dec)) (?pubR ps)=?pubP (decode_represented_publications ?dec ps)"
    if ps: "represented_publications_targets ps\<subseteq>?K" for ps
  proof (cases "those ireps")
    case None
    then show ?thesis by (simp add: Is[symmetric] seed_those_map)
  next
    case (Some gs)
    note S=seed_snapshot_targets[OF ireps Some]
    have decoded: "decode_represented_snapshot ?dec (fset_of_list gs)=fset_of_list (map (map_generation_structure ?dec) gs)"
      by (simp add: decode_represented_snapshot_def fset_of_list_map)
    show ?thesis
      using seed_reference_pub_decoded[OF distinct S ps] Some
      by (simp add: Is[symmetric] seed_those_map decoded)
  qed
  note targets_list=seed_publications_targets
  have equal: "(map_option generation_payload (?D G)=map_option generation_payload (?D H)) \<longleftrightarrow>
      (map_option generation_payload G=map_option generation_payload H)"
    if G: "\<And>g. g\<in>set_option G \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and H: "\<And>g. g\<in>set_option H \<Longrightarrow> set_generation_structure g\<subseteq>?K" for G H
  proof (cases G)
    case None
    then show ?thesis by (cases H) simp_all
  next
    case (Some g)
    show ?thesis
    proof (cases H)
      case None
      then show ?thesis using Some by simp
    next
      case (Some h)
      have "generation_payload g\<in>?K" using G \<open>G=Some g\<close> seed_payload_member by fastforce
      moreover have "generation_payload h\<in>?K" using H Some seed_payload_member by fastforce
      ultimately show ?thesis using \<open>G=Some g\<close> Some inj by (simp add: seed_payload_map inj_on_eq_iff)
    qed
  qed
  have row: "(\<lambda>(Q,G,H,rs,e). (?D Q,?D G,?D H,map (map_option (decode_represented_result ?dec)) rs,e))
      ((\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) x)=
    (\<lambda>(I,Q,G,H). (Q,G,H,?pubP [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (seed_quad_decode T x)"
    if x: "x\<in>set rows" for x
  proof -
    obtain I Q G H where shape: "x=(I,Q,G,H)" by (metis prod.collapse)
    have tI: "\<And>g. g\<in>set_option I \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tQ: "\<And>g. g\<in>set_option Q \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tG: "\<And>g. g\<in>set_option G \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      and tH: "\<And>g. g\<in>set_option H \<Longrightarrow> set_generation_structure g\<subseteq>?K"
      using Rtargets[OF x] by (auto simp: shape)
    have pub: "map (map_option (decode_represented_result ?dec)) (?pubR [(None,Q),(I,G),(I,H)])=
        ?pubP [(None,?D Q),(?D I,?D G),(?D I,?D H)]"
      using publish[OF targets_list] tI tQ tG tH by (simp add: decode_represented_publications_def)
    show ?thesis using pub equal[OF tG tH] by (simp add: shape seed_quad_decode_def)
  qed
  have rowsmap: "map (\<lambda>(Q,G,H,rs,e). (?D Q,?D G,?D H,map (map_option (decode_represented_result ?dec)) rs,e))
      (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows)=
    map (\<lambda>(I,Q,G,H). (Q,G,H,?pubP [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) (map (seed_quad_decode T) rows)"
    using row by simp
  have round_targets: "represented_publications_targets ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@
      map (\<lambda>(I,Q,G,H). (I,G)) rows)\<subseteq>?K"
    by (rule targets_list) (use Seltargets Rtargets in fastforce)
  have round_decoded: "decode_represented_publications ?dec ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@
      map (\<lambda>(I,Q,G,H). (I,G)) rows)=
    (None,Sel)#map (\<lambda>(I,Q,G,H). (None,Q)) (map (seed_quad_decode T) rows)@
      map (\<lambda>(I,Q,G,H). (I,G)) (map (seed_quad_decode T) rows)"
    by (simp add: decode_represented_publications_def Sel[symmetric] seed_quad_decode_def case_prod_unfold)
  have snapshot: "map_option (decode_represented_snapshot ?dec) (map_option fset_of_list (those ireps))=
      map_option fset_of_list (those Is)"
    by (cases "those ireps") (simp_all add: Is[symmetric] seed_those_map decode_represented_snapshot_def fset_of_list_map)
  show ?thesis
  proof (cases d)
    case None
    show ?thesis
      by (simp only: seed_round_assemble_def seed_round_decode_def prod.case Let_def Parallel.map_def None option.case
        snapshot Sel rowsmap rows' list.map(1))
  next
    case (Some x)
    show ?thesis
      by (simp only: seed_round_assemble_def seed_round_decode_def prod.case Let_def Parallel.map_def Some option.case
        snapshot Sel rowsmap rows' publish[OF round_targets] round_decoded)
  qed
qed

lemma seed_plain_reps_parts:
  "seed_plain_reps (incs,sel,rows)=((map seed_made_generation incs,seed_made_generation sel,map seed_row_plain_reps rows),())"
  by (simp add: seed_plain_reps_def seed_row_plain_reps_def)

lemma seed_reference_round_represented:
  obtains ireps sel rows T Is Sel rows' where
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (seed_represents T)) ireps Is" "rel_option (seed_represents T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    "seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) (development_seed_decisions A)=development_seed_publication A"
proof -
  let ?d="development_seed_decisions A"
  obtain cs q0 where prepared: "seed_prepared_state ?d=(cs,q0)" by (cases "seed_prepared_state ?d")
  obtain T0 where rep0: "keyed_reference_state seed_target_key q0 T0" and dist0: "distinct T0"
    and lookup0: "seed_lookup_valid T0 (seed_lookup cs)"
    using seed_prepared_state_valid[OF prepared] by blast
  let ?L="seed_lookup cs"
  let ?m="seed_made_round_of ?L finite_construct_formed_cause_generation ?d"
  obtain incs sel rows where m: "?m=(incs,sel,rows)" by (metis prod.collapse)
  let ?ts="seed_round_targets ?m"
  obtain ns q where seq: "seed_keyed_sequence ?ts q0=(ns,q)" by (cases "seed_keyed_sequence ?ts q0")
  have exact: "ns=fst (value_reference_sequence ?ts T0)"
    "keyed_reference_state seed_target_key q (snd (value_reference_sequence ?ts T0))"
    using seed_keyed_sequence_exact[OF rep0, of ?ts] seq by simp_all
  define T where "T=snd (value_reference_sequence ?ts T0)"
  have Tq: "rev (snd (snd q))=T" using seed_state_table[OF exact(2)] by (simp add: T_def)
  have distinct: "distinct T" using value_reference_sequence_distinct[OF dist0] by (simp add: T_def)
  have kept: "value_reference_read T0 i=Some y \<Longrightarrow> value_reference_read T i=Some y" for i y
    using value_reference_sequence_preserves by (simp add: T_def)
  have reads: "seed_reads T ns ?ts" using seed_reads_sequence[of ?ts T0] exact(1) by (simp add: T_def)
  have lookup: "seed_lookup_valid T ?L" by (rule seed_lookup_valid_preserved[OF lookup0 kept])
  have judged: "\<And>t. fst (?L t)=development_payload_judgment t" using lookup by (simp add: seed_lookup_valid_def)
  let ?inc="\<lambda>p. seed_record ?L finite_construct_formed_cause_generation (development_incumbent_key development_seed_state p)
    (finite_enumerated_environment [] []) []"
  let ?xs="zip development_seed_problems (map fst incs)"
  have incs: "incs=map ?inc development_seed_problems"
    using m by (simp add: seed_made_round_of_def Let_def Parallel.map_def split: option.splits prod.splits)
  have made_rows: "\<exists>selected issues. rows=map (seed_row_made ?L finite_construct_formed_cause_generation ?xs selected) issues"
    using m by (auto simp: seed_made_round_of_def Let_def Parallel.map_def incs split: option.splits prod.splits)
  have made_sel: "sel=(None,None) \<or> (\<exists>selected. sel=seed_row_selection ?L finite_construct_generation_record selected
      (finite_enumerated_environment [] []))"
    using m by (auto simp: seed_made_round_of_def Let_def split: option.splits prod.splits)
  have V_incs: "\<forall>m\<in>set incs. seed_made_valid T [] m"
    using seed_record_valid[OF seed_construct_core_formed_cause lookup] by (simp add: incs)
  have V_sel: "seed_made_valid T [] sel"
    using made_sel seed_record_valid[OF seed_construct_core_record lookup]
    by (auto simp: seed_made_valid_def seed_row_selection_def)
  have V_rows: "\<forall>row\<in>set rows. seed_row_valid T row"
    using made_rows seed_row_made_valid[OF seed_construct_core_formed_cause lookup] by auto
  have split: "seed_reads T ns (concat (map seed_made_targets incs))"
    "seed_reads T (drop (length (concat (map seed_made_targets incs))) ns) (seed_made_targets sel)"
    "seed_reads T (drop (length (seed_made_targets sel)) (drop (length (concat (map seed_made_targets incs))) ns))
      (concat (map seed_row_targets rows))"
    using reads by (simp_all add: m seed_round_targets_def seed_reads_append)
  let ?ireps="seed_consume_list ns incs"
  have R_incs: "list_all2 (rel_option (seed_represents T)) ?ireps (map seed_made_generation incs)"
    by (rule seed_consume_list_represents[OF split(1) V_incs])
  have R_sel: "rel_option (seed_represents T) (seed_made_rep (drop (length (concat (map seed_made_targets incs))) ns) sel [])
      (seed_made_generation sel)"
    by (rule seed_made_rep_represents[OF V_sel split(2)]) simp
  have lengths: "length development_seed_problems=length incs" by (simp add: incs)
  have incumbents: "\<forall>row\<in>set rows. rel_option (seed_represents T)
      (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ?ireps)) snd) (fst (snd row))"
  proof
    fix row
    assume "row\<in>set rows"
    then obtain selected r reading where row: "row=seed_row_made ?L finite_construct_formed_cause_generation ?xs selected (r,reading)"
      using made_rows by fastforce
    have "rel_option (seed_represents T) (Option.bind (find (\<lambda>(q,g). q=fst r) (zip development_seed_problems ?ireps)) snd)
        (Option.bind (find (\<lambda>(q,z). q=fst r) (zip development_seed_problems incs)) (\<lambda>(q,z). seed_made_generation z))"
      by (rule seed_find_rel[OF R_incs lengths])
    then show "rel_option (seed_represents T)
        (Option.bind (find (\<lambda>(q,g). q=fst row) (zip development_seed_problems ?ireps)) snd) (fst (snd row))"
      by (simp add: row seed_row_made_fields development_seed_incumbent_of_def seed_incumbent_find)
  qed
  have R_rows: "list_all2 (seed_quad_rel T)
      (seed_rows_rep ?ireps (drop (length (seed_made_targets sel)) (drop (length (concat (map seed_made_targets incs))) ns)) rows)
      (map seed_row_plain_reps rows)"
    by (rule seed_rows_rep_represents[OF split(3) V_rows incumbents])
  have round: "development_seed_reference_round A=
      (seed_round_assemble ((seed_reps_of ns ?m),T) seed_reference_pub ?d,T)"
    by (simp add: development_seed_reference_round_def development_seed_round_def prepared seed_reference_reps_def seq Tq
      Let_def)
  have plain: "seed_round_assemble (seed_plain_reps ?m) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
        else map (\<lambda>q. None)) ?d=development_seed_publication A"
    by (simp only: seed_round_assemble_plain[OF judged] development_seed_publication_formed_causes
      parallel_computed_function_exact Let_def)
  show ?thesis
    using that[OF round[unfolded m seed_reps_of_def Let_def prod.case] distinct R_incs R_sel R_rows
      plain[unfolded m seed_plain_reps_parts]] .
qed


subsection \<open>Every target of the reference round is in its table\<close>

fun seed_result_held :: "'t represented_transaction_result \<Rightarrow> 't held_transaction_result" where
  "seed_result_held (Represented_Applied S)=Inl S"
| "seed_result_held (Represented_Conflict C)=Inr C"

lemma seed_result_decoded:
  "finite_transaction_result_held (decode_represented_result t r)=
    map_sum (fimage (map_generation_structure t)) (fimage (map_prod t (map_option (map_generation_structure t))))
      (seed_result_held r)"
  by (cases r) (simp_all add: decode_represented_snapshot_def decode_represented_observation_def map_prod_def)

lemma seed_observed_targets:
  "observation_targets (represented_observed_comparison S T)\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
proof
  fix x
  assume "x\<in>observation_targets (represented_observed_comparison S T)"
  then obtain l where l: "l|\<in>|represented_comparison_loci T"
    and x: "x=l \<or> (\<exists>H. represented_snapshot_lookup S l=Some H \<and> x\<in>set_generation_structure H)"
    by (auto simp: observation_targets_def represented_observed_comparison_def)
  show "x\<in>represented_snapshot_targets S\<union>represented_transaction_targets T"
  proof (cases "x=l")
    case True
    then show ?thesis using l represented_comparison_loci_targets[of T] by auto
  next
    case False
    then obtain H where H: "represented_snapshot_lookup S l=Some H" "x\<in>set_generation_structure H" using x by blast
    have "H\<in>fset S" using represented_snapshot_lookup_member[OF H(1)] by simp
    then show ?thesis using H(2) by (auto simp: represented_snapshot_targets_def)
  qed
qed

lemma seed_publications_within:
  "represented_snapshot_targets S\<subseteq>K \<Longrightarrow> represented_publications_targets ps\<subseteq>K \<Longrightarrow>
    \<forall>r\<in>set (represented_publications_with (represented_transact_body tf) S ps). \<forall>x\<in>set_option r.
      held_result_targets (seed_result_held x)\<subseteq>K"
proof (induction ps arbitrary: S)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain I A where p: "p=(I,A)" by (cases p)
  have rest: "represented_publications_targets ps\<subseteq>K"
    using Cons.prems(2) by (auto simp: p represented_publications_targets_def)
  show ?case
  proof (cases A)
    case None
    then show ?thesis using Cons.IH[OF Cons.prems(1) rest] by (simp add: p)
  next
    case (Some G)
    note AG=this
    let ?T="represented_locus_transaction I G"
    have T: "represented_transaction_targets ?T\<subseteq>K"
      using represented_locus_transaction_targets[of I G] Cons.prems(2) by (auto simp: p Some represented_publications_targets_def)
    have step: "held_result_targets (seed_result_held (represented_transaction_step S ?T))\<subseteq>K"
    proof (cases "represented_comparison_passes S ?T")
      case True
      then show ?thesis using represented_transaction_update_targets[of S ?T] Cons.prems(1) T
        by (auto simp: represented_transaction_step_def)
    next
      case False
      then show ?thesis using seed_observed_targets[of S ?T] Cons.prems(1) T
        by (auto simp: represented_transaction_step_def)
    qed
    have later: "\<forall>r\<in>set (represented_publications_with (represented_transact_body tf) U ps). \<forall>x\<in>set_option r.
        held_result_targets (seed_result_held x)\<subseteq>K"
      if "represented_transact_body tf S ?T=Some (Represented_Applied U)" for U
    proof -
      have "represented_snapshot_targets U\<subseteq>K"
        using represented_transact_applied(3)[OF that] Cons.prems(1) T by blast
      then show ?thesis by (rule Cons.IH[OF _ rest])
    qed
    show ?thesis
    proof (cases "represented_transact_body tf S ?T")
      case None
      then show ?thesis using Cons.IH[OF Cons.prems(1) rest] by (simp add: p AG)
    next
      case (Some r)
      note result=this
      have r: "r=represented_transaction_step S ?T" using result by (simp add: represented_transact_body_def split: if_splits)
      show ?thesis
      proof (cases r)
        case (Represented_Applied U)
        then show ?thesis using later[of U] result step r by (simp add: p AG)
      next
        case (Represented_Conflict C)
        then show ?thesis using Cons.IH[OF Cons.prems(1) rest] result step r by (simp add: p AG)
      qed
    qed
  qed
qed

lemma seed_reference_pub_within:
  assumes S: "represented_snapshot_targets S\<subseteq>K" and ps: "represented_publications_targets ps\<subseteq>K"
  shows "\<forall>r\<in>set (seed_reference_pub T S ps). \<forall>x\<in>set_option r. held_result_targets (seed_result_held x)\<subseteq>K"
  using seed_publications_within[OF S ps]
  by (simp add: seed_reference_pub_def represented_locus_publications_body_def)

definition seed_round_within :: "nat set \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow> bool" where
  "seed_round_within K v \<longleftrightarrow> (case v of (S0,Sel,rows,results) \<Rightarrow>
     (\<forall>S\<in>set_option S0. represented_snapshot_targets S\<subseteq>K) \<and> (\<forall>G\<in>set_option Sel. set_generation_structure G\<subseteq>K) \<and>
     (\<forall>x\<in>set rows. (\<forall>X\<in>set_option (fst x)\<union>set_option (fst (snd x))\<union>set_option (fst (snd (snd x))).
         set_generation_structure X\<subseteq>K) \<and>
       (\<forall>r\<in>set (fst (snd (snd (snd x)))). \<forall>y\<in>set_option r. held_result_targets (seed_result_held y)\<subseteq>K)) \<and>
     (\<forall>r\<in>set results. \<forall>y\<in>set_option r. held_result_targets (seed_result_held y)\<subseteq>K))"


theorem development_seed_reference_round_decoded:
  "seed_round_decode (snd (development_seed_reference_round A)) (fst (development_seed_reference_round A))=
    development_seed_publication A"
proof -
  obtain ireps sel rows T Is Sel rows' where parts:
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (seed_represents T)) ireps Is" "rel_option (seed_represents T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    "seed_round_assemble ((Is,Sel,rows'),()) (\<lambda>s S. if finite_snapshot_loci_formed S then finite_locus_publications_body S
      else map (\<lambda>q. None)) (development_seed_decisions A)=development_seed_publication A"
    by (rule seed_reference_round_represented)
  show ?thesis using seed_round_assemble_decoded[OF parts(2-5)] parts(1,6) by simp
qed

lemma seed_round_assemble_within:
  assumes ireps: "list_all2 (rel_option (seed_represents T)) ireps Is" and sel: "rel_option (seed_represents T) sel Sel"
    and rows: "list_all2 (seed_quad_rel T) rows rows'"
  shows "seed_round_within {..<length T} (seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub d)"
proof -
  let ?K="{..<length T}"
  let ?pubR="case map_option fset_of_list (those ireps) of None \<Rightarrow> (\<lambda>ps. []) | Some S \<Rightarrow> seed_reference_pub T S"
  have publish: "\<forall>r\<in>set (?pubR ps). \<forall>y\<in>set_option r. held_result_targets (seed_result_held y)\<subseteq>?K"
    if ps: "represented_publications_targets ps\<subseteq>?K" for ps
  proof (cases "those ireps")
    case None
    then show ?thesis by simp
  next
    case (Some gs)
    then show ?thesis using seed_reference_pub_within[OF seed_snapshot_targets[OF ireps Some] ps] by simp
  qed
  have S0: "\<forall>S\<in>set_option (map_option fset_of_list (those ireps)). represented_snapshot_targets S\<subseteq>?K"
    using seed_snapshot_targets[OF ireps] by auto
  have Sel: "\<forall>G\<in>set_option sel. set_generation_structure G\<subseteq>?K" using seed_decode_option(2)[OF sel] by blast
  have rows_within: "\<forall>y\<in>set (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows).
      (\<forall>X\<in>set_option (fst y)\<union>set_option (fst (snd y))\<union>set_option (fst (snd (snd y))). set_generation_structure X\<subseteq>?K) \<and>
      (\<forall>r\<in>set (fst (snd (snd (snd y)))). \<forall>z\<in>set_option r. held_result_targets (seed_result_held z)\<subseteq>?K)"
  proof
    fix y
    assume "y\<in>set (map (\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) rows)"
    then obtain x where x: "x\<in>set rows" and y: "y=(\<lambda>(I,Q,G,H). (Q,G,H,?pubR [(None,Q),(I,G),(I,H)],
        map_option generation_payload G=map_option generation_payload H)) x" by auto
    obtain I Q G H where shape: "x=(I,Q,G,H)" by (metis prod.collapse)
    have inside: "\<forall>g\<in>set_option I\<union>set_option Q\<union>set_option G\<union>set_option H. set_generation_structure g\<subseteq>?K"
      using seed_quad_targets[OF rows x] by (simp add: shape)
    have "represented_publications_targets [(None,Q),(I,G),(I,H)]\<subseteq>?K"
      by (rule seed_publications_targets) (use inside in auto)
    then show "(\<forall>X\<in>set_option (fst y)\<union>set_option (fst (snd y))\<union>set_option (fst (snd (snd y))). set_generation_structure X\<subseteq>?K) \<and>
      (\<forall>r\<in>set (fst (snd (snd (snd y)))). \<forall>z\<in>set_option r. held_result_targets (seed_result_held z)\<subseteq>?K)"
      using publish inside by (simp add: y shape)
  qed
  have round_pub: "represented_publications_targets ((None,sel)#map (\<lambda>(I,Q,G,H). (None,Q)) rows@map (\<lambda>(I,Q,G,H). (I,G)) rows)\<subseteq>?K"
    by (rule seed_publications_targets) (use Sel seed_quad_targets[OF rows] in fastforce)
  show ?thesis
    unfolding seed_round_assemble_def seed_round_within_def Let_def Parallel.map_def prod.case
    using S0 Sel rows_within publish[OF round_pub] by (cases d) simp_all
qed

lemma development_seed_reference_round_within:
  "distinct (snd (development_seed_reference_round A)) \<and>
    seed_round_within {..<length (snd (development_seed_reference_round A))} (fst (development_seed_reference_round A))"
proof -
  obtain ireps sel rows T Is Sel rows' where parts:
    "development_seed_reference_round A=(seed_round_assemble ((ireps,sel,rows),T) seed_reference_pub (development_seed_decisions A),T)"
    "distinct T" "list_all2 (rel_option (seed_represents T)) ireps Is" "rel_option (seed_represents T) sel Sel"
    "list_all2 (seed_quad_rel T) rows rows'"
    by (rule seed_reference_round_represented)
  show ?thesis using seed_round_assemble_within[OF parts(3-5)] parts(1,2) by simp
qed

section \<open>The round's shared presentation and its word\<close>

text \<open>
  The round's table holds target leaves only, each once: a formed table of distinct leaf shapes with no pairs,
  keyed by the injective \<open>seed_target_key\<close>. Presented through the publication notions' presenters at the
  table's presentation, with the reference constructor as the target presenter, the round is a canonical shared
  term, every target leaf a reference, and it decodes to the presentation of the round. The word read off it is
  the word of the report.
\<close>

definition seed_shapes :: "finite_exact_target list \<Rightarrow> shape list" where
  "seed_shapes T=map (\<lambda>x. Leaf_Shape (Target_Leaf x)) T"

lemma seed_shapes_read:
  "value_reference_read (seed_shapes T) i=map_option (\<lambda>x. Leaf_Shape (Target_Leaf x)) (value_reference_read T i)"
  by (simp add: seed_shapes_def value_reference_read_def)

theorem seed_shapes_formed: "distinct T \<Longrightarrow> table_formed (seed_shapes T)"
  by (auto simp: table_formed_def seed_shapes_read distinct_map inj_on_def seed_shapes_def value_reference_read_def)

lemma seed_reference_term: "i<length T \<Longrightarrow> reference_term (seed_shapes T) i=Some (Finite_Target (T!i))"
  using reference_factor_leaf[of "seed_shapes T" i "Target_Leaf (T!i)"] by (simp add: seed_shapes_def value_reference_read_def)

theorem seed_presented_targets:
  "presented_targets (table_presentation (seed_shapes T)) {s. shared_canonical (seed_shapes T) s} Shared_Reference
    (\<lambda>i. T!i) {..<length T}"
  by (simp add: presented_targets_def table_presentation_def seed_reference_term) (simp add: seed_shapes_def)

lemma seed_index_absent: "x\<notin>set xs \<Longrightarrow> value_reference_index x xs=None"
  by (simp add: value_reference_index_absent)

definition seed_find :: "shape list \<Rightarrow> shape \<Rightarrow> nat option" where
  "seed_find T s=(case s of Leaf_Shape (Target_Leaf x) \<Rightarrow> table_find T s | _ \<Rightarrow> None)"

lemma seed_find_exact: "seed_find (seed_shapes T)=table_find (seed_shapes T)"
proof
  fix s
  show "seed_find (seed_shapes T) s=table_find (seed_shapes T) s"
  proof (cases "\<exists>x. s=Leaf_Shape (Target_Leaf x)")
    case True
    then show ?thesis by (auto simp: seed_find_def)
  next
    case False
    then have "s\<notin>set (seed_shapes T)" by (auto simp: seed_shapes_def)
    then have "table_find (seed_shapes T) s=None" by (simp add: table_find_def value_reference_index_absent)
    moreover have "seed_find (seed_shapes T) s=None" using False
      by (auto simp: seed_find_def split: shape.split factor_leaf.split)
    ultimately show ?thesis by simp
  qed
qed

definition seed_table_presentation :: "finite_exact_target list \<Rightarrow> shared_term term_presentation" where
  "seed_table_presentation T=shared_presentation (value_reference_read (seed_shapes T)) (seed_find (seed_shapes T))
     (reference_term (seed_shapes T))"

lemma seed_table_presentation_exact: "seed_table_presentation T=table_presentation (seed_shapes T)"
  by (simp add: seed_table_presentation_def table_presentation_def seed_find_exact)

definition seed_round_presented :: "'p term_presentation \<Rightarrow> ('t \<Rightarrow> 'p) \<Rightarrow> ('t,'t represented_transaction_result) seed_round \<Rightarrow> 'p" where
  "seed_round_presented P f=presented_pair_value P (presented_option P (presented_snapshot_value P f))
     (presented_pair_value P (presented_option P (presented_generation_value P f))
       (presented_pair_value P (presented_sequence P
         (presented_pair_value P (presented_option P (presented_generation_value P f))
           (presented_pair_value P (presented_option P (presented_generation_value P f))
             (presented_pair_value P (presented_option P (presented_generation_value P f))
               (presented_pair_value P (presented_sequence P (presented_option P (\<lambda>r. presented_result_value P f (seed_result_held r))))
                 (presented_boolean P))))))
         (presented_sequence P (presented_option P (\<lambda>r. presented_result_value P f (seed_result_held r))))))"

definition seed_presents :: "'p term_presentation \<Rightarrow> 'p set \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "seed_presents P D f g A \<longleftrightarrow> (\<forall>x. A x \<longrightarrow> f x\<in>D \<and> presented_decode P (f x)=g x)"

lemma seed_presents_pair:
  assumes terms: "presented_terms P D" and f: "seed_presents P D f g A" and h: "seed_presents P D f' g' B"
  shows "seed_presents P D (presented_pair_value P f f') (finite_pair_presentation g g') (\<lambda>z. A (fst z) \<and> B (snd z))"
  unfolding seed_presents_def
proof (intro allI impI)
  fix z
  assume z: "A (fst z) \<and> B (snd z)"
  have fz: "f (fst z)\<in>D" "presented_decode P (f (fst z))=g (fst z)"
    and hz: "f' (snd z)\<in>D" "presented_decode P (f' (snd z))=g' (snd z)"
    using f h z by (simp_all add: seed_presents_def)
  show "presented_pair_value P f f' z\<in>D \<and> presented_decode P (presented_pair_value P f f' z)=finite_pair_presentation g g' z"
    using presented_terms.presented_pair_value_decode[OF terms, where f=f and g=f' and z=z, OF fz(1) hz(1)] fz(2) hz(2)
    by (simp add: finite_pair_presentation_def)
qed

lemma seed_presents_option:
  assumes terms: "presented_terms P D" and f: "seed_presents P D f g A"
  shows "seed_presents P D (presented_option P f) (finite_option_presentation g) (\<lambda>x. \<forall>a\<in>set_option x. A a)"
  unfolding seed_presents_def
proof (intro allI impI)
  fix x
  assume x: "\<forall>a\<in>set_option x. A a"
  have each: "\<And>a. x=Some a \<Longrightarrow> f a\<in>D" using f x by (auto simp: seed_presents_def)
  show "presented_option P f x\<in>D \<and> presented_decode P (presented_option P f x)=finite_option_presentation g x"
    using presented_terms.presented_option_decode[OF terms, where f=f and x=x, OF each] f x
    by (cases x) (auto simp: seed_presents_def)
qed

lemma seed_presents_sequence:
  assumes terms: "presented_terms P D" and f: "seed_presents P D f g A"
  shows "seed_presents P D (presented_sequence P f) (finite_sequence_presentation g) (\<lambda>xs. \<forall>a\<in>set xs. A a)"
  unfolding seed_presents_def
proof (intro allI impI)
  fix xs
  assume xs: "\<forall>a\<in>set xs. A a"
  have each: "\<forall>a\<in>set xs. f a\<in>D" using f xs by (auto simp: seed_presents_def)
  show "presented_sequence P f xs\<in>D \<and> presented_decode P (presented_sequence P f xs)=finite_sequence_presentation g xs"
  proof -
    have m: "map (presented_decode P \<circ> f) xs=map g xs" using f xs by (auto simp: seed_presents_def map_eq_conv)
    have eq: "finite_sequence_presentation (presented_decode P \<circ> f) xs=finite_sequence_presentation g xs"
      by (simp only: finite_sequence_presentation_def m)
    have dec: "presented_sequence P f xs\<in>D \<and>
        presented_decode P (presented_sequence P f xs)=finite_sequence_presentation (presented_decode P \<circ> f) xs"
      by (rule presented_terms.presented_sequence_decode[OF terms, where f=f and xs=xs, OF each])
    show ?thesis using dec eq by auto
  qed
qed

lemma seed_presents_boolean: "presented_terms P D \<Longrightarrow> seed_presents P D (presented_boolean P) finite_boolean_data (\<lambda>b. True)"
  by (simp add: seed_presents_def presented_terms.presented_boolean_decode)

lemma seed_presents_generation:
  assumes terms: "presented_terms P D" and targets: "presented_targets P D f t K"
  shows "seed_presents P D (presented_generation_value P f) (\<lambda>G. finite_target_generation_value (map_generation_structure t G))
    (\<lambda>G. set_generation_structure G\<subseteq>K)"
  unfolding seed_presents_def
proof (intro allI impI)
  fix G
  assume "set_generation_structure G\<subseteq>K"
  then have "presented_targets P D f t (set_generation_structure G)" using targets by (auto simp: presented_targets_def)
  then show "presented_generation_value P f G\<in>D \<and>
      presented_decode P (presented_generation_value P f G)=finite_target_generation_value (map_generation_structure t G)"
    by (rule presented_terms.presented_generation_value_targets[OF terms])
qed

lemma seed_presents_snapshot:
  assumes terms: "presented_terms P D" and targets: "presented_targets P D f t K"
  shows "seed_presents P D (presented_snapshot_value P f) (\<lambda>S. finite_snapshot_value (decode_represented_snapshot t S))
    (\<lambda>S. represented_snapshot_targets S\<subseteq>K)"
  unfolding seed_presents_def
proof (intro allI impI)
  fix S
  assume "represented_snapshot_targets S\<subseteq>K"
  then have "presented_targets P D f t (represented_snapshot_targets S)" using targets by (auto simp: presented_targets_def)
  then show "presented_snapshot_value P f S\<in>D \<and>
      presented_decode P (presented_snapshot_value P f S)=finite_snapshot_value (decode_represented_snapshot t S)"
    using presented_terms.presented_snapshot_value_decode[OF terms] by (simp add: decode_represented_snapshot_def)
qed

lemma seed_presents_result:
  assumes terms: "presented_terms P D" and targets: "presented_targets P D f t K"
  shows "seed_presents P D (\<lambda>r. presented_result_value P f (seed_result_held r))
    (\<lambda>r. finite_transaction_result_value (decode_represented_result t r)) (\<lambda>r. held_result_targets (seed_result_held r)\<subseteq>K)"
  unfolding seed_presents_def
proof (intro allI impI)
  fix r
  assume "held_result_targets (seed_result_held r)\<subseteq>K"
  then have held: "presented_targets P D f t (held_result_targets (seed_result_held r))"
    using targets by (auto simp: presented_targets_def)
  show "presented_result_value P f (seed_result_held r)\<in>D \<and>
      presented_decode P (presented_result_value P f (seed_result_held r))=
        finite_transaction_result_value (decode_represented_result t r)"
    using presented_terms.presented_result_value_decode[OF terms held]
    by (simp add: presented_result_value_plain[symmetric] seed_result_decoded)
qed

definition seed_round_data :: "finite_exact_target list \<Rightarrow> (nat,nat represented_transaction_result) seed_round \<Rightarrow> finite_factor_term" where
  "seed_round_data T=finite_pair_presentation
     (finite_option_presentation (\<lambda>S. finite_snapshot_value (decode_represented_snapshot (\<lambda>i. T!i) S)))
     (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
       (finite_pair_presentation (finite_sequence_presentation
         (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
           (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
             (finite_pair_presentation (finite_option_presentation (\<lambda>G. finite_target_generation_value (map_generation_structure (\<lambda>i. T!i) G)))
               (finite_pair_presentation (finite_sequence_presentation (finite_option_presentation
                   (\<lambda>r. finite_transaction_result_value (decode_represented_result (\<lambda>i. T!i) r))))
                 finite_boolean_data)))))
         (finite_sequence_presentation (finite_option_presentation
           (\<lambda>r. finite_transaction_result_value (decode_represented_result (\<lambda>i. T!i) r))))))"

lemma seed_option_map: "finite_option_presentation f (map_option d x)=finite_option_presentation (\<lambda>a. f (d a)) x"
  by (cases x) simp_all

lemma seed_sequence_map: "finite_sequence_presentation f (map d xs)=finite_sequence_presentation (\<lambda>a. f (d a)) xs"
  by (simp add: finite_sequence_presentation_def o_def)

lemma seed_round_data_decode: "seed_round_data T v=development_seed_publication_data (seed_round_decode T v)"
  by (cases v) (simp add: seed_round_data_def development_seed_publication_data_def seed_round_decode_def
    finite_pair_presentation_def[abs_def] seed_option_map seed_sequence_map case_prod_unfold)

theorem seed_round_presented_decode:
  assumes terms: "presented_terms P D" and targets: "presented_targets P D f (\<lambda>i. T!i) {..<length T}"
    and within: "seed_round_within {..<length T} v"
  shows "seed_round_presented P f v\<in>D \<and>
    presented_decode P (seed_round_presented P f v)=development_seed_publication_data (seed_round_decode T v)"
proof -
  note gen=seed_presents_generation[OF terms targets]
  note res=seed_presents_result[OF terms targets]
  note snap=seed_presents_snapshot[OF terms targets]
  note opt=seed_presents_option[OF terms] and seq=seed_presents_sequence[OF terms] and pair=seed_presents_pair[OF terms]
  note whole=pair[OF opt[OF snap] pair[OF opt[OF gen] pair[OF seq[OF pair[OF opt[OF gen] pair[OF opt[OF gen]
    pair[OF opt[OF gen] pair[OF seq[OF opt[OF res]] seed_presents_boolean[OF terms]]]]]] seq[OF opt[OF res]]]]]
  obtain S0 Sel rows results where v: "v=(S0,Sel,rows,results)" by (metis prod.collapse)
  have "seed_round_presented P f v\<in>D \<and> presented_decode P (seed_round_presented P f v)=seed_round_data T v"
    unfolding seed_round_presented_def seed_round_data_def
    by (rule whole[unfolded seed_presents_def, rule_format]) (use within in \<open>auto simp: v seed_round_within_def\<close>)
  then show ?thesis by (simp add: seed_round_data_decode)
qed

definition development_seed_publication_word_fold :: "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> development_problem fset \<Rightarrow> 's \<Rightarrow> 's" where
  "development_seed_publication_word_fold f A z=finite_term_shared_word_fold f (development_seed_publication_value A) z"

theorem development_seed_publication_word_fold_code [code]:
  "development_seed_publication_word_fold f A z=(case development_seed_reference_round A of (v,T) \<Rightarrow>
     shared_term_word_fold f (seed_shapes T) (seed_round_presented (seed_table_presentation T) Shared_Reference v) z)"
proof -
  obtain v T where round: "development_seed_reference_round A=(v,T)" by (cases "development_seed_reference_round A")
  have distinct: "distinct T" and within: "seed_round_within {..<length T} v"
    using development_seed_reference_round_within[of A] by (simp_all add: round)
  have decoded: "seed_round_decode T v=development_seed_publication A"
    using development_seed_reference_round_decoded[of A] by (simp add: round)
  let ?P="table_presentation (seed_shapes T)"
  have formed: "table_formed (seed_shapes T)" by (rule seed_shapes_formed[OF distinct])
  have terms: "presented_terms ?P {s. shared_canonical (seed_shapes T) s}" by (rule table_presentation_terms[OF formed])
  have presented: "seed_round_presented ?P Shared_Reference v\<in>{s. shared_canonical (seed_shapes T) s} \<and>
      presented_decode ?P (seed_round_presented ?P Shared_Reference v)=development_seed_publication_value A"
    using seed_round_presented_decode[OF terms seed_presented_targets within] decoded
    by (simp add: development_seed_publication_value_def)
  obtain t where t: "shared_decode (seed_shapes T) (seed_round_presented ?P Shared_Reference v)=Some t"
    using canonical_decodes[OF formed] presented by blast
  have "t=development_seed_publication_value A" using presented t by (simp add: table_presentation_def)
  then show ?thesis
    using t by (simp add: round development_seed_publication_word_fold_def seed_table_presentation_exact
      shared_term_word_fold_exact)
qed

end
