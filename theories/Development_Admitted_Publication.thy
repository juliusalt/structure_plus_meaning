theory Development_Admitted_Publication
  imports Development_Decision_Generations RRA_Formed_Snapshot_Transactions Parallel_Computed_Preparation
begin

section \<open>The request an answer is admitted against\<close>

text \<open>
  A judged answer is admitted against its own request when the verdict accepts it. When the verdict
  refuses it only for constants the answer introduces, the repair judges the same answer again against
  the request issued over the extension that defines them (\<open>Development_Refinement_Repair\<close>); when the
  extension and that judgment both accept, the answer is admitted against the reissued request in the
  extended state, as the repaired successor of the development moves it. Otherwise the answer is not
  admitted, and its own request is the one it was refused against. The extension keeps every entity
  and position of the request state, so the incumbent a problem has there is the one it has in the
  request state.
\<close>

definition development_admitted_route ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow>
      isabelle_rooted_context\<times>development_request" where
  "development_admitted_route S r S' I=(let v=development_refinement_verdict S r S' in
     if development_refinement_accepted v then (S,r)
     else (case development_refinement_repair S r S' I of (e,ds,r',v',a') \<Rightarrow>
       if development_extension_accepted e \<and> a' then (development_repair_state S r S' I,r') else (S,r)))"

section \<open>An admitted answer is published over the incumbent it was judged against\<close>

text \<open>
  An admitted answer is recorded as a certified generation beside the incumbent it was judged against and
  the issue of its request, and it cites the issue, which cites the incumbent. The issue is recorded at
  the problem's issue locus; a request judged here is made on demand, so no selection is cited, and it
  rests on the reading of the development library, which holds no rule. The published state the judgment publishes
  into holds the incumbent alone: a judgment concerns one request, and the transactions record what
  publishing its issue and its answer does. The issue is admitted where no issue stood, and the answer
  replaces the incumbent at the problem's locus. Admission and selection stay apart: the answer is
  admitted whether or not it is published, and a refused answer is recorded as nothing and publishes
  nothing, while its incumbent and its issue are still judged, so the publication shows what the answer
  was measured against.
\<close>

type_synonym development_answer_publication =
  "finite_generation option\<times>finite_generation option\<times>finite_generation option\<times>finite_transaction_result option list"

definition development_answer_publication_using ::
    "development_constructor \<Rightarrow> development_payload_judge \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> development_answer_publication" where
  "development_answer_publication_using construct judge S r S'=(case development_incumbent_with judge S (fst r) of
     None \<Rightarrow> (None,None,None,[])
   | Some (B,u,I) \<Rightarrow> (case development_recorded_issue_using construct judge (fst (snd S)) None r
         (development_library_reading {||} (fst r)) (B,u,I) of
       None \<Rightarrow> (Some I,None,None,[])
     | Some (B2,rows,Q) \<Rightarrow> (let G=map_option (\<lambda>(B',u',G). G) (development_answer_using construct judge S r S' B2 rows) in
         (Some I,Some Q,G,finite_locus_publications {|I|} [(None,Some Q),(Some I,G)]))))"

definition development_answer_publication_with ::
    "development_payload_judge \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_answer_publication" where
  "development_answer_publication_with=development_answer_publication_using finite_construct_generation_record"

lemma development_answer_publication_with_unfold:
  "development_answer_publication_with judge S r S'=(case development_incumbent_with judge S (fst r) of
     None \<Rightarrow> (None,None,None,[])
   | Some (B,u,I) \<Rightarrow> (case development_recorded_issue_with judge (fst (snd S)) None r
         (development_library_reading {||} (fst r)) (B,u,I) of
       None \<Rightarrow> (Some I,None,None,[])
     | Some (B2,rows,Q) \<Rightarrow> (let G=map_option (\<lambda>(B',u',G). G) (development_answer_with judge S r S' B2 rows) in
         (Some I,Some Q,G,finite_locus_publications {|I|} [(None,Some Q),(Some I,G)]))))"
  by (simp only: development_answer_publication_with_def development_answer_publication_using_def
    development_recorded_issue_with_def development_answer_with_def)

definition development_answer_publication ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_answer_publication" where
  "development_answer_publication=development_answer_publication_with development_payload_judgment"

definition development_admitted_publication ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow>
      development_answer_publication" where
  "development_admitted_publication S r S' I=(case development_admitted_route S r S' I of
     (S0,r0) \<Rightarrow> development_answer_publication S0 r0 S')"

section \<open>The publication of an admitted answer applies\<close>

text \<open>
  A recorded generation stands at the locus it was recorded at and is formed, whatever judge supplied its
  judgment; the incumbent and the answer of one request are recorded at the locus of the request's
  problem, and its issue at the problem's issue locus, which is not the locus of any problem. The
  transaction admitting the issue therefore applies, and the transaction publishing the answer over its
  incumbent then applies and selects the answer: these are the admission and replacement theorems of the
  published state (\<open>development_publication_admitted\<close>, \<open>development_publication_applied\<close>), instantiated,
  not proved again.
\<close>

lemma development_incumbent_with_fields:
  assumes built: "development_incumbent_with judge S p=Some (B,u,I)"
  shows "development_data_target (development_problem_locus (fst (snd S)) p)=Some (generation_locus I)"
    "finite_generation_formed I"
proof -
  obtain l t where key: "development_incumbent_key S p=Some (l,t)"
    and generated: "development_payload_generation_with judge t (finite_enumerated_environment [] []) l []=Some (B,u,I)"
    using built by (auto simp: development_incumbent_with_def bind_eq_Some_conv split: prod.splits)
  have locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    using key by (auto simp: development_incumbent_key_def bind_eq_Some_conv)
  note fields=development_payload_generation_fields[OF generated]
  show "development_data_target (development_problem_locus (fst (snd S)) p)=Some (generation_locus I)"
    using locus fields(1) by simp
  show "finite_generation_formed I" by (rule fields(2))
qed

lemma development_answer_with_fields:
  assumes built: "development_answer_with judge S r S' H rows=Some (B,u,G)"
  shows "development_data_target (development_problem_locus (fst (snd S)) (fst r))=Some (generation_locus G)"
    "finite_generation_formed G"
proof -
  obtain l t where key: "development_answer_key S r S'=Some (l,t)"
    and generated: "development_payload_generation_with judge t H l
      (development_answer_citations (fst (snd S)) (fst r) l rows)=Some (B,u,G)"
    using built by (auto simp: development_answer_with_unfold bind_eq_Some_conv split: prod.splits)
  obtain p E payload v where generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
    and locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    using key by (auto simp: development_answer_key_def bind_eq_Some_conv split: option.splits)
  have problem: "p=fst r"
    using generation by (auto simp: development_answer_generation_def Let_def split: prod.splits if_splits)
  note fields=development_payload_generation_fields[OF generated]
  show "development_data_target (development_problem_locus (fst (snd S)) (fst r))=Some (generation_locus G)"
    using locus fields(1) problem by simp
  show "finite_generation_formed G" by (rule fields(2))
qed

theorem development_answer_publication_applied:
  assumes published: "development_answer_publication_with judge S r S'=(Some I,Some Q,Some G,results)"
  obtains U V where "results=[Some (Finite_Applied U),Some (Finite_Applied V)]" "finite_snapshot_formed V"
    "finite_snapshot_lookup V (generation_locus G)=Some G" "finite_snapshot_lookup V (generation_locus Q)=Some Q"
    "generation_locus G=generation_locus I"
proof -
  obtain B u B2 rows where incumbent: "development_incumbent_with judge S (fst r)=Some (B,u,I)"
    and issue: "development_recorded_issue_with judge (fst (snd S)) None r
      (development_library_reading {||} (fst r)) (B,u,I)=Some (B2,rows,Q)"
    and answer: "map_option (\<lambda>(B',u',G). G) (development_answer_with judge S r S' B2 rows)=Some G"
    and listed: "results=finite_locus_publications {|I|} [(None,Some Q),(Some I,Some G)]"
    using published by (auto simp: development_answer_publication_with_unfold Let_def simp del: finite_locus_publications.simps
      split: option.splits prod.splits)
  obtain B' u' where recorded: "development_answer_with judge S r S' B2 rows=Some (B',u',G)"
    using answer by auto
  note incumbent_fields=development_incumbent_with_fields[OF incumbent]
  note answer_fields=development_answer_with_fields[OF recorded]
  obtain B1 cited uq where issue_fields: "development_data_target (development_issue_locus (fst (snd S)) (fst r))=
      Some (generation_locus Q)" "finite_generation_formed Q"
    by (rule development_recorded_issue_fields[OF issue]) blast
  have locus: "generation_locus G=generation_locus I"
    using incumbent_fields(1) answer_fields(1) by simp
  have separate: "generation_locus Q\<noteq>generation_locus I"
    by (rule development_data_targets_distinct[OF issue_fields(1) incumbent_fields(1)])
      (simp_all add: development_decision_loci_distinct)
  have formed: "finite_snapshot_formed {|I|}"
    using incumbent_fields(2) by (simp add: finite_snapshot_formed_def finite_snapshot_loci_def fcard_finsert_if fcard_fempty)
  have absent: "finite_snapshot_lookup {|I|} (generation_locus Q)=None"
    using separate by (simp add: finite_snapshot_lookup_none[OF formed] finite_snapshot_loci_def)
  obtain U where admit: "finite_transact {|I|} (finite_locus_transaction None Q)=Some (Finite_Applied U)"
    and admitted: "finite_snapshot_formed U" and issued: "finite_snapshot_lookup U (generation_locus Q)=Some Q"
    and kept: "\<And>l. l\<noteq>generation_locus Q \<Longrightarrow> finite_snapshot_lookup U l=finite_snapshot_lookup {|I|} l"
  proof (rule development_publication_admitted[OF formed absent issue_fields(2)])
    fix U assume "finite_transact {|I|} (finite_locus_transaction None Q)=Some (Finite_Applied U)"
      "finite_snapshot_formed U" "finite_snapshot_lookup U (generation_locus Q)=Some Q"
      "\<And>l. l\<noteq>generation_locus Q \<Longrightarrow> finite_snapshot_lookup U l=finite_snapshot_lookup {|I|} l"
    then show thesis by (rule that)
  qed
  have standing: "finite_snapshot_lookup U (generation_locus G)=Some I"
    using kept[of "generation_locus G"] separate locus
    by (simp add: finite_snapshot_lookup_formed[OF formed])
  obtain V where replace: "finite_transact U (finite_locus_transaction (Some I) G)=Some (Finite_Applied V)"
    and replaced: "finite_snapshot_formed V" and selected: "finite_snapshot_lookup V (generation_locus G)=Some G"
    and others: "\<And>l. l\<noteq>generation_locus G \<Longrightarrow> finite_snapshot_lookup V l=finite_snapshot_lookup U l"
  proof (rule development_publication_applied[OF admitted standing answer_fields(2)])
    fix V assume "finite_transact U (finite_locus_transaction (Some I) G)=Some (Finite_Applied V)"
      "finite_snapshot_formed V" "finite_snapshot_lookup V (generation_locus G)=Some G"
      "\<And>l. l\<noteq>generation_locus G \<Longrightarrow> finite_snapshot_lookup V l=finite_snapshot_lookup U l"
    then show thesis by (rule that)
  qed
  have still: "finite_snapshot_lookup V (generation_locus Q)=Some Q"
    using others[of "generation_locus Q"] separate locus issued by simp
  have "results=[Some (Finite_Applied U),Some (Finite_Applied V)]"
    using listed admit replace by simp
  then show thesis by (rule that[OF _ replaced selected still locus])
qed

corollary development_admitted_publication_applied:
  assumes admitted: "development_admitted_publication S r S' X=(Some I,Some Q,Some G,results)"
  obtains U V where "results=[Some (Finite_Applied U),Some (Finite_Applied V)]" "finite_snapshot_formed V"
    "finite_snapshot_lookup V (generation_locus G)=Some G" "finite_snapshot_lookup V (generation_locus Q)=Some Q"
    "generation_locus G=generation_locus I"
proof -
  obtain S0 r0 where route: "development_admitted_route S r S' X=(S0,r0)" by (cases "development_admitted_route S r S' X") auto
  have published: "development_answer_publication_with development_payload_judgment S0 r0 S'=(Some I,Some Q,Some G,results)"
    using admitted by (simp add: development_admitted_publication_def development_answer_publication_def route)
  show thesis
    by (rule development_answer_publication_applied[OF published]) (rule that; assumption)
qed

section \<open>The chain of a publication records with known readings\<close>

text \<open>
  The incumbent is recorded in an environment of its own; the issue is recorded in that environment,
  citing the incumbent, and the answer in the issue's, citing the issue. Every environment the chain
  records in is one it has recorded, and every generation it cites is one it has recorded there, so the
  chain is executed with the known constructor (\<open>development_recorded_issue_using_known\<close>,
  \<open>development_answer_using_known\<close>) and reads no predecessor back.
\<close>

declare development_answer_publication_with_def [code del]

lemma development_answer_publication_known [code]:
  "development_answer_publication_with judge S r S'=
    development_answer_publication_using finite_construct_known_original_generation judge S r S'"
proof (cases "development_incumbent_with judge S (fst r)")
  case None
  then show ?thesis by (simp add: development_answer_publication_using_def development_answer_publication_with_unfold)
next
  case (Some incumbent)
  obtain B u I where built: "development_incumbent_with judge S (fst r)=Some (B,u,I)"
    using Some by (cases incumbent) auto
  note recorded=development_incumbent_with_recorded[OF built]
  have issued: "development_recorded_issue_using finite_construct_known_original_generation judge (fst (snd S)) None r
      (development_library_reading {||} (fst r)) (B,u,I)=
    development_recorded_issue_with judge (fst (snd S)) None r (development_library_reading {||} (fst r)) (B,u,I)"
    by (rule development_recorded_issue_using_known[OF recorded])
  show ?thesis
  proof (cases "development_recorded_issue_with judge (fst (snd S)) None r (development_library_reading {||} (fst r)) (B,u,I)")
    case None
    then show ?thesis
      by (simp add: built issued development_answer_publication_using_def development_answer_publication_with_unfold)
  next
    case (Some result)
    obtain B2 rows Q where issue: "development_recorded_issue_with judge (fst (snd S)) None r
        (development_library_reading {||} (fst r)) (B,u,I)=Some (B2,rows,Q)"
      using Some by (cases result) auto
    note known=development_recorded_issue_recorded[OF issue]
    have answered: "development_answer_using finite_construct_known_original_generation judge S r S' B2 rows=
        development_answer_with judge S r S' B2 rows"
      by (rule development_answer_using_known[OF known])
    show ?thesis
      by (simp add: built issued issue answered development_answer_publication_using_def
        development_answer_publication_with_unfold)
  qed
qed

section \<open>Each family is judged once, in parallel\<close>

text \<open>
  The incumbent and the answer are judged by their families' presentations with their names, and the
  issue by its payload. An answer that changes nothing presents the incumbent's family and is judged with
  it once; otherwise the judgments are independent and are made in parallel. The prepared function is the
  judgment itself.
\<close>

declare development_answer_publication_def [code del]

lemma development_answer_publication_prepared [code]:
  "development_answer_publication S r S'=development_answer_publication_with
     (parallel_computed_function development_payload_judgment
       (List.map_filter (map_option snd) [development_incumbent_key S (fst r),development_answer_key S r S']@
        [development_issue_payload (fst (snd S)) r (development_library_reading {||} (fst r))])) S r S'"
  by (simp only: development_answer_publication_def parallel_computed_function_exact)

section \<open>The publication is presented through the presentations of its notions\<close>

definition development_answer_publication_data :: "development_answer_publication \<Rightarrow> finite_factor_term" where
  "development_answer_publication_data=finite_pair_presentation (finite_option_presentation finite_target_generation_value)
    (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
      (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
        (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value))))"

lemma development_answer_publication_data_injective [intro]: "inj development_answer_publication_data"
  unfolding development_answer_publication_data_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective) blast+

definition development_answer_published :: "development_answer_publication \<Rightarrow> bool" where
  "development_answer_published P \<longleftrightarrow> (case P of
     (Some I,Some Q,Some G,[Some (Finite_Applied U),Some (Finite_Applied V)]) \<Rightarrow> True | _ \<Rightarrow> False)"

end
