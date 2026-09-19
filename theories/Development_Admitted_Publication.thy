theory Development_Admitted_Publication
  imports Development_Certified_Generations RRA_Formed_Snapshot_Transactions Parallel_Computed_Preparation
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
  An admitted answer is recorded as a certified generation beside the incumbent it was judged against
  and is selected by the transaction that expects that incumbent at the problem's locus. The published
  state that transaction is executed on holds the incumbent alone: a judgment concerns one request, and
  the transaction records what publishing the answer does at its locus. Admission and selection stay
  apart: the generation is admitted whether or not it is published, and a refused answer is recorded
  as nothing and publishes nothing, while its incumbent is still judged, so the publication shows what
  the answer was measured against.
\<close>

type_synonym development_answer_publication =
  "finite_generation option\<times>finite_generation option\<times>finite_transaction_result option list"

definition development_answer_publication_with ::
    "development_payload_judge \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_answer_publication" where
  "development_answer_publication_with judge S r S'=(case development_incumbent_with judge S (fst r) of
     None \<Rightarrow> (None,None,[])
   | Some (B,u,I) \<Rightarrow> (let G=map_option (\<lambda>(B',u',G). G) (development_answer_with judge S r S' B [((u,[]),I)]) in
       (Some I,G,finite_locus_publications {|I|} [(Some I,G)])))"

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
  A recorded generation stands at the locus it was recorded at and is formed, whatever judge supplied
  its judgment; the incumbent and the answer of one request are recorded at the locus of the request's
  problem. The transaction publishing the answer over its incumbent therefore always applies and
  selects the answer at that locus: this is the replacement theorem of the published state
  (\<open>development_publication_applied\<close>), instantiated, not proved again.
\<close>

lemma development_judged_generation_fields:
  assumes recorded: "development_judged_generation judged H l rows=Some (B,u,G)"
  shows "generation_locus G=l" "finite_generation_formed G"
proof -
  obtain R j where judged: "judged=(R,j)" by (cases judged) auto
  obtain d K pu B0 au root J C where shape: "j=(d,K,pu,B0,au,root,J,C)" by (cases j) auto
  have built: "finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows=Some (B,u,G)"
    using recorded by (simp add: development_judged_generation_def development_recorded_generation_def judged shape)
  note constructed=finite_construct_generation_record_correct[OF built]
  show "generation_locus G=l" using constructed(2) by (simp add: finite_generation_record_core_def)
  show "finite_generation_formed G" by (rule finite_check_generation_formed[OF constructed(6)])
qed

lemma development_incumbent_with_fields:
  assumes built: "development_incumbent_with judge S p=Some (B,u,I)"
  shows "development_data_target (development_problem_locus (fst (snd S)) p)=Some (generation_locus I)"
    "finite_generation_formed I"
proof -
  obtain l t judged where key: "development_incumbent_key S p=Some (l,t)"
    and recorded: "development_judged_generation judged (finite_enumerated_environment [] []) l []=Some (B,u,I)"
    using built by (auto simp: development_incumbent_with_def bind_eq_Some_conv split: prod.splits)
  have locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    using key by (auto simp: development_incumbent_key_def bind_eq_Some_conv)
  note fields=development_judged_generation_fields[OF recorded]
  show "development_data_target (development_problem_locus (fst (snd S)) p)=Some (generation_locus I)"
    using locus fields(1) by simp
  show "finite_generation_formed I" by (rule fields(2))
qed

lemma development_answer_with_fields:
  assumes built: "development_answer_with judge S r S' H rows=Some (B,u,G)"
  shows "development_data_target (development_problem_locus (fst (snd S)) (fst r))=Some (generation_locus G)"
    "finite_generation_formed G"
proof -
  obtain l t judged where key: "development_answer_key S r S'=Some (l,t)"
    and recorded: "development_judged_generation judged H l (filter (\<lambda>(d,G). generation_locus G=l) rows)=Some (B,u,G)"
    using built by (auto simp: development_answer_with_def bind_eq_Some_conv split: prod.splits)
  obtain p E payload v where generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
    and locus: "development_data_target (development_problem_locus (fst (snd S)) p)=Some l"
    using key by (auto simp: development_answer_key_def bind_eq_Some_conv split: option.splits)
  have problem: "p=fst r"
    using generation by (auto simp: development_answer_generation_def Let_def split: prod.splits if_splits)
  note fields=development_judged_generation_fields[OF recorded]
  show "development_data_target (development_problem_locus (fst (snd S)) (fst r))=Some (generation_locus G)"
    using locus fields(1) problem by simp
  show "finite_generation_formed G" by (rule fields(2))
qed

theorem development_answer_publication_applied:
  assumes published: "development_answer_publication_with judge S r S'=(Some I,Some G,results)"
  obtains U where "results=[Some (Finite_Applied U)]" "finite_snapshot_formed U"
    "finite_snapshot_lookup U (generation_locus G)=Some G" "generation_locus G=generation_locus I"
proof -
  obtain B u where incumbent: "development_incumbent_with judge S (fst r)=Some (B,u,I)"
    and answer: "map_option (\<lambda>(B',u',G). G) (development_answer_with judge S r S' B [((u,[]),I)])=Some G"
    and listed: "results=finite_locus_publications {|I|} [(Some I,Some G)]"
    using published by (auto simp: development_answer_publication_with_def Let_def split: option.splits prod.splits)
  obtain B' u' where recorded: "development_answer_with judge S r S' B [((u,[]),I)]=Some (B',u',G)"
    using answer by auto
  note incumbent_fields=development_incumbent_with_fields[OF incumbent]
  note answer_fields=development_answer_with_fields[OF recorded]
  have locus: "generation_locus G=generation_locus I"
    using incumbent_fields(1) answer_fields(1) by simp
  have formed: "finite_snapshot_formed {|I|}"
    using incumbent_fields(2) by (simp add: finite_snapshot_formed_def finite_snapshot_loci_def fcard_finsert_if fcard_fempty)
  have lookup: "finite_snapshot_lookup {|I|} (generation_locus G)=Some I"
    using locus by (simp only: finite_snapshot_lookup_formed[OF formed]) simp
  obtain U where transact: "finite_transact {|I|} (finite_locus_transaction (Some I) G)=Some (Finite_Applied U)"
    and successor: "finite_snapshot_formed U" and selected: "finite_snapshot_lookup U (generation_locus G)=Some G"
    by (rule development_publication_applied[OF formed lookup answer_fields(2)])
  have "results=[Some (Finite_Applied U)]"
    using listed transact by (simp add: Let_def)
  then show thesis using successor selected locus by (rule that)
qed

corollary development_admitted_publication_applied:
  assumes admitted: "development_admitted_publication S r S' X=(Some I,Some G,results)"
  obtains U where "results=[Some (Finite_Applied U)]" "finite_snapshot_formed U"
    "finite_snapshot_lookup U (generation_locus G)=Some G" "generation_locus G=generation_locus I"
proof -
  obtain S0 r0 where route: "development_admitted_route S r S' X=(S0,r0)" by (cases "development_admitted_route S r S' X") auto
  have published: "development_answer_publication_with development_payload_judgment S0 r0 S'=(Some I,Some G,results)"
    using admitted by (simp add: development_admitted_publication_def development_answer_publication_def route)
  show thesis
    by (rule development_answer_publication_applied[OF published]) (rule that; assumption)
qed

section \<open>Each family is judged once, in parallel\<close>

text \<open>
  The incumbent and the answer are judged by their families' presentations with their names. An
  answer that changes nothing presents the incumbent's family and is judged with it once; otherwise the
  two judgments are independent and are made in parallel. The prepared function is the judgment itself.
\<close>

declare development_answer_publication_def [code del]

lemma development_answer_publication_prepared [code]:
  "development_answer_publication S r S'=development_answer_publication_with
     (parallel_computed_function development_payload_judgment
       (List.map_filter (map_option snd) [development_incumbent_key S (fst r),development_answer_key S r S'])) S r S'"
  by (simp only: development_answer_publication_def parallel_computed_function_exact)

section \<open>The publication is presented through the presentations of its notions\<close>

definition development_answer_publication_data :: "development_answer_publication \<Rightarrow> finite_factor_term" where
  "development_answer_publication_data=finite_pair_presentation (finite_option_presentation finite_target_generation_value)
    (finite_pair_presentation (finite_option_presentation finite_target_generation_value)
      (finite_sequence_presentation (finite_option_presentation finite_transaction_result_value)))"

lemma development_answer_publication_data_injective [intro]: "inj development_answer_publication_data"
  unfolding development_answer_publication_data_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective
    finite_sequence_presentation_injective) blast+

definition development_answer_published :: "development_answer_publication \<Rightarrow> bool" where
  "development_answer_published P \<longleftrightarrow> (case P of (Some I,Some G,[Some (Finite_Applied U)]) \<Rightarrow> True | _ \<Rightarrow> False)"

end
