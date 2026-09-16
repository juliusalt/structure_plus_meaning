theory Factor_Source_Development_Cycle
  imports Factor_Source_Development_Subjects Factor_Steered_Development
begin

type_synonym source_development_entry =
  "local_address option definition_site\<times>local_address option finite_artifact_environment\<times>local_address option"

type_synonym source_development_execution =
  "nat\<times>native_development_question\<times>native_development_report\<times>
    finite_factor_term list option\<times>finite_factor_term list option"

record source_development_report =
  source_report_proposals :: "source_development_proposal list"
  source_report_observations :: "(nat\<times>bool list) list"
  source_report_question :: "native_development_question option"
  source_report_execution :: "source_development_execution option"
  source_report_selected :: "source_development_proposal option"
  source_report_installed :: "source_development_entry option"
  source_report_stage :: "native_workflow_stage option"
  source_report_query :: "native_workflow_stage_result option"

definition source_development_observations where
  "source_development_observations R=map (\<lambda>i. (i,map (source_development_observation R i) [0,1,2,3]))
    (source_development_indices R)"

lemma source_development_observations_shared [code]:
  "source_development_observations R=(let complete=finite_development_scope_complete (source_development_values R) in
    map (\<lambda>i. (i,[source_development_observation R i 0,source_development_observation R i 1,
      source_development_observation R i 2,complete])) (source_development_indices R))"
  unfolding source_development_observations_def Let_def
  by (rule map_cong[OF refl])
    (use source_development_scope_observation in \<open>auto simp: source_development_indices_def\<close>)

definition source_development_install where
  "source_development_install R proposal=(case proposal of (Q,e) \<Rightarrow>
    finite_install_source_entry (source_development_environment R) (source_development_use R)
      (source_development_root R) Q e)"

definition source_development_query_stage :: "source_development_request \<Rightarrow>
    source_development_entry \<Rightarrow> native_workflow_stage" where
  "source_development_query_stage R installed=(case installed of (d,F,u) \<Rightarrow>
    \<lparr>workflow_source=F,workflow_source_use=u,workflow_source_root=[],workflow_entry=d,
      workflow_outputs=Workflow_Values (source_development_outputs R)\<rparr>)"

definition construct_source_development :: "nat \<Rightarrow> source_development_request \<Rightarrow> source_development_report" where
  "construct_source_development m R=(let
    question=source_development_question R;
    execution=map_option (steered_development_result m) question;
    selected=(case execution of Some (k,Q,report,claim,Some accepted) \<Rightarrow>
      source_development_selection R accepted | _ \<Rightarrow> None);
    installed=(case selected of None \<Rightarrow> None | Some proposal \<Rightarrow> source_development_install R proposal);
    stage=map_option (source_development_query_stage R) installed;
    query=(case stage of None \<Rightarrow> None | Some S \<Rightarrow> evaluate_workflow_stage S (source_development_input R))
    in \<lparr>source_report_proposals=source_development_proposals R,
      source_report_observations=source_development_observations R,
      source_report_question=question,source_report_execution=execution,
      source_report_selected=selected,source_report_installed=installed,
      source_report_stage=stage,source_report_query=query\<rparr>)"

definition source_development_admission :: "source_development_request \<Rightarrow> source_development_report \<Rightarrow>
    (source_development_proposal\<times>source_development_entry\<times>native_workflow_stage_result) option" where
  "source_development_admission R report=(case
    (source_report_question report,source_report_execution report,source_report_selected report,
      source_report_installed report,source_report_stage report,source_report_query report) of
    (Some Q,Some (m,q,native,claim,Some accepted),Some proposal,Some installed,Some S,Some query) \<Rightarrow>
      if source_report_proposals report=source_development_proposals R \<and>
        source_report_observations report=source_development_observations R \<and>
        source_development_question R=Some Q \<and> q=Q \<and> claim=Some accepted \<and>
        source_report_execution report=Some (steered_development_result m Q) \<and>
        native_development_admission Q native=Some accepted \<and>
        source_development_selection R accepted=Some proposal \<and>
        source_development_install R proposal=Some installed \<and>
        S=source_development_query_stage R installed \<and>
        workflow_stage_evidence S (source_development_input R) query
      then Some (proposal,installed,query) else None
    | _ \<Rightarrow> None)"

definition source_development_packet where
  "source_development_packet m R=(let report=construct_source_development m R in
    (R,report,source_development_admission R report))"

definition native_source_development where
  "native_source_development qs requests=(let policy=native_steered_development qs [];
    chosen=fst (snd (snd policy)) in
    (requests,policy,map_option (\<lambda>m. Parallel.map (source_development_packet m) requests) chosen))"

lemma native_source_development_requests:
  "fst (native_source_development qs requests)=requests"
  by (simp only: native_source_development_def Let_def fst_conv)

lemma native_source_development_dispatch:
  assumes chosen: "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
  shows "snd (snd (native_source_development qs requests))=Some (map (source_development_packet m) requests)"
  by (simp only: native_source_development_def native_steered_development_def Let_def
    fst_conv snd_conv chosen option.simps Parallel.map_def)

lemma native_source_development_no_choice:
  assumes "development_steering_choice (snd (snd (development_steering_packet qs)))=None"
  shows "snd (snd (native_source_development qs requests))=None"
  using assms by (simp only: native_source_development_def native_steered_development_def
    Let_def fst_conv snd_conv option.simps)

theorem native_source_development_producer:
  assumes execution: "snd (snd (native_source_development qs requests))=Some packets"
  obtains m where
    "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
    "packets=map (source_development_packet m) requests"
    "\<forall>q\<in>set qs. \<forall>f\<in>set development_facets.
      development_producer_condition f (development_producer m) q"
proof -
  obtain m where chosen: "development_steering_choice (snd (snd (development_steering_packet qs)))=Some m"
    and packets: "packets=map (source_development_packet m) requests"
    using execution by (auto simp: native_source_development_def native_steered_development_def
      Let_def Parallel.map_def split: option.splits)
  have conditions: "\<forall>q\<in>set qs. \<forall>f\<in>set development_facets.
      development_producer_condition f (development_producer m) q"
    using development_chosen_producer_conditions[OF chosen] by blast
  show thesis by (rule that[OF chosen packets conditions])
qed

lemma source_development_packet_original:
  "fst (source_development_packet m R)=R"
  by (simp only: source_development_packet_def Let_def fst_conv)

definition source_development_boundary where
  "source_development_boundary qs requests=(qs,requests)"

definition reconstruct_source_development where
  "reconstruct_source_development boundary=(case boundary of (qs,requests) \<Rightarrow>
    native_source_development qs requests)"

lemma source_development_reconstructs:
  "reconstruct_source_development (source_development_boundary qs requests)=native_source_development qs requests"
  by (simp only: reconstruct_source_development_def source_development_boundary_def case_prod_conv)

text \<open>
  The existing computed producer choice runs each actual source-change question.
  Only its admitted proposal can reach installation. The resulting environment,
  package selector and placed entry supply the next native query directly.
  Final admission rechecks every original field and the complete query evidence;
  a missing installation or unavailable required query cannot commit a change.
  Independent requests execute in parallel after the shared native policy choice.

  The retained original questions and source requests reconstruct all results.
  This local equation has no accumulated process-history argument; it does not
  establish a global physical-cost bound or historical authority to amend an
  active normative package.
\<close>

end
