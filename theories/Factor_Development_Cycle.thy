theory Factor_Development_Cycle
  imports Factor_Development_Conditions Finite_Assessment_Reports
begin

type_synonym native_development_call = "local_address option definition_site\<times>finite_factor_term"
type_synonym native_development_application =
  "(local_address option definition_site\<times>local_address)\<times>finite_factor_term\<times>
    (local_address\<times>finite_factor_term) fset\<times>(local_address\<times>native_development_call) fset"
type_synonym native_development_generation = "local_address option finite_native_system\<times>
  native_development_call fset\<times>native_development_call fset\<times>native_development_application list"
type_synonym native_development_comparison = "(nat\<times>nat\<times>nat) list\<times>(nat\<times>nat) list\<times>nat list\<times>nat list"

type_synonym native_development_basis =
  "bool\<times>(nat\<times>nat) list\<times>(nat\<times>(nat\<times>nat) list) list\<times>(nat\<times>nat\<times>(nat\<times>nat) list) list"
type_synonym native_development_repairs =
  "nat list\<times>(nat\<times>nat\<times>nat\<times>nat) list\<times>(nat\<times>nat\<times>nat\<times>nat) list\<times>(nat\<times>nat) list"
type_synonym native_development_revision =
  "nat list\<times>nat list\<times>(nat\<times>nat\<times>nat\<times>nat) list\<times>nat list\<times>(nat\<times>nat) list"
type_synonym native_development_cycle =
  "nat list\<times>native_development_basis\<times>native_development_repairs\<times>native_development_revision\<times>native_development_basis"

record native_development_question =
  development_source :: "local_address option finite_artifact_environment"
  development_source_use :: "local_address option"
  development_source_root :: local_address
  development_generator_entry :: "local_address option definition_site"
  development_problem :: finite_factor_term
  development_conditions :: "native_development_condition list"
  development_scope_criticism :: native_development_condition
  development_selected_facets :: "nat list"

definition development_condition_input :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option definition_site admission_goal list \<Rightarrow>
    native_development_condition" where
  "development_condition_input E u r gs=\<lparr>condition_source=E,condition_source_use=u,
    condition_source_root=r,condition_goals=gs\<rparr>"

definition native_development_question_input :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option definition_site \<Rightarrow>
    finite_factor_term \<Rightarrow> native_development_condition list \<Rightarrow> native_development_condition \<Rightarrow>
    nat list \<Rightarrow> native_development_question" where
  "native_development_question_input E u r d x cs critic selected=\<lparr>development_source=E,
    development_source_use=u,development_source_root=r,development_generator_entry=d,development_problem=x,
    development_conditions=cs,development_scope_criticism=critic,development_selected_facets=selected\<rparr>"

record native_development_report =
  development_generation :: "native_development_generation option"
  development_compiled_conditions :: "native_workflow_stage option list option"
  development_observed_conditions :: "native_condition_execution option list option"
  development_scope_review :: "native_condition_execution option"
  development_comparison :: "native_development_comparison option"
  development_revision :: "native_development_cycle option"

fun development_optional_outputs where
  "development_optional_outputs None=[]"
| "development_optional_outputs (Some execution)=development_condition_outputs execution"

definition development_generated_values ::
    "native_development_question \<Rightarrow> native_development_generation \<Rightarrow> finite_factor_term list" where
  "development_generated_values Q generation=(case generation of (P,D,A,rows) \<Rightarrow>
    finite_generated_outputs (development_generator_entry Q) (development_problem Q) rows)"

definition development_question_value ::
    "native_development_question \<Rightarrow> finite_factor_term" where
  "development_question_value Q=finite_data_sequence [finite_environment_value (development_source Q),
    development_site_value (development_source_use Q,development_source_root Q),
    development_site_value (development_generator_entry Q),development_problem Q,
    finite_data_sequence (map development_condition_value (development_conditions Q)),
    development_condition_value (development_scope_criticism Q),
    finite_data_sequence (map (\<lambda>n. the (finite_self_contained_term (natural_data_term n)))
      (development_selected_facets Q))]"

definition development_review_values ::
    "native_development_question \<Rightarrow> finite_factor_term list \<Rightarrow> finite_factor_term list option list \<Rightarrow> finite_factor_term" where
  "development_review_values Q ys observations=finite_data_sequence [development_question_value Q,
    finite_data_sequence ys,finite_data_sequence (map (\<lambda>result. case result of None \<Rightarrow> Finite_Payload []
      | Some values \<Rightarrow> Finite_Pair (Finite_Payload []) (finite_data_sequence values)) observations)]"

definition development_review_input ::
    "native_development_question \<Rightarrow> finite_factor_term list \<Rightarrow> native_condition_execution option list \<Rightarrow> finite_factor_term" where
  "development_review_input Q ys observations=development_review_values Q ys
    (map (map_option development_condition_outputs) observations)"

definition development_candidate_observation :: "finite_factor_term list \<Rightarrow>
    native_condition_execution option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "development_candidate_observation ys observations m w f=(m<length ys \<and> f<length observations \<and>
    (case observations!f of None \<Rightarrow> False | Some execution \<Rightarrow>
      ys!m\<in>set (development_condition_outputs execution)))"

definition development_compare :: "finite_factor_term list \<Rightarrow> native_condition_execution option list \<Rightarrow>
    native_development_comparison" where
  "development_compare ys observations=assessed_subject_investigation [0..<length ys] [0..<length observations] [0]
    (\<lambda>m w. m) (\<lambda>m. development_candidate_observation ys observations m 0)"

definition development_revise :: "finite_factor_term list \<Rightarrow> native_condition_execution option list \<Rightarrow>
    nat list \<Rightarrow> native_development_cycle" where
  "development_revise ys observations selected=(case development_compare ys observations of
    (rows,relation,chosen,adequate) \<Rightarrow> investigation_cycle_report
      [0..<length ys] [0..<length observations] rows relation selected)"

definition construct_native_development ::
    "native_development_question \<Rightarrow> native_development_report" where
  "construct_native_development Q=(let generation=finite_native_generation (development_source Q)
      (development_source_use Q) (development_source_root Q) (development_problem Q) in
    case generation of None \<Rightarrow> \<lparr>development_generation=None,development_compiled_conditions=None,
      development_observed_conditions=None,development_scope_review=None,development_comparison=None,development_revision=None\<rparr>
    | Some G \<Rightarrow> (let ys=development_generated_values Q G;
      compiled=map (\<lambda>C. compile_workflow_requirement (development_condition_requirement C ys)) (development_conditions Q);
      observations=map (\<lambda>C. execute_development_condition C (development_problem Q) ys) (development_conditions Q);
      input=development_review_input Q ys observations;
      review=execute_development_condition (development_scope_criticism Q) input [input];
      comparison=development_compare ys observations in
      \<lparr>development_generation=Some G,development_compiled_conditions=Some compiled,
        development_observed_conditions=Some observations,development_scope_review=review,
        development_comparison=Some comparison,
        development_revision=Some (development_revise ys observations (development_selected_facets Q))\<rparr>))"

definition development_condition_family_evidence ::
    "native_development_question \<Rightarrow> finite_factor_term list \<Rightarrow> native_condition_execution option list \<Rightarrow> bool" where
  "development_condition_family_evidence Q ys observations=(length observations=length (development_conditions Q) \<and>
    (\<forall>i<length observations. case observations!i of None \<Rightarrow> False
      | Some execution \<Rightarrow> development_condition_evidence (development_conditions Q!i) (development_problem Q) ys execution))"

definition native_development_admission ::
    "native_development_question \<Rightarrow> native_development_report \<Rightarrow> finite_factor_term list option" where
  "native_development_admission Q report=(case development_generation report of None \<Rightarrow> None
    | Some G \<Rightarrow> (case development_observed_conditions report of None \<Rightarrow> None
    | Some observations \<Rightarrow> (case development_scope_review report of None \<Rightarrow> None
    | Some review \<Rightarrow> (let ys=development_generated_values Q G; input=development_review_input Q ys observations in
      if development_generation report=finite_native_generation (development_source Q) (development_source_use Q)
          (development_source_root Q) (development_problem Q) \<and>
        development_conditions Q\<noteq>[] \<and> condition_goals (development_scope_criticism Q)\<noteq>[] \<and>
        development_compiled_conditions report=Some (map (\<lambda>C.
          compile_workflow_requirement (development_condition_requirement C ys)) (development_conditions Q)) \<and>
        development_condition_family_evidence Q ys observations \<and>
        development_condition_evidence (development_scope_criticism Q) input [input] review \<and>
        development_condition_outputs review=[input] \<and>
        development_comparison report=Some (development_compare ys observations) \<and>
        development_revision report=Some (development_revise ys observations (development_selected_facets Q)) \<and>
        fst (fst (snd (development_revise ys observations (development_selected_facets Q))))
      then Some (map (nth ys) (snd (snd (snd (development_compare ys observations))))) else None))))"

definition native_development_packet where
  "native_development_packet Q=(let report=construct_native_development Q in
    (Q,report,native_development_admission Q report))"

definition native_development_boundary where
  "native_development_boundary Q=Q"

definition reconstruct_native_development where
  "reconstruct_native_development boundary=native_development_packet boundary"

lemma native_development_reconstructs:
  "reconstruct_native_development (native_development_boundary Q)=native_development_packet Q"
  by (simp only: reconstruct_native_development_def native_development_boundary_def)

text \<open>
  This closed composition performs the actual operations: reading the reusable
  native source, constructing guards for the original conditions, generating
  every candidate occurrence from actual premise answers, observing all
  candidates with native certificates, independently checking complete evidence
  and a native criticism of the original question and whole candidate family,
  then deriving comparison, revision and admission. A partial observation scope
  can guide revision but cannot weaken the full original condition family used
  for admission. The complete typed evidence is inspected independently; the
  additional native scope critic receives the original complete source-and-goal
  question, ordered candidates, and every optional observation output.

  The retained local question reconstructs all operations; no accumulated
  development history enters this function. The declared finite one-step
  generation boundary remains explicit. Its adequacy for any broader problem
  is not implied by successful execution of these operations.
\<close>

end
