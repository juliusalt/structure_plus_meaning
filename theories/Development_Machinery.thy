theory Development_Machinery
  imports Native_Control_Seed_Subject Development_Admitted_Publication Development_Presentation
begin

section \<open>The loop's own notions as a checked state\<close>

text \<open>
  The notions the first loop's judgments consult were defined outside the native process, like
  the seeded roots: which problem a constant poses and what it depends on, when a problem is
  ready, how the next problems are selected and issued, what a request carries, how an answer is
  judged and a refused one repaired, which policy admits a payload, how a certified generation is
  recorded, where a problem stands, how the loop's decisions are recorded, how an admitted answer
  is published and how the development moves to its successor. The checked context presents these
  notions as a state in the same way as the seed: the roots are expanded, and every development
  constant they mention stands on the frontier and is extended when work demands it. Which
  notions are roots is a residual choice generated outside the process; it gains no authority
  from this definition.
\<close>

local_setup \<open>Isabelle_Entity_Export.define \<^binding>\<open>development_machinery\<close>
  [("_problem_roots", [\<^term>\<open>development_constant_problem\<close>, \<^term>\<open>development_constant_dependencies\<close>,
     \<^term>\<open>development_ready\<close>, \<^term>\<open>development_selection_question\<close>, \<^term>\<open>development_issuable\<close>]),
   ("_answer_roots", [\<^term>\<open>development_refinement_request\<close>, \<^term>\<open>development_refinement_verdict\<close>,
     \<^term>\<open>development_refinement_repair\<close>]),
   ("_admission_roots", [\<^term>\<open>development_policy_source_with\<close>, \<^term>\<open>development_payload_generation_with\<close>,
     \<^term>\<open>development_problem_locus\<close>, \<^term>\<open>development_loop_decisions\<close>,
     \<^term>\<open>development_answer_publication\<close>, \<^term>\<open>development_successor\<close>])]\<close>

declare development_machinery_context_def [code] development_machinery_roots_def [code]
  development_machinery_problem_roots_def [code] development_machinery_answer_roots_def [code]
  development_machinery_admission_roots_def [code]

definition development_machinery_state :: isabelle_rooted_context where
  "development_machinery_state=(development_machinery_roots,development_machinery_context)"

section \<open>Every root notion is a residual problem of its definition\<close>

text \<open>
  Each root notion is a choice made outside the process, and it is represented as the problem of
  its constant under the definition reading: its subject is the constant, its contract the
  constant as the checked context declares it, marked as a definition, its incumbent the kernel
  definitions the state states for it, its origin a residual and its authority generated. The
  residual record of these notions is therefore part of the native state: a residual is
  discharged or superseded only by an answer admitted at its problem's locus, and until then it
  justifies nothing. A residual depends on the residuals of the other roots its kernel definitions
  mention, because its definition means what it does only through theirs; that relation is read
  from the definitions, not supplied, and it orders the discharge of the residuals.
\<close>

definition development_machinery_root_constants :: "nat list" where
  "development_machinery_root_constants=
    remdups (List.map_filter isabelle_head_constant development_machinery_roots)"

definition development_machinery_problems :: "development_problem list" where
  "development_machinery_problems=development_constant_problems isabelle_definition_proposition
    Development_Definition development_machinery_context Development_Residual Development_Generated
    development_machinery_root_constants"

definition development_machinery_unstated :: "nat fset" where
  "development_machinery_unstated=development_constant_unstated isabelle_definition_proposition
    development_machinery_context development_machinery_root_constants"

definition development_machinery_dependencies :: development_dependencies where
  "development_machinery_dependencies=development_constant_dependencies isabelle_definition_proposition
    Development_Definition development_machinery_context Development_Residual Development_Generated
    development_machinery_root_constants"

theorem development_machinery_problems_residual:
  assumes member: "p\<in>set development_machinery_problems"
  shows "problem_origin p=Development_Residual \<and> problem_authority p=Development_Generated \<and>
    (\<exists>t. problem_contract p=Development_Definition t)"
proof -
  obtain c where "development_constant_problem isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some p"
    using member by (auto simp: development_machinery_problems_def development_constant_problems_exact)
  then show ?thesis
    by (auto simp: development_constant_problem_def development_constant_contract_def map_option_eq_Some)
qed

definition development_machinery_unanswered :: "development_problem fset" where
  "development_machinery_unanswered={||}"

section \<open>The loop decides on its own residuals natively\<close>

text \<open>
  The incumbent of every residual is the admitted answer of the definition question over its
  constant's scope, and which residuals are taken next is the admitted answer of the selection
  question over the residual problems: the questions the loop asks of the seeded refinement
  problems, asked of the loop's own notions, with the contracts of those questions
  (`development_constant_admitted_statement`, `development_packet_selected_ready`) and nothing
  stated again. Every selected residual is ready, so no selected residual waits for another.
\<close>

definition development_machinery_contract_packets where
  "development_machinery_contract_packets=development_contract_packets isabelle_definition_proposition
    development_machinery_context development_machinery_root_constants"

section \<open>The report presents the residual record and the loop's decisions on it\<close>

type_synonym development_machinery_problem_report =
  "development_problem list\<times>nat fset\<times>development_dependencies\<times>development_problem_assessment"

definition development_machinery_problem_report ::
    "development_problem fset \<Rightarrow> development_machinery_problem_report" where
  "development_machinery_problem_report answered=(development_machinery_problems,
    development_machinery_unstated,development_machinery_dependencies,
    development_problem_assessment development_machinery_context development_machinery_dependencies
      answered development_machinery_problems)"

definition development_machinery_problem_data ::
    "development_machinery_problem_report \<Rightarrow> finite_factor_term" where
  "development_machinery_problem_data=finite_pair_presentation development_problems_data
    (finite_pair_presentation isabelle_positions_data
      (finite_pair_presentation development_dependencies_data development_problem_assessment_data))"

lemma development_machinery_problem_data_injective [intro]: "inj development_machinery_problem_data"
  unfolding development_machinery_problem_data_def
  by (intro finite_pair_presentation_injective development_problems_data_injective
    isabelle_collections_injective development_dependencies_data_injective
    development_problem_assessment_data_injective)

definition development_machinery_problem_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_problem_value answered=
    development_machinery_problem_data (development_machinery_problem_report answered)"

type_synonym development_machinery_packet =
  "native_development_question\<times>native_development_report\<times>finite_factor_term list option"

type_synonym development_machinery_loop_report = "development_machinery_packet option list\<times>
  development_machinery_packet option\<times>development_problem list option"

text \<open>
  The selection is executed once: the report presents its packet and reads the selected
  residuals from that packet's admission, which is `development_packet_selected` with the packet
  shared.
\<close>

definition development_machinery_loop_report ::
    "development_problem fset \<Rightarrow> development_machinery_loop_report" where
  "development_machinery_loop_report answered=(let packet=development_selection_packet
      development_machinery_dependencies answered development_machinery_problems in
    (development_machinery_contract_packets,packet,
     Option.bind packet (native_packet_subjects development_machinery_problems)))"

lemma development_machinery_loop_report_selected:
  "snd (snd (development_machinery_loop_report answered))=development_packet_selected
    development_machinery_dependencies answered development_machinery_problems"
  by (simp add: development_machinery_loop_report_def development_packet_selected_def Let_def)

definition development_machinery_loop_data :: "development_machinery_loop_report \<Rightarrow> finite_factor_term" where
  "development_machinery_loop_data=finite_pair_presentation
    (finite_sequence_presentation (finite_option_presentation finite_development_context_value))
    (finite_pair_presentation (finite_option_presentation finite_development_context_value)
      (finite_option_presentation development_problems_data))"

lemma development_machinery_loop_data_injective [intro]: "inj development_machinery_loop_data"
  unfolding development_machinery_loop_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    finite_option_presentation_injective finite_development_values_injective
    development_problems_data_injective)

definition development_machinery_loop_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_loop_value answered=
    development_machinery_loop_data (development_machinery_loop_report answered)"

text \<open>
  The state report is the seed's assessment and acceptance of a rooted state, applied to this
  state. The problem report presents the residuals, the roots the definition reading states no
  problem for, the dependencies read from the definitions and the assessment of the problems;
  the loop report presents the contract decision of every root, the selection and the selected
  residuals. Whether these roots are adequate to the loop, the requirements an answer to a
  residual must meet, and the verifier of a definition answer are not established here.
\<close>

end
