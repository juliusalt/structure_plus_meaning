theory Development_Machinery
  imports Native_Control_Seed_Subject Development_Admitted_Publication Development_Presentation
    Development_Definition_Verification Development_Native_Answers
begin

section \<open>The loop's own notions and their constituents as a checked state\<close>

text \<open>
  The notions the first loop's judgments consult were defined outside the native process, like
  the seeded roots: which problem a constant poses and what it depends on, when a problem is
  ready, how the next problems are selected and issued, what a request carries, how an answer is
  judged and a refused one repaired, what a definition request carries and how a definition answer
  is judged, which policy admits a payload, how a certified generation is
  recorded, where a problem stands, how the loop's decisions are recorded, how an admitted answer
  is published and how the development moves to its successor. So were the development constants
  their definitions are made of. The checked context presents these notions and their
  constituents as a state in the same way as the seed: the notions and every development constant
  their items mention are the roots and are expanded, and every development constant the
  constituents mention in turn stands on the frontier and is extended when work demands it.
  Which notions are roots, and how far the record reaches, are residual choices generated
  outside the process; they gain no authority from this definition.
\<close>

local_setup \<open>fn lthy =>
  let
    val thy = Proof_Context.theory_of lthy;
    val notions =
      [("_problem_roots", [\<^term>\<open>development_constant_problem\<close>, \<^term>\<open>development_constant_dependencies\<close>,
         \<^term>\<open>development_ready\<close>, \<^term>\<open>development_selection_question\<close>, \<^term>\<open>development_issuable\<close>]),
       ("_answer_roots", [\<^term>\<open>development_refinement_request\<close>, \<^term>\<open>development_refinement_verdict\<close>,
         \<^term>\<open>development_refinement_repair\<close>, \<^term>\<open>development_definition_request\<close>,
         \<^term>\<open>development_definition_verdict\<close>]),
       ("_admission_roots", [\<^term>\<open>development_policy_source_with\<close>, \<^term>\<open>development_payload_generation_with\<close>,
         \<^term>\<open>development_problem_locus\<close>, \<^term>\<open>development_loop_decisions\<close>,
         \<^term>\<open>development_answer_publication\<close>, \<^term>\<open>development_successor\<close>])];
    val names = distinct (op =) (maps (fn (_, ts) => maps (fn t => rev (Term.add_const_names t [])) ts) notions);
    (*The constituents are the development constants the notions' items mention: the frontier of the
      state the notions alone would define.*)
    val (reached, _) = Isabelle_Entity_Export.context_items thy (member (op =) names) names;
    val constituents = filter (fn c => not (Isabelle_Entity_Export.base_constant thy c)
      andalso not (member (op =) names c)) reached;
  in
    Isabelle_Entity_Export.define \<^binding>\<open>development_machinery\<close>
      (notions @ [("_constituent_roots", map (fn c => Const (c, Sign.the_const_type thy c)) constituents)]) lthy
  end\<close>

declare development_machinery_context_def [code] development_machinery_roots_def [code]
  development_machinery_problem_roots_def [code] development_machinery_answer_roots_def [code]
  development_machinery_admission_roots_def [code] development_machinery_constituent_roots_def [code]

definition development_machinery_state :: isabelle_rooted_context where
  "development_machinery_state=(development_machinery_roots,development_machinery_context)"

section \<open>Every root is a residual problem of its definition\<close>

text \<open>
  Each root is a choice made outside the process, and it is represented as the problem of
  its constant under the definition reading: its subject is the constant, its contract the
  constant as the checked context declares it, marked as a definition, its incumbent the kernel
  definitions the state states for it, its origin a residual and its authority generated. The
  residual record of these notions is therefore part of the native state: a residual is
  discharged or superseded only by an answer admitted at its problem's locus, and until then it
  justifies nothing. A residual depends on the residuals of the other roots its kernel definitions
  mention, because its definition means what it does only through theirs; that relation is read
  from the definitions, not supplied, and it orders the discharge of the residuals. With the
  constituents among the roots, a notion's residual depends on the residuals of what it is made of,
  so the loop takes constituents before the notions composed of them; a constituent's own
  constituents stand on the frontier, so its readiness is relative to how far the record reaches.
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
     Option.bind packet (development_packet_problems development_machinery_dependencies answered
       development_machinery_problems)))"

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

section \<open>The selected residuals are issued as definition requests\<close>

text \<open>
  A residual is a definition problem, so the loop issues its selected residuals as definition
  requests: the request of the problem's one subject constant under the definition reading, with the
  support and the least context of the constant's scope. The machinery's library holds no
  decomposition rule, so every selected residual is a leaf and is issued with the reading of that
  absence. No answer to a definition request exists yet, so the definition verdict is exercised on
  the answer states derived from each request under the definition reading
  (`development_answer_controls`): the unchanged state and its renaming must be accepted; the
  subject's definitions stated as axioms, dropped, or stated through a constant the state does not
  know must be refused, as must dropping the other residuals' definitions; and dropping the
  subject's code equations must be accepted, since they are derived from its definition and a
  definition answer replaces them.
\<close>

definition development_machinery_renamed :: isabelle_rooted_context where
  "development_machinery_renamed=isabelle_rooted_rename
    (isabelle_reversal (length (fst development_machinery_context)))
    (rev (fst development_machinery_context)) development_machinery_state"

definition development_machinery_request_of :: "development_problem \<Rightarrow> development_request option" where
  "development_machinery_request_of p=(case sorted_list_of_fset (problem_subject p) of
     [c] \<Rightarrow> development_definition_request development_machinery_context Development_Residual Development_Generated c
   | _ \<Rightarrow> None)"

theorem development_machinery_issued:
  assumes selection: "development_loop_selection (development_machinery_state,development_machinery_problems,
      development_machinery_dependencies,answered,[])=Some (L,xs)"
    and issue: "development_loop_issue {||} development_machinery_request_of L xs=(L',issued,unissued)"
    and member: "r\<in>set issued"
  shows "fst r\<in>set development_machinery_problems \<and> development_ready development_machinery_dependencies answered (fst r)"
    "\<exists>c. problem_subject (fst r)={|c|} \<and>
      development_definition_request development_machinery_context Development_Residual Development_Generated c=Some r"
proof -
  obtain Q where state: "L=(development_machinery_state,development_machinery_problems,
      development_machinery_dependencies,answered,[Development_Selection_Record (native_development_packet Q) xs])"
    using selection by (auto simp: development_loop_selection_def Let_def split: option.splits)
  note leaf=development_loop_issue_leaf[OF issue[unfolded state] member]
  show "fst r\<in>set development_machinery_problems \<and> development_ready development_machinery_dependencies answered (fst r)"
    by (rule development_loop_selection_ready(1)[OF selection leaf(1)])
  obtain c where requested: "development_definition_request development_machinery_context
      Development_Residual Development_Generated c=Some r"
    using leaf(4) by (auto simp: development_machinery_request_of_def split: list.splits)
  obtain p s S E where parts: "r=(p,s,S,E)" by (cases r) auto
  have "problem_subject p={|c|}"
    by (rule development_definition_request_fields(3)[OF requested[unfolded parts]])
  then show "\<exists>c. problem_subject (fst r)={|c|} \<and>
      development_definition_request development_machinery_context Development_Residual Development_Generated c=Some r"
    using requested parts by auto
qed

text \<open>
  The loop selects the ready residuals and issues the selected leaves once; the verification and the
  native answers below both read the requests that one issue made.
\<close>

definition development_machinery_issue ::
    "development_problem fset \<Rightarrow> (development_loop\<times>development_request list\<times>development_problem list) option" where
  "development_machinery_issue answered=map_option (\<lambda>(L,xs). development_loop_issue {||} development_machinery_request_of L xs)
     (development_loop_selection (development_machinery_state,development_machinery_problems,
       development_machinery_dependencies,answered,[]))"

definition development_machinery_requests :: "development_problem fset \<Rightarrow> development_request list" where
  "development_machinery_requests answered=(case development_machinery_issue answered of None \<Rightarrow> []
     | Some (L,issued,unissued) \<Rightarrow> issued)"

type_synonym development_machinery_verification =
  "(development_request list\<times>development_problem list\<times>(development_constant_verdict\<times>bool) list list) option"

definition development_machinery_verification ::
    "development_problem fset \<Rightarrow> development_machinery_verification" where
  "development_machinery_verification answered=map_option (\<lambda>(L',issued,unissued).
       (issued,unissued,Parallel.map (\<lambda>r. map (\<lambda>S'.
          let v=development_definition_verdict development_machinery_state r S' in (v,development_verdict_accepted v))
         (development_answer_controls isabelle_definition_proposition Isabelle_Definition development_machinery_state
           development_machinery_renamed (fset_of_list development_machinery_root_constants) r)) issued))
     (development_machinery_issue answered)"

definition development_machinery_verification_data ::
    "development_machinery_verification \<Rightarrow> finite_factor_term" where
  "development_machinery_verification_data=finite_option_presentation
    (finite_pair_presentation development_requests_data (finite_pair_presentation development_problems_data
      (finite_sequence_presentation (finite_sequence_presentation
        (finite_pair_presentation development_verdict_data finite_boolean_data)))))"

lemma development_machinery_verification_data_injective [intro]: "inj development_machinery_verification_data"
  unfolding development_machinery_verification_data_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective development_requests_data_injective
    development_problems_data_injective finite_sequence_presentation_injective development_verdict_data_injective
    finite_boolean_data_injective)

definition development_machinery_verification_value ::
    "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_verification_value answered=
    development_machinery_verification_data (development_machinery_verification answered)"

text \<open>
  The expected verdicts are fixed by the kinds of answer, not by the residuals: both unchanged
  answers are accepted; the axiom is an added entity that is no definition or code equation of the
  subject; the dropped definitions leave the subject without a definition; the unknown constant is
  an added declaration and the one constant outside the support; the other residuals' definitions
  are removed entities a definition answer may not remove; the dropped code equations are
  replaceable statements of the subject. An actual definition answer is judged by the same verdict
  on the state its checked context defines.
\<close>

section \<open>The issued definition requests are answered natively\<close>

text \<open>
  Every issued definition request is answered natively, as a seeded request is: the restating answer
  removes the subject's kernel definitions its context holds and adds them again, is transported as
  its word, read back by its exact reader and judged by the definition verdict; the word without its
  terminating bit is refused. An executor's answer to a residual named by its subject is judged in
  the same way, and the request is presented to the executor natively as its packet.
\<close>

definition development_machinery_native_answers ::
    "development_problem fset \<Rightarrow> (development_native_judgment\<times>bool) list" where
  "development_machinery_native_answers answered=development_native_answers development_definition_verdict
    isabelle_definition_proposition development_machinery_state (development_machinery_requests answered)"

definition development_machinery_native_answers_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_native_answers_value answered=
    development_native_answers_data (development_machinery_native_answers answered)"

definition development_machinery_native_judgment_value :: "String.literal \<Rightarrow> bool list \<Rightarrow> finite_factor_term" where
  "development_machinery_native_judgment_value n bits=development_named_native_judgment_data
    (development_named_native_judgment development_definition_verdict development_machinery_state
      (development_machinery_requests development_machinery_unanswered) n bits)"

definition development_machinery_native_summary ::
    "String.literal \<Rightarrow> bool list \<Rightarrow> (bool\<times>bool\<times>nat list\<times>String.literal list\<times>nat list) option" where
  "development_machinery_native_summary n bits=development_native_summary development_definition_verdict
    development_machinery_state (development_machinery_requests development_machinery_unanswered) n bits"

definition development_machinery_native_packet_value :: "String.literal \<Rightarrow> finite_factor_term" where
  "development_machinery_native_packet_value n=development_named_native_packet_data isabelle_definition_proposition
    development_machinery_state (development_machinery_requests development_machinery_unanswered) n"

end
