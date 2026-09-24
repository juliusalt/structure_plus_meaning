theory Development_Seed_Verification
  imports Development_Seed_Loop Development_Refinement_Verification Development_Successor
    Development_Native_Answers Development_Loop_Presentations
begin

section \<open>The verdict is exercised on answer states derived from each request\<close>

text \<open>
  No answer to a seeded request has been verified yet, so the verdict is exercised on answer
  states computed from the seeded state and the request itself, each standing for one kind of
  answer. The unchanged state and its reversed table are answers that keep the demanded
  statement; the verdict must accept both, and the second shows that it reads no position.
  Every other control changes what a refinement may not change, or changes the subject's
  equation outside the support: stating the subject's equations as axioms, dropping the
  subject's equations, stating the equation through a constant the state does not know,
  changing the equations of the other seeded subjects, and removing the subject's kernel
  definition. The controls are native answers derived from the request and the state under the
  code-equation reading (`development_control_answers`), applied to the seeded state as an
  executor's answer is (`development_answer_controls`): each names no position of either list and
  selects no subject.
\<close>

definition development_seed_controls :: "development_request \<Rightarrow> isabelle_rooted_context list" where
  "development_seed_controls=development_answer_controls isabelle_code_equation_proposition Isabelle_Code_Equation
    development_seed_state development_seed_renamed (fset_of_list development_seed_root_constants)"

type_synonym development_seed_verification = "(development_constant_verdict\<times>bool) list list"

definition development_seed_verification :: "development_problem fset \<Rightarrow> development_seed_verification" where
  "development_seed_verification answered=Parallel.map (\<lambda>r. map (\<lambda>S'.
     let v=development_refinement_verdict development_seed_state r S' in (v,development_verdict_accepted v))
     (development_seed_controls r)) (development_seed_requests answered)"

definition development_seed_verification_data :: "development_seed_verification \<Rightarrow> finite_factor_term" where
  "development_seed_verification_data=finite_sequence_presentation (finite_sequence_presentation
    (finite_pair_presentation development_verdict_data finite_boolean_data))"

lemma development_seed_verification_data_injective [intro]: "inj development_seed_verification_data"
  unfolding development_seed_verification_data_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
    development_verdict_data_injective finite_boolean_data_injective)

definition development_seed_verification_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_verification_value answered=
    development_seed_verification_data (development_seed_verification answered)"

text \<open>
  The expected verdicts are fixed by the kinds of answer, not by the seeded values: both
  unchanged answers are accepted; the axiom is an added entity that is no equation of the
  subject; the dropped equations leave the subject without an equation; the unknown constant
  is an added declaration and the one constant outside the support; the other subjects'
  equations and the subject's definition are removed entities a refinement may not remove.
  These controls exercise the verdict's refusals; an actual answer is judged by the same
  verdict on the state its checked context defines.
\<close>


section \<open>The issued requests are answered natively\<close>

text \<open>
  An executor answers a request natively: its answer is the edit it makes to the request state,
  presented with the names it uses, and it arrives as the padded word of that presentation. For every
  issued request the restating answer is transported as its word, read back by the answer's exact
  reader and judged by the refinement verdict on the answer state; the same word without its
  terminating bit presents no answer and is refused. An executor's answer is judged in the same way
  against the request named by its subject, and that request is presented to the executor natively
  as its packet. These judgments establish that an answer is admissible for installation; whether
  its equation holds is Isabelle's acceptance when it is installed, a request of its own.
\<close>

definition development_seed_native_answers ::
    "development_problem fset \<Rightarrow> (development_native_judgment\<times>bool) list" where
  "development_seed_native_answers answered=development_native_answers development_refinement_verdict
    isabelle_code_equation_proposition development_seed_state (development_seed_requests answered)"

definition development_seed_native_answers_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_native_answers_value answered=
    development_native_answers_data (development_seed_native_answers answered)"

definition development_seed_native_judgment_value :: "String.literal \<Rightarrow> bool list \<Rightarrow> finite_factor_term" where
  "development_seed_native_judgment_value n bits=finite_store_option id
    (development_named_native_judgment_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None)
      (development_named_native_judgment development_refinement_verdict development_seed_state
        (development_seed_requests development_seed_unanswered) n bits))"

definition development_seed_native_summary ::
    "String.literal \<Rightarrow> bool list \<Rightarrow> (bool\<times>bool\<times>nat list\<times>String.literal list\<times>nat list) option" where
  "development_seed_native_summary n bits=development_native_summary development_refinement_verdict
    development_seed_state (development_seed_requests development_seed_unanswered) n bits"

definition development_seed_native_packet_value :: "String.literal \<Rightarrow> finite_factor_term" where
  "development_seed_native_packet_value n=development_named_native_packet_data isabelle_code_equation_proposition
    development_seed_state (development_seed_requests development_seed_unanswered) n"

section \<open>An admitted answer moves the seeded development to its successor\<close>

text \<open>
  The seeded development starts from the seeded state, its problems and dependencies, nothing
  answered and no history. For every request, the unchanged answer and the answer with the
  reversed table are admitted, and the successor carries the answered problem, the generation
  and every other problem; the readiness of the successor and the currency of the other
  requests are computed on it. Both answers change nothing a request reads, so every other
  request stays current and every other problem stays ready.
\<close>

definition development_seed_loop_state :: "development_problem fset \<Rightarrow> development_loop" where
  "development_seed_loop_state answered=(development_seed_state,development_seed_problems,
    development_seed_dependencies,answered,[])"

text \<open>
  The seeded development library holds no decomposition rule, so every selected problem is a
  leaf and is issued with the reading of that absence. A control library that decomposes every
  problem into itself issues nothing: each problem is refused as a broad request, and the
  unsupported cycle settles nothing. The request of a problem is the refinement request of its one
  subject constant, read from the problem itself.
\<close>

definition development_seed_library :: development_dependencies where
  "development_seed_library={||}"

definition development_seed_cyclic_library :: development_dependencies where
  "development_seed_cyclic_library=fset_of_list (map (\<lambda>p. (p,{|(0,p)|})) development_seed_problems)"

definition development_seed_request_of :: "development_problem \<Rightarrow> development_request option" where
  "development_seed_request_of p=(case sorted_list_of_fset (problem_subject p) of
     [c] \<Rightarrow> development_refinement_request development_seed_context Development_Residual Development_Generated c
   | _ \<Rightarrow> None)"

type_synonym development_seed_succession =
  "bool\<times>(development_problem list\<times>development_request list\<times>development_problem list\<times>development_problem list\<times>
    development_request list\<times>development_request list\<times>
    (development_problem fset\<times>development_record list\<times>development_problem list\<times>bool list) option list list) option"

text \<open>
  The selection is made once, as the recorded native decision of the seeded development, and the
  admitted problems are issued once; every successor starts from the development that recorded
  both. The report presents the problems the selection admitted, whose executed packet the loop
  report already presents, the issued requests, the problems left unissued, the problems the
  cyclic control refuses, and for each successor only the records it adds. It also decides a
  condition sufficient for the premise under which the answers to the independent requests keep
  each other current: the seeded state's declared constants are distinct, from which
  @{thm [source] isabelle_declared_once_distinct} derives the exporter's obligation
  @{const isabelle_declared_once}. Finally it re-evaluates the issue records against the seeded
  library, where every reading still holds, and against the cyclic library, where every issued
  request relied on an absence that no longer holds.
\<close>

definition development_seed_succession :: "development_problem fset \<Rightarrow> development_seed_succession" where
  "development_seed_succession answered=(distinct (List.map_filter isabelle_declared_constant (snd development_seed_context)),
   case development_loop_selection (development_seed_loop_state answered) of
     None \<Rightarrow> None
   | Some (L,xs) \<Rightarrow> (case development_loop_issue development_seed_library development_seed_request_of L xs of
       (L2,issued,unissued) \<Rightarrow> (case development_loop_issue development_seed_cyclic_library development_seed_request_of L xs of
         (L3,control,refused) \<Rightarrow> (case L2 of (S,ps,D,done0,recorded) \<Rightarrow>
           Some (xs,issued,unissued,refused,development_reevaluations development_seed_library recorded,
             development_reevaluations development_seed_cyclic_library recorded,Parallel.map (\<lambda>r. map (\<lambda>S'. map_option (\<lambda>(S2,ps,D,closed,history).
             (closed,drop (length recorded) history,development_ready_problems D closed ps,
              map (development_request_current (snd development_seed_state) (snd S')) issued))
             (development_successor L2 r S'))
             [development_seed_state,development_seed_renamed]) issued)))))"

text \<open>
  The succession is presented in the context of its loops. The seeded loops pose no demanded problem and
  record no repair, so every problem they hold is residual, and a context meeting the row premise cites
  nothing on a residual problem (@{text Development_Row_Data}): their context is the seed's residual record, with the seed's
  names, which every successor keeps. The answered problems of a successor are a table of their rows.
\<close>

definition development_seed_succession_data :: "development_seed_succession \<Rightarrow> finite_factor_term option" where
  "development_seed_succession_data=finite_partial_pair (Some \<circ> finite_boolean_data) (finite_partial_option (finite_partial_pair
    (development_problems_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
    (finite_partial_pair (development_requests_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
      (finite_partial_pair (development_problems_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
        (finite_partial_pair (development_problems_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
          (finite_partial_pair (development_requests_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
            (finite_partial_pair (development_requests_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
              (finite_partial_sequence (finite_partial_sequence (finite_partial_option (finite_partial_pair
                (development_problems_table state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
                (finite_partial_pair (finite_partial_sequence (development_record_data finite_development_context_value
                    state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None)))
                  (finite_partial_pair (development_problems_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None))
                    (Some \<circ> finite_sequence_presentation finite_boolean_data))))))))))))))"

lemma development_seed_succession_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
    and requests: "development_request_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) R"
    and repairs: "\<And>r. r\<in>R \<Longrightarrow> finite_presented_on
      (development_refinement_repair_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None) r) (RR r)"
  shows "finite_presented_on development_seed_succession_data (UNIV\<times>{x. set_option x\<subseteq>
    lists P\<times>lists R\<times>lists P\<times>lists P\<times>lists R\<times>lists R\<times>
    lists (lists {y. set_option y\<subseteq>{A. fset A\<subseteq>P}\<times>lists (development_record_domain P R RR)\<times>lists P\<times>UNIV})})"
  unfolding development_seed_succession_data_def
  by (intro finite_partial_pair_presented finite_partial_option_presented finite_partial_sequence_presented
    finite_presented_total finite_boolean_data_injective development_problems_data_presented
    development_requests_data_presented development_problems_table_presented development_record_data_presented
    finite_development_values_injective(3) finite_sequence_presentation_injective domain requests repairs)

definition development_seed_succession_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_succession_value answered=finite_store_option id
    (development_seed_succession_data (development_seed_succession answered))"

text \<open>
  Wherever the answered problems are the seed's, the succession lies in its presentation's domain: its loops
  hold the seed's problems, issue and record the seed's requests, and record answers to them, no repair
  among them. So its value is the presentation itself, never the store's absence.
\<close>

theorem development_seed_succession_domain:
  assumes answered: "fset answered\<subseteq>set development_seed_problems"
  defines P_def: "P\<equiv>set development_seed_problems"
    and R_def: "R\<equiv>{q. \<exists>c. development_constant_request isabelle_code_equation_proposition Development_Refinement
      development_seed_context Development_Residual Development_Generated c=Some q}"
  shows "development_seed_succession answered\<in>UNIV\<times>{x. set_option x\<subseteq>
    lists P\<times>lists R\<times>lists P\<times>lists P\<times>lists R\<times>lists R\<times>
    lists (lists {y. set_option y\<subseteq>{A. fset A\<subseteq>P}\<times>lists (development_record_domain P R (\<lambda>_. {}))\<times>lists P\<times>UNIV})}"
proof (cases "development_loop_selection (development_seed_loop_state answered)")
  case None
  then show ?thesis by (simp add: development_seed_succession_def)
next
  case (Some Lx)
  obtain L xs where Lx: "Lx=(L,xs)" by (cases Lx) auto
  have selection: "development_loop_selection (development_seed_state,development_seed_problems,
      development_seed_dependencies,answered,[])=Some (L,xs)"
    using Some by (simp add: Lx development_seed_loop_state_def)
  obtain Q where L: "L=(development_seed_state,development_seed_problems,development_seed_dependencies,answered,
      [Development_Selection_Record (native_development_packet Q) xs])"
    using selection by (auto simp: development_loop_selection_def Let_def split: option.splits)
  have xs: "set xs\<subseteq>P" using development_loop_selection_ready(1)[OF selection] by (auto simp: P_def)
  obtain L2 issued unissued where issue: "development_loop_issue development_seed_library development_seed_request_of
      L xs=(L2,issued,unissued)"
    by (cases "development_loop_issue development_seed_library development_seed_request_of L xs") auto
  obtain L3 control refused where control: "development_loop_issue development_seed_cyclic_library
      development_seed_request_of L xs=(L3,control,refused)"
    by (cases "development_loop_issue development_seed_cyclic_library development_seed_request_of L xs") auto
  define recorded where "recorded=[Development_Selection_Record (native_development_packet Q) xs]@map (\<lambda>r. Development_Issue_Record r
      (development_library_reading development_seed_library (fst r))) issued"
  have L2: "L2=(development_seed_state,development_seed_problems,development_seed_dependencies,answered,recorded)"
    and unissued: "set unissued\<subseteq>set xs"
    using issue by (auto simp: L recorded_def development_loop_issue_def Let_def)
  have refused: "set refused\<subseteq>set xs" using control by (auto simp: L development_loop_issue_def Let_def)
  have issued: "set issued\<subseteq>R"
  proof
    fix r assume r: "r\<in>set issued"
    have "development_seed_request_of (fst r)=Some r" by (rule development_loop_issue_leaf(4)[OF issue[unfolded L] r])
    then show "r\<in>R"
      by (auto simp: R_def development_seed_request_of_def development_refinement_request_def split: list.splits)
  qed
  have problem: "fst r\<in>P" if r: "r\<in>set issued" for r
    using development_loop_issue_leaf(1)[OF issue[unfolded L] r] xs by blast
  have reevaluated: "set (development_reevaluations Lib recorded)\<subseteq>R" for Lib
    using issued by (auto simp: development_reevaluations_exact recorded_def)
  let ?G="\<lambda>r S'. map_option (\<lambda>(S2,ps,D,closed,history). (closed,drop (length recorded) history,
      development_ready_problems D closed ps,map (development_request_current (snd development_seed_state) (snd S')) issued))
      (development_successor L2 r S')"
  let ?Y="{y. set_option y\<subseteq>{A. fset A\<subseteq>P}\<times>lists (development_record_domain P R (\<lambda>_. {}))\<times>lists P\<times>UNIV}"
  have successor: "?G r S'\<in>?Y" if r: "r\<in>set issued" for r S'
  proof (cases "development_successor L2 r S'")
    case None
    then show ?thesis by simp
  next
    case (Some L')
    obtain S2 ps' D' closed history' where L': "L'=(S2,ps',D',closed,history')" by (cases L') auto
    note fields=development_successor_answered[OF Some[unfolded L2 L']]
    obtain G where G: "development_answer_generation development_seed_state r
        (isabelle_rooted_read (fst (snd development_seed_state)) S')=Some G"
      and history': "history'=recorded@[Development_Answer_Record G]"
      using fields(3) by blast
    obtain p0 s0 su0 E0 where rr: "r=(p0,s0,su0,E0)" by (cases r) auto
    have "fst G=fst r" using G by (auto simp: rr development_answer_generation_def Let_def split: if_splits)
    then have answer_record: "Development_Answer_Record G\<in>development_record_domain P R (\<lambda>_. {})"
      using problem[OF r] by (simp add: development_record_domain_def development_record_parts_def
        development_record_parts_domain_def mem_Times_iff)
    have closed: "fset closed\<subseteq>P" using fields(6) answered problem[OF r] by (auto simp: P_def)
    show ?thesis using answer_record closed
      by (auto simp: Some L' history' fields(4) P_def development_ready_problems_def in_lists_conv_set)
  qed
  have nested: "map (\<lambda>r. map (?G r) [development_seed_state,development_seed_renamed]) issued\<in>lists (lists ?Y)"
  proof (rule in_listsI, rule ballI)
    fix x assume x: "x\<in>set (map (\<lambda>r. map (?G r) [development_seed_state,development_seed_renamed]) issued)"
    obtain r where r: "r\<in>set issued" and xr: "x=map (?G r) [development_seed_state,development_seed_renamed]"
      using x by auto
    show "x\<in>lists ?Y" using successor[OF r, of development_seed_state] successor[OF r, of development_seed_renamed]
      by (simp add: xr)
  qed
  have computed: "development_seed_succession answered=(distinct (List.map_filter isabelle_declared_constant
      (snd development_seed_context)),Some (xs,issued,unissued,refused,
      development_reevaluations development_seed_library recorded,development_reevaluations development_seed_cyclic_library recorded,
      map (\<lambda>r. map (?G r) [development_seed_state,development_seed_renamed]) issued))"
    by (simp add: development_seed_succession_def Some Lx issue control L2)
  have "set unissued\<subseteq>P" "set refused\<subseteq>P" using unissued refused xs by blast+
  then show ?thesis unfolding computed using xs issued reevaluated nested by (simp add: lists_eq_set)
qed

text \<open>
  The native judgment of a named answer carries its request, one of the seed's requests, so it too lies in
  its presentation's domain, at every answered set, for every name and answer.
\<close>

theorem development_seed_native_judgment_domain:
  "development_named_native_judgment development_refinement_verdict development_seed_state
    (development_seed_requests answered) n bits\<in>{x. set_option x\<subseteq>{q. \<exists>c. development_constant_request
      isabelle_code_equation_proposition Development_Refinement development_seed_context
        Development_Residual Development_Generated c=Some q}\<times>UNIV}"
proof (cases "development_named_request (snd development_seed_state) (development_seed_requests answered) n")
  case None
  then show ?thesis by (simp add: development_named_native_judgment_def)
next
  case (Some r)
  have "r\<in>set (development_seed_requests answered)" by (rule development_named_request_member[OF Some])
  then show ?thesis using development_seed_requests_family[of answered]
    by (auto simp: development_named_native_judgment_def Some)
qed

corollary development_seed_native_judgment_presentation:
  "development_named_native_judgment_data state_constant_key development_seed_inert (\<lambda>_. None) (\<lambda>_. None)
    (development_named_native_judgment development_refinement_verdict development_seed_state
      (development_seed_requests answered) n bits)\<noteq>None"
  by (rule finite_presented_on_some[OF development_named_native_judgment_data_presented[OF
    development_seed_request_family_domain, where inert=development_seed_inert]
    development_seed_native_judgment_domain[of answered n bits]]) simp

corollary development_seed_succession_presentation:
  assumes "fset answered\<subseteq>set development_seed_problems"
  shows "development_seed_succession_data (development_seed_succession answered)\<noteq>None"
proof -
  have repairs: "finite_presented_on (development_refinement_repair_data state_constant_key development_seed_inert
      (\<lambda>_. None) (\<lambda>_. None) r) {}" for r
    by (simp add: finite_presented_on_def)
  show ?thesis
    by (rule finite_presented_on_some[OF development_seed_succession_data_presented[OF development_seed_problems_domain
      development_seed_request_family_domain repairs] development_seed_succession_domain[OF assms]]) simp
qed

end
