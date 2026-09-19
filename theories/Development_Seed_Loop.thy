theory Development_Seed_Loop
  imports Development_Seed Development_Requests Development_Presentation
begin

section \<open>The seeded state's decisions are executed native questions\<close>

text \<open>
  Two kinds of decision of the first loop are native questions on the seeded state. The
  contract of each root constant is the admitted answer of its refinement question over the
  constant's own scope; which problems are taken next is the admitted answer of the
  selection question over the state's problems. Each question is executed by its native
  producer and checked by its admission, and the executed packet (question, report and
  admission) is what the report presents, so the evidence of these decisions is
  reconstructed with the state rather than recorded beside it.
\<close>

definition development_seed_contract_packets where
  "development_seed_contract_packets=development_contract_packets isabelle_code_equation_proposition
    development_seed_context development_seed_root_constants"

definition development_seed_selection_packet where
  "development_seed_selection_packet answered=development_selection_packet development_seed_dependencies
    answered development_seed_problems"

definition development_seed_selected :: "development_problem fset \<Rightarrow> development_problem list option" where
  "development_seed_selected answered=development_packet_selected development_seed_dependencies
    answered development_seed_problems"

theorem development_seed_selected_ready:
  assumes selected: "development_seed_selected answered=Some xs" and member: "p\<in>set xs"
  shows "p\<in>set development_seed_problems \<and>
    development_ready development_seed_dependencies answered p"
  by (rule development_packet_selected_ready[OF selected[unfolded development_seed_selected_def] member])

corollary development_seed_selected_independent:
  assumes selected: "development_seed_selected answered=Some xs" and first: "p\<in>set xs" and second: "q\<in>set xs"
  shows "q |\<notin>| development_premises development_seed_dependencies p"
proof -
  have "development_ready development_seed_dependencies answered p"
      "development_ready development_seed_dependencies answered q"
    using development_seed_selected_ready[OF selected first] development_seed_selected_ready[OF selected second]
    by simp_all
  then show ?thesis by (rule development_ready_independent)
qed

section \<open>Every admitted problem is requested with its support and least context\<close>

definition development_seed_requests :: "development_problem fset \<Rightarrow> development_request list" where
  "development_seed_requests answered=(case development_seed_selected answered of None \<Rightarrow> []
    | Some xs \<Rightarrow> List.map_filter (\<lambda>c. case development_seed_problem c of None \<Rightarrow> None
        | Some p \<Rightarrow> if p\<in>set xs then development_refinement_request development_seed_context
            Development_Residual Development_Generated c else None) development_seed_root_constants)"

theorem development_seed_request_selected:
  assumes request: "r\<in>set (development_seed_requests answered)"
  obtains xs c p s S E where "development_seed_selected answered=Some xs" "r=(p,s,S,E)" "p\<in>set xs"
    "development_refinement_request development_seed_context Development_Residual Development_Generated c=Some (p,s,S,E)"
proof -
  obtain xs where selected: "development_seed_selected answered=Some xs"
  proof (cases "development_seed_selected answered")
    case None
    then show ?thesis using request by (simp add: development_seed_requests_def)
  next
    case (Some xs)
    then show ?thesis by (rule that)
  qed
  have listed: "r\<in>set (List.map_filter (\<lambda>c. case development_seed_problem c of None \<Rightarrow> None
        | Some p \<Rightarrow> if p\<in>set xs then development_refinement_request development_seed_context
            Development_Residual Development_Generated c else None) development_seed_root_constants)"
    using request by (simp add: development_seed_requests_def selected)
  obtain c where built: "(case development_seed_problem c of None \<Rightarrow> None
        | Some p \<Rightarrow> if p\<in>set xs then development_refinement_request development_seed_context
            Development_Residual Development_Generated c else None)=Some r"
    using listed by (auto simp: map_filter_member)
  obtain p where problem: "development_seed_problem c=Some p" and chosen: "p\<in>set xs"
    and constructed: "development_refinement_request development_seed_context
      Development_Residual Development_Generated c=Some r"
    using built by (auto split: option.splits if_splits)
  obtain q s S E where shape: "r=(q,s,S,E)" by (metis prod.collapse)
  have same: "q=p"
    using development_refinement_request_fields(1)[OF constructed[unfolded shape]] problem
    by (simp add: development_seed_problem_def)
  show thesis by (rule that[OF selected shape chosen[folded same] constructed[unfolded shape]])
qed

section \<open>The report presents every decision, the admitted group and its requests\<close>

type_synonym development_seed_packet =
  "native_development_question\<times>native_development_report\<times>finite_factor_term list option"

type_synonym development_seed_loop_report = "development_seed_packet option list\<times>
  development_seed_packet option\<times>development_problem list option\<times>development_request list"

definition development_seed_loop_report :: "development_problem fset \<Rightarrow> development_seed_loop_report" where
  "development_seed_loop_report answered=(development_seed_contract_packets,
    development_seed_selection_packet answered,development_seed_selected answered,
    development_seed_requests answered)"

definition development_seed_loop_data :: "development_seed_loop_report \<Rightarrow> finite_factor_term" where
  "development_seed_loop_data=finite_pair_presentation
    (finite_sequence_presentation (finite_option_presentation finite_development_context_value))
    (finite_pair_presentation (finite_option_presentation finite_development_context_value)
      (finite_pair_presentation (finite_option_presentation development_problems_data)
        development_requests_data))"

lemma development_seed_loop_data_injective [intro]: "inj development_seed_loop_data"
  unfolding development_seed_loop_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    finite_option_presentation_injective finite_development_values_injective
    development_problems_data_injective development_requests_data_injective)

definition development_seed_loop_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_loop_value answered=development_seed_loop_data (development_seed_loop_report answered)"

text \<open>
  With nothing answered every seeded problem is ready, so the selection admits all ten, they
  form one independent group, and each is requested with its demanded code equation, the
  constants its definition and code equation mention, and the declarations of those constants.
  The requests are constructed, not issued: their leafhood rests on the absence of any
  refinement decomposition in the development library, and that absence is retained. The
  choice of the seeded roots remains the residual every problem records.
\<close>

end
