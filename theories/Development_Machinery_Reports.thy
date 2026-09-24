theory Development_Machinery_Reports
  imports Development_Machinery Development_Loop_Presentations Development_State_Presenter
begin

section \<open>The machinery's reports present its residual record\<close>

text \<open>
  The machinery is a residual record: every problem its constructor poses is residual and generated, so it
  cites nothing, and its problems are presented as their rows keyed by the state's constant keys, their
  contract terms carried in the machinery's names. A report that is not a presentation is the store's
  absence.
\<close>

abbreviation development_machinery_inert :: "isabelle_term \<Rightarrow> finite_factor_term" where
  "development_machinery_inert \<equiv> development_local_term_data (fst development_machinery_context)"

definition development_machinery_problem_data ::
    "development_machinery_problem_report \<Rightarrow> finite_factor_term option" where
  "development_machinery_problem_data=finite_partial_pair
    (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
    (finite_partial_pair (Some \<circ> isabelle_positions_data)
      (finite_partial_pair
        (development_dependencies_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
        (development_problem_assessment_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))))"

lemma development_machinery_problem_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
  shows "finite_presented_on development_machinery_problem_data
    (lists P\<times>UNIV\<times>{D. fset D\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}}\<times>(lists P\<times>lists P\<times>lists P\<times>lists P\<times>UNIV))"
  unfolding development_machinery_problem_data_def
  by (intro finite_partial_pair_presented development_problems_data_presented finite_presented_total
    isabelle_collections_injective(2) development_dependencies_data_presented
    development_problem_assessment_data_presented domain)

definition development_machinery_problem_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_problem_value answered=finite_store_option id
    (development_machinery_problem_data (development_machinery_problem_report answered))"

definition development_machinery_loop_data :: "development_machinery_loop_report \<Rightarrow> finite_factor_term option" where
  "development_machinery_loop_data=finite_partial_pair
    (Some \<circ> finite_sequence_presentation (finite_option_presentation finite_development_context_value))
    (finite_partial_pair (Some \<circ> finite_option_presentation finite_development_context_value)
      (finite_partial_option
        (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))))"

lemma development_machinery_loop_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
  shows "finite_presented_on development_machinery_loop_data (UNIV\<times>UNIV\<times>{x. set_option x\<subseteq>lists P})"
  unfolding development_machinery_loop_data_def
  by (intro finite_partial_pair_presented finite_presented_total finite_sequence_presentation_injective
    finite_option_presentation_injective finite_development_values_injective finite_partial_option_presented
    development_problems_data_presented domain)

definition development_machinery_loop_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_loop_value answered=finite_store_option id
    (development_machinery_loop_data (development_machinery_loop_report answered))"

definition development_machinery_verification_data ::
    "development_machinery_verification \<Rightarrow> finite_factor_term option" where
  "development_machinery_verification_data=finite_partial_option (finite_partial_pair
    (development_requests_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
    (finite_partial_pair (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
      (Some \<circ> finite_sequence_presentation (finite_sequence_presentation
        (finite_pair_presentation development_verdict_data finite_boolean_data)))))"

lemma development_machinery_verification_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
    and requests: "development_request_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) R"
  shows "finite_presented_on development_machinery_verification_data {x. set_option x\<subseteq>lists R\<times>lists P\<times>UNIV}"
  unfolding development_machinery_verification_data_def
  by (intro finite_partial_option_presented finite_partial_pair_presented development_requests_data_presented
    development_problems_data_presented finite_presented_total finite_sequence_presentation_injective
    finite_pair_presentation_injective development_verdict_data_injective finite_boolean_data_injective domain requests)

definition development_machinery_verification_value ::
    "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_verification_value answered=finite_store_option id
    (development_machinery_verification_data (development_machinery_verification answered))"

text \<open>
  The machinery's problems and requests are those of one constant construction, a domain of its residual
  record, and its reports hold only them and the problems their dependencies cite: each report lies in its
  presentation's domain, so its value is the presentation itself, never the store's absence.
\<close>

lemma development_machinery_family_domain:
  "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) {p. \<exists>c. development_constant_problem
    isabelle_definition_proposition Development_Definition development_machinery_context
      Development_Residual Development_Generated c=Some p}"
  by (rule development_constant_problems_domain[OF state_constant_key_injective,
    where reading=isabelle_definition_proposition and kind=Development_Definition and C=development_machinery_context
      and r=Development_Residual and a=Development_Generated]) simp_all

lemma development_machinery_request_family_domain:
  "development_request_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) {q. \<exists>c. development_constant_request
    isabelle_definition_proposition Development_Definition development_machinery_context
      Development_Residual Development_Generated c=Some q}"
  by (rule development_constant_requests_domain[OF state_constant_key_injective,
    where reading=isabelle_definition_proposition and kind=Development_Definition and C=development_machinery_context
      and r=Development_Residual and a=Development_Generated]) simp_all

theorem development_machinery_problem_report_domain:
  defines P_def: "P\<equiv>{p. \<exists>c. development_constant_problem isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some p}"
  shows "development_machinery_problem_report answered\<in>lists P\<times>UNIV\<times>{D. fset D\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}}\<times>
    (lists P\<times>lists P\<times>lists P\<times>lists P\<times>UNIV)"
proof -
  have problems: "set development_machinery_problems\<subseteq>P"
    by (auto simp: P_def development_machinery_problems_def development_constant_problems_exact)
  have dependencies: "fset development_machinery_dependencies\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}"
    by (auto simp: P_def development_machinery_dependencies_def development_constant_dependencies_def
      development_constant_premises_def fset_of_list.rep_eq map_filter_member) blast
  show ?thesis using problems dependencies
    by (auto simp: development_machinery_problem_report_def development_problem_assessment_def
      development_ready_problems_def development_without_subject_def development_residual_problems_def
      development_ambiguous_def in_lists_conv_set)
qed

theorem development_machinery_loop_report_domain:
  defines P_def: "P\<equiv>{p. \<exists>c. development_constant_problem isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some p}"
  shows "development_machinery_loop_report answered\<in>UNIV\<times>UNIV\<times>{x. set_option x\<subseteq>lists P}"
  by (auto simp: P_def development_machinery_loop_report_def Let_def development_packet_problems_def
    development_admitted_problems_def development_machinery_problems_def development_constant_problems_exact
    in_lists_conv_set split: prod.splits)

lemma development_machinery_issued_family:
  assumes issue: "development_machinery_issue answered=Some (L',issued,unissued)"
  shows "set issued\<subseteq>{q. \<exists>c. development_constant_request isabelle_definition_proposition Development_Definition
    development_machinery_context Development_Residual Development_Generated c=Some q}"
proof
  fix r assume r: "r\<in>set issued"
  obtain L xs where selection: "development_loop_selection (development_machinery_state,development_machinery_problems,
      development_machinery_dependencies,answered,[])=Some (L,xs)"
    and issue': "development_loop_issue (development_loop_library development_machinery_sources L)
      development_machinery_request_of L xs=(L',issued,unissued)"
    using issue by (auto simp: development_machinery_issue_def split: prod.splits)
  obtain c where "development_definition_request development_machinery_context Development_Residual
      Development_Generated c=Some r"
    using development_machinery_issued(2)[OF selection issue' r] by blast
  then show "r\<in>{q. \<exists>c. development_constant_request isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some q}"
    by (auto simp: development_definition_request_def)
qed

lemma development_machinery_requests_family:
  "set (development_machinery_requests answered)\<subseteq>{q. \<exists>c. development_constant_request isabelle_definition_proposition
    Development_Definition development_machinery_context Development_Residual Development_Generated c=Some q}"
proof (cases "development_machinery_issue answered")
  case None
  then show ?thesis by (simp add: development_machinery_requests_def)
next
  case (Some z)
  obtain L' issued unissued where z: "z=(L',issued,unissued)" by (cases z) auto
  show ?thesis using development_machinery_issued_family[OF Some[unfolded z]]
    by (simp add: development_machinery_requests_def Some z)
qed

theorem development_machinery_verification_domain:
  defines P_def: "P\<equiv>{p. \<exists>c. development_constant_problem isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some p}"
    and R_def: "R\<equiv>{q. \<exists>c. development_constant_request isabelle_definition_proposition Development_Definition
      development_machinery_context Development_Residual Development_Generated c=Some q}"
  shows "development_machinery_verification answered\<in>{x. set_option x\<subseteq>lists R\<times>lists P\<times>UNIV}"
proof (cases "development_machinery_issue answered")
  case None
  then show ?thesis by (simp add: development_machinery_verification_def)
next
  case (Some z)
  obtain L xs where selection: "development_loop_selection (development_machinery_state,development_machinery_problems,
      development_machinery_dependencies,answered,[])=Some (L,xs)"
    and issue: "development_loop_issue (development_loop_library development_machinery_sources L)
      development_machinery_request_of L xs=z"
    using Some by (auto simp: development_machinery_issue_def split: prod.splits)
  obtain L' issued unissued where z: "z=(L',issued,unissued)" by (cases z) auto
  have issued: "set issued\<subseteq>R"
    unfolding R_def by (rule development_machinery_issued_family[OF Some[unfolded z]])
  obtain S ps D done0 history where L: "L=(S,ps,D,done0,history)" by (cases L) auto
  have "set unissued\<subseteq>set xs" using issue by (auto simp: z L development_loop_issue_def Let_def)
  moreover have "set xs\<subseteq>set development_machinery_problems"
    using development_loop_selection_ready(1)[OF selection] by blast
  moreover have "set development_machinery_problems\<subseteq>P"
    by (auto simp: P_def development_machinery_problems_def development_constant_problems_exact)
  ultimately have unissued: "set unissued\<subseteq>P" by blast
  show ?thesis using issued unissued by (auto simp: development_machinery_verification_def Some z lists_eq_set)
qed

corollary development_machinery_problem_presentation:
  "development_machinery_problem_data (development_machinery_problem_report answered)\<noteq>None"
  by (rule finite_presented_on_some[OF development_machinery_problem_data_presented[OF
    development_machinery_family_domain] development_machinery_problem_report_domain[of answered]]) simp

corollary development_machinery_loop_presentation:
  "development_machinery_loop_data (development_machinery_loop_report answered)\<noteq>None"
  by (rule finite_presented_on_some[OF development_machinery_loop_data_presented[OF
    development_machinery_family_domain] development_machinery_loop_report_domain[of answered]]) simp

corollary development_machinery_verification_presentation:
  "development_machinery_verification_data (development_machinery_verification answered)\<noteq>None"
  by (rule finite_presented_on_some[OF development_machinery_verification_data_presented[OF
    development_machinery_family_domain development_machinery_request_family_domain]
    development_machinery_verification_domain[of answered]]) simp

definition development_machinery_native_judgment_value :: "String.literal \<Rightarrow> bool list \<Rightarrow> finite_factor_term" where
  "development_machinery_native_judgment_value n bits=finite_store_option id
    (development_named_native_judgment_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None)
      (development_named_native_judgment development_definition_verdict development_machinery_state
        (development_machinery_requests development_machinery_unanswered) n bits))"

text \<open>
  The native judgment of a named answer carries its request, one of the machinery's requests, so it too
  lies in its presentation's domain, for every name and answer.
\<close>

theorem development_machinery_native_judgment_domain:
  "development_named_native_judgment development_definition_verdict development_machinery_state
    (development_machinery_requests answered) n bits\<in>{x. set_option x\<subseteq>{q. \<exists>c. development_constant_request
      isabelle_definition_proposition Development_Definition development_machinery_context
        Development_Residual Development_Generated c=Some q}\<times>UNIV}"
proof (cases "development_named_request (snd development_machinery_state) (development_machinery_requests answered) n")
  case None
  then show ?thesis by (simp add: development_named_native_judgment_def)
next
  case (Some r)
  have "r\<in>set (development_machinery_requests answered)" by (rule development_named_request_member[OF Some])
  then show ?thesis using development_machinery_requests_family[of answered]
    by (auto simp: development_named_native_judgment_def Some)
qed

corollary development_machinery_native_judgment_presentation:
  "development_named_native_judgment_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None)
    (development_named_native_judgment development_definition_verdict development_machinery_state
      (development_machinery_requests answered) n bits)\<noteq>None"
  by (rule finite_presented_on_some[OF development_named_native_judgment_data_presented[OF
    development_machinery_request_family_domain, where inert=development_machinery_inert]
    development_machinery_native_judgment_domain[of answered n bits]]) simp

end
