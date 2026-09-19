theory Development_Requests
  imports Development_Refinement_Contracts Development_Native_Selection
begin

section \<open>The next problems are the admitted answer of a native question on the actual problems\<close>

text \<open>
  The next problems are the admitted answer of a question whose scope is the candidates of the problems
  and whose condition is native readiness. No table of computed readiness is supplied: the condition is the
  native definition, and the question states only its candidates, each the row a problem is read by with
  the rows its settledness reads. A question is posed only over a closed problem scope, one whose
  dependencies and answered problems are among its problems; the problems admitted are those whose
  candidates the question admits.
\<close>

definition development_selection_question :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> native_development_question option" where
  "development_selection_question D answered ps=(if development_readiness_scope_closed D answered ps
    then finite_subject_question (Finite_Payload []) (development_readiness_candidates D answered ps)
      [native_readiness_condition] else None)"

definition development_admitted_problems :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> finite_factor_term list option \<Rightarrow> development_problem list option" where
  "development_admitted_problems D answered ps admission=map_option (\<lambda>accepted.
    let E=development_readiness_closure D answered in
    filter (\<lambda>p. development_readiness_candidate D answered ps E p\<in>set accepted) ps) admission"

theorem development_admitted_ready:
  assumes question: "development_selection_question D answered ps=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and p: "p\<in>set ps"
    and chosen: "development_readiness_candidate D answered ps (development_readiness_closure D answered) p\<in>set accepted"
  shows "development_ready D answered p"
proof -
  have closed: "development_readiness_scope_closed D answered ps"
    and constructed: "finite_subject_question (Finite_Payload []) (development_readiness_candidates D answered ps)
      [native_readiness_condition]=Some Q"
    using question by (simp_all add: development_selection_question_def split: if_splits)
  obtain C where condition: "native_readiness_condition=Some C"
    using native_readiness_condition_total by blast
  have holds: "development_condition_holds C (Finite_Payload [])
      (development_readiness_candidate D answered ps (development_readiness_closure D answered) p)"
    by (rule finite_subject_question_conditions[OF constructed admission chosen]) (simp add: condition)
  let ?key="development_readiness_key ps"
  let ?hs="development_readiness_decompositions D ps"
  let ?cone="development_readiness_cone D answered ps (development_readiness_closure D answered)"
  have presents: "readiness_presents ?key D answered ps ?hs ?cone"
    by (rule development_readiness_presents[OF closed])
  have native: "(readiness_ready,Pair_Term (Payload_Term []) (Pair_Term (readiness_table_term (?cone p))
      (Pair_Term (path_term (?key p)) (readiness_value (p |\<in>| answered) (?hs p)))))\<in>positive_meaning native_readiness_system"
    using holds by (simp add: native_readiness_condition_exact[OF condition] development_readiness_candidate_def
      decode_finite_readiness_table decode_finite_readiness_row)
  have xf: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  show ?thesis using native_development_ready[OF presents p xf] native by simp
qed

theorem development_selected_ready:
  assumes question: "development_selection_question D answered ps=Some Q"
    and selected: "development_admitted_problems D answered ps (native_development_admission Q report)=Some xs"
    and member: "p\<in>set xs"
  shows "p\<in>set ps \<and> development_ready D answered p"
proof -
  obtain accepted where admission: "native_development_admission Q report=Some accepted"
    and xs: "xs=filter (\<lambda>p. development_readiness_candidate D answered ps
      (development_readiness_closure D answered) p\<in>set accepted) ps"
    using selected by (auto simp: development_admitted_problems_def Let_def)
  have p: "p\<in>set ps"
    and chosen: "development_readiness_candidate D answered ps (development_readiness_closure D answered) p\<in>set accepted"
    using member xs by simp_all
  show ?thesis using development_admitted_ready[OF question admission p chosen] p by blast
qed

theorem development_selected_independent:
  assumes question: "development_selection_question D answered ps=Some Q"
    and selected: "development_admitted_problems D answered ps (native_development_admission Q report)=Some xs"
    and first: "p\<in>set xs" and second: "q\<in>set xs"
  shows "q |\<notin>| development_premises D p"
proof -
  have "development_ready D answered p" "development_ready D answered q"
    using development_selected_ready[OF question selected first]
      development_selected_ready[OF question selected second] by simp_all
  then show ?thesis by (rule development_ready_independent)
qed

section \<open>The admitted problems are one group of independent work\<close>

text \<open>
  The schedule of the admitted problems is read from the same dependencies: no admitted
  problem is a prerequisite of another (\<open>development_selected_independent\<close>), so they form one
  group that may be worked on concurrently. Adopting their answers concurrently is a separate
  question for the transaction contracts; this group establishes only that no admitted answer
  waits for another.
\<close>

section \<open>An executed selection admits only ready problems\<close>

text \<open>
  A selection is executed by the native producer of its question and checked by its admission.
  The executed packet (question, report and admission) is the evidence of the decision, and the
  selected problems are read from its admission without admitting the report a second time. Every
  selected problem is ready: that is the question's admission contract read through the packet,
  so every development that selects its next problems natively instantiates it here.
\<close>

definition development_selection_packet ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      (native_development_question\<times>native_development_report\<times>finite_factor_term list option) option" where
  "development_selection_packet D answered ps=map_option native_development_packet
    (development_selection_question D answered ps)"

definition development_packet_problems ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      native_development_question\<times>native_development_report\<times>finite_factor_term list option \<Rightarrow>
      development_problem list option" where
  "development_packet_problems D answered ps packet=(case packet of (Q,report,admission) \<Rightarrow>
    development_admitted_problems D answered ps admission)"

definition development_packet_selected ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      development_problem list option" where
  "development_packet_selected D answered ps=Option.bind (development_selection_packet D answered ps)
    (development_packet_problems D answered ps)"

theorem development_packet_problems_ready:
  assumes question: "development_selection_question D answered ps=Some Q"
    and admitted: "development_packet_problems D answered ps (native_development_packet Q)=Some xs"
    and member: "p\<in>set xs"
  shows "p\<in>set ps \<and> development_ready D answered p"
proof -
  have "development_admitted_problems D answered ps
      (native_development_admission Q (construct_native_development Q))=Some xs"
    using admitted by (simp add: development_packet_problems_def native_development_packet_def Let_def)
  then show ?thesis by (rule development_selected_ready[OF question _ member])
qed

theorem development_packet_selected_ready:
  assumes selected: "development_packet_selected D answered ps=Some xs" and member: "p\<in>set xs"
  shows "p\<in>set ps \<and> development_ready D answered p"
proof -
  obtain Q where question: "development_selection_question D answered ps=Some Q"
    and admitted: "development_packet_problems D answered ps (native_development_packet Q)=Some xs"
    using selected by (auto simp: development_packet_selected_def development_selection_packet_def
      bind_eq_Some_conv map_option_eq_Some)
  show ?thesis by (rule development_packet_problems_ready[OF question admitted member])
qed

section \<open>A request carries its constant, its support and its least context\<close>

text \<open>
  A refinement request carries its problem, the constant its answer refines, the support its
  answer may use and the context that support needs; the incumbent statements an answer
  replaces are the refined entities of that context. The support starts from the
  exported dependencies of the entities being refined: the constants their statements
  mention. The context is those entities together with the declarations of the support in
  the state, and nothing else, so it is exactly determined by the state; it is closed under
  the constants its statements mention, and it is contained in every closed part of the
  state that contains the refined entities.
\<close>

type_synonym development_request = "development_problem\<times>isabelle_term\<times>nat fset\<times>isabelle_entity fset"

definition development_request_support :: "isabelle_context \<Rightarrow> nat \<Rightarrow> nat fset" where
  "development_request_support C c=fset_of_list (concat (List.map_filter
     (\<lambda>e. map_option isabelle_term_constants (isabelle_specified_proposition e))
     (development_constant_scope C c)))"

definition development_request_context :: "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_entity fset" where
  "development_request_context C c=fset_of_list (filter (\<lambda>e. e\<in>set (development_constant_scope C c) \<or>
     (case isabelle_declared_constant e of None \<Rightarrow> False
      | Some d \<Rightarrow> d |\<in>| development_request_support C c)) (snd C))"

lemma development_request_support_member:
  "d |\<in>| development_request_support C c \<longleftrightarrow>
    (\<exists>e\<in>set (development_constant_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p))"
proof
  assume "d |\<in>| development_request_support C c"
  then obtain l where listed: "l\<in>set (List.map_filter
      (\<lambda>e. map_option isabelle_term_constants (isabelle_specified_proposition e))
      (development_constant_scope C c))" and inside: "d\<in>set l"
    by (auto simp: development_request_support_def fset_of_list_elem)
  obtain e where scope: "e\<in>set (development_constant_scope C c)"
    and read: "map_option isabelle_term_constants (isabelle_specified_proposition e)=Some l"
    using listed by (auto simp: map_filter_member)
  obtain p where statement: "isabelle_specified_proposition e=Some p" and constants: "l=isabelle_term_constants p"
    using read by (auto simp: map_option_eq_Some)
  show "\<exists>e\<in>set (development_constant_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p)"
    using scope statement inside constants by blast
next
  assume "\<exists>e\<in>set (development_constant_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p)"
  then obtain e p where scope: "e\<in>set (development_constant_scope C c)"
    and statement: "isabelle_specified_proposition e=Some p" and inside: "d\<in>set (isabelle_term_constants p)"
    by blast
  have "isabelle_term_constants p\<in>set (List.map_filter
      (\<lambda>e. map_option isabelle_term_constants (isabelle_specified_proposition e))
      (development_constant_scope C c))"
    using scope statement by (auto simp: map_filter_member)
  then show "d |\<in>| development_request_support C c"
    using inside by (auto simp: development_request_support_def fset_of_list_elem)
qed

theorem development_request_context_exact:
  "e |\<in>| development_request_context C c \<longleftrightarrow> e\<in>set (snd C) \<and>
    (e\<in>set (development_constant_scope C c) \<or>
     (\<exists>d. isabelle_declared_constant e=Some d \<and> d |\<in>| development_request_support C c))"
  by (auto simp: development_request_context_def fset_of_list_elem split: option.splits)

lemma isabelle_declaration_specifies_nothing:
  "isabelle_declared_constant e=Some d \<Longrightarrow> isabelle_specified_proposition e=None"
  by (cases e) simp_all

theorem development_request_context_closed:
  assumes member: "e |\<in>| development_request_context C c"
    and statement: "isabelle_specified_proposition e=Some p" and mentioned: "d\<in>set (isabelle_term_constants p)"
    and declared: "e'\<in>set (snd C)" and declares: "isabelle_declared_constant e'=Some d"
  shows "e' |\<in>| development_request_context C c"
proof -
  have refined: "e\<in>set (development_constant_scope C c)"
  proof -
    have "e\<in>set (development_constant_scope C c) \<or>
        (\<exists>d. isabelle_declared_constant e=Some d \<and> d |\<in>| development_request_support C c)"
      using member by (simp only: development_request_context_exact)
    then show ?thesis using statement isabelle_declaration_specifies_nothing by fastforce
  qed
  have "d |\<in>| development_request_support C c"
    using refined statement mentioned by (auto simp: development_request_support_member)
  then show ?thesis using declared declares by (simp add: development_request_context_exact)
qed

theorem development_request_context_least:
  assumes scope: "set (development_constant_scope C c)\<subseteq>F"
    and closed: "\<And>e p d e'. e\<in>F \<Longrightarrow> isabelle_specified_proposition e=Some p \<Longrightarrow>
      d\<in>set (isabelle_term_constants p) \<Longrightarrow> e'\<in>set (snd C) \<Longrightarrow> isabelle_declared_constant e'=Some d \<Longrightarrow> e'\<in>F"
  shows "fset (development_request_context C c)\<subseteq>F"
proof
  fix e assume "e\<in>fset (development_request_context C c)"
  then have state: "e\<in>set (snd C)" and origin: "e\<in>set (development_constant_scope C c) \<or>
      (\<exists>d. isabelle_declared_constant e=Some d \<and> d |\<in>| development_request_support C c)"
    by (simp_all only: development_request_context_exact)
  show "e\<in>F"
  proof (cases "e\<in>set (development_constant_scope C c)")
    case True
    then show ?thesis using scope by blast
  next
    case False
    then obtain d where declares: "isabelle_declared_constant e=Some d"
      and supported: "d |\<in>| development_request_support C c" using origin by blast
    obtain x p where refined: "x\<in>set (development_constant_scope C c)"
      and statement: "isabelle_specified_proposition x=Some p" and mentioned: "d\<in>set (isabelle_term_constants p)"
      using supported by (auto simp: development_request_support_member)
    show ?thesis by (rule closed[OF _ statement mentioned state declares]) (use refined scope in blast)
  qed
qed

text \<open>
  A request of a problem of a constant carries the problem, the constant as the state declares it,
  the support and the least context; the kind of the problem selects only which statements of the
  constant's scope are its incumbent, and the context holds them all. The construction is stated
  once over the reading and the kind: the refinement request is its instance under the
  code-equation reading, the definition request its instance under the definition reading.
\<close>

definition development_constant_request :: "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow>
    (isabelle_term \<Rightarrow> development_contract) \<Rightarrow> isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_request option" where
  "development_constant_request reading kind C r a c=map_option (\<lambda>s.
     (Development_Problem {|c|} (kind s) r a,s,development_request_support C c,development_request_context C c))
     (development_stated_constant reading C c)"

theorem development_constant_request_fields:
  assumes request: "development_constant_request reading kind C r a c=Some (p,s,S,E)"
  shows "development_constant_problem reading kind C r a c=Some p" "problem_contract p=kind s"
    "problem_subject p={|c|}" "S=development_request_support C c" "E=development_request_context C c"
    "\<And>q. q\<in>set (development_statements reading C c) \<Longrightarrow> \<exists>e. reading e=Some q \<and> e |\<in>| E"
proof -
  have stated: "development_stated_constant reading C c=Some s"
    and problem: "p=Development_Problem {|c|} (kind s) r a"
    and fields: "S=development_request_support C c" "E=development_request_context C c"
    using request by (auto simp: development_constant_request_def)
  show "development_constant_problem reading kind C r a c=Some p"
    by (simp add: development_constant_problem_def development_constant_contract_def stated problem)
  show "problem_contract p=kind s" by (simp add: problem)
  show "problem_subject p={|c|}" by (simp add: problem)
  show "S=development_request_support C c" by (rule fields(1))
  show "E=development_request_context C c" by (rule fields(2))
  show "\<exists>e. reading e=Some q \<and> e |\<in>| E" if statement: "q\<in>set (development_statements reading C c)" for q
  proof -
    obtain e where scope: "e\<in>set (development_constant_scope C c)" and read: "reading e=Some q"
      using statement unfolding development_statements_exact by blast
    have state: "e\<in>set (snd C)" using scope by (simp only: development_constant_scope_member)
    have "e |\<in>| E" unfolding fields(2) development_request_context_exact using state scope by blast
    then show ?thesis using read by blast
  qed
qed

definition development_refinement_request :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_request option" where
  "development_refinement_request C r a c=development_constant_request isabelle_code_equation_proposition
     Development_Refinement C r a c"

theorem development_refinement_request_fields:
  assumes request: "development_refinement_request C r a c=Some (p,s,S,E)"
  shows "development_refinement_problem C r a c=Some p" "problem_contract p=Development_Refinement s"
    "problem_subject p={|c|}" "S=development_request_support C c" "E=development_request_context C c"
    "\<forall>q\<in>set (development_refinement_statements C c). Isabelle_Code_Equation q |\<in>| E"
proof -
  note fields=development_constant_request_fields[OF request[unfolded development_refinement_request_def]]
  show "development_refinement_problem C r a c=Some p"
    by (simp only: development_refinement_problem_def fields(1))
  show "problem_contract p=Development_Refinement s" by (rule fields(2))
  show "problem_subject p={|c|}" by (rule fields(3))
  show "S=development_request_support C c" by (rule fields(4))
  show "E=development_request_context C c" by (rule fields(5))
  show "\<forall>q\<in>set (development_refinement_statements C c). Isabelle_Code_Equation q |\<in>| E"
  proof
    fix q assume "q\<in>set (development_refinement_statements C c)"
    then have "q\<in>set (development_statements isabelle_code_equation_proposition C c)"
      by (simp only: development_refinement_statements_def)
    then obtain e where read: "isabelle_code_equation_proposition e=Some q" and member: "e |\<in>| E"
      using fields(6) by blast
    have "e=Isabelle_Code_Equation q" using read by (simp only: isabelle_code_equation_proposition_exact)
    then show "Isabelle_Code_Equation q |\<in>| E" using member by simp
  qed
qed

definition development_request_data :: "development_request \<Rightarrow> finite_factor_term" where
  "development_request_data=finite_pair_presentation development_problem_data
    (finite_pair_presentation isabelle_term_data
      (finite_pair_presentation isabelle_positions_data isabelle_entities_data))"

lemma development_request_data_injective [intro]: "inj development_request_data"
  unfolding development_request_data_def
  by (intro finite_pair_presentation_injective development_problem_data_injective
    isabelle_term_data_injective isabelle_collections_injective)

definition development_requests_data :: "development_request list \<Rightarrow> finite_factor_term" where
  "development_requests_data=finite_sequence_presentation development_request_data"

lemma development_requests_data_injective [intro]: "inj development_requests_data"
  unfolding development_requests_data_def
  by (intro finite_sequence_presentation_injective development_request_data_injective)

text \<open>
  A request is constructed, not yet issued. Issuing it as a leaf needs an admitted account
  of its decomposition scope; no decomposition schema for a refinement problem is
  represented in the development library yet, so that absence is the only ground for
  leafhood and is retained as such. Whether an answer states equations of the constant, stays
  within the support and leaves every other entity unchanged is the verifier's question.
\<close>

end
