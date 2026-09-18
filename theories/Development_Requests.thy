theory Development_Requests
  imports Development_Refinement_Contracts
begin

section \<open>The next problems are the admitted answer of a native question on the actual problems\<close>

text \<open>
  Which problems to take next is itself decided through the native process: the candidates
  are the actual problems and the single original condition is their computed readiness, so
  the existing filtered question and its admission contract apply without restating them.
  Every ready problem is admitted and no preference among them is supplied; ties stay
  explicit, and no list position or name orders them.
\<close>

definition development_selection_question ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      native_development_question option" where
  "development_selection_question D answered ps=
    filtered_development_question ps (development_ready D answered)"

theorem development_selected_ready:
  assumes admitted: "native_admitted_subjects ps (development_selection_question D answered ps) report=Some xs"
    and member: "p\<in>set xs"
  shows "p\<in>set ps \<and> development_ready D answered p"
  by (rule filtered_admitted_subjects_condition[OF admitted[unfolded development_selection_question_def] member])

section \<open>The admitted problems are one group of independent work\<close>

text \<open>
  The schedule of the admitted problems is read from the same dependencies: no admitted
  problem is a prerequisite of another, so they form one group that may be worked on
  concurrently. Adopting their answers concurrently is a separate question for the
  transaction contracts; this group establishes only that no admitted answer waits for
  another.
\<close>

theorem development_selected_independent:
  assumes admitted: "native_admitted_subjects ps (development_selection_question D answered ps) report=Some xs"
    and first: "p\<in>set xs" and second: "q\<in>set xs"
  shows "q |\<notin>| development_premises D p"
proof -
  have "development_ready D answered p" "development_ready D answered q"
    using development_selected_ready[OF admitted first] development_selected_ready[OF admitted second]
    by simp_all
  then show ?thesis by (rule development_ready_independent)
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
     (development_refinement_scope C c)))"

definition development_request_context :: "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_entity fset" where
  "development_request_context C c=fset_of_list (filter (\<lambda>e. e\<in>set (development_refinement_scope C c) \<or>
     (case isabelle_declared_constant e of None \<Rightarrow> False
      | Some d \<Rightarrow> d |\<in>| development_request_support C c)) (snd C))"

lemma development_request_support_member:
  "d |\<in>| development_request_support C c \<longleftrightarrow>
    (\<exists>e\<in>set (development_refinement_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p))"
proof
  assume "d |\<in>| development_request_support C c"
  then obtain l where listed: "l\<in>set (List.map_filter
      (\<lambda>e. map_option isabelle_term_constants (isabelle_specified_proposition e))
      (development_refinement_scope C c))" and inside: "d\<in>set l"
    by (auto simp: development_request_support_def fset_of_list_elem)
  obtain e where scope: "e\<in>set (development_refinement_scope C c)"
    and read: "map_option isabelle_term_constants (isabelle_specified_proposition e)=Some l"
    using listed by (auto simp: map_filter_member)
  obtain p where statement: "isabelle_specified_proposition e=Some p" and constants: "l=isabelle_term_constants p"
    using read by (auto simp: map_option_eq_Some)
  show "\<exists>e\<in>set (development_refinement_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p)"
    using scope statement inside constants by blast
next
  assume "\<exists>e\<in>set (development_refinement_scope C c). \<exists>p. isabelle_specified_proposition e=Some p \<and>
      d\<in>set (isabelle_term_constants p)"
  then obtain e p where scope: "e\<in>set (development_refinement_scope C c)"
    and statement: "isabelle_specified_proposition e=Some p" and inside: "d\<in>set (isabelle_term_constants p)"
    by blast
  have "isabelle_term_constants p\<in>set (List.map_filter
      (\<lambda>e. map_option isabelle_term_constants (isabelle_specified_proposition e))
      (development_refinement_scope C c))"
    using scope statement by (auto simp: map_filter_member)
  then show "d |\<in>| development_request_support C c"
    using inside by (auto simp: development_request_support_def fset_of_list_elem)
qed

theorem development_request_context_exact:
  "e |\<in>| development_request_context C c \<longleftrightarrow> e\<in>set (snd C) \<and>
    (e\<in>set (development_refinement_scope C c) \<or>
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
  have refined: "e\<in>set (development_refinement_scope C c)"
  proof -
    have "e\<in>set (development_refinement_scope C c) \<or>
        (\<exists>d. isabelle_declared_constant e=Some d \<and> d |\<in>| development_request_support C c)"
      using member by (simp only: development_request_context_exact)
    then show ?thesis using statement isabelle_declaration_specifies_nothing by fastforce
  qed
  have "d |\<in>| development_request_support C c"
    using refined statement mentioned by (auto simp: development_request_support_member)
  then show ?thesis using declared declares by (simp add: development_request_context_exact)
qed

theorem development_request_context_least:
  assumes scope: "set (development_refinement_scope C c)\<subseteq>F"
    and closed: "\<And>e p d e'. e\<in>F \<Longrightarrow> isabelle_specified_proposition e=Some p \<Longrightarrow>
      d\<in>set (isabelle_term_constants p) \<Longrightarrow> e'\<in>set (snd C) \<Longrightarrow> isabelle_declared_constant e'=Some d \<Longrightarrow> e'\<in>F"
  shows "fset (development_request_context C c)\<subseteq>F"
proof
  fix e assume "e\<in>fset (development_request_context C c)"
  then have state: "e\<in>set (snd C)" and origin: "e\<in>set (development_refinement_scope C c) \<or>
      (\<exists>d. isabelle_declared_constant e=Some d \<and> d |\<in>| development_request_support C c)"
    by (simp_all only: development_request_context_exact)
  show "e\<in>F"
  proof (cases "e\<in>set (development_refinement_scope C c)")
    case True
    then show ?thesis using scope by blast
  next
    case False
    then obtain d where declares: "isabelle_declared_constant e=Some d"
      and supported: "d |\<in>| development_request_support C c" using origin by blast
    obtain x p where refined: "x\<in>set (development_refinement_scope C c)"
      and statement: "isabelle_specified_proposition x=Some p" and mentioned: "d\<in>set (isabelle_term_constants p)"
      using supported by (auto simp: development_request_support_member)
    show ?thesis by (rule closed[OF _ statement mentioned state declares]) (use refined scope in blast)
  qed
qed

definition development_refinement_request :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_request option" where
  "development_refinement_request C r a c=(case development_refinement_problem C r a c of None \<Rightarrow> None
     | Some p \<Rightarrow> (case problem_contract p of
         Development_Refinement s \<Rightarrow> Some (p,s,development_request_support C c,development_request_context C c)
       | _ \<Rightarrow> None))"

theorem development_refinement_request_fields:
  assumes request: "development_refinement_request C r a c=Some (p,s,S,E)"
  shows "development_refinement_problem C r a c=Some p" "problem_contract p=Development_Refinement s"
    "problem_subject p={|c|}" "S=development_request_support C c" "E=development_request_context C c"
    "\<forall>q\<in>set (development_refinement_statements C c). Isabelle_Code_Equation q |\<in>| E"
proof -
  obtain k where problem: "development_refinement_problem C r a c=Some p"
    and contract: "development_refinement_contract C c=Some k" and shape: "p=Development_Problem {|c|} k r a"
    using request by (auto simp: development_refinement_request_def development_refinement_problem_def
      split: option.splits development_contract.splits)
  have statement: "problem_contract p=Development_Refinement s" "S=development_request_support C c"
    "E=development_request_context C c"
    using request problem by (auto simp: development_refinement_request_def split: development_contract.splits)
  show "development_refinement_problem C r a c=Some p" by (rule problem)
  show "problem_contract p=Development_Refinement s" by (rule statement(1))
  show "problem_subject p={|c|}" by (rule development_refinement_problem_subject[OF problem])
  show "S=development_request_support C c" by (rule statement(2))
  show "E=development_request_context C c" by (rule statement(3))
  show "\<forall>q\<in>set (development_refinement_statements C c). Isabelle_Code_Equation q |\<in>| E"
    by (auto simp: statement(3) development_request_context_exact development_refinement_scope_member
      development_refinement_statements_state)
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
