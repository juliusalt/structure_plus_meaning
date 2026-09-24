theory Development_Constant_Verification
  imports Development_Requests Isabelle_State_Difference
begin

section \<open>An answer to a problem of a constant is judged by the difference it makes\<close>

text \<open>
  An answer to a request is read as the state of the checked context that contains it, exported
  from the same roots by the same exporter. The verdict never constructs an answer: it reads the
  difference between the state the request was made against and the answer state, through the
  names both tables share. Which statements of its subject an answer may replace, and which kind
  of statement it must state, is the kind of the problem: a refinement replaces the code equations
  of its constant and must state one; a definition replaces the kernel definitions of its constant,
  and with them the code equations derived from them, and must state a kernel definition. Nothing
  else may change; declarations may disappear only when nothing mentions their constants any more,
  which the closure of the answer state decides. Every statement the answer makes of its subject
  must mention only constants of the issued support, and the answer state must be closed and keep
  the roots of the request. The verdict is stated once over the two readings, and every kind of
  answer is its instance.
\<close>

definition development_answer_statement ::
    "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "development_answer_statement kind C P e \<longleftrightarrow> kind e \<and>
    list_ex (\<lambda>c. c |\<in>| P) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"

definition development_answer_statements ::
    "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity list" where
  "development_answer_statements kind C P=filter (development_answer_statement kind C P) (snd C)"

definition development_answer_statements_excess ::
    "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> isabelle_context \<Rightarrow> nat fset \<Rightarrow> nat fset \<Rightarrow> nat list" where
  "development_answer_statements_excess kind C P S=remdups (filter (\<lambda>d. d |\<notin>| S)
    (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition)
      (development_answer_statements kind C P))))"

definition isabelle_assessment_closed :: "isabelle_context_assessment \<Rightarrow> bool" where
  "isabelle_assessment_closed a \<longleftrightarrow> (case a of (unknown,undeclared,malformed,unreached,frontier) \<Rightarrow>
    unknown={||} \<and> undeclared={||} \<and> malformed={||} \<and> unreached={||})"

type_synonym development_constant_verdict =
  "isabelle_entity list\<times>isabelle_entity list\<times>isabelle_entity list\<times>isabelle_entity list\<times>
    isabelle_entity list\<times>nat list\<times>isabelle_context_assessment\<times>bool\<times>bool"

text \<open>
  The verdict retains the whole difference, the parts of it the kind of answer does not permit,
  the statements of the demanded kind the answer makes of the subject, the constants its replaced
  statements mention outside the support, the assessment of the answer state, whether the roots
  are kept and whether both tables are free of repeated names. Nothing is summarized away: a
  refusal carries its reasons.
\<close>

definition development_constant_verdict ::
    "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> (isabelle_entity \<Rightarrow> bool) \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_constant_verdict" where
  "development_constant_verdict replaceable demanded S r S'=(case r of (p,s,support,E) \<Rightarrow>
    let C=snd S; C'=snd S'; f=isabelle_state_embedding (fst C) (fst C');
      P=problem_subject p; P'=fimage f P; removed=isabelle_state_removed C C';
      added=isabelle_state_added C C' in
    (removed,added,
     filter (\<lambda>e. \<not>development_answer_statement replaceable C P e \<and> isabelle_declared_constant e=None) removed,
     filter (\<lambda>e. \<not>development_answer_statement replaceable C' P' e) added,
     development_answer_statements demanded C' P',
     development_answer_statements_excess replaceable C' P' (fimage f support),
     isabelle_context_assessment (fst S') C',
     map (isabelle_term_rename f) (fst S)=fst S',
     distinct (fst C) \<and> distinct (fst C')))"

definition development_verdict_accepted :: "development_constant_verdict \<Rightarrow> bool" where
  "development_verdict_accepted v \<longleftrightarrow> (case v of
    (removed,added,unpermitted_removed,unpermitted_added,statements,excess,assessment,roots,tables) \<Rightarrow>
      unpermitted_removed=[] \<and> unpermitted_added=[] \<and> statements\<noteq>[] \<and> excess=[] \<and>
      isabelle_assessment_closed assessment \<and> roots \<and> tables)"

section \<open>An accepted verdict is the local contract of the answer\<close>

text \<open>
  An accepted verdict states exactly what the request demanded of the answer state: every entity
  other than the replaceable statements of the subject and the declarations persists under the
  correspondence, nothing but replaceable statements of the subject is added, the subject has a
  statement of the demanded kind, every replaceable statement of the subject stays within the
  issued support, the answer state is closed and keeps the roots, and the correspondence is
  injective. A use of an accepted answer consumes these conclusions; none of them is established
  again, and every kind of answer consumes them through its instance.
\<close>

theorem development_constant_verdict_contract:
  assumes accepted: "development_verdict_accepted
      (development_constant_verdict replaceable demanded S (p,s,support,E) S')"
  defines "f\<equiv>isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  shows "\<And>e. e\<in>set (snd (snd S)) \<Longrightarrow> \<not>development_answer_statement replaceable (snd S) (problem_subject p) e \<Longrightarrow>
      isabelle_declared_constant e=None \<Longrightarrow> isabelle_entity_rename f e\<in>set (snd (snd S'))"
    and "\<And>e'. e'\<in>set (snd (snd S')) \<Longrightarrow>
      (\<exists>e\<in>set (snd (snd S)). e'=isabelle_entity_rename f e) \<or>
      development_answer_statement replaceable (snd S') (fimage f (problem_subject p)) e'"
    and "\<exists>e'\<in>set (snd (snd S')). development_answer_statement demanded (snd S') (fimage f (problem_subject p)) e'"
    and "\<And>e' q d. e'\<in>set (snd (snd S')) \<Longrightarrow>
      development_answer_statement replaceable (snd S') (fimage f (problem_subject p)) e' \<Longrightarrow>
      isabelle_specified_proposition e'=Some q \<Longrightarrow> d\<in>set (isabelle_term_constants q) \<Longrightarrow> d |\<in>| fimage f support"
    and "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))"
    and "map (isabelle_term_rename f) (fst S)=fst S'"
    and "inj f"
proof -
  let ?C="snd S" and ?C'="snd S'" and ?P="problem_subject p"
  let ?P'="fimage f ?P"
  have fields: "filter (\<lambda>e. \<not>development_answer_statement replaceable ?C ?P e \<and> isabelle_declared_constant e=None)
        (isabelle_state_removed ?C ?C')=[]"
      "filter (\<lambda>e. \<not>development_answer_statement replaceable ?C' ?P' e) (isabelle_state_added ?C ?C')=[]"
      "development_answer_statements demanded ?C' ?P'\<noteq>[]"
      "development_answer_statements_excess replaceable ?C' ?P' (fimage f support)=[]"
      "isabelle_assessment_closed (isabelle_context_assessment (fst S') ?C')"
      "map (isabelle_term_rename f) (fst S)=fst S'"
      "distinct (fst ?C) \<and> distinct (fst ?C')"
    using accepted by (simp_all add: development_verdict_accepted_def development_constant_verdict_def
      f_def Let_def)
  show "isabelle_entity_rename f e\<in>set (snd ?C')" if member: "e\<in>set (snd ?C)"
      and other: "\<not>development_answer_statement replaceable ?C ?P e" and undeclared: "isabelle_declared_constant e=None" for e
  proof (rule ccontr)
    assume "isabelle_entity_rename f e\<notin>set (snd ?C')"
    then have "e\<in>set (isabelle_state_removed ?C ?C')"
      using member by (simp add: isabelle_state_removed_exact f_def)
    then show False using fields(1) other undeclared by (auto simp: filter_empty_conv)
  qed
  show "(\<exists>e\<in>set (snd ?C). e'=isabelle_entity_rename f e) \<or> development_answer_statement replaceable ?C' ?P' e'"
    if member: "e'\<in>set (snd ?C')" for e'
  proof (cases "e'\<in>set (isabelle_state_added ?C ?C')")
    case True
    then show ?thesis using fields(2) by (auto simp: filter_empty_conv)
  next
    case False
    then show ?thesis using member by (auto simp: isabelle_state_added_exact f_def)
  qed
  show "\<exists>e'\<in>set (snd ?C'). development_answer_statement demanded ?C' ?P' e'"
    using fields(3) by (auto simp: development_answer_statements_def filter_empty_conv)
  show "d |\<in>| fimage f support"
    if member: "e'\<in>set (snd ?C')" and answer: "development_answer_statement replaceable ?C' ?P' e'"
      and statement: "isabelle_specified_proposition e'=Some q" and mentioned: "d\<in>set (isabelle_term_constants q)"
    for e' q d
  proof (rule ccontr)
    assume outside: "d |\<notin>| fimage f support"
    have "e'\<in>set (development_answer_statements replaceable ?C' ?P')"
      using member answer by (simp add: development_answer_statements_def)
    then have "isabelle_term_constants q\<in>set (List.map_filter
        (map_option isabelle_term_constants \<circ> isabelle_specified_proposition)
        (development_answer_statements replaceable ?C' ?P'))"
      using statement by (auto simp: map_filter_member)
    then have "d\<in>set (development_answer_statements_excess replaceable ?C' ?P' (fimage f support))"
      using mentioned outside by (auto simp: development_answer_statements_excess_def)
    then show False using fields(4) by simp
  qed
  show "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))" by (rule fields(5))
  show "map (isabelle_term_rename f) (fst S)=fst S'" by (rule fields(6))
  show "inj f" unfolding f_def by (rule isabelle_state_embedding_injective) (use fields(7) in blast)
qed

text \<open>
  A refusal is not a failure of the verdict: an answer that states its subject through a constant
  the state does not know adds a declaration and exceeds the support, and the verdict names that
  constant. The constant becomes the subject of a definition problem and the request is issued
  again with the extended support, through the same process; the verdict itself grants nothing.
\<close>

section \<open>An answer names its request through the subject's name\<close>

text \<open>
  An executor's answer names the request it answers by the name of the subject constant, the
  kernel's identity of that constant. The name is read in the table of the requested state, and
  the request is the single request whose subject is that position; a name the table does not
  hold, or several requests of one subject, select no request.
\<close>

definition development_named_request ::
    "isabelle_context \<Rightarrow> development_request list \<Rightarrow> String.literal \<Rightarrow> development_request option" where
  "development_named_request C rs n=(case isabelle_name_position (fst C) n of None \<Rightarrow> None
    | Some c \<Rightarrow> list_singleton_option (filter (\<lambda>r. problem_subject (fst r)={|c|}) rs))"

text \<open>A request read by its name is one of the requests it is read among.\<close>

lemma development_named_request_member:
  assumes "development_named_request C rs n=Some r"
  shows "r\<in>set rs"
proof -
  obtain d where "set (filter (\<lambda>q. problem_subject (fst q)={|d|}) rs)={r}"
    using assms by (auto simp: development_named_request_def list_singleton_option_some split: option.splits)
  then show ?thesis by (metis filter_is_subset insertI1 subsetD)
qed

definition development_verdict_counts :: "development_constant_verdict \<Rightarrow> nat list" where
  "development_verdict_counts v=(case v of
    (removed,added,unpermitted_removed,unpermitted_added,statements,excess,assessment,roots,tables) \<Rightarrow>
      [length removed,length added,length unpermitted_removed,length unpermitted_added,length statements])"

definition development_verdict_excess :: "development_constant_verdict \<Rightarrow> nat list" where
  "development_verdict_excess v=(case v of
    (removed,added,unpermitted_removed,unpermitted_added,statements,excess,assessment,roots,tables) \<Rightarrow> excess)"

definition development_verdict_data :: "development_constant_verdict \<Rightarrow> finite_factor_term" where
  "development_verdict_data=
    finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_position_data)
    (finite_pair_presentation isabelle_context_assessment_data
    (finite_pair_presentation finite_boolean_data finite_boolean_data)))))))"

lemma development_verdict_data_injective [intro]: "inj development_verdict_data"
  unfolding development_verdict_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    isabelle_entity_data_injective isabelle_position_data_injective
    isabelle_context_assessment_data_injective finite_boolean_data_injective)

end
