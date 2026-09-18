theory Development_Refinement_Verification
  imports Development_Requests Isabelle_State_Difference
begin

section \<open>A refinement answer is judged by the difference it makes to the requested state\<close>

text \<open>
  An answer to a refinement request is read as the state of the checked context that contains
  it, exported from the same roots by the same exporter. The verdict never constructs an
  answer: it reads the difference between the state the request was made against and the
  answer state, through the names both tables share. A refinement may replace the code
  equations of its subject and nothing else; declarations may disappear only when nothing
  mentions their constants any more, which the closure of the answer state decides. Every
  equation the answer states for its subject must mention only constants of the issued
  support, and the answer state must be closed and keep the roots of the request.
\<close>

definition development_answer_equation :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "development_answer_equation C P e \<longleftrightarrow> isabelle_code_equation_proposition e\<noteq>None \<and>
    list_ex (\<lambda>c. c |\<in>| P) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"

definition development_answer_equations :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity list" where
  "development_answer_equations C P=filter (development_answer_equation C P) (snd C)"

definition development_answer_excess :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> nat fset \<Rightarrow> nat list" where
  "development_answer_excess C P S=remdups (filter (\<lambda>d. d |\<notin>| S)
    (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition)
      (development_answer_equations C P))))"

definition isabelle_assessment_closed :: "isabelle_context_assessment \<Rightarrow> bool" where
  "isabelle_assessment_closed a \<longleftrightarrow> (case a of (unknown,undeclared,malformed,unreached,frontier) \<Rightarrow>
    unknown={||} \<and> undeclared={||} \<and> malformed={||} \<and> unreached={||})"

type_synonym development_refinement_verdict =
  "isabelle_entity list\<times>isabelle_entity list\<times>isabelle_entity list\<times>isabelle_entity list\<times>
    isabelle_entity list\<times>nat list\<times>isabelle_context_assessment\<times>bool\<times>bool"

text \<open>
  The verdict retains the whole difference, the parts of it a refinement does not permit, the
  equations the answer states for the subject, the constants they mention outside the support,
  the assessment of the answer state, whether the roots are kept and whether both tables are
  free of repeated names. Nothing is summarized away: a refusal carries its reasons.
\<close>

definition development_refinement_verdict ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_refinement_verdict" where
  "development_refinement_verdict S r S'=(case r of (p,s,support,E) \<Rightarrow>
    let C=snd S; C'=snd S'; f=isabelle_state_embedding (fst C) (fst C');
      P=problem_subject p; P'=fimage f P; removed=isabelle_state_removed C C';
      added=isabelle_state_added C C' in
    (removed,added,
     filter (\<lambda>e. \<not>development_answer_equation C P e \<and> isabelle_declared_constant e=None) removed,
     filter (\<lambda>e. \<not>development_answer_equation C' P' e) added,
     development_answer_equations C' P',
     development_answer_excess C' P' (fimage f support),
     isabelle_context_assessment (fst S') C',
     map (isabelle_term_rename f) (fst S)=fst S',
     distinct (fst C) \<and> distinct (fst C')))"

definition development_refinement_accepted :: "development_refinement_verdict \<Rightarrow> bool" where
  "development_refinement_accepted v \<longleftrightarrow> (case v of
    (removed,added,unpermitted_removed,unpermitted_added,equations,excess,assessment,roots,tables) \<Rightarrow>
      unpermitted_removed=[] \<and> unpermitted_added=[] \<and> equations\<noteq>[] \<and> excess=[] \<and>
      isabelle_assessment_closed assessment \<and> roots \<and> tables)"

section \<open>An accepted verdict is the local contract of the answer\<close>

text \<open>
  An accepted verdict states exactly what the request demanded of the answer state: every
  entity other than the subject's code equations and the declarations persists under the
  correspondence, nothing but code equations of the subject is added, the subject has an
  equation, every equation of the subject stays within the issued support, the answer state
  is closed and keeps the roots, and the correspondence is injective. A use of an accepted
  answer consumes these conclusions; none of them is established again.
\<close>

theorem development_refinement_verdict_contract:
  assumes accepted: "development_refinement_accepted (development_refinement_verdict S (p,s,support,E) S')"
  defines "f\<equiv>isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  shows "\<And>e. e\<in>set (snd (snd S)) \<Longrightarrow> \<not>development_answer_equation (snd S) (problem_subject p) e \<Longrightarrow>
      isabelle_declared_constant e=None \<Longrightarrow> isabelle_entity_rename f e\<in>set (snd (snd S'))"
    and "\<And>e'. e'\<in>set (snd (snd S')) \<Longrightarrow>
      (\<exists>e\<in>set (snd (snd S)). e'=isabelle_entity_rename f e) \<or>
      development_answer_equation (snd S') (fimage f (problem_subject p)) e'"
    and "\<exists>e'\<in>set (snd (snd S')). development_answer_equation (snd S') (fimage f (problem_subject p)) e'"
    and "\<And>e' q d. e'\<in>set (snd (snd S')) \<Longrightarrow> development_answer_equation (snd S') (fimage f (problem_subject p)) e' \<Longrightarrow>
      isabelle_specified_proposition e'=Some q \<Longrightarrow> d\<in>set (isabelle_term_constants q) \<Longrightarrow> d |\<in>| fimage f support"
    and "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))"
    and "map (isabelle_term_rename f) (fst S)=fst S'"
    and "inj f"
proof -
  let ?C="snd S" and ?C'="snd S'" and ?P="problem_subject p"
  let ?P'="fimage f ?P"
  have fields: "filter (\<lambda>e. \<not>development_answer_equation ?C ?P e \<and> isabelle_declared_constant e=None)
        (isabelle_state_removed ?C ?C')=[]"
      "filter (\<lambda>e. \<not>development_answer_equation ?C' ?P' e) (isabelle_state_added ?C ?C')=[]"
      "development_answer_equations ?C' ?P'\<noteq>[]"
      "development_answer_excess ?C' ?P' (fimage f support)=[]"
      "isabelle_assessment_closed (isabelle_context_assessment (fst S') ?C')"
      "map (isabelle_term_rename f) (fst S)=fst S'"
      "distinct (fst ?C) \<and> distinct (fst ?C')"
    using accepted by (simp_all add: development_refinement_accepted_def development_refinement_verdict_def
      f_def Let_def)
  show "isabelle_entity_rename f e\<in>set (snd ?C')" if member: "e\<in>set (snd ?C)"
      and other: "\<not>development_answer_equation ?C ?P e" and undeclared: "isabelle_declared_constant e=None" for e
  proof (rule ccontr)
    assume "isabelle_entity_rename f e\<notin>set (snd ?C')"
    then have "e\<in>set (isabelle_state_removed ?C ?C')"
      using member by (simp add: isabelle_state_removed_exact f_def)
    then show False using fields(1) other undeclared by (auto simp: filter_empty_conv)
  qed
  show "(\<exists>e\<in>set (snd ?C). e'=isabelle_entity_rename f e) \<or> development_answer_equation ?C' ?P' e'"
    if member: "e'\<in>set (snd ?C')" for e'
  proof (cases "e'\<in>set (isabelle_state_added ?C ?C')")
    case True
    then show ?thesis using fields(2) by (auto simp: filter_empty_conv)
  next
    case False
    then show ?thesis using member by (auto simp: isabelle_state_added_exact f_def)
  qed
  show "\<exists>e'\<in>set (snd ?C'). development_answer_equation ?C' ?P' e'"
    using fields(3) by (auto simp: development_answer_equations_def filter_empty_conv)
  show "d |\<in>| fimage f support"
    if member: "e'\<in>set (snd ?C')" and answer: "development_answer_equation ?C' ?P' e'"
      and statement: "isabelle_specified_proposition e'=Some q" and mentioned: "d\<in>set (isabelle_term_constants q)"
    for e' q d
  proof (rule ccontr)
    assume outside: "d |\<notin>| fimage f support"
    have "e'\<in>set (development_answer_equations ?C' ?P')"
      using member answer by (simp add: development_answer_equations_def)
    then have "isabelle_term_constants q\<in>set (List.map_filter
        (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) (development_answer_equations ?C' ?P'))"
      using statement by (auto simp: map_filter_member)
    then have "d\<in>set (development_answer_excess ?C' ?P' (fimage f support))"
      using mentioned outside by (auto simp: development_answer_excess_def)
    then show False using fields(4) by simp
  qed
  show "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))" by (rule fields(5))
  show "map (isabelle_term_rename f) (fst S)=fst S'" by (rule fields(6))
  show "inj f" unfolding f_def by (rule isabelle_state_embedding_injective) (use fields(7) in blast)
qed

text \<open>
  A refusal is not a failure of the verdict: an answer that states its equation through a
  constant the state does not know adds a declaration and exceeds the support, and the verdict
  names that constant. The constant becomes the subject of a definition problem and the request
  is issued again with the extended support, through the same process; the verdict itself
  grants nothing.
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

definition development_refinement_verdict_counts :: "development_refinement_verdict \<Rightarrow> nat list" where
  "development_refinement_verdict_counts v=(case v of
    (removed,added,unpermitted_removed,unpermitted_added,equations,excess,assessment,roots,tables) \<Rightarrow>
      [length removed,length added,length unpermitted_removed,length unpermitted_added,length equations])"

definition development_refinement_verdict_excess :: "development_refinement_verdict \<Rightarrow> nat list" where
  "development_refinement_verdict_excess v=(case v of
    (removed,added,unpermitted_removed,unpermitted_added,equations,excess,assessment,roots,tables) \<Rightarrow> excess)"

definition development_refinement_verdict_data :: "development_refinement_verdict \<Rightarrow> finite_factor_term" where
  "development_refinement_verdict_data=
    finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_position_data)
    (finite_pair_presentation isabelle_context_assessment_data
    (finite_pair_presentation finite_boolean_data finite_boolean_data)))))))"

lemma development_refinement_verdict_data_injective [intro]: "inj development_refinement_verdict_data"
  unfolding development_refinement_verdict_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    isabelle_entity_data_injective isabelle_position_data_injective
    isabelle_context_assessment_data_injective finite_boolean_data_injective)

end
