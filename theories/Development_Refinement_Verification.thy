theory Development_Refinement_Verification
  imports Development_Constant_Verification
begin

section \<open>A refinement answer replaces the code equations of its constant\<close>

text \<open>
  A refinement may replace the code equations of its subject and nothing else, and it must state
  one. Its verdict is the verdict of an answer to a problem of a constant under the code-equation
  reading, both for what it may replace and for what it must state; the statements below are the
  instances the requests, the repair and the successor read, and the contract of an accepted
  refinement is the instance of the general contract.
\<close>

definition development_answer_equation :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "development_answer_equation=development_answer_statement (development_demanded isabelle_code_equation_proposition)"

lemma development_answer_equation_exact:
  "development_answer_equation C P e \<longleftrightarrow> isabelle_code_equation_proposition e\<noteq>None \<and>
    list_ex (\<lambda>c. c |\<in>| P) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"
  by (simp only: development_answer_equation_def development_answer_statement_def development_demanded_def)

definition development_answer_equations :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> isabelle_entity list" where
  "development_answer_equations=development_answer_statements
    (development_demanded isabelle_code_equation_proposition)"

lemma development_answer_equations_exact:
  "development_answer_equations C P=filter (development_answer_equation C P) (snd C)"
  by (simp only: development_answer_equations_def development_answer_statements_def
    development_answer_equation_def)

definition development_answer_excess :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> nat fset \<Rightarrow> nat list" where
  "development_answer_excess=development_answer_statements_excess
    (development_demanded isabelle_code_equation_proposition)"

definition development_refinement_verdict ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow>
      development_constant_verdict" where
  "development_refinement_verdict=development_constant_verdict
    (development_demanded isabelle_code_equation_proposition)
    (development_demanded isabelle_code_equation_proposition)"

section \<open>An accepted verdict is the local contract of the answer\<close>

text \<open>
  An accepted refinement verdict states exactly what the request demanded of the answer state:
  every entity other than the subject's code equations and the declarations persists under the
  correspondence, nothing but code equations of the subject is added, the subject has an
  equation, every equation of the subject stays within the issued support, the answer state is
  closed and keeps the roots, and the correspondence is injective. These are the general contract
  read through the code-equation instance; nothing is proved again.
\<close>

theorem development_refinement_verdict_contract:
  assumes accepted: "development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
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
  using development_constant_verdict_contract[OF accepted[unfolded development_refinement_verdict_def]]
  unfolding f_def development_answer_equation_def by blast+

end
