theory Development_Constant_Problems
  imports Isabelle_Code_Equations Development_Problems Filtered_Native_Questions
    Finite_Singleton_Selection "HOL-Library.Parallel"
begin

section \<open>Selecting from a list by an optional reading\<close>

text \<open>
  Every selection below reads each element of an actual list and keeps the results the
  reading returns. Its membership is the library's optional image of that reading, so the
  argument is instantiated once here and never repeated in the selections that follow.
\<close>

lemma map_filter_member:
  "y\<in>set (List.map_filter f xs) \<longleftrightarrow> (\<exists>x\<in>set xs. f x=Some y)"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

section \<open>A problem of a constant reads one kind of its statements\<close>

text \<open>
  A problem of a constant is about that constant, and what its answer must establish is one
  kind of statement the state makes of it. Two readings carry that, and they are kept apart.
  The scope of a constant is the entities the state presents about it, read by the existing
  subject reading; it fixes what the problem is about. Which entities of that scope the
  problem demands is read by one reading of the entity language: a refinement reads the code
  equations it replaces, a definition reads the kernel definitions. A definition and a code
  equation of one constant have the same subjects, so only the reading tells the two kinds of
  problem apart. Neither reading is supplied: both are computed on the actual entities of the
  state, and every construction below takes the reading as a parameter, so it is stated once
  for every kind of problem of a constant.
\<close>

definition development_constant_scope ::
    "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_entity list" where
  "development_constant_scope C c=filter
    (\<lambda>e. c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))
    (snd C)"

lemma development_constant_scope_member:
  "e\<in>set (development_constant_scope C c) \<longleftrightarrow> e\<in>set (snd C) \<and>
    c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"
  by (simp add: development_constant_scope_def)

definition development_demanded ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "development_demanded reading e \<longleftrightarrow> reading e\<noteq>None"

definition development_statements ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_term list" where
  "development_statements reading C c=List.map_filter reading (development_constant_scope C c)"

theorem development_statements_exact:
  "p\<in>set (development_statements reading C c) \<longleftrightarrow>
    (\<exists>e\<in>set (development_constant_scope C c). reading e=Some p)"
  by (simp only: development_statements_def map_filter_member)

theorem development_statements_demanded:
  "p\<in>set (development_statements reading C c) \<longleftrightarrow>
    (\<exists>e\<in>set (development_constant_scope C c). development_demanded reading e \<and> reading e=Some p)"
  by (auto simp: development_statements_exact development_demanded_def)

text \<open>
  The code-equation reading and the definition reading separate the two kinds of statement
  within one scope: each demands its own kind and refuses the other, and both refuse
  declarations and specifications.
\<close>

theorem development_readings_separate:
  assumes equation: "Isabelle_Code_Equation p\<in>set (snd C)"
    and kernel: "Isabelle_Definition p\<in>set (snd C)"
    and subject: "c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C))
      (Isabelle_Code_Equation p))"
  shows "Isabelle_Code_Equation p\<in>set (development_constant_scope C c) \<and>
    Isabelle_Definition p\<in>set (development_constant_scope C c) \<and>
    development_demanded isabelle_code_equation_proposition (Isabelle_Code_Equation p) \<and>
    \<not>development_demanded isabelle_code_equation_proposition (Isabelle_Definition p) \<and>
    development_demanded isabelle_definition_proposition (Isabelle_Definition p) \<and>
    \<not>development_demanded isabelle_definition_proposition (Isabelle_Code_Equation p)"
  using assms by (simp add: development_constant_scope_member development_demanded_def)

lemma development_readings_refuse_other_kinds:
  "\<not>development_demanded isabelle_code_equation_proposition (Isabelle_Development_Constant t)"
  "\<not>development_demanded isabelle_code_equation_proposition (Isabelle_Specification p)"
  "\<not>development_demanded isabelle_definition_proposition (Isabelle_Development_Constant t)"
  "\<not>development_demanded isabelle_definition_proposition (Isabelle_Specification p)"
  by (simp_all add: development_demanded_def)

section \<open>The contract of a problem of a constant is the constant as the state declares it\<close>

text \<open>
  A problem of a constant is fixed by its constant: an answer establishes new statements of
  that constant, and the statements it replaces are what the state already states of it, not
  a term the answer must establish. The contract is therefore the constant as the state
  declares it, a term of the state's table with its declared type, marked with the kind of
  problem; the incumbent is the whole family of demanded statements, read from the scope and
  never chosen among. The constant is recognized by the existing singleton reading of its
  declarations, so a repeated declaration is still one and distinct declarations are refused
  rather than resolved by position. A constant the state declares other than exactly once, or
  of which it states no demanded statement, is not stated and has no contract; it is retained
  instead. Because the contract names the constant and not its current statements, the problem
  keeps its identity when an adopted answer replaces them, and because the kind is part of the
  contract, a refinement and a definition of one constant are different problems.
\<close>

definition development_constant_declarations :: "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_term list" where
  "development_constant_declarations C c=List.map_filter
    (\<lambda>e. if isabelle_declared_constant e=Some c then isabelle_declaration_term e else None) (snd C)"

lemma development_constant_declarations_member:
  "t\<in>set (development_constant_declarations C c) \<longleftrightarrow>
    (\<exists>e\<in>set (snd C). isabelle_declared_constant e=Some c \<and> isabelle_declaration_term e=Some t)"
  by (simp only: development_constant_declarations_def map_filter_member) (auto split: if_splits)

definition development_stated_constant ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_term option" where
  "development_stated_constant reading C c=(if development_statements reading C c=[] then None
    else list_singleton_option (development_constant_declarations C c))"

theorem development_stated_constant_exact:
  "development_stated_constant reading C c=Some t \<longleftrightarrow>
    set (development_constant_declarations C c)={t} \<and> development_statements reading C c\<noteq>[]"
  by (cases "development_statements reading C c=[]")
    (simp_all add: development_stated_constant_def list_singleton_option_some)

corollary development_stated_constant_declared:
  assumes "development_stated_constant reading C c=Some t"
  shows "(\<exists>e\<in>set (snd C). isabelle_declared_constant e=Some c \<and> isabelle_declaration_term e=Some t) \<and>
    development_statements reading C c\<noteq>[]"
proof -
  have single: "set (development_constant_declarations C c)={t}"
    and stated: "development_statements reading C c\<noteq>[]"
    using assms by (simp_all add: development_stated_constant_exact)
  have "t\<in>set (development_constant_declarations C c)" by (simp only: single) simp
  then show ?thesis using stated by (simp only: development_constant_declarations_member) blast
qed

lemma development_stated_constant_unstated:
  assumes "development_statements reading C c=[] \<or>
    (\<nexists>t. set (development_constant_declarations C c)={t})"
  shows "development_stated_constant reading C c=None"
proof (rule ccontr)
  assume "development_stated_constant reading C c\<noteq>None"
  then obtain t where "development_stated_constant reading C c=Some t" by auto
  then have "set (development_constant_declarations C c)={t}"
    and "development_statements reading C c\<noteq>[]"
    by (simp_all add: development_stated_constant_exact)
  then show False using assms by blast
qed

definition development_constant_contract ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> development_contract) \<Rightarrow>
      isabelle_context \<Rightarrow> nat \<Rightarrow> development_contract option" where
  "development_constant_contract reading kind C c=map_option kind (development_stated_constant reading C c)"

theorem development_constant_contract_exact:
  "development_constant_contract reading kind C c=Some k \<longleftrightarrow>
    (\<exists>t. k=kind t \<and> set (development_constant_declarations C c)={t} \<and>
      development_statements reading C c\<noteq>[])"
  by (auto simp: development_constant_contract_def development_stated_constant_exact map_option_eq_Some)

section \<open>The incumbent is the admitted answer of a native question on the constant's scope\<close>

text \<open>
  The candidates of the question are the entities of the constant's own scope and its single
  original condition is the demand of the reading, so the existing filtered question contract
  applies without restating it. Admission establishes the demand at every admitted entity,
  and the admitted entity's statement is one of the demanded statements: the question admits
  every entity of the scope the reading demands, which is the incumbent family of the problem.
  Ranging the candidates over the whole entity list instead would conflate what the problem is
  about with what its answer must establish, and would submit every entity of the state to a
  question about one constant.
\<close>

definition development_constant_question ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat \<Rightarrow>
      native_development_question option" where
  "development_constant_question reading C c=filtered_development_question
    (development_constant_scope C c) (development_demanded reading)"

theorem development_constant_admission:
  assumes question: "development_constant_question reading C c=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  shows "i<length (development_constant_scope C c) \<and>
    development_demanded reading (development_constant_scope C c!i)"
  by (rule filtered_development_admission[OF question[unfolded development_constant_question_def]
    admission selected])

theorem development_constant_admitted_statement:
  assumes question: "development_constant_question reading C c=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  obtains p where "reading (development_constant_scope C c!i)=Some p"
    "p\<in>set (development_statements reading C c)"
proof -
  have condition: "i<length (development_constant_scope C c)"
      "development_demanded reading (development_constant_scope C c!i)"
    using development_constant_admission[OF assms] by simp_all
  obtain p where read: "reading (development_constant_scope C c!i)=Some p"
    using condition(2) by (auto simp: development_demanded_def)
  have "p\<in>set (development_statements reading C c)"
    by (simp only: development_statements_exact) (use read nth_mem[OF condition(1)] in blast)
  then show thesis by (rule that[OF read])
qed

text \<open>
  The contract decisions of a list of constants are these questions executed by their native
  producer and checked by their admission, each as its packet of question, report and
  admission; the constants are independent, so the questions are executed in parallel and the
  list keeps their order.
\<close>

definition development_contract_packets ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat list \<Rightarrow>
      (native_development_question\<times>native_development_report\<times>finite_factor_term list option) option list" where
  "development_contract_packets reading C cs=Parallel.map (\<lambda>c. map_option native_development_packet
    (development_constant_question reading C c)) cs"

section \<open>Problems and their dependencies are computed from the same state\<close>

text \<open>
  A problem of a constant carries that constant as its subject and the constant as the state
  declares it, marked with the problem's kind, as its contract; a constant with no contract
  yields no problem. The origin and authority are supplied by the use, not by this
  construction. A problem depends on the problems of the other constants of the given scope
  that its own demanded statements mention, which is read from the statements rather than
  from a grouping: the mentioned constant is the premise slot, so distinct constants occupy
  distinct slots and no list order enters.
\<close>

definition development_constant_problem ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> development_contract) \<Rightarrow>
      isabelle_context \<Rightarrow> development_origin \<Rightarrow> development_authority \<Rightarrow> nat \<Rightarrow>
      development_problem option" where
  "development_constant_problem reading kind C r a c=map_option
    (\<lambda>k. Development_Problem {|c|} k r a) (development_constant_contract reading kind C c)"

lemma development_constant_problem_subject:
  assumes "development_constant_problem reading kind C r a c=Some p"
  shows "problem_subject p={|c|}"
  using assms by (auto simp: development_constant_problem_def)

lemma development_constant_problem_injective:
  assumes first: "development_constant_problem reading kind C r a c=Some p"
    and second: "development_constant_problem reading kind C r a d=Some p"
  shows "c=d"
proof -
  have subjects: "{|c|}={|d|}"
    using development_constant_problem_subject[OF first]
      development_constant_problem_subject[OF second] by simp
  have "c |\<in>| {|c|}" by simp
  then have "c |\<in>| {|d|}" by (simp only: subjects)
  then show "c=d" by simp
qed

definition development_constant_mentions ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "development_constant_mentions reading C cs c=remdups (filter (\<lambda>d. d\<in>set cs \<and> d\<noteq>c)
    (concat (map isabelle_term_constants (development_statements reading C c))))"

theorem development_constant_mentions_exact:
  "d\<in>set (development_constant_mentions reading C cs c) \<longleftrightarrow>
    d\<in>set cs \<and> d\<noteq>c \<and> (\<exists>p\<in>set (development_statements reading C c).
      d\<in>set (isabelle_term_constants p))"
  by (auto simp: development_constant_mentions_def)

definition development_constant_premises ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> development_contract) \<Rightarrow>
      isabelle_context \<Rightarrow> development_origin \<Rightarrow> development_authority \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
      (nat\<times>development_problem) fset" where
  "development_constant_premises reading kind C r a cs c=fset_of_list (List.map_filter
    (\<lambda>d. map_option (Pair d) (development_constant_problem reading kind C r a d))
    (development_constant_mentions reading C cs c))"

definition development_constant_dependencies ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> development_contract) \<Rightarrow>
      isabelle_context \<Rightarrow> development_origin \<Rightarrow> development_authority \<Rightarrow> nat list \<Rightarrow>
      development_dependencies" where
  "development_constant_dependencies reading kind C r a cs=fset_of_list (List.map_filter
    (\<lambda>c. map_option (\<lambda>p. (p,development_constant_premises reading kind C r a cs c))
      (development_constant_problem reading kind C r a c)) cs)"

definition development_constant_problems ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> development_contract) \<Rightarrow>
      isabelle_context \<Rightarrow> development_origin \<Rightarrow> development_authority \<Rightarrow> nat list \<Rightarrow>
      development_problem list" where
  "development_constant_problems reading kind C r a cs=List.map_filter
    (development_constant_problem reading kind C r a) cs"

definition development_constant_unstated ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat list \<Rightarrow> nat fset" where
  "development_constant_unstated reading C cs=fset_of_list
    (filter (\<lambda>c. development_stated_constant reading C c=None) cs)"

theorem development_constant_problems_exact:
  "p\<in>set (development_constant_problems reading kind C r a cs) \<longleftrightarrow>
    (\<exists>c\<in>set cs. development_constant_problem reading kind C r a c=Some p)"
  by (simp only: development_constant_problems_def map_filter_member)

theorem development_constant_unstated_exact:
  "c |\<in>| development_constant_unstated reading C cs \<longleftrightarrow>
    c\<in>set cs \<and> development_constant_problem reading kind C r a c=None"
  by (auto simp: development_constant_unstated_def development_constant_problem_def
    development_constant_contract_def fset_of_list_elem)

text \<open>
  Each problem in scope contributes exactly one decomposition, namely the premises computed
  from its own statements. Two constants in scope never yield one problem, so the
  decompositions of a problem are not joined and the state reports no ambiguity that the
  computation did not find.
\<close>

theorem development_constant_decomposition_exact:
  assumes problem: "development_constant_problem reading kind C r a c=Some p" and scope: "c\<in>set cs"
  shows "development_decompositions (development_constant_dependencies reading kind C r a cs) p=
    {|development_constant_premises reading kind C r a cs c|}"
proof -
  let ?entry="\<lambda>c. map_option (\<lambda>p. (p,development_constant_premises reading kind C r a cs c))
    (development_constant_problem reading kind C r a c)"
  have member: "(q,H) |\<in>| development_constant_dependencies reading kind C r a cs \<longleftrightarrow>
      (\<exists>d\<in>set cs. ?entry d=Some (q,H))" for q H
    by (simp only: development_constant_dependencies_def fset_of_list_elem map_filter_member)
  have selected: "(q,H) |\<in>| development_constant_dependencies reading kind C r a cs \<and> q=p \<longleftrightarrow>
      q=p \<and> H=development_constant_premises reading kind C r a cs c" for q H
  proof
    assume "(q,H) |\<in>| development_constant_dependencies reading kind C r a cs \<and> q=p"
    then obtain d where inside: "d\<in>set cs" and entry: "?entry d=Some (q,H)" and equal: "q=p"
      using member by blast
    have found: "development_constant_problem reading kind C r a d=Some q"
      and computed: "H=development_constant_premises reading kind C r a cs d"
      using entry by (auto split: option.splits)
    have "d=c" using development_constant_problem_injective[OF found[unfolded equal] problem] .
    then show "q=p \<and> H=development_constant_premises reading kind C r a cs c" using equal computed by simp
  next
    assume "q=p \<and> H=development_constant_premises reading kind C r a cs c"
    then show "(q,H) |\<in>| development_constant_dependencies reading kind C r a cs \<and> q=p"
      using member[of q H] problem scope by auto
  qed
  have rows: "ffilter (\<lambda>(q,H). q=p) (development_constant_dependencies reading kind C r a cs)=
      {|(p,development_constant_premises reading kind C r a cs c)|}"
    by (rule fset_eqI) (use selected in \<open>auto split: prod.splits\<close>)
  show ?thesis by (simp only: development_decompositions_def rows) simp
qed

corollary development_constant_premises_exact:
  assumes problem: "development_constant_problem reading kind C r a c=Some p" and scope: "c\<in>set cs"
  shows "development_premises (development_constant_dependencies reading kind C r a cs) p=
    fimage snd (development_constant_premises reading kind C r a cs c)"
proof (rule fset_eqI)
  fix q
  show "q |\<in>| development_premises (development_constant_dependencies reading kind C r a cs) p \<longleftrightarrow>
      q |\<in>| fimage snd (development_constant_premises reading kind C r a cs c)"
    by (simp only: development_premises_member
      development_constant_decomposition_exact[OF problem scope]) simp
qed

corollary development_constant_not_ambiguous:
  assumes problem: "development_constant_problem reading kind C r a c=Some p" and scope: "c\<in>set cs"
  shows "p\<notin>set (development_ambiguous (development_constant_dependencies reading kind C r a cs) ps)"
proof -
  have single: "fcard (development_decompositions (development_constant_dependencies reading kind C r a cs) p)=1"
    by (simp only: development_constant_decomposition_exact[OF problem scope] fcard_finsert_if) simp
  show ?thesis by (simp add: development_ambiguous_def single)
qed

end
