theory Development_Refinement_Contracts
  imports Isabelle_Code_Equations Development_Problems Filtered_Native_Questions
    Finite_Singleton_Selection
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

section \<open>The contract of a refinement is a code equation of its subject\<close>

text \<open>
  A problem's contract is the term its answer must establish. A refinement replaces the
  executable content of one constant, so the term it must establish is a code equation of
  that constant in the state it is made against.

  Two readings carry that, and they are kept apart. The scope of a constant is the entities
  the state presents about it, read by the existing subject reading; it fixes what the
  problem is about. What a refinement demands of an entity of that scope is read separately
  by the code-equation reading. A kernel definition of the constant is in the same scope,
  because it has the same subject, and is refused by the demand, because a refinement does
  not replace a definition. Neither reading is supplied: both are computed on the actual
  entities of the state.
\<close>

definition development_refinement_scope ::
    "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_entity list" where
  "development_refinement_scope C c=filter
    (\<lambda>e. c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))
    (snd C)"

definition development_refinement_demanded :: "isabelle_entity \<Rightarrow> bool" where
  "development_refinement_demanded e \<longleftrightarrow> isabelle_code_equation_proposition e\<noteq>None"

lemma development_refinement_scope_member:
  "e\<in>set (development_refinement_scope C c) \<longleftrightarrow> e\<in>set (snd C) \<and>
    c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"
  by (simp add: development_refinement_scope_def)

definition development_refinement_statements :: "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_term list" where
  "development_refinement_statements C c=List.map_filter isabelle_code_equation_proposition
    (development_refinement_scope C c)"

theorem development_refinement_statements_exact:
  "p\<in>set (development_refinement_statements C c) \<longleftrightarrow>
    Isabelle_Code_Equation p\<in>set (development_refinement_scope C c)"
  by (simp only: development_refinement_statements_def map_filter_member
    isabelle_code_equation_proposition_exact) blast

corollary development_refinement_statements_state:
  "p\<in>set (development_refinement_statements C c) \<longleftrightarrow>
    Isabelle_Code_Equation p\<in>set (snd C) \<and>
    c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C))
      (Isabelle_Code_Equation p))"
  by (simp only: development_refinement_statements_exact development_refinement_scope_member)

theorem development_refinement_statements_demanded:
  "p\<in>set (development_refinement_statements C c) \<longleftrightarrow>
    (\<exists>e\<in>set (development_refinement_scope C c).
      development_refinement_demanded e \<and> isabelle_code_equation_proposition e=Some p)"
  by (simp only: development_refinement_statements_def map_filter_member
    development_refinement_demanded_def) auto

text \<open>
  A definition and a code equation of one constant have the same subjects, so only the
  entity kind separates the two demands. Both statements are computed on the actual state;
  neither is supplied.
\<close>

theorem development_refinement_separates_definition:
  assumes equation: "Isabelle_Code_Equation p\<in>set (snd C)"
    and kernel: "Isabelle_Definition p\<in>set (snd C)" and subject: "c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C))
      (Isabelle_Code_Equation p))"
  shows "Isabelle_Code_Equation p\<in>set (development_refinement_scope C c) \<and>
    Isabelle_Definition p\<in>set (development_refinement_scope C c) \<and>
    development_refinement_demanded (Isabelle_Code_Equation p) \<and>
    \<not>development_refinement_demanded (Isabelle_Definition p)"
  using assms by (simp add: development_refinement_scope_member development_refinement_demanded_def)

lemma development_refinement_refuses_declaration:
  "\<not>development_refinement_demanded (Isabelle_Development_Constant t)"
  by (simp add: development_refinement_demanded_def)

lemma development_refinement_refuses_specification:
  "\<not>development_refinement_demanded (Isabelle_Specification p)"
  by (simp add: development_refinement_demanded_def)

section \<open>A demanded statement is selected only when the state states exactly one\<close>

text \<open>
  The contract is the state's single demanded statement for the constant, recognized by the
  existing singleton reading: the same statement presented twice is still one statement, and
  no position of the entity list decides the contract. A constant the state states more than
  one distinct statement for, or none, has no contract, and the state retains that absence
  instead of taking one of them.
\<close>

definition development_refinement_contract ::
    "isabelle_context \<Rightarrow> nat \<Rightarrow> development_contract option" where
  "development_refinement_contract C c=map_option Development_Refinement
    (list_singleton_option (development_refinement_statements C c))"

theorem development_refinement_contract_exact:
  "development_refinement_contract C c=Some k \<longleftrightarrow>
    (\<exists>p. k=Development_Refinement p \<and> set (development_refinement_statements C c)={p})"
  by (auto simp: development_refinement_contract_def list_singleton_option_some
    split: option.splits)

lemma development_refinement_contract_refuses_ambiguity:
  assumes "\<nexists>p. set (development_refinement_statements C c)={p}"
  shows "development_refinement_contract C c=None"
proof (rule ccontr)
  assume "development_refinement_contract C c\<noteq>None"
  then obtain k where "development_refinement_contract C c=Some k" by auto
  then obtain p where "set (development_refinement_statements C c)={p}"
    by (simp only: development_refinement_contract_exact) auto
  then show False using assms by blast
qed

corollary development_refinement_contract_statement:
  assumes "development_refinement_contract C c=Some (Development_Refinement p)"
  shows "Isabelle_Code_Equation p\<in>set (snd C) \<and>
    c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C))
      (Isabelle_Code_Equation p))"
proof -
  have single: "set (development_refinement_statements C c)={p}"
    using assms by (simp only: development_refinement_contract_exact) auto
  have "p\<in>set (development_refinement_statements C c)" by (simp only: single) simp
  then show ?thesis by (simp only: development_refinement_statements_state)
qed

section \<open>The selection is the admitted answer of a native question on the actual state\<close>

text \<open>
  The candidates of the question are the entities of the constant's own scope and its single
  original condition is the computed demand, so the existing filtered question contract
  applies without restating it. Admission establishes the demand at every admitted entity,
  and the admitted entity's proposition is one of the demanded statements. The question
  admits every entity of the scope satisfying the demand; the contract is obtained only when
  that is exactly one. Ranging the candidates over the whole entity list instead would
  conflate what the problem is about with what its answer must establish, and would submit
  every entity of the state to a question about one constant.
\<close>

definition development_refinement_question where
  "development_refinement_question C c=filtered_development_question
    (development_refinement_scope C c) development_refinement_demanded"

theorem development_refinement_admission:
  assumes question: "development_refinement_question C c=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  shows "i<length (development_refinement_scope C c) \<and>
    development_refinement_demanded (development_refinement_scope C c!i)"
  by (rule filtered_development_admission[OF question[unfolded development_refinement_question_def]
    admission selected])

theorem development_refinement_admitted_statement:
  assumes question: "development_refinement_question C c=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "finite_development_index i\<in>set accepted"
  obtains p where "development_refinement_scope C c!i=Isabelle_Code_Equation p"
    "p\<in>set (development_refinement_statements C c)"
proof -
  have condition: "i<length (development_refinement_scope C c)"
      "development_refinement_demanded (development_refinement_scope C c!i)"
    using development_refinement_admission[OF assms] by simp_all
  obtain p where equation: "development_refinement_scope C c!i=Isabelle_Code_Equation p"
    using condition(2) by (cases "development_refinement_scope C c!i")
      (auto simp: development_refinement_demanded_def)
  have present: "Isabelle_Code_Equation p\<in>set (development_refinement_scope C c)"
    using nth_mem[OF condition(1)] by (simp only: equation)
  show thesis
    by (rule that[OF equation])
      (simp only: development_refinement_statements_demanded, rule bexI[OF _ present],
        simp add: development_refinement_demanded_def)
qed

section \<open>Problems and their dependencies are computed from the same state\<close>

text \<open>
  A refinement problem of a constant carries that constant as its subject and the state's
  demanded statement as its contract; a constant with no contract yields no problem. The
  origin and authority are supplied by the use, not by this construction. A problem depends
  on the problems of the other constants of the given scope that its own statement mentions,
  which is read from the statement rather than from a grouping: the mentioned constant is
  the premise slot, so distinct constants occupy distinct slots and no list order enters.
\<close>

definition development_refinement_problem :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_problem option" where
  "development_refinement_problem C r a c=map_option
    (\<lambda>k. Development_Problem {|c|} k r a) (development_refinement_contract C c)"

lemma development_refinement_problem_subject:
  assumes "development_refinement_problem C r a c=Some p"
  shows "problem_subject p={|c|}"
  using assms by (auto simp: development_refinement_problem_def)

lemma development_refinement_problem_injective:
  assumes first: "development_refinement_problem C r a c=Some p"
    and second: "development_refinement_problem C r a d=Some p"
  shows "c=d"
proof -
  have subjects: "{|c|}={|d|}"
    using development_refinement_problem_subject[OF first]
      development_refinement_problem_subject[OF second] by simp
  have "c |\<in>| {|c|}" by simp
  then have "c |\<in>| {|d|}" by (simp only: subjects)
  then show "c=d" by simp
qed

definition development_refinement_mentions ::
    "isabelle_context \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "development_refinement_mentions C cs c=remdups (filter (\<lambda>d. d\<in>set cs \<and> d\<noteq>c)
    (concat (map isabelle_term_constants (development_refinement_statements C c))))"

theorem development_refinement_mentions_exact:
  "d\<in>set (development_refinement_mentions C cs c) \<longleftrightarrow>
    d\<in>set cs \<and> d\<noteq>c \<and> (\<exists>p\<in>set (development_refinement_statements C c).
      d\<in>set (isabelle_term_constants p))"
  by (auto simp: development_refinement_mentions_def)

definition development_refinement_premises :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (nat\<times>development_problem) fset" where
  "development_refinement_premises C r a cs c=fset_of_list (List.map_filter
    (\<lambda>d. map_option (Pair d) (development_refinement_problem C r a d))
    (development_refinement_mentions C cs c))"

definition development_refinement_dependencies :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat list \<Rightarrow> development_dependencies" where
  "development_refinement_dependencies C r a cs=fset_of_list (List.map_filter
    (\<lambda>c. map_option (\<lambda>p. (p,development_refinement_premises C r a cs c))
      (development_refinement_problem C r a c)) cs)"

definition development_refinement_problems :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat list \<Rightarrow> development_problem list" where
  "development_refinement_problems C r a cs=List.map_filter
    (development_refinement_problem C r a) cs"

definition development_refinement_unstated ::
    "isabelle_context \<Rightarrow> nat list \<Rightarrow> nat fset" where
  "development_refinement_unstated C cs=fset_of_list
    (filter (\<lambda>c. development_refinement_contract C c=None) cs)"

theorem development_refinement_problems_exact:
  "p\<in>set (development_refinement_problems C r a cs) \<longleftrightarrow>
    (\<exists>c\<in>set cs. development_refinement_problem C r a c=Some p)"
  by (simp only: development_refinement_problems_def map_filter_member)

theorem development_refinement_unstated_exact:
  "c |\<in>| development_refinement_unstated C cs \<longleftrightarrow>
    c\<in>set cs \<and> development_refinement_problem C r a c=None"
  by (auto simp: development_refinement_unstated_def development_refinement_problem_def
    fset_of_list_elem)

text \<open>
  Each problem in scope contributes exactly one decomposition, namely the premises computed
  from its own statement. Two constants in scope never yield one problem, so the
  decompositions of a problem are not joined and the state reports no ambiguity that the
  computation did not find.
\<close>

theorem development_refinement_decomposition_exact:
  assumes problem: "development_refinement_problem C r a c=Some p" and scope: "c\<in>set cs"
  shows "development_decompositions (development_refinement_dependencies C r a cs) p=
    {|development_refinement_premises C r a cs c|}"
proof -
  let ?entry="\<lambda>c. map_option (\<lambda>p. (p,development_refinement_premises C r a cs c))
    (development_refinement_problem C r a c)"
  have member: "(q,H) |\<in>| development_refinement_dependencies C r a cs \<longleftrightarrow>
      (\<exists>d\<in>set cs. ?entry d=Some (q,H))" for q H
    by (simp only: development_refinement_dependencies_def fset_of_list_elem map_filter_member)
  have selected: "(q,H) |\<in>| development_refinement_dependencies C r a cs \<and> q=p \<longleftrightarrow>
      q=p \<and> H=development_refinement_premises C r a cs c" for q H
  proof
    assume "(q,H) |\<in>| development_refinement_dependencies C r a cs \<and> q=p"
    then obtain d where inside: "d\<in>set cs" and entry: "?entry d=Some (q,H)" and equal: "q=p"
      using member by blast
    have found: "development_refinement_problem C r a d=Some q"
      and computed: "H=development_refinement_premises C r a cs d"
      using entry by (auto split: option.splits)
    have "d=c" using development_refinement_problem_injective[OF found[unfolded equal] problem] .
    then show "q=p \<and> H=development_refinement_premises C r a cs c" using equal computed by simp
  next
    assume "q=p \<and> H=development_refinement_premises C r a cs c"
    then show "(q,H) |\<in>| development_refinement_dependencies C r a cs \<and> q=p"
      using member[of q H] problem scope by auto
  qed
  have rows: "ffilter (\<lambda>(q,H). q=p) (development_refinement_dependencies C r a cs)=
      {|(p,development_refinement_premises C r a cs c)|}"
    by (rule fset_eqI) (use selected in \<open>auto split: prod.splits\<close>)
  show ?thesis by (simp only: development_decompositions_def rows) simp
qed

corollary development_refinement_premises_exact:
  assumes problem: "development_refinement_problem C r a c=Some p" and scope: "c\<in>set cs"
  shows "development_premises (development_refinement_dependencies C r a cs) p=
    fimage snd (development_refinement_premises C r a cs c)"
proof (rule fset_eqI)
  fix q
  show "q |\<in>| development_premises (development_refinement_dependencies C r a cs) p \<longleftrightarrow>
      q |\<in>| fimage snd (development_refinement_premises C r a cs c)"
    by (simp only: development_premises_member
      development_refinement_decomposition_exact[OF problem scope]) simp
qed

corollary development_refinement_not_ambiguous:
  assumes problem: "development_refinement_problem C r a c=Some p" and scope: "c\<in>set cs"
  shows "p\<notin>set (development_ambiguous (development_refinement_dependencies C r a cs) ps)"
proof -
  have single: "fcard (development_decompositions (development_refinement_dependencies C r a cs) p)=1"
    by (simp only: development_refinement_decomposition_exact[OF problem scope] fcard_finsert_if) simp
  show ?thesis by (simp add: development_ambiguous_def single)
qed

end
