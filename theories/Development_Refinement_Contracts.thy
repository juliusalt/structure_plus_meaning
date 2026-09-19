theory Development_Refinement_Contracts
  imports Development_Constant_Problems
begin

section \<open>A refinement is the problem of a constant that reads its code equations\<close>

text \<open>
  A refinement replaces the executable content of one constant, so the statements it demands
  are the code equations of that constant in the state it is made against, never a kernel
  definition, and its contract is the constant as the state declares it, marked as a
  refinement. A constant of several code equations is one problem whose incumbent is that
  whole family. Each construction below is the problem of a constant under the code-equation
  reading; the request, the seed and the loop use these instances, and every contract they
  carry is the contract of the general construction.
\<close>

definition development_refinement_statements :: "isabelle_context \<Rightarrow> nat \<Rightarrow> isabelle_term list" where
  "development_refinement_statements C c=development_statements isabelle_code_equation_proposition C c"

corollary development_refinement_statements_state:
  "p\<in>set (development_refinement_statements C c) \<longleftrightarrow>
    Isabelle_Code_Equation p\<in>set (snd C) \<and>
    c\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C))
      (Isabelle_Code_Equation p))"
  by (simp add: development_refinement_statements_def development_statements_exact
    isabelle_code_equation_proposition_exact development_constant_scope_member)

definition development_refinement_contract :: "isabelle_context \<Rightarrow> nat \<Rightarrow> development_contract option" where
  "development_refinement_contract C c=development_constant_contract isabelle_code_equation_proposition
    Development_Refinement C c"

definition development_refinement_problem :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat \<Rightarrow> development_problem option" where
  "development_refinement_problem C r a c=development_constant_problem isabelle_code_equation_proposition
    Development_Refinement C r a c"

lemma development_refinement_problem_contract:
  "development_refinement_problem C r a c=map_option (\<lambda>k. Development_Problem {|c|} k r a)
    (development_refinement_contract C c)"
  by (simp only: development_refinement_problem_def development_constant_problem_def
    development_refinement_contract_def)

lemma development_refinement_problem_subject:
  assumes "development_refinement_problem C r a c=Some p"
  shows "problem_subject p={|c|}"
  by (rule development_constant_problem_subject[OF assms[unfolded development_refinement_problem_def]])

definition development_refinement_problems :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat list \<Rightarrow> development_problem list" where
  "development_refinement_problems C r a cs=development_constant_problems isabelle_code_equation_proposition
    Development_Refinement C r a cs"

definition development_refinement_dependencies :: "isabelle_context \<Rightarrow> development_origin \<Rightarrow>
    development_authority \<Rightarrow> nat list \<Rightarrow> development_dependencies" where
  "development_refinement_dependencies C r a cs=development_constant_dependencies
    isabelle_code_equation_proposition Development_Refinement C r a cs"

definition development_refinement_unstated :: "isabelle_context \<Rightarrow> nat list \<Rightarrow> nat fset" where
  "development_refinement_unstated C cs=development_constant_unstated isabelle_code_equation_proposition C cs"

end
