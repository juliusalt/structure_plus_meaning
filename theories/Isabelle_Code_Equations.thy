theory Isabelle_Code_Equations
  imports Isabelle_Entities
begin

section \<open>A state reads the executable content of a constant separately\<close>

text \<open>
  A development constant contributes its kernel definitions and the code equations in
  effect, and both belong to the head constant of their left side. A refinement replaces
  executable content, so the statement it must establish is a code equation and never a
  kernel definition. The existing subject reading cannot make that distinction, because it
  treats both kinds alike; this reading states it explicitly on the entity language, so a
  demand for executable content is separate from a demand for a definition.
\<close>

fun isabelle_code_equation_proposition :: "isabelle_entity \<Rightarrow> isabelle_term option" where
  "isabelle_code_equation_proposition (Isabelle_Base_Constant t)=None"
| "isabelle_code_equation_proposition (Isabelle_Development_Constant t)=None"
| "isabelle_code_equation_proposition (Isabelle_Frontier_Constant t)=None"
| "isabelle_code_equation_proposition (Isabelle_Definition p)=None"
| "isabelle_code_equation_proposition (Isabelle_Specification p)=None"
| "isabelle_code_equation_proposition (Isabelle_Code_Equation p)=Some p"

lemma isabelle_code_equation_proposition_exact:
  "isabelle_code_equation_proposition e=Some p \<longleftrightarrow> e=Isabelle_Code_Equation p"
  by (cases e) simp_all

lemma isabelle_code_equation_is_specified:
  assumes "isabelle_code_equation_proposition e=Some p"
  shows "isabelle_specified_proposition e=Some p"
  using assms by (cases e) simp_all

lemma isabelle_code_equation_declares_nothing:
  assumes "isabelle_code_equation_proposition e=Some p"
  shows "isabelle_declared_constant e=None"
  using assms by (cases e) simp_all

text \<open>
  The reading refuses every other entity kind. A definition of the same constant states the
  same subject under the existing subject reading, so only this distinction separates the
  two demands.
\<close>

lemma isabelle_code_equation_refuses_definition:
  "isabelle_code_equation_proposition (Isabelle_Definition p)=None"
  by simp

lemma isabelle_code_equation_refuses_specification:
  "isabelle_code_equation_proposition (Isabelle_Specification p)=None"
  by simp

lemma isabelle_definition_and_code_equation_share_subjects:
  "isabelle_entity_subjects names D (Isabelle_Definition p)=
    isabelle_entity_subjects names D (Isabelle_Code_Equation p)"
  by simp

end
