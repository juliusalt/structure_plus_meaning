theory Lambda_Head_Evaluation
  imports Lambda_Closure_Interpretation
begin

section \<open>Substitution-based evaluation and captured closures\<close>

inductive lambda_head_evaluates :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  abstraction: "lambda_head_evaluates (Lambda_Abstraction p) (Lambda_Abstraction p)"
| application: "lambda_head_evaluates p (Lambda_Abstraction b) \<Longrightarrow>
    lambda_head_evaluates (lambda_substitute b q 0) v \<Longrightarrow>
    lambda_head_evaluates (Lambda_Application p q) v"

lemma lambda_head_evaluation_value:
  assumes "lambda_head_evaluates p v"
  shows "\<exists>b. v=Lambda_Abstraction b"
  using assms by (induction rule: lambda_head_evaluates.induct) auto

theorem lambda_evaluation_head_interpretation:
  assumes "lambda_evaluates c v" "lambda_closure_formed c"
  shows "lambda_head_evaluates (interpret_lambda_closure c) (interpret_lambda_closure v)"
  using assms
proof (induction rule: lambda_evaluates.induct)
  case (abstraction p e)
  have environment: "list_all lambda_closure_formed e" using abstraction.prems by simp
  show ?case by (simp only: lambda_closure_abstraction_interpretation[OF environment],
    rule lambda_head_evaluates.abstraction)
next
  case (variable n e v)
  have environment: "list_all lambda_closure_formed e" using variable.prems by simp
  have formed: "lambda_closure_formed (e!n)"
    using environment variable.hyps(1) by (auto simp: list_all_iff)
  show ?case using variable.IH[OF formed]
    by (simp only: lambda_closure_variable_interpretation[OF variable.hyps(1) environment])
next
  case (application p e b f q v)
  have function_formed: "lambda_closure_formed (Lambda_Closure p e)"
    and argument: "lambda_closure_formed (Lambda_Closure q e)"
    using application.prems by simp_all
  have value_formed: "lambda_closure_formed (Lambda_Closure (Lambda_Abstraction b) f)"
    by (rule lambda_evaluation_preserves_formation[OF application.hyps(1) function_formed])
  have environment: "list_all lambda_closure_formed f" using value_formed by simp
  have body_formed: "lambda_closure_formed (Lambda_Closure b (Lambda_Closure q e#f))"
    using value_formed argument by simp
  let ?b = "lambda_close b (map interpret_lambda_closure f) (Suc 0)"
  have head: "lambda_head_evaluates (interpret_lambda_closure (Lambda_Closure p e))
    (Lambda_Abstraction ?b)"
    using application.IH(1)[OF function_formed]
    by (simp only: lambda_closure_abstraction_interpretation[OF environment])
  have tail: "lambda_head_evaluates
    (lambda_substitute ?b (interpret_lambda_closure (Lambda_Closure q e)) 0)
    (interpret_lambda_closure v)"
    using application.IH(2)[OF body_formed]
    by (simp only: lambda_closure_body_interpretation[OF environment argument])
  show ?case
    unfolding lambda_closure_application_interpretation
    by (rule lambda_head_evaluates.application[OF head tail])
qed

lemma lambda_closure_variable_evaluation:
  assumes formed: "lambda_closure_formed (Lambda_Closure (Lambda_Variable n) e)"
    and source: "interpret_lambda_closure (Lambda_Closure (Lambda_Variable n) e)=p"
    and lookup: "\<And>a. a\<in>set e \<Longrightarrow> lambda_closure_formed a \<Longrightarrow>
      interpret_lambda_closure a=p \<Longrightarrow>
      \<exists>v. lambda_evaluates a v \<and> interpret_lambda_closure v=q"
  shows "\<exists>v. lambda_evaluates (Lambda_Closure (Lambda_Variable n) e) v \<and>
    interpret_lambda_closure v=q"
proof -
  have index: "n<length e" and environment: "list_all lambda_closure_formed e"
    using formed by simp_all
  have member: "e!n\<in>set e" using index by simp
  have entry_formed: "lambda_closure_formed (e!n)"
    using environment member by (simp add: list_all_iff)
  have same: "interpret_lambda_closure (e!n)=p"
    using source by (simp only: lambda_closure_variable_interpretation[OF index environment])
  obtain v where evaluation: "lambda_evaluates (e!n) v" and result: "interpret_lambda_closure v=q"
    using lookup[OF member entry_formed same] by blast
  show ?thesis using lambda_evaluates.variable[OF index evaluation] result by blast
qed

theorem lambda_head_evaluation_closure:
  assumes "lambda_head_evaluates p q" "lambda_closure_formed c"
    "interpret_lambda_closure c=p"
  shows "\<exists>v. lambda_evaluates c v \<and> interpret_lambda_closure v=q"
  using assms
proof (induction arbitrary: c rule: lambda_head_evaluates.induct)
  case (abstraction p)
  show ?case using abstraction.prems
  proof (induction c)
    case source_closure: (Lambda_Closure t e)
    show ?case
    proof (cases t)
      case (Lambda_Variable n)
      have formed: "lambda_closure_formed (Lambda_Closure (Lambda_Variable n) e)"
        and same: "interpret_lambda_closure (Lambda_Closure (Lambda_Variable n) e)=Lambda_Abstraction p"
        using source_closure.prems Lambda_Variable by simp_all
      show ?thesis unfolding Lambda_Variable
      proof (rule lambda_closure_variable_evaluation[OF formed same])
        fix a
        assume "a\<in>set e" "lambda_closure_formed a" "interpret_lambda_closure a=Lambda_Abstraction p"
        then show "\<exists>v. lambda_evaluates a v \<and> interpret_lambda_closure v=Lambda_Abstraction p"
          using source_closure.IH by blast
      qed
    next
      case (Lambda_Application l r)
      then show ?thesis using source_closure.prems(2) by (simp add: lambda_close_application)
    next
      case (Lambda_Abstraction b)
      have evaluation: "lambda_evaluates (Lambda_Closure t e) (Lambda_Closure t e)"
        using Lambda_Abstraction by (simp add: lambda_evaluates.abstraction)
      show ?thesis using evaluation source_closure.prems(2) by blast
    qed
  qed
next
  case (application p b q v)
  show ?case using application.prems
  proof (induction c)
    case source_closure: (Lambda_Closure t e)
    show ?case
    proof (cases t)
      case (Lambda_Variable n)
      have formed: "lambda_closure_formed (Lambda_Closure (Lambda_Variable n) e)"
        and same: "interpret_lambda_closure (Lambda_Closure (Lambda_Variable n) e)=Lambda_Application p q"
        using source_closure.prems Lambda_Variable by simp_all
      show ?thesis unfolding Lambda_Variable
      proof (rule lambda_closure_variable_evaluation[OF formed same])
        fix a
        assume "a\<in>set e" "lambda_closure_formed a" "interpret_lambda_closure a=Lambda_Application p q"
        then show "\<exists>w. lambda_evaluates a w \<and> interpret_lambda_closure w=v"
          using source_closure.IH by blast
      qed
    next
      case (Lambda_Application l r)
      have function_formed: "lambda_closure_formed (Lambda_Closure l e)"
        and argument_formed: "lambda_closure_formed (Lambda_Closure r e)"
        using source_closure.prems(1) Lambda_Application by simp_all
      have function_source: "interpret_lambda_closure (Lambda_Closure l e)=p"
        and argument_source: "interpret_lambda_closure (Lambda_Closure r e)=q"
        using source_closure.prems(2) Lambda_Application by (auto simp: lambda_close_application)
      obtain w where function_evaluation: "lambda_evaluates (Lambda_Closure l e) w"
        and function_result: "interpret_lambda_closure w=Lambda_Abstraction b"
        using application.IH(1)[OF function_formed function_source] by blast
      obtain b' f where shape: "w=Lambda_Closure (Lambda_Abstraction b') f"
        using lambda_evaluation_value[OF function_evaluation] by blast
      have head: "lambda_evaluates (Lambda_Closure l e) (Lambda_Closure (Lambda_Abstraction b') f)"
        using function_evaluation shape by simp
      have value_formed: "lambda_closure_formed (Lambda_Closure (Lambda_Abstraction b') f)"
        by (rule lambda_evaluation_preserves_formation[OF head function_formed])
      have environment: "list_all lambda_closure_formed f" using value_formed by simp
      have head_body: "lambda_close b' (map interpret_lambda_closure f) (Suc 0)=b"
        using function_result
        by (simp only: shape lambda_closure_abstraction_interpretation[OF environment] lambda_term.inject)
      have body_formed: "lambda_closure_formed (Lambda_Closure b' (Lambda_Closure r e#f))"
        using value_formed argument_formed by simp
      have body_source: "interpret_lambda_closure (Lambda_Closure b' (Lambda_Closure r e#f))=
        lambda_substitute b q 0"
        by (simp only: lambda_closure_body_interpretation[OF environment argument_formed]
          head_body argument_source)
      obtain result where tail: "lambda_evaluates (Lambda_Closure b' (Lambda_Closure r e#f)) result"
        and result_source: "interpret_lambda_closure result=v"
        using application.IH(2)[OF body_formed body_source] by blast
      have evaluation: "lambda_evaluates (Lambda_Closure (Lambda_Application l r) e) result"
        by (rule lambda_evaluates.application[OF head tail])
      show ?thesis using evaluation result_source Lambda_Application by blast
    next
      case (Lambda_Abstraction b')
      have environment: "list_all lambda_closure_formed e" using source_closure.prems(1) by simp
      then show ?thesis using source_closure.prems(2) Lambda_Abstraction
        by (simp add: lambda_close_abstraction lambda_closure_environment_closed)
    qed
  qed
qed

theorem closed_lambda_head_evaluation_iff:
  assumes "lambda_scoped 0 p"
  shows "lambda_head_evaluates p q \<longleftrightarrow>
    (\<exists>v. lambda_evaluates (Lambda_Closure p []) v \<and> interpret_lambda_closure v=q)"
proof -
  have formed: "lambda_closure_formed (Lambda_Closure p [])" using assms by simp
  show ?thesis
  proof
    assume head: "lambda_head_evaluates p q"
    show "\<exists>v. lambda_evaluates (Lambda_Closure p []) v \<and> interpret_lambda_closure v=q"
      using lambda_head_evaluation_closure[OF head formed] by simp
  next
    assume "\<exists>v. lambda_evaluates (Lambda_Closure p []) v \<and> interpret_lambda_closure v=q"
    then obtain v where evaluation: "lambda_evaluates (Lambda_Closure p []) v"
      and result: "interpret_lambda_closure v=q" by blast
    show "lambda_head_evaluates p q"
      using lambda_evaluation_head_interpretation[OF evaluation formed] result by simp
  qed
qed

text \<open>
  This auxiliary evaluator substitutes an unevaluated argument and stops at an
  abstraction, just as the captured-closure evaluator does. The two relations
  agree in both directions on every formed closure after its finite environment
  is substituted. The reverse proof follows the evaluation derivation for
  applications and the finite closure tree for variable lookups. It does not
  assume that the source closure already evaluates.
\<close>

end
