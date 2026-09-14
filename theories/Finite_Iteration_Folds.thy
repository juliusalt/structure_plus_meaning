theory Finite_Iteration_Folds
  imports Finite_Iteration_Histories
begin

theorem iteration_prefix_fold_projection:
  assumes path: "iteration_prefix b f x xs y"
    and initial: "project s=x"
    and step: "\<And>x s. project s=x \<Longrightarrow> project (g x s)=f x"
  shows "project (fold g xs s)=y"
  using path initial
proof (induction xs arbitrary: x s)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have head: "a=x" and tail: "iteration_prefix b f (f x) xs y"
    using Cons.prems(1) by simp_all
  have advanced: "project (g a s)=f x"
    by (simp only: head; rule step[OF Cons.prems(2)])
  show ?case using Cons.IH[OF tail advanced] by simp
qed

text \<open>
  A complete preceding-state history can drive a separate construction fold.
  Its projection agrees with the original final state when every construction
  step recovers the corresponding original transition. The construction state
  can retain additional witnesses and need not have an injective projection.
\<close>

end
