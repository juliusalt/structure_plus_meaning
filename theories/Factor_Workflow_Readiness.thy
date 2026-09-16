theory Factor_Workflow_Readiness
  imports Factor_Workflow_Execution
begin

fun workflow_ready where
  "workflow_ready [] problem prior \<longleftrightarrow> True"
| "workflow_ready (S#Ss) problem prior \<longleftrightarrow>
    (\<exists>P D A T ys. evaluate_workflow_stage S (workflow_stage_input problem prior)=Some (P,D,A,T,ys)) \<and>
    (\<forall>y. workflow_stage_relation S (workflow_stage_input problem prior) y \<longrightarrow>
      workflow_ready Ss problem (prior@[y]))"

theorem execute_workflow_all_paths:
  assumes ready: "workflow_ready stages problem prior"
  shows "final\<in>set (workflow_completed_paths (execute_workflow stages problem prior)) \<longleftrightarrow>
    workflow_path_holds stages problem prior final"
  using ready
proof (induction stages arbitrary: prior)
  case Nil
  then show ?case by simp
next
  case (Cons S Ss)
  obtain P D A T ys where result:
    "evaluate_workflow_stage S (workflow_stage_input problem prior)=Some (P,D,A,T,ys)"
    using Cons.prems by auto
  have exact: "set ys={y. workflow_stage_relation S (workflow_stage_input problem prior) y}"
    by (rule evaluate_workflow_stage_exact(1)[OF result])
  have ready: "workflow_ready Ss problem (prior@[y])"
    if "workflow_stage_relation S (workflow_stage_input problem prior) y" for y
    using Cons.prems that by auto
  show ?case using Cons.IH[OF ready] exact
    by (auto simp: Let_def result)
qed

fun unavailable_workflow_stages where
  "unavailable_workflow_stages (Workflow_Finished ys)=[]"
| "unavailable_workflow_stages (Workflow_Unavailable S input)=[(S,input)]"
| "unavailable_workflow_stages (Workflow_Executed S input result children)=
    concat (map (\<lambda>(y,child). unavailable_workflow_stages child) children)"

theorem workflow_ready_has_no_unavailable_stage:
  assumes "workflow_ready stages problem prior"
  shows "unavailable_workflow_stages (execute_workflow stages problem prior)=[]"
  using assms
proof (induction stages arbitrary: prior)
  case Nil
  then show ?case by simp
next
  case (Cons S Ss)
  obtain P D A T ys where result:
    "evaluate_workflow_stage S (workflow_stage_input problem prior)=Some (P,D,A,T,ys)"
    using Cons.prems by auto
  have each: "unavailable_workflow_stages (execute_workflow Ss problem (prior@[y]))=[]"
    if "y\<in>set ys" for y
  proof (rule Cons.IH)
    have stage: "workflow_stage_relation S (workflow_stage_input problem prior) y"
      using that evaluate_workflow_stage_exact(1)[OF result] by blast
    show "workflow_ready Ss problem (prior@[y])" using Cons.prems stage by auto
  qed
  show ?case using each by (simp add: Let_def result concat_eq_Nil_conv)
qed

text \<open>
  Completeness requires availability on every actually admitted branch. Empty
  candidate results and unavailable native computations stay distinct. The
  readiness condition is established from real source computations, never a
  caller's flag. Missing stages remain visible as concrete source/input pairs.
\<close>

export_code unavailable_workflow_stages checking SML

end
