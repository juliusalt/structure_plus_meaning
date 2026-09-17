theory Factor_Workflow_Execution
  imports Factor_Workflow_Stage
begin

definition workflow_stage_input where
  "workflow_stage_input problem prior=Finite_Pair problem (finite_data_sequence prior)"

datatype native_workflow_execution =
    Workflow_Finished "finite_factor_term list"
  | Workflow_Unavailable native_workflow_stage finite_factor_term
  | Workflow_Executed native_workflow_stage finite_factor_term native_workflow_stage_result
      "(finite_factor_term \<times> native_workflow_execution) list"

fun execute_workflow where
  "execute_workflow [] problem prior=Workflow_Finished prior"
| "execute_workflow (S#Ss) problem prior=(let input=workflow_stage_input problem prior in
    case evaluate_workflow_stage S input of None \<Rightarrow> Workflow_Unavailable S input
    | Some result \<Rightarrow> (case result of (P,D,A,T,ys) \<Rightarrow>
      Workflow_Executed S input result
        (map (\<lambda>y. (y,execute_workflow Ss problem (prior@[y]))) ys)))"

fun workflow_completed_paths where
  "workflow_completed_paths (Workflow_Finished ys)=[ys]"
| "workflow_completed_paths (Workflow_Unavailable S input)=[]"
| "workflow_completed_paths (Workflow_Executed S input result children)=
    concat (map (\<lambda>(y,child). workflow_completed_paths child) children)"

fun workflow_path_holds where
  "workflow_path_holds [] problem prior final \<longleftrightarrow> final=prior"
| "workflow_path_holds (S#Ss) problem prior final \<longleftrightarrow>
    (\<exists>y. workflow_stage_relation S (workflow_stage_input problem prior) y \<and>
      workflow_path_holds Ss problem (prior@[y]) final)"

theorem execute_workflow_complete_path:
  assumes completed: "final\<in>set (workflow_completed_paths (execute_workflow stages problem prior))"
  shows "workflow_path_holds stages problem prior final"
  using completed
proof (induction stages arbitrary: prior)
  case Nil
  then show ?case by simp
next
  case (Cons S Ss)
  obtain P D A T ys where result:
    "evaluate_workflow_stage S (workflow_stage_input problem prior)=Some (P,D,A,T,ys)"
    using Cons.prems
    by (auto simp: Let_def split: option.splits prod.splits)
  obtain y where selected: "y\<in>set ys"
    and continued: "final\<in>set (workflow_completed_paths (execute_workflow Ss problem (prior@[y])))"
    using Cons.prems by (auto simp: Let_def result)
  have stage: "workflow_stage_relation S (workflow_stage_input problem prior) y"
    using selected evaluate_workflow_stage_exact(1)[OF result] by blast
  show ?case using stage Cons.IH[OF continued] by auto
qed

lemma workflow_path_length:
  "workflow_path_holds stages problem prior final \<Longrightarrow>
    length final=length prior+length stages"
  by (induction stages arbitrary: prior) auto

lemma workflow_path_prefix:
  "workflow_path_holds stages problem prior final \<Longrightarrow>
    \<exists>rest. final=prior@rest"
proof (induction stages arbitrary: prior)
  case Nil
  then show ?case by auto
next
  case (Cons S Ss)
  obtain y where rest: "workflow_path_holds Ss problem (prior@[y]) final"
    using Cons.prems by auto
  obtain zs where "final=(prior@[y])@zs" using Cons.IH[OF rest] by blast
  then show ?case by auto
qed

theorem completed_workflow_at_stage:
  assumes completed: "workflow_path_holds stages problem prior final"
    and index: "i<length stages"
  shows "workflow_stage_relation (stages!i)
    (workflow_stage_input problem (take (length prior+i) final)) (final!(length prior+i))"
  using completed index
proof (induction stages arbitrary: prior i)
  case Nil
  then show ?case by simp
next
  case (Cons S Ss)
  obtain y where stage: "workflow_stage_relation S (workflow_stage_input problem prior) y"
    and rest: "workflow_path_holds Ss problem (prior@[y]) final"
    using Cons.prems(1) by auto
  obtain zs where final: "final=(prior@[y])@zs"
    using workflow_path_prefix[OF rest] by blast
  show ?case
  proof (cases i)
    case 0
    show ?thesis using stage by (simp add: 0 final)
  next
    case (Suc j)
    have bound: "j<length Ss" using Cons.prems(2) by (simp add: Suc)
    show ?thesis using Cons.IH[OF rest bound] by (simp add: Suc)
  qed
qed

text \<open>
  Every stage receives the same original problem and all actual preceding
  outputs. Every permitted branch is executed, and complete failed stages and
  proof results remain in the execution tree. There is no external callback
  that supplies admission. A completed path has one actual native judgment
  per original stage; omissions, reordered results and another problem's
  prefix cannot be substituted for those judgments.
\<close>

end
