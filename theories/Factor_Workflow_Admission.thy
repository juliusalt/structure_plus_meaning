theory Factor_Workflow_Admission
  imports Factor_Workflow_Protocol Factor_Workflow_Reference
begin

fun workflow_trace_valid where
  "workflow_trace_valid stages problem prior (Workflow_Finished ys)=(stages=[] \<and> ys=prior)"
| "workflow_trace_valid stages problem prior (Workflow_Unavailable S input)=(case stages of
    [] \<Rightarrow> False | V#Vs \<Rightarrow> S=V \<and> input=workflow_stage_input problem prior \<and>
      workflow_stage_reference S input=None)"
| "workflow_trace_valid stages problem prior (Workflow_Executed S input (P,D,A,T,ys) children)=
    (case stages of [] \<Rightarrow> False | V#Vs \<Rightarrow> S=V \<and> input=workflow_stage_input problem prior \<and>
      workflow_stage_evidence S input (P,D,A,T,ys) \<and> map fst children=ys \<and>
      list_all (\<lambda>(y,child). workflow_trace_valid Vs problem (prior@[y]) child) children)"

theorem execute_workflow_valid:
  "workflow_trace_valid stages problem prior (execute_workflow stages problem prior)"
proof (induction stages arbitrary: prior)
  case Nil
  then show ?case by simp
next
  case (Cons S Ss)
  show ?case
  proof (cases "evaluate_workflow_stage S (workflow_stage_input problem prior)")
    case None
    have reference: "workflow_stage_reference S (workflow_stage_input problem prior)=None"
      using workflow_stage_reference_projection[of S "workflow_stage_input problem prior"] None by simp
    show ?thesis by (simp add: Let_def None reference)
  next
    case (Some result)
    obtain P D A T ys where shape: "result=(P,D,A,T,ys)" by (cases result) auto
    have evidence: "workflow_stage_evidence S (workflow_stage_input problem prior) result"
      by (rule evaluate_workflow_stage_evidence[OF Some])
    show ?thesis using Cons.IH evidence
      by (simp add: Let_def Some shape comp_def list_all_iff)
  qed
qed

lemma workflow_stage_evidence_reference:
  "workflow_stage_evidence S input (P,D,A,T,ys) \<Longrightarrow>
    workflow_stage_reference S input=Some ys"
  by (auto simp: workflow_stage_evidence_def workflow_stage_reference_def Let_def)

theorem valid_workflow_trace_paths:
  assumes valid: "workflow_trace_valid stages problem prior execution"
  shows "workflow_completed_paths execution=workflow_reference_paths stages problem prior"
  using valid
proof (induction stages arbitrary: prior execution)
  case Nil
  then show ?case by (cases execution) auto
next
  case (Cons S Ss)
  show ?case
  proof (cases execution)
    case (Workflow_Finished ys)
    then show ?thesis using Cons.prems by simp
  next
    case (Workflow_Unavailable V input)
    then show ?thesis using Cons.prems by auto
  next
    case (Workflow_Executed V input result children)
    obtain P D A T ys where shape: "result=(P,D,A,T,ys)" by (cases result) auto
    have same: "V=S" "input=workflow_stage_input problem prior"
      and evidence: "workflow_stage_evidence S (workflow_stage_input problem prior) (P,D,A,T,ys)"
      and rows: "map fst children=ys"
      and children: "\<forall>y child. (y,child)\<in>set children \<longrightarrow>
        workflow_trace_valid Ss problem (prior@[y]) child"
      using Cons.prems by (auto simp: Workflow_Executed shape list_all_iff)
    have each: "workflow_completed_paths child=workflow_reference_paths Ss problem (prior@[y])"
      if "(y,child)\<in>set children" for y child
      by (rule Cons.IH) (use children that in blast)
    have mapped: "map (\<lambda>(y,child). workflow_completed_paths child) children=
      map (\<lambda>y. workflow_reference_paths Ss problem (prior@[y])) ys"
      unfolding rows[symmetric] map_map
      by (rule map_cong[OF refl]) (use each in \<open>auto simp: comp_def split: prod.splits\<close>)
    show ?thesis by (simp only: Workflow_Executed shape workflow_completed_paths.simps
      workflow_reference_paths.simps workflow_stage_evidence_reference[OF evidence] option.simps mapped)
  qed
qed

definition admit_development_workflow where
  "admit_development_workflow W problem execution=(if workflow_trace_valid
    (development_workflow_stages W) problem [] execution then Some (workflow_completed_paths execution) else None)"

theorem constructed_workflow_admitted:
  "admit_development_workflow W problem (construct_development_workflow W problem)=
    Some (development_workflow_results W problem)"
  by (simp only: admit_development_workflow_def construct_development_workflow_def
    execute_workflow_valid if_True development_workflow_results_def)

theorem admitted_workflow_complete_results:
  "admit_development_workflow W problem execution=Some paths \<Longrightarrow>
    paths=development_workflow_results W problem"
  using valid_workflow_trace_paths[of "development_workflow_stages W" problem "[]" execution]
  by (auto simp: admit_development_workflow_def development_workflow_results_def
    construct_development_workflow_def workflow_reference_paths_exact split: if_splits)

context development_workflow_contract
begin

theorem admitted_required_transition:
  assumes admitted: "admit_development_workflow W problem execution=Some paths"
    and path: "ys\<in>set paths" and required: "i<8"
  shows "required i problem (take i ys) (ys!i)"
  by (rule every_required_transition[OF _ required])
    (use admitted_workflow_complete_results[OF admitted] path in simp)

end

text \<open>
  Submission checks the complete original workflow and every actual input,
  answer, certificate and branch. A caller cannot turn an omitted stage,
  unrelated source, altered prefix or missing proof into completion by
  supplying an acceptance flag. Successful submission recovers exactly the
  original ordered result family. A correctly represented unavailable stage
  is valid diagnostic evidence and produces no completion through that branch.

  Original stage-meaning contracts still govern semantic use. This gate does
  not certify an arbitrary protocol's adequacy for an external problem.
\<close>

export_code workflow_trace_valid admit_development_workflow checking SML

end
