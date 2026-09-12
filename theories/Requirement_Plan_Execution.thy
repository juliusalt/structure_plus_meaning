theory Requirement_Plan_Execution
  imports Factor_Portable_Table_Development Factor_Investigation_Input_Development Factor_Reasoning_Execution
begin

section \<open>Complete executable observations accompany the actual subjects\<close>

definition portable_table_diagnostics where
  "portable_table_diagnostics xs ys=
    [finite_keyed_rows_formed xs,finite_keyed_rows_formed ys,
     distinct (map fst xs),distinct (map fst ys),
     (\<forall>(k,v)\<in>set xs. finite_data_projection v=Some v),
     (\<forall>(k,v)\<in>set ys. finite_data_projection v=Some v),set xs=set ys]"

theorem portable_table_diagnostics_exact:
  "list_all id (portable_table_diagnostics xs ys) \<longleftrightarrow> finite_portable_table_comparison xs ys"
  by (auto simp: portable_table_diagnostics_def finite_portable_table_comparison_def
    finite_keyed_table_comparison_def)

definition portable_requirement_controls ::
  "((finite_factor_term\<times>finite_factor_term) list\<times>
    (finite_factor_term\<times>finite_factor_term) list) list" where
  "portable_requirement_controls=
    (let a=(Finite_Payload [0],Finite_Payload [7]);
         b=(Finite_Payload [1],Finite_Payload [8]);
         bad_key=(Finite_Payload [256],Finite_Payload [7]);
         bad_value=(Finite_Payload [1],Finite_Payload [256]);
         reference=(Finite_Payload [0],Finite_Target (Finite_Whole finite_empty_artifact))
     in [([],[]),([a],[a]),([a],[b]),([a,b],[b,a]),([a,a],[a,a]),
         ([bad_key],[bad_key]),([bad_value],[bad_value]),([reference],[reference]),
         ([a,bad_value],[a,bad_value])])"

definition portable_requirement_reports where
  "portable_requirement_reports n=map (\<lambda>(xs,ys).
    (xs,ys,portable_table_diagnostics xs ys,finite_keyed_table_comparison xs ys,
      portable_requirement_execution n xs ys)) portable_requirement_controls"

definition admission_sequence_controls :: "(admission_goal list\<times>nat) list" where
  "admission_sequence_controls=
    [([],360),([Existing_Admission 2],360),(portable_table_goals,360),
     ([Existing_Admission 353,Existing_Admission 2],360),
     ([Existing_Admission 2,Existing_Admission 2,Existing_Admission 353],360),
     ([Paired_Admission (Existing_Admission 2) (Existing_Admission 2),
       Collected_Admission (Existing_Admission 2)],360),
     ([investigation_input_goal,Collected_Admission investigation_input_goal],360)]"

definition admission_sequence_reports where
  "admission_sequence_reports=map (\<lambda>(gs,n). (gs,n,admission_sequence gs n)) admission_sequence_controls"

export_code admission_sequence admission_sequence_reports portable_requirement_reports
  portable_requirement_execution portable_table_diagnostics portable_table_goals
  Existing_Admission Paired_Admission Collected_Admission Pair_Admission_Instruction List_Admission_Instruction
  Finite_Payload Finite_Pair Finite_Target Finite_Whole finite_empty_artifact
  finite_reasoning_term_equal nat_of_integer integer_of_nat
  in SML module_name Requirement_Plans file_prefix requirement_plans

text \<open>
  Each report retains both complete table inputs, all seven actual condition
  observations, the original table predicate, and the generated guard's
  execution result. Their conjunction has the original condition's exact
  equation. The reference control distinguishes table identity from the
  additional self-contained-value requirement; malformed unused rows remain
  part of the actual subject.

  The planning family includes empty, repeated, reordered, and compound goals.
  Its last case reuses the existing investigation-input goal twice through
  different surrounding constructions. These executions supplement the
  universal native contracts and do not establish whole-workflow adequacy.
\<close>

end
