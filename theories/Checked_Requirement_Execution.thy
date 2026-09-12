theory Checked_Requirement_Execution
  imports Factor_Checked_Requirement_Plans Requirement_Plan_Execution
begin

section \<open>The source program fixes the admission checks before each request\<close>

definition checked_requirement_source :: "nat list" where
  "checked_requirement_source=sorted_list_of_set (system_definitions data_recognition_system)"

lemma checked_requirement_source_code [code]: "checked_requirement_source=[0,1,2]"
  by (simp add: checked_requirement_source_def)

definition checked_requirement_report where
  "checked_requirement_report gs n=
    (let D=system_definitions data_recognition_system;
         plan=admission_sequence gs n;
         ds=fst plan; k=fst (snd plan); cs=snd (snd plan)
     in (gs,n,plan,
       (364,data_list_term (map admission_goal_value gs))\<in>positive_meaning (admission_request_system D),
       (365,admission_counter n)\<in>positive_meaning (admission_request_system D),
       (367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
         (data_list_term (map admission_counter ds)) (admission_counter k)
         (data_list_term (map admission_instruction_value cs)))\<in>positive_meaning (admission_request_system D),
       checked_admission_sequence D gs n))"

lemma checked_requirement_report_code [code]:
  "checked_requirement_report gs n=
    (gs,n,admission_sequence gs n,
      (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>{0,1,2}),3\<le>n,
      admission_request_supported {0,1,2} gs n,checked_admission_sequence {0,1,2} gs n)"
proof -
  have domain: "system_definitions data_recognition_system={0,1,2}" by simp
  have finite: "finite ({0,1,2}::nat set)" by simp
  have floor: "admission_source_floor {0,1,2}=3" by (simp add: admission_source_floor_def)
  obtain ds k cs where sequence: "admission_sequence gs n=(ds,k,cs)"
    by (cases "admission_sequence gs n") auto
  show ?thesis
    by (simp only: checked_requirement_report_def Let_def domain sequence fst_conv snd_conv
      admission_supported_goals_at_values[OF finite] admission_fresh_counter_at_counter
      checked_admission_sequence_at_values[OF finite] floor)
      (auto simp: checked_admission_sequence_def sequence)
qed

definition checked_requirement_controls :: "(admission_goal list\<times>nat) list" where
  "checked_requirement_controls=
    [([],0),([],2),([],3),([Existing_Admission 2],2),([Existing_Admission 2],3),
     ([Existing_Admission 3],3),
     ([Paired_Admission (Existing_Admission 2) (Existing_Admission 2)],3),
     ([Collected_Admission (Existing_Admission 2)],3),
     ([Paired_Admission (Existing_Admission 2) (Collected_Admission (Existing_Admission 353))],3),
     ([Existing_Admission 2,Existing_Admission 2],3),
     ([Existing_Admission 2,Existing_Admission 1],3),
     ([investigation_input_goal],3),([Existing_Admission 2],1000),
     ([Existing_Admission 2,Collected_Admission (Existing_Admission 2)],3)]"

definition checked_requirement_reports where
  "checked_requirement_reports=map (\<lambda>(gs,n). checked_requirement_report gs n) checked_requirement_controls"

export_code checked_requirement_source checked_requirement_reports
  admission_sequence admission_sequence_reports portable_requirement_reports
  portable_requirement_execution portable_table_diagnostics portable_table_goals
  Existing_Admission Paired_Admission Collected_Admission Pair_Admission_Instruction List_Admission_Instruction
  Finite_Payload Finite_Pair Finite_Target Finite_Whole finite_empty_artifact
  finite_reasoning_term_equal nat_of_integer integer_of_nat
  in SML module_name Requirement_Plans file_prefix checked_requirement_plans

text \<open>
  The returned candidate is computed even when its request is refused. The
  report then gives the actual native support, allocation, and complete-plan
  judgments, together with the checked constructor's optional result. An
  unsupported nested leaf and an occupied counter therefore remain visible
  as different failures; a formed candidate cannot excuse either one.

  This execution source is the existing data-recognition program. Its domain
  is obtained from that program's definitions, not supplied by the proposer.
  The original investigation-input goal remains unsupported here because its
  required scope predicate is absent from this smaller source program.
\<close>

end
