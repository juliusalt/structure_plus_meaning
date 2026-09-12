theory Requirement_Artifact_Execution
  imports Finite_Requirement_Artifact_Admission Factor_Requirement_Generations
    Checked_Requirement_Execution Factor_Executable_Artifact_Values
begin

section \<open>Complete artifact controls are judged against their original requests\<close>

definition requirement_artifact_add_count :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "requirement_artifact_add_count C=C\<lparr>finite_data :=
    (finite_data C)\<lparr>finite_bag := add_mset ([],[9]) (finite_bag (finite_data C))\<rparr>\<rparr>"

definition requirement_artifact_add_atom :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "requirement_artifact_add_atom C=C\<lparr>finite_structure :=
    (finite_structure C)\<lparr>finite_carrier := finsert [255] (finite_carrier (finite_structure C))\<rparr>\<rparr>"

definition requirement_artifact_controls :: "(admission_goal list\<times>nat\<times>finite_exact_artifact) list" where
  "requirement_artifact_controls=(let
    gs=[Existing_Admission 2]; n=3; plan=admission_sequence gs n;
    C=finite_requirement_candidate gs n plan;
    other=[Existing_Admission 1]; pair=[Paired_Admission (Existing_Admission 2) (Existing_Admission 2)];
    collection=[Collected_Admission (Existing_Admission 2)]; absent=[Existing_Admission 3];
    family=[Existing_Admission 2,Existing_Admission 1]
   in [(gs,n,C),
     (gs,n,finite_requirement_candidate gs n ([1],3,[])),
     (gs,n,finite_requirement_candidate gs n ([2],4,[])),
     (gs,n,finite_requirement_candidate gs n ([2],3,[List_Admission_Instruction 3 2])),
     (gs,n,finite_requirement_candidate other n (admission_sequence other n)),
     (gs,n,finite_requirement_candidate gs 4 (admission_sequence gs 4)),
     (gs,n,finite_payload_syntax [256]),
     (gs,n,requirement_artifact_add_count C),
     (gs,n,requirement_artifact_add_atom C),
     (gs,n,finite_payload_syntax []),
     ([],n,finite_requirement_candidate [] n (admission_sequence [] n)),
     ([],2,finite_requirement_candidate [] 2 (admission_sequence [] 2)),
     (pair,n,finite_requirement_candidate pair n (admission_sequence pair n)),
     (collection,n,finite_requirement_candidate collection n (admission_sequence collection n)),
     (absent,n,finite_requirement_candidate absent n (admission_sequence absent n)),
     (family,n,finite_requirement_candidate family n (admission_sequence family n)),
     (family,n,finite_requirement_candidate (rev family) n (admission_sequence (rev family) n))])"

definition requirement_artifact_report where
  "requirement_artifact_report gs n C=
    (gs,n,finite_artifact_rows C,finite_exact_formed C,checked_admission_sequence {0,1,2} gs n,
      (369,Target_Term (Whole_Artifact (decode_finite_object C)))\<in>positive_meaning
        (requirement_artifact_system (system_definitions data_recognition_system) gs n))"

lemma requirement_artifact_report_code [code]:
  "requirement_artifact_report gs n C=
    (gs,n,finite_artifact_rows C,finite_exact_formed C,checked_admission_sequence {0,1,2} gs n,
      finite_requirement_artifact_admitted {0,1,2} gs n C)"
  by (simp only: requirement_artifact_report_def
    finite_requirement_artifact_original_source[OF data_recognition_system_formed, symmetric]; simp)

definition requirement_artifact_reports where
  "requirement_artifact_reports=map (\<lambda>(gs,n,C). requirement_artifact_report gs n C) requirement_artifact_controls"

export_code requirement_artifact_reports checked_requirement_source checked_requirement_reports
  admission_sequence admission_sequence_reports portable_requirement_reports
  portable_requirement_execution portable_table_diagnostics portable_table_goals
  Existing_Admission Paired_Admission Collected_Admission Pair_Admission_Instruction List_Admission_Instruction
  Finite_Payload Finite_Pair Finite_Target Finite_Whole finite_empty_artifact
  finite_reasoning_term_equal nat_of_integer integer_of_nat
  in SML module_name Requirement_Plans file_prefix requirement_artifacts

text \<open>
  Each report retains all four complete artifact fields and the independently
  fixed request, the actual formation result, the checked constructor output,
  and the native artifact judgment. Mutations change actual subjects: result
  entries, counters, instructions, requests, payload bytes, counted data, and
  carrier atoms. The fixture contains no supplied satisfaction column.
\<close>

end
