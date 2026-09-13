theory Factor_Finite_Native_Histories
  imports Factor_Finite_Program_Histories Factor_Finite_Native_Evaluation
begin

section \<open>Actual source recovery supplies the program for the complete history\<close>

definition finite_native_program_history where
  "finite_native_program_history E u r D=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> map_option (Pair P) (finite_program_history P D))"

theorem finite_native_program_history_conditions:
  "finite_native_program_history E u r D=Some (P,A,Hs) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_history P D=Some (A,Hs)"
  by (auto simp: finite_native_program_history_def finite_native_source_correct[symmetric]
    split: option.splits)

theorem finite_native_program_history_projection:
  "map_option (map_prod id fst) (finite_native_program_history E u r D)=
    finite_native_program_evaluation E u r D"
proof (cases "finite_native_source E u r")
  case None
  then show ?thesis by (simp add: finite_native_program_history_def finite_native_program_evaluation_def)
next
  case (Some P)
  have projected: "map_option fst (finite_program_history P D)=finite_program_evaluation P D"
    by (rule finite_program_history_projection)
  show ?thesis
    by (simp add: finite_native_program_history_def finite_native_program_evaluation_def Some
      projected[symmetric] option.map_comp comp_def)
qed

theorem finite_native_program_history_evaluation:
  "finite_native_program_history E u r D=Some (P,A,Hs) \<Longrightarrow>
    finite_native_program_evaluation E u r D=Some (P,A)"
  using finite_native_program_history_projection[of E u r D] by simp

export_code finite_native_program_history checking SML

end
