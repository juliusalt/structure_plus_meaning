theory Factor_Finite_Native_Histories
  imports Factor_Finite_Program_Histories Factor_Finite_Native_Evaluation
begin

section \<open>Actual source recovery supplies the program for the complete history\<close>

definition finite_native_program_history where
  "finite_native_program_history E u r D=
    finite_source_computation E u r (\<lambda>P. finite_program_history P D)"

theorem finite_native_program_history_conditions:
  "finite_native_program_history E u r D=Some (P,A,Hs) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_history P D=Some (A,Hs)"
  by (simp only: finite_native_program_history_def finite_source_computation_exact)

theorem finite_native_program_history_projection:
  "map_option (map_prod id fst) (finite_native_program_history E u r D)=
    finite_native_program_evaluation E u r D"
  by (simp only: finite_native_program_history_def finite_source_computation_projection
    finite_program_history_projection finite_native_program_evaluation_def)

theorem finite_native_program_history_evaluation:
  "finite_native_program_history E u r D=Some (P,A,Hs) \<Longrightarrow>
    finite_native_program_evaluation E u r D=Some (P,A)"
  using finite_native_program_history_projection[of E u r D] by simp

export_code finite_native_program_history checking SML

end
