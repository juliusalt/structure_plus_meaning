theory Factor_Finite_Native_Evaluation_Readings
  imports Factor_Finite_Native_Evaluation
begin

theorem finite_native_program_evaluation_semantics:
  "finite_native_program_evaluation E u r D=Some (P,A) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation_ready P D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
  by (simp only: finite_native_program_evaluation_conditions finite_program_evaluation_semantics)

end
