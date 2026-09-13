theory Factor_Finite_Native_Evaluation_Readings
  imports Factor_Finite_Native_Evaluation
begin

theorem finite_native_program_evaluation_semantics:
  "finite_native_program_evaluation E u r D=Some (P,A) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation_ready P D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
proof
  assume result: "finite_native_program_evaluation E u r D=Some (P,A)"
  have evaluated: "finite_program_evaluation P D=Some A"
    using result by (simp only: finite_native_program_evaluation_conditions; blast)
  have ready: "finite_program_evaluation_ready P D"
    using evaluated by (auto simp: finite_program_evaluation_def split: if_splits)
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation_ready P D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    using ready finite_native_program_evaluation_exact[OF result] by blast
next
  assume condition: "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation_ready P D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
  obtain B where evaluated: "finite_program_evaluation P D=Some B"
    using condition by (simp only: finite_program_evaluation_ready_def finite_program_evaluation_conditions[symmetric]; blast)
  have equal: "A=B"
    using condition finite_program_evaluation_exact(2)[OF evaluated]
    by (simp only: fset_inject[symmetric]; blast)
  show "finite_native_program_evaluation E u r D=Some (P,A)"
    using condition evaluated by (simp only: finite_native_program_evaluation_conditions equal; blast)
qed

end
