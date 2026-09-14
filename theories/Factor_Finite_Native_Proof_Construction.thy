theory Factor_Finite_Native_Proof_Construction
  imports Factor_Finite_Program_Proofs Factor_Finite_Native_Evaluation
begin

definition finite_native_program_proofs where
  "finite_native_program_proofs E u r D=
    finite_source_computation E u r (\<lambda>P. finite_program_proofs P D)"

theorem finite_native_program_proofs_conditions:
  "finite_native_program_proofs E u r D=Some (P,A,T) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_proofs P D=Some (A,T)"
  by (simp only: finite_native_program_proofs_def finite_source_computation_exact)

theorem finite_native_program_proofs_projection:
  "map_option (map_prod id fst) (finite_native_program_proofs E u r D)=
    finite_native_program_evaluation E u r D"
  by (simp only: finite_native_program_proofs_def finite_source_computation_projection
    finite_program_proofs_projection finite_native_program_evaluation_def)

theorem finite_native_program_proofs_evaluation:
  "finite_native_program_proofs E u r D=Some (P,A,T) \<Longrightarrow>
    finite_native_program_evaluation E u r D=Some (P,A)"
  using finite_native_program_proofs_projection[of E u r D] by simp

theorem finite_native_program_proofs_correct:
  assumes result: "finite_native_program_proofs E u r D=Some (P,A,T)"
  shows "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "fimage fst T=A" "finite_proofs_sound P T"
proof -
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using result by (simp only: finite_native_program_proofs_conditions; blast)
  have proofs: "finite_program_proofs P D=Some (A,T)"
    using result by (simp only: finite_native_program_proofs_conditions; blast)
  show "fimage fst T=A" "finite_proofs_sound P T"
    by (rule finite_program_proofs_correct[OF proofs])+
qed

export_code finite_native_program_proofs checking SML

text \<open>
  The original native source supplies every clause, binding and socket in the
  constructed certificates. Each requested positive answer has an actual
  certificate accepted by the original proof checker. These finite values
  retain the original local coordinates. Positioned metadata, complete graph
  placement, native artifact replay and mathematical-proof admission remain
  separate construction and checking requirements.
\<close>

end
