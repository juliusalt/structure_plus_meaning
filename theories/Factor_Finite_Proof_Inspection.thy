theory Factor_Finite_Proof_Inspection
  imports Factor_Finite_Proof_Checking Factor_Finite_Application_Proofs Finite_Inspection_Rows
begin

definition finite_proof_inspection where
  "finite_proof_inspection P T=finite_inspection_rows
    (\<lambda>((d,t),p). finite_checks_schema_proof P p d t) T"

theorem finite_proof_inspection_row:
  "(((d,t),p),b) |\<in>| finite_proof_inspection P T \<longleftrightarrow>
    ((d,t),p) |\<in>| T \<and>
      b=checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
  by (simp only: finite_proof_inspection_def finite_inspection_row_exact
    case_prod_conv finite_checks_schema_proof_exact)

theorem finite_proof_inspection_complete:
  "fimage fst (finite_proof_inspection P T)=T"
  by (simp only: finite_proof_inspection_def finite_inspection_rows_domain)

theorem finite_proof_inspection_exact:
  "finite_inspection_rows_hold (finite_proof_inspection P T)=finite_proofs_sound P T"
  by (simp only: finite_proof_inspection_def finite_inspection_rows_hold_exact
    finite_proofs_sound_def Ball_def split_paired_All case_prod_conv finite_checks_schema_proof_exact)

export_code finite_proof_inspection checking SML

text \<open>
  Each claimed call retains its entire recursive certificate and the result
  of checking that certificate against the independently supplied source.
  The complete report preserves every member and exactly characterizes the
  original validity condition. Source identity and answer coverage are separate.
\<close>

end
