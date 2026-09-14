theory Factor_Native_Certificate_Inputs
  imports Factor_Native_Certificate_Correctness Factor_Finite_Proof_Inspection
begin

datatype native_certificate_input =
    Native_Certificate_Query native_certificate_problem
  | Native_Certificate_Supplied "local_address option finite_artifact_environment"
      "local_address option" local_address "native_history_call fset" native_derivation_family

definition native_certificate_supplied_inspection where
  "native_certificate_supplied_inspection E u r A T=map_option (\<lambda>P.
    (P,fimage fst T=A,finite_proof_inspection P T)) (finite_native_source E u r)"

definition native_certificate_supplied_original where
  "native_certificate_supplied_original E u r A T=(case native_certificate_supplied_inspection E u r A T of
    None \<Rightarrow> None | Some (P,covered,rows) \<Rightarrow>
      if covered \<and> finite_inspection_rows_hold rows then Some (P,A,T) else None)"

theorem native_certificate_supplied_original_exact:
  "native_certificate_supplied_original E u r A T=Some (P,B,U) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    B=A \<and> U=T \<and> fimage fst T=A \<and> finite_proofs_sound P T"
proof -
  have finite: "native_certificate_supplied_original E u r A T=Some (P,B,U) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and> B=A \<and> U=T \<and> fimage fst T=A \<and> finite_proofs_sound P T"
    by (auto simp: native_certificate_supplied_original_def native_certificate_supplied_inspection_def
      finite_proof_inspection_exact split: option.splits if_splits)
  show ?thesis by (simp only: finite finite_native_source_correct)
qed

fun native_certificate_input_original where
  "native_certificate_input_original (Native_Certificate_Query X)=native_certificate_original X"
| "native_certificate_input_original (Native_Certificate_Supplied E u r A T)=
    native_certificate_supplied_original E u r A T"

fun native_certificate_input_supplied_inspection where
  "native_certificate_input_supplied_inspection (Native_Certificate_Query X)=None"
| "native_certificate_input_supplied_inspection (Native_Certificate_Supplied E u r A T)=
    native_certificate_supplied_inspection E u r A T"

definition native_certificate_input_method where
  "native_certificate_input_method m X=native_certificate_apply m
    (native_certificate_base_from (native_certificate_input_original X))"

definition native_certificate_input_condition where
  "native_certificate_input_condition f method X=
    native_certificate_condition_on f (native_certificate_input_original X) (method X)"

definition native_certificate_input_assessment where
  "native_certificate_input_assessment X result=native_certificate_assessment_from
    (native_certificate_input_original X) result"

theorem native_certificate_input_assessment_exact:
  "native_certificate_inspect (native_certificate_input_assessment X (method X)) f=
    native_certificate_input_condition f method X"
  by (simp only: native_certificate_input_assessment_def native_certificate_assessment_from_exact
    native_certificate_input_condition_def)

theorem native_certificate_query_method:
  "native_certificate_input_method m (Native_Certificate_Query X)=native_certificate_method m X"
  by (simp only: native_certificate_input_method_def native_certificate_input_original.simps
    native_certificate_method_def native_certificate_base_def)

theorem native_certificate_query_condition:
  "native_certificate_input_condition f (native_certificate_input_method m) (Native_Certificate_Query X)=
    native_certificate_condition f (native_certificate_method m) X"
  by (simp only: native_certificate_input_condition_def native_certificate_input_original.simps
    native_certificate_query_method native_certificate_condition_def)

theorem native_certificate_input_constructor_all_conditions:
  assumes "f<7"
  shows "native_certificate_input_condition f (native_certificate_input_method 0) X"
  by (simp only: native_certificate_input_condition_def native_certificate_input_method_def
    native_certificate_apply_def; cases "native_certificate_base_from (native_certificate_input_original X)")
    (use native_certificate_base_from_all_conditions[OF assms, of "native_certificate_input_original X"] in
      \<open>simp_all add: native_certificate_variant_original\<close>)

export_code native_certificate_input_original native_certificate_input_method
  native_certificate_input_assessment native_certificate_supplied_inspection checking SML

text \<open>
  A query retains the entire earlier input and its original behavior. A supplied
  family instead retains its complete native source, stated positive calls and
  every supplied certificate. The original source reader and independent proof
  checker establish exactly when it is available. Different valid certificates
  for one call remain distinct; no functionality on the call-to-proof relation
  or finite-demand completeness is required. Failed source, coverage and proof
  checks retain their actual inspection fields and cannot produce an original.
\<close>

end
