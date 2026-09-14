theory Factor_Finite_Native_Evaluation
  imports Factor_Finite_Program_Evaluation Factor_Finite_Source_Computation
    Factor_Executable_Environment_Values Factor_Positive_Admission
begin

section \<open>Recover the actual package before deciding its requested calls\<close>

definition finite_native_program_evaluation where
  "finite_native_program_evaluation E u r D=
    finite_source_computation E u r (\<lambda>P. finite_program_evaluation P D)"

theorem finite_native_program_evaluation_conditions:
  "finite_native_program_evaluation E u r D=Some (P,A) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation P D=Some A"
  by (simp only: finite_native_program_evaluation_def finite_source_computation_exact)

theorem finite_native_program_evaluation_failure:
  "finite_native_program_evaluation E u r D=None \<longleftrightarrow>
    finite_native_source E u r=None \<or>
      (\<exists>P. finite_native_source E u r=Some P \<and> finite_program_evaluation P D=None)"
  by (auto simp: finite_native_program_evaluation_def finite_source_computation_def split: option.splits)

theorem finite_native_program_evaluation_exact:
  assumes result: "finite_native_program_evaluation E u r D=Some (P,A)"
  shows "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
proof -
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using result by (simp only: finite_native_program_evaluation_conditions; blast)
  have evaluated: "finite_program_evaluation P D=Some A"
    using result by (simp only: finite_native_program_evaluation_conditions; blast)
  show "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    by (rule finite_program_evaluation_exact(2)[OF evaluated])
qed

corollary finite_native_program_evaluation_call:
  assumes result: "finite_native_program_evaluation E u r D=Some (P,A)"
    and demand: "(d,t) |\<in>| D"
  shows "(d,t) |\<in>| A \<longleftrightarrow> (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system P)"
  by (simp add: finite_native_program_evaluation_exact(2)[OF result] demand)

section \<open>The existing native query predicate supplies the independent condition\<close>

theorem finite_native_program_evaluation_query:
  fixes E :: "local_address option finite_artifact_environment"
  assumes result: "finite_native_program_evaluation E u r D=Some (P,A)"
    and demand: "(d,t) |\<in>| D"
  shows "(d,t) |\<in>| A \<longleftrightarrow>
    (114,package_subject_argument (finite_environment_term E) (use_data_term u) (Payload_Term r)
      (Pair_Term (definition_site_value d) (decode_finite_term t)))\<in>positive_meaning positive_query_system"
proof -
  have package: "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    by (rule finite_native_program_evaluation_exact(1)[OF result])
  have formed: "environment_formed (decode_finite_environment E)"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have presented: "environment_value_presents (decode_finite_environment E) (finite_environment_term E)"
    using finite_environment_value_exact[of "decode_finite_environment E" E]
    by (simp add: finite_environment_formed_correct formed)
  show ?thesis by (simp only: positive_query_at_package[OF presented package]
    finite_native_program_evaluation_call[OF result demand])
qed

export_code finite_native_program_evaluation checking SML

text \<open>
  No source model, coordinate function or initial truths are supplied. The
  actual complete reader returns the program in its original native
  coordinates. The checked finite evaluator then supplies the exact requested
  part of its positive meaning. Its successful answers also decide the existing
  positive-query predicate on the complete original environment value, selector,
  definition and term. Missing source, incomplete head scope and an open demand
  remain distinct reasons for the operation to return no answer.

  This composition executes judgments about actual native programs. It does
  not construct a native proof artifact for each answer or enforce the entire
  development cycle. The Isabelle bootstrap contract remains its authority.
\<close>

end
