theory Factor_Native_Derivation_Correctness
  imports Factor_Native_Derivation_Assessment
begin

lemma native_derivation_constructor_projection:
  "map_option (\<lambda>(P,A,T). (P,A)) (native_derivation_method 0 X)=native_history_original X"
  by (cases X) (simp add: native_derivation_method_original native_history_original_def
    finite_native_program_proofs_projection[symmetric] map_prod_def split_def)

lemma native_derivation_constructor_result:
  assumes result: "native_derivation_method 0 X=Some (P,A,T)"
  shows "native_history_original X=Some (P,A)" "fimage fst T=A" "finite_proofs_sound P T"
proof -
  obtain E u r D where fields: "X=(E,u,r,D)" by (cases X)
  have constructed: "finite_native_program_proofs E u r D=Some (P,A,T)"
    using result by (simp only: fields native_derivation_method_original)
  show "native_history_original X=Some (P,A)"
    using native_derivation_constructor_projection[of X] by (simp only: result option.simps case_prod_conv)
  show "fimage fst T=A" "finite_proofs_sound P T"
    by (rule finite_native_program_proofs_correct[OF constructed])+
qed

theorem native_derivation_constructor_all_conditions:
  assumes facet: "f<6"
  shows "native_derivation_condition f (native_derivation_method 0) X"
proof (cases "native_derivation_method 0 X")
  case None
  have unavailable: "native_history_original X=None"
    using native_derivation_constructor_projection[of X] by (simp only: None option.simps)
  show ?thesis
    using facet by (auto simp: native_derivation_assessment_exact[symmetric]
      native_derivation_inspect_def native_derivation_assessment_def finite_partial_result_inspect_def
      native_history_ready_def unavailable None Let_def split: if_splits; arith)
next
  case (Some v)
  obtain P A T where shape: "v=(P,A,T)" by (cases v)
  have result: "native_derivation_method 0 X=Some (P,A,T)" using Some by (simp only: shape)
  have original: "native_history_original X=Some (P,A)" and domain: "fimage fst T=A"
    and valid: "finite_proofs_sound P T"
    by (rule native_derivation_constructor_result[OF result])+
  show ?thesis
    using facet by (auto simp: native_derivation_assessment_exact[symmetric]
      native_derivation_inspect_def native_derivation_assessment_def finite_partial_result_inspect_def
      native_history_ready_def native_history_answer_observation_def native_history_program_observation_def
      native_derivation_evidence_review_def native_derivation_review_from_original_def
      finite_term_observation_comparison_def finite_proof_inspection_exact
      original result domain valid Let_def split: if_splits; arith)
qed

text \<open>
  The unmodified constructor satisfies every original condition on all native
  inputs. The result follows from source recovery, the complete inference
  history, actual certificate construction and the independent checker.
  Finite candidate comparisons can expose distinctions and scope gaps; their
  sampled adequacy is not the basis of this universal construction theorem.
\<close>

end
