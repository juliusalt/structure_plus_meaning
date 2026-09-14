theory Factor_Native_Derivation_Assessment
  imports Factor_Native_Derivation_Cases Factor_Finite_Proof_Inspection Factor_Native_History_Assessment
begin

type_synonym native_derivation_assessment =
  "native_history_call finite_partial_result_assessment\<times>bool\<times>bool"

definition native_derivation_review_from_original where
  "native_derivation_review_from_original original result=(case original of None \<Rightarrow> None
    | Some (P,B) \<Rightarrow> map_option (\<lambda>(Q,A,T).
      (finite_proof_inspection P T,fimage fst T |-| A,A |-| fimage fst T)) result)"

definition native_derivation_evidence_review where
  "native_derivation_evidence_review X result=
    native_derivation_review_from_original (native_history_original X) result"

lemma native_derivation_evidence_valid_exact:
  "(map_option (\<lambda>(rows,extra,missing). finite_inspection_rows_hold rows)
      (native_derivation_evidence_review X result)=Some True)=
    native_history_program_condition (\<lambda>P Q A T. finite_proofs_sound P T) X result"
  apply (simp only: native_history_program_observation_exact[symmetric])
  by (cases "native_history_original X"; cases result)
    (simp_all add: native_derivation_evidence_review_def native_derivation_review_from_original_def
      native_history_program_observation_def finite_proof_inspection_exact split: prod.splits)

lemma native_derivation_evidence_domain_exact:
  "(map_option (\<lambda>(rows,extra,missing). extra={||} \<and> missing={||})
      (native_derivation_evidence_review X result)=Some True)=
    native_history_program_condition (\<lambda>P Q A T. fimage fst T=A) X result"
  apply (simp only: native_history_program_observation_exact[symmetric])
  by (cases "native_history_original X"; cases result)
    (simp_all only: native_derivation_evidence_review_def native_derivation_review_from_original_def
      native_history_program_observation_def option.simps case_prod_unfold fst_conv snd_conv
      finite_differences_empty simp_thms)

definition native_derivation_assessment where
  "native_derivation_assessment X result=(let review=native_derivation_evidence_review X result in
    ((native_history_ready X,native_history_answer_observation X result,
      native_history_program_observation (\<lambda>P Q A T. P=Q) X result,result=None),
    map_option (\<lambda>(rows,extra,missing). finite_inspection_rows_hold rows) review=Some True,
    map_option (\<lambda>(rows,extra,missing). extra={||} \<and> missing={||}) review=Some True))"

definition native_derivation_inspect :: "native_derivation_assessment\<Rightarrow>nat\<Rightarrow>bool" where
  "native_derivation_inspect A f=(case A of (base,valid,domain) \<Rightarrow>
    if f<3 then finite_partial_result_inspect base f
    else if f=5 then finite_partial_result_inspect base 3
    else if f<5 then (fst base \<longrightarrow> (if f=3 then valid else domain)) else False)"

definition native_derivation_condition ::
    "nat\<Rightarrow>(native_history_problem\<Rightarrow>native_derivation_result)\<Rightarrow>native_history_problem\<Rightarrow>bool" where
  "native_derivation_condition f method X=(if f=5 then
    (\<not>native_history_ready_condition X \<longrightarrow> method X=None)
    else if f<5 then (native_history_ready_condition X \<longrightarrow>
      (if f=2 then native_history_program_condition (\<lambda>P Q A T. P=Q) X (method X)
        else if f=3 then native_history_program_condition (\<lambda>P Q A T. finite_proofs_sound P T) X (method X)
        else if f=4 then native_history_program_condition (\<lambda>P Q A T. fimage fst T=A) X (method X)
        else native_history_answer_condition f X (method X))) else False)"

theorem native_derivation_assessment_exact:
  "native_derivation_inspect (native_derivation_assessment X (method X)) f=
    native_derivation_condition f method X"
  apply (simp only: native_derivation_assessment_def Let_def
    native_derivation_evidence_valid_exact native_derivation_evidence_domain_exact)
  by (auto simp: native_derivation_inspect_def case_prod_conv fst_conv
    finite_partial_result_inspect_def native_derivation_condition_def native_history_ready_exact
    native_history_program_observation_exact native_history_answer_exact split: if_splits; arith)

export_code native_derivation_assessment native_derivation_inspect native_derivation_evidence_review checking SML

text \<open>
  The original native source and request supply the reference meaning and
  certificate checker. Candidate source substitutions cannot change that
  boundary. Every full certificate and its actual validity result are retained,
  together with every extra or missing claim in the certificate domain.
  The six independent conditions cover answer soundness and completeness,
  source identity, certificate validity, exact answer coverage and refusal
  when the original source or evaluation prerequisites are unavailable.
\<close>

end
