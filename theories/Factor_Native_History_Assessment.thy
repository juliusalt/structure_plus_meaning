theory Factor_Native_History_Assessment
  imports Factor_Native_History_Cases Factor_Finite_Program_History_Inspection
    Factor_Finite_Native_Evaluation_Readings Finite_Term_Observation_Comparisons Finite_Partial_Result_Inspection
begin

type_synonym native_history_assessment =
  "native_history_call finite_partial_result_assessment\<times>bool\<times>bool"

definition native_history_original where
  "native_history_original X=(case X of (E,u,r,D) \<Rightarrow> finite_native_program_evaluation E u r D)"

definition native_history_source_condition where
  "native_history_source_condition X P=(case X of (E,u,r,D) \<Rightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    finite_program_evaluation_ready P D)"

definition native_history_meaning where
  "native_history_meaning X P=(case X of (E,u,r,D) \<Rightarrow>
    {q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)})"

lemma native_history_original_reading:
  "native_history_original X=Some (P,A) \<longleftrightarrow>
    native_history_source_condition X P \<and> fset A=native_history_meaning X P"
  by (simp add: native_history_original_def native_history_source_condition_def
    native_history_meaning_def finite_native_program_evaluation_semantics split: prod.splits)

lemma native_history_original_total:
  assumes "native_history_source_condition X P"
  shows "\<exists>A. native_history_original X=Some (P,A)"
proof -
  obtain E u r D where fields: "X=(E,u,r,D)" by (cases X)
  have package: "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    and ready: "finite_program_evaluation_ready P D"
    using assms by (simp only: fields native_history_source_condition_def case_prod_conv; blast)+
  obtain A where answer: "finite_program_evaluation P D=Some A"
    using ready by (simp only: finite_program_evaluation_ready_def finite_program_evaluation_conditions[symmetric]; blast)
  show ?thesis by (rule exI[of _ A])
    (simp only: fields native_history_original_def case_prod_conv finite_native_program_evaluation_conditions
      package answer)
qed

definition native_history_ready where
  "native_history_ready X=(native_history_original X\<noteq>None)"

definition native_history_ready_condition where
  "native_history_ready_condition X=(\<exists>P. native_history_source_condition X P)"

lemma native_history_ready_exact:
  "native_history_ready X=native_history_ready_condition X"
  unfolding native_history_ready_def native_history_ready_condition_def
  by (rule partial_source_result_available)
    (rule native_history_original_reading, rule native_history_original_total)

definition native_history_program_observation where
  "native_history_program_observation test X result=(case native_history_original X of
    None \<Rightarrow> False | Some (P,B) \<Rightarrow>
      (case result of None \<Rightarrow> False | Some (Q,A,Hs) \<Rightarrow> test P Q A Hs))"

definition native_history_program_condition where
  "native_history_program_condition test X result=(case result of None \<Rightarrow> False
    | Some (Q,A,Hs) \<Rightarrow> \<exists>P. native_history_source_condition X P \<and> test P Q A Hs)"

lemma native_history_program_observation_exact:
  "native_history_program_observation test X result=native_history_program_condition test X result"
proof
  assume observed: "native_history_program_observation test X result"
  obtain P B Q A Hs where original: "native_history_original X=Some (P,B)"
    and candidate: "result=Some (Q,A,Hs)" and tested: "test P Q A Hs"
    using observed by (auto simp: native_history_program_observation_def split: option.splits prod.splits)
  have ready: "native_history_source_condition X P"
    using original by (simp only: native_history_original_reading; blast)
  show "native_history_program_condition test X result"
    using ready tested by (simp only: native_history_program_condition_def candidate option.case case_prod_conv; blast)
next
  assume condition: "native_history_program_condition test X result"
  obtain P Q A Hs where candidate: "result=Some (Q,A,Hs)"
    and ready: "native_history_source_condition X P" and tested: "test P Q A Hs"
    using condition by (auto simp: native_history_program_condition_def split: option.splits prod.splits)
  obtain B where original: "native_history_original X=Some (P,B)"
    using native_history_original_total[OF ready] by blast
  show "native_history_program_observation test X result"
    by (simp only: native_history_program_observation_def original candidate option.case case_prod_conv tested)
qed

definition native_history_answer_observation where
  "native_history_answer_observation X result=finite_term_observation_comparison
    (native_history_original X) (map_option (\<lambda>(Q,A,Hs). (Q,A)) result)"

definition native_history_answer_condition where
  "native_history_answer_condition f X result=(\<exists>P Q A Hs.
    native_history_source_condition X P \<and> result=Some (Q,A,Hs) \<and>
      (if f=0 then fset A\<subseteq>native_history_meaning X P
        else native_history_meaning X P\<subseteq>fset A))"

lemma native_history_answer_exact:
  "(case native_history_answer_observation X result of None \<Rightarrow> False
    | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))=
      native_history_answer_condition f X result"
proof -
  have compared: "finite_term_observation_comparison_holds f (native_history_original X)
      (map_option (\<lambda>(Q,A,Hs). (Q,A)) result) \<longleftrightarrow>
    (\<exists>P Q A. native_history_source_condition X P \<and>
      map_option (\<lambda>(Q,A,Hs). (Q,A)) result=Some (Q,A) \<and>
      (if f=0 then fset A\<subseteq>native_history_meaning X P
        else native_history_meaning X P\<subseteq>fset A))"
    by (rule finite_term_observation_comparison_containment[OF _ native_history_original_total])
      (simp only: native_history_original_reading)
  show ?thesis using compared
    by (auto simp: finite_term_observation_comparison_holds_def native_history_answer_observation_def
      native_history_answer_condition_def split: prod.splits)
qed

definition native_history_steps_observation where
  "native_history_steps_observation X result=(case X of (E,u,r,D) \<Rightarrow>
    native_history_program_observation (\<lambda>P Q A Hs. finite_program_history_steps P D A Hs) X result)"
definition native_history_steps_condition where
  "native_history_steps_condition X result=(case X of (E,u,r,D) \<Rightarrow>
    native_history_program_condition (\<lambda>P Q A Hs. program_history_steps P D A Hs) X result)"

lemma native_history_steps_exact:
  "native_history_steps_observation X result=native_history_steps_condition X result"
  by (simp add: native_history_steps_observation_def native_history_steps_condition_def
    native_history_program_observation_exact finite_program_history_steps_exact split: prod.splits)

definition native_history_witness_observation where
  "native_history_witness_observation X result=(case X of (E,u,r,D) \<Rightarrow>
    native_history_program_observation (\<lambda>P Q A Hs. finite_program_history_witnesses P D Hs) X result)"
definition native_history_witness_condition where
  "native_history_witness_condition X result=(case X of (E,u,r,D) \<Rightarrow>
    native_history_program_condition (\<lambda>P Q A Hs. program_history_witnesses P D Hs) X result)"

lemma native_history_witness_exact:
  "native_history_witness_observation X result=native_history_witness_condition X result"
  by (auto simp: native_history_witness_observation_def native_history_witness_condition_def
    native_history_program_observation_exact native_history_program_condition_def
    native_history_source_condition_def finite_program_evaluation_ready_def
    finite_program_history_witnesses_exact split: prod.splits option.splits)

definition native_history_evidence_review where
  "native_history_evidence_review X result=(case X of (E,u,r,D) \<Rightarrow>
    (case native_history_original X of None \<Rightarrow> None | Some (P,B) \<Rightarrow>
      map_option (\<lambda>(Q,A,Hs). (finite_program_history_step_review P D A Hs,
        finite_program_history_witness_review P D Hs)) result))"

lemma native_history_evidence_step_exact:
  "(map_option (\<lambda>(steps,witnesses). iteration_review_holds steps)
    (native_history_evidence_review X result)=Some True)=native_history_steps_observation X result"
  by (cases X; cases "native_history_original X"; cases result)
    (simp_all only: native_history_evidence_review_def native_history_steps_observation_def
    native_history_program_observation_def finite_program_history_step_review_exact
    option.simps option.map_comp comp_def split_def fst_conv snd_conv simp_thms)

lemma native_history_evidence_witness_exact:
  "(map_option (\<lambda>(steps,witnesses). finite_inference_witness_review_holds witnesses)
    (native_history_evidence_review X result)=Some True)=native_history_witness_observation X result"
  by (cases X; cases "native_history_original X"; cases result)
    (simp_all only: native_history_evidence_review_def native_history_witness_observation_def
    native_history_program_observation_def finite_program_history_witness_review_exact
    option.simps option.map_comp comp_def split_def fst_conv snd_conv simp_thms)

definition native_history_assessment where
  "native_history_assessment X result=(let review=native_history_evidence_review X result in
    ((native_history_ready X,native_history_answer_observation X result,
      native_history_program_observation (\<lambda>P Q A Hs. P=Q) X result,result=None),
    map_option (\<lambda>(steps,witnesses). iteration_review_holds steps) review=Some True,
    map_option (\<lambda>(steps,witnesses). finite_inference_witness_review_holds witnesses) review=Some True))"

definition native_history_inspect :: "native_history_assessment\<Rightarrow>nat\<Rightarrow>bool" where
  "native_history_inspect A f=(case A of (base,steps,witnesses) \<Rightarrow>
    if f<4 then finite_partial_result_inspect base f
    else if f<6 then (fst base \<longrightarrow> (if f=4 then steps else witnesses)) else False)"

definition native_history_condition where
  "native_history_condition f method X=(if f=3 then
    (\<not>native_history_ready_condition X \<longrightarrow> method X=None)
    else if f<6 then (native_history_ready_condition X \<longrightarrow>
      (if f=2 then native_history_program_condition (\<lambda>P Q A Hs. P=Q) X (method X)
        else if f=4 then native_history_steps_condition X (method X)
        else if f=5 then native_history_witness_condition X (method X)
        else native_history_answer_condition f X (method X))) else False)"

theorem native_history_assessment_exact:
  "native_history_inspect (native_history_assessment X (method X)) f=native_history_condition f method X"
  apply (simp only: native_history_assessment_def Let_def
    native_history_evidence_step_exact native_history_evidence_witness_exact)
  by (auto simp: native_history_inspect_def case_prod_conv fst_conv
    finite_partial_result_inspect_def native_history_condition_def native_history_ready_exact
    native_history_program_observation_exact native_history_steps_exact native_history_witness_exact
    native_history_answer_exact split: if_splits; arith)

export_code native_history_assessment native_history_inspect native_history_evidence_review checking SML

text \<open>
  Answers are compared with the original positive meaning, restricted to the
  actual demand. Extra and missing calls are retained completely. Availability
  requires the actual package, program formation, complete head scope and a
  closed demand. The positive obligations are conditional on that availability;
  its absence requires refusal and supplies no negative judgment about calls.

  Source identity, every progressive preceding state, the final fixed state,
  and every complete admitted schema instance are separate obligations. Every
  history is assessed against the actual original source, including histories
  that claim a different program. Neither the candidate's program claim nor
  its answer supplies the reference meaning or application family.

  Complete reviews retain every expected and offered state occurrence, every
  actual progress test, both final states and the final stop test. At each
  offered state they also retain every extra and missing activation row. Their
  exact equations preserve the independently stated conditions; a Boolean
  failure does not replace its complete structural reasons.
\<close>

end
