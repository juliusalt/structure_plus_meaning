theory Factor_Finite_Program_Evaluation
  imports Factor_Finite_Program_Applications Inference_Demands
begin

section \<open>A complete finite demand has the original program's exact meaning\<close>

definition finite_program_demand_closed where
  "finite_program_demand_closed P D \<longleftrightarrow>
    fBall (finite_program_rule_table P D) (\<lambda>(q,H). fimage snd H |\<subseteq>| D)"

definition program_demand_closed where
  "program_demand_closed P D \<longleftrightarrow>
    (\<forall>q H. q\<in>D \<longrightarrow> schema_inference_rules P q H \<longrightarrow> rel_ran H\<subseteq>D)"

lemma finite_program_demand_closed_correct:
  assumes covered: "finite_program_head_covered P D"
  shows "finite_program_demand_closed P D \<longleftrightarrow>
    program_demand_closed (decode_finite_system P) (decode_finite_call_term ` fset D)"
proof
  assume closed: "finite_program_demand_closed P D"
  show "program_demand_closed (decode_finite_system P) (decode_finite_call_term ` fset D)"
    unfolding program_demand_closed_def
  proof (intro allI impI)
    fix q H assume demand: "q\<in>decode_finite_call_term ` fset D"
      and rule: "schema_inference_rules (decode_finite_system P) q H"
    have embedded: "embedded_inferences decode_finite_call_term
      (finite_inference_rules (finite_program_rule_table P D)) q H"
      using demand rule by (simp only: finite_program_rules_exact[OF covered])
    obtain a G where member: "(a,G) |\<in>| finite_program_rule_table P D"
      and fields: "H=decode_finite_premises G"
      using embedded by (auto simp: embedded_inferences_def finite_inference_rules_def
        decode_finite_premises_def)
    have support: "fimage snd G |\<subseteq>| D"
      using fbspec[OF closed[unfolded finite_program_demand_closed_def] member] by simp
    show "rel_ran H\<subseteq>decode_finite_call_term ` fset D"
      using support by (simp only: fields decode_finite_premises_def
        finite_relation_values_support[OF decode_finite_call_inj(2)])
  qed
next
  assume closed: "program_demand_closed (decode_finite_system P) (decode_finite_call_term ` fset D)"
  have each: "fimage snd G |\<subseteq>| D"
    if member: "(q,G) |\<in>| finite_program_rule_table P D" for q G
  proof -
    have functional: "single_valued (fset G)" by (rule finite_program_rule_functional[OF member])
    have embedded: "embedded_inferences decode_finite_call_term
      (finite_inference_rules (finite_program_rule_table P D))
      (decode_finite_call_term q) (decode_finite_premises G)"
      unfolding embedded_inferences_def
      by (rule exI[of _ q], rule exI[of _ "fset G"])
        (use member functional in \<open>auto simp: finite_inference_rules_def decode_finite_premises_def\<close>)
    have support: "rel_ran (decode_finite_premises G)\<subseteq>decode_finite_call_term ` fset D"
      using closed embedded by (simp only: finite_program_rules_exact[OF covered] program_demand_closed_def; blast)
    show "fimage snd G |\<subseteq>| D"
      using support by (simp only: decode_finite_premises_def
        finite_relation_values_support[OF decode_finite_call_inj(2)])
  qed
  show "finite_program_demand_closed P D"
    unfolding finite_program_demand_closed_def
  proof (rule fBallI)
    fix x assume member: "x |\<in>| finite_program_rule_table P D"
    obtain q G where shape: "x=(q,G)" by (cases x)
    show "(case x of (q,H) \<Rightarrow> fimage snd H |\<subseteq>| D)"
      using each[OF member[unfolded shape]] by (simp only: shape case_prod_conv)
  qed
qed

theorem finite_program_closure_exact:
  assumes covered: "finite_program_head_covered P D" and closed: "finite_program_demand_closed P D"
    and demand: "q |\<in>| D"
  shows "q\<in>finite_inference_result (finite_program_rule_table P D) {||} \<longleftrightarrow>
    decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  let ?f="decode_finite_call_term"
  let ?F="finite_program_rule_table P D"
  let ?R="schema_inference_rules (decode_finite_system P)"
  let ?D="?f ` fset D"
  have rules: "embedded_inferences ?f (finite_inference_rules ?F)=(\<lambda>q H. ?R q H \<and> q\<in>?D)"
    by (rule ext, rule ext, rule finite_program_rules_exact[OF covered])
  have image: "?f ` finite_inference_result ?F {||}=
    inference_closure (\<lambda>q H. ?R q H \<and> q\<in>?D) {}"
    using finite_inference_result_embedding[OF decode_finite_call_inj(2), of ?F "{||}"]
    by (simp only: rules bot_fset.rep_eq image_empty)
  have native_closed: "program_demand_closed (decode_finite_system P) ?D"
    using closed by (simp only: finite_program_demand_closed_correct[OF covered])
  have inside: "?f q\<in>?D" by (rule imageI[OF demand])
  have restricted: "?f q\<in>inference_closure (\<lambda>q H. ?R q H \<and> q\<in>?D) {} \<longleftrightarrow>
    ?f q\<in>inference_closure ?R {}"
    by (rule inference_restriction_on_closed_demand[OF _ inside])
      (use native_closed in \<open>unfold program_demand_closed_def; blast\<close>)
  have reflect: "?f q\<in>?f ` finite_inference_result ?F {||} \<longleftrightarrow>
    q\<in>finite_inference_result ?F {||}"
    using decode_finite_call_inj(2) by (auto dest: injD)
  show ?thesis by (simp only: reflect[symmetric] image restricted schema_inference_closure)
qed

definition finite_program_evaluation_ready where
  "finite_program_evaluation_ready P D=
    (finite_system_formed P \<and> finite_program_head_covered P D \<and> finite_program_demand_closed P D)"

definition finite_program_evaluation where
  "finite_program_evaluation P D=(if finite_program_evaluation_ready P D then
      Some (let settled=finite_inference_result (finite_program_rule_table P D) {||}
        in ffilter (\<lambda>q. q\<in>settled) D) else None)"

theorem finite_program_evaluation_conditions:
  "(\<exists>A. finite_program_evaluation P D=Some A) \<longleftrightarrow>
    finite_system_formed P \<and> finite_program_head_covered P D \<and> finite_program_demand_closed P D"
  by (auto simp: finite_program_evaluation_def finite_program_evaluation_ready_def Let_def split: if_splits)

theorem finite_program_evaluation_exact:
  assumes result: "finite_program_evaluation P D=Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
proof -
  have formed: "finite_system_formed P" and covered: "finite_program_head_covered P D"
    and closed: "finite_program_demand_closed P D"
    and answer: "A=ffilter (\<lambda>q. q\<in>finite_inference_result (finite_program_rule_table P D) {||}) D"
    using result by (auto simp: finite_program_evaluation_def finite_program_evaluation_ready_def Let_def split: if_splits)
  show "schema_system_formed (decode_finite_system P)"
    using formed by (simp only: finite_system_formed_correct)
  show "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    using finite_program_closure_exact[OF covered closed]
    by (auto simp: answer)
qed

lemma finite_program_evaluation_semantics:
  "finite_program_evaluation Q D=Some A \<longleftrightarrow> finite_program_evaluation_ready Q D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system Q)}"
proof
  assume computed: "finite_program_evaluation Q D=Some A"
  show "finite_program_evaluation_ready Q D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system Q)}"
    using finite_program_evaluation_exact(2)[OF computed] computed
    by (auto simp: finite_program_evaluation_def split: if_splits)
next
  assume original: "finite_program_evaluation_ready Q D \<and>
    fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system Q)}"
  obtain B where computed: "finite_program_evaluation Q D=Some B"
    using original by (auto simp: finite_program_evaluation_def split: if_splits)
  have "A=B" using original finite_program_evaluation_exact(2)[OF computed]
    by (simp only: fset_inject[symmetric]; blast)
  then show "finite_program_evaluation Q D=Some A" using computed by simp
qed

export_code finite_program_demand_closed finite_program_evaluation checking SML

text \<open>
  The independent condition is the original positive meaning. The operation
  first checks program formation, complete requested head scope, and closure
  of every generated premise within the requested family. Success returns
  exactly the calls in that family having the original meaning. The finite
  inference operation starts with no supplied truths; cyclic support alone
  cannot establish a call.

  Failure to cover head variables or to close the demand returns no answer.
  It is not a negative judgment on the requested calls. This terminating
  conditional decision procedure does not decide unrestricted programs.
\<close>

end
