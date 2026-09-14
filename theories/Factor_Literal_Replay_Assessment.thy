theory Factor_Literal_Replay_Assessment
  imports Factor_Literal_Replay_Cases Boolean_Decision_Assessments
begin

definition literal_replay_condition where
  "literal_replay_condition f method X=boolean_decision_condition f literal_replay_holds method X"

definition literal_replay_optional_condition where
  "literal_replay_optional_condition f method X=optional_decision_condition f literal_replay_holds method X"

definition literal_replay_row_assessment where
  "literal_replay_row_assessment m row=assess_decision_row literal_replay_report
    (literal_replay_decide 0) (literal_replay_decide m) row"

definition literal_replay_row_inspect where
  "literal_replay_row_inspect row f=decision_row_inspect row f"

lemma literal_replay_read_decisions:
  "literal_replay_decide 0 \<circ> literal_replay_report=literal_replay_holds"
  "literal_replay_decide m \<circ> literal_replay_report=literal_replay_method m"
  by (rule ext; simp only: comp_apply literal_replay_method_def[symmetric] literal_replay_original_exact)+

lemma literal_replay_reference_function:
  "literal_replay_method 0=literal_replay_holds"
  by (rule ext) (rule literal_replay_original_exact)

lemma literal_replay_row_exact:
  "literal_replay_row_inspect (literal_replay_row_assessment m (c,X)) f=
    literal_replay_optional_condition f (literal_replay_method m) X"
  by (simp only: literal_replay_row_inspect_def literal_replay_row_assessment_def
    decision_row_assessment_exact literal_replay_read_decisions literal_replay_reference_function
    literal_replay_optional_condition_def)

definition literal_replay_family_condition where
  "literal_replay_family_condition f method problem=(case problem of (seed,w) \<Rightarrow>
    (\<exists>c X. (c,Some X) |\<in>| literal_replay_family seed 0 \<and> literal_replay_holds X) \<and>
    (\<forall>(c,X)\<in>fset (literal_replay_family seed w). literal_replay_optional_condition f method X))"

definition literal_replay_family_assessment where
  "literal_replay_family_assessment m problem=(case problem of (seed,w) \<Rightarrow>
    decision_family_assessment literal_replay_report (literal_replay_decide 0) (literal_replay_decide m)
      (literal_replay_covered seed,literal_replay_family seed w))"

definition literal_replay_family_inspect where
  "literal_replay_family_inspect report f=decision_family_inspect report f"

theorem literal_replay_family_assessment_exact:
  "literal_replay_family_inspect (literal_replay_family_assessment m X) f=
    literal_replay_family_condition f (literal_replay_method m) X"
  by (cases X) (simp only: literal_replay_family_inspect_def literal_replay_family_assessment_def
    case_prod_conv decision_family_assessment_exact literal_replay_read_decisions literal_replay_reference_function
    decision_family_condition_def literal_replay_family_condition_def literal_replay_covered_exact
    literal_replay_optional_condition_def)

text \<open>
  The shared Boolean and optional-family assessment consumes the all-input
  literal-replay contract. Full native package, application and proof readings
  precede each method decision. The original valid case is still required for
  coverage, and every unavailable replay remains a failed required subject.
\<close>

end
