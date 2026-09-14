theory Factor_Literal_Replay_Assessment
  imports Factor_Literal_Replay_Cases Finite_Assessment_Reports
begin

definition literal_replay_condition where
  "literal_replay_condition (f::nat) method X=(if f=0 then (method X \<longrightarrow> literal_replay_holds X)
    else if f=1 then (literal_replay_holds X \<longrightarrow> method X) else False)"

definition literal_replay_optional_condition where
  "literal_replay_optional_condition f method X=(case X of None \<Rightarrow> False
    | Some x \<Rightarrow> literal_replay_condition f method x)"

definition literal_replay_row_assessment where
  "literal_replay_row_assessment m row=(case row of (c,X) \<Rightarrow>
    (c,map_option (\<lambda>x. let report=literal_replay_report x in
      (x,report,literal_replay_decide 0 report,literal_replay_decide m report)) X))"

definition literal_replay_row_inspect where
  "literal_replay_row_inspect row (f::nat)=(case row of (c,result) \<Rightarrow>
    case result of None \<Rightarrow> False | Some (X,report,original,chosen) \<Rightarrow>
      if f=0 then (chosen \<longrightarrow> original) else if f=1 then (original \<longrightarrow> chosen) else False)"

lemma literal_replay_row_exact:
  "literal_replay_row_inspect (literal_replay_row_assessment m (c,X)) f=
    literal_replay_optional_condition f (literal_replay_method m) X"
  by (cases X) (simp_all add: literal_replay_row_assessment_def literal_replay_row_inspect_def
    literal_replay_optional_condition_def literal_replay_condition_def Let_def
    literal_replay_method_def[symmetric] literal_replay_original_exact)

definition literal_replay_family_condition where
  "literal_replay_family_condition f method problem=(case problem of (seed,w) \<Rightarrow>
    (\<exists>c X. (c,Some X) |\<in>| literal_replay_family seed 0 \<and> literal_replay_holds X) \<and>
    (\<forall>(c,X)\<in>fset (literal_replay_family seed w). literal_replay_optional_condition f method X))"

definition literal_replay_family_assessment where
  "literal_replay_family_assessment m problem=(case problem of (seed,w) \<Rightarrow>
    (literal_replay_covered seed,fimage (literal_replay_row_assessment m) (literal_replay_family seed w)))"

definition literal_replay_family_inspect where
  "literal_replay_family_inspect report f=(case report of (covered,rows) \<Rightarrow>
    covered \<and> fBall rows (\<lambda>row. literal_replay_row_inspect row f))"

theorem literal_replay_family_assessment_exact:
  "literal_replay_family_inspect (literal_replay_family_assessment m X) f=
    literal_replay_family_condition f (literal_replay_method m) X"
proof -
  have rows: "fBall (fimage (literal_replay_row_assessment m) R)
      (\<lambda>row. literal_replay_row_inspect row f)=
    (\<forall>(c,Y)\<in>fset R. literal_replay_optional_condition f (literal_replay_method m) Y)" for R
  proof -
    have mapped: "fBall (fimage (literal_replay_row_assessment m) R)
        (\<lambda>row. literal_replay_row_inspect row f)=
      fBall R (\<lambda>row. literal_replay_row_inspect (literal_replay_row_assessment m row) f)"
      by (rule FSet.ball_simps(7))
    have each: "literal_replay_row_inspect (literal_replay_row_assessment m row) f=
      (case row of (c,Y) \<Rightarrow> literal_replay_optional_condition f (literal_replay_method m) Y)" for row
      by (cases row) (simp only: literal_replay_row_exact case_prod_conv)
    show ?thesis by (simp only: mapped each)
  qed
  show ?thesis by (cases X) (simp only: literal_replay_family_inspect_def
    literal_replay_family_assessment_def literal_replay_family_condition_def
    case_prod_conv literal_replay_covered_exact rows)
qed

text \<open>
  Soundness and completeness concern the original actual native source, call,
  evidence root and whole requested payload. Full package, application and
  replay readings accompany every computed decision. The original valid case
  is required for coverage, and each unavailable returned replay remains a
  failed required subject. No supplied satisfaction table enters the comparison.
\<close>

end
