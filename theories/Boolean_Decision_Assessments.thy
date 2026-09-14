theory Boolean_Decision_Assessments
  imports Finite_Assessment_Reports
begin

definition boolean_decision_facet where
  "boolean_decision_facet (f::nat) original chosen=(if f=0 then (chosen \<longrightarrow> original)
    else if f=1 then (original \<longrightarrow> chosen) else False)"

definition boolean_decision_condition where
  "boolean_decision_condition f original method x=boolean_decision_facet f (original x) (method x)"

definition optional_decision_condition where
  "optional_decision_condition f original method X=(case X of None \<Rightarrow> False
    | Some x \<Rightarrow> boolean_decision_condition f original method x)"

definition prepare_decision_row where
  "prepare_decision_row read row=(case row of (k,X) \<Rightarrow> (k,map_option (\<lambda>x. (x,read x)) X))"

definition assess_prepared_decision_row where
  "assess_prepared_decision_row original select_result row=(case row of (k,X) \<Rightarrow>
    (k,map_option (\<lambda>(x,r). (x,r,original r,select_result r)) X))"

definition assess_decision_row where
  "assess_decision_row read original select_result row=
    assess_prepared_decision_row original select_result (prepare_decision_row read row)"

definition decision_row_inspect where
  "decision_row_inspect row f=(case row of (k,X) \<Rightarrow> case X of None \<Rightarrow> False
    | Some (x,r,original,chosen) \<Rightarrow> boolean_decision_facet f original chosen)"

theorem decision_row_assessment_exact:
  "decision_row_inspect (assess_decision_row read original select_result (k,X)) f=
    optional_decision_condition f (original \<circ> read) (select_result \<circ> read) X"
  by (cases X) (simp_all add: decision_row_inspect_def assess_decision_row_def
    assess_prepared_decision_row_def prepare_decision_row_def optional_decision_condition_def
    boolean_decision_condition_def comp_def)

definition prepare_decision_family where
  "prepare_decision_family read R=fimage (prepare_decision_row read) R"

definition assess_prepared_decision_family where
  "assess_prepared_decision_family original select_result report=(case report of (covered,rows) \<Rightarrow>
    (covered,fimage (assess_prepared_decision_row original select_result) rows))"

definition decision_family_assessment where
  "decision_family_assessment read original select_result problem=(case problem of (covered,rows) \<Rightarrow>
    assess_prepared_decision_family original select_result (covered,prepare_decision_family read rows))"

definition decision_family_inspect where
  "decision_family_inspect report f=(case report of (covered,rows) \<Rightarrow>
    covered \<and> fBall rows (\<lambda>row. decision_row_inspect row f))"

definition decision_family_condition where
  "decision_family_condition f original method problem=(case problem of (covered,rows) \<Rightarrow>
    covered \<and> (\<forall>(k,X)\<in>fset rows. optional_decision_condition f original method X))"

lemma decision_family_assessment_rows:
  "decision_family_assessment read original select_result (covered,rows)=
    (covered,fimage (assess_decision_row read original select_result) rows)"
  by (simp add: decision_family_assessment_def assess_prepared_decision_family_def prepare_decision_family_def
    fimage_fimage comp_def assess_decision_row_def[abs_def])

theorem decision_family_assessment_exact:
  "decision_family_inspect (decision_family_assessment read original select_result X) f=
    decision_family_condition f (original \<circ> read) (select_result \<circ> read) X"
proof -
  have rows: "fBall (fimage (assess_decision_row read original select_result) R)
      (\<lambda>row. decision_row_inspect row f)=
    (\<forall>(k,Y)\<in>fset R. optional_decision_condition f (original \<circ> read) (select_result \<circ> read) Y)" for R
  proof -
    have mapped: "fBall (fimage (assess_decision_row read original select_result) R)
        (\<lambda>row. decision_row_inspect row f)=
      fBall R (\<lambda>row. decision_row_inspect (assess_decision_row read original select_result row) f)"
      by (rule FSet.ball_simps(7))
    have each: "decision_row_inspect (assess_decision_row read original select_result row) f=
      (case row of (k,Y) \<Rightarrow> optional_decision_condition f (original \<circ> read) (select_result \<circ> read) Y)" for row
      by (cases row) (simp only: decision_row_assessment_exact case_prod_conv)
    show ?thesis by (simp only: mapped each)
  qed
  show ?thesis by (cases X) (simp only: decision_family_assessment_rows decision_family_inspect_def
    decision_family_condition_def case_prod_conv rows)
qed

text \<open>
  Each original subject and its complete reader result are retained before any
  candidate decision. Every unavailable required row fails both conditions.
  Coverage is an explicit separate premise whose source contract belongs to the
  caller. A client must connect the reference decision after reading to its
  independently defined condition. This common calculation supplies no such
  subject meaning by itself.
\<close>

end
