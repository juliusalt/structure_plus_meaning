theory Finite_Prepared_Reader_Inspections
  imports Finite_Reader_Identity_Maps Finite_Assessment_Reports
begin

definition prepared_reader_inspection where
  "prepared_reader_inspection encode report=(case report of (result,reference) \<Rightarrow>
    let results=fimage encode result; references=fimage encode reference
    in finite_reader_inspect (results,references))"

lemma prepared_reader_inspection_exact:
  assumes "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "prepared_reader_inspection encode report=finite_reader_inspect report"
  by (rule ext; cases report)
    (simp add: prepared_reader_inspection_def Let_def finite_reader_inspect_identity_map[OF assms])

declare context_assessment_investigation_def[code del]

lemma context_assessment_prepared_inspection_code [code]:
  "context_assessment_investigation cs fs ws table inspect=
    assessed_subject_investigation cs fs ws (context_assessment_lookup table)
      (\<lambda>A. case A of None \<Rightarrow> (\<lambda>f. False) | Some a \<Rightarrow> inspect a)"
proof -
  have same: "(\<lambda>A f. case A of None \<Rightarrow> False | Some a \<Rightarrow> inspect a f)=
      (\<lambda>A. case A of None \<Rightarrow> (\<lambda>f. False) | Some a \<Rightarrow> inspect a)"
    by (rule ext; rename_tac A; case_tac A) simp_all
  show ?thesis by (simp only: context_assessment_investigation_def same)
qed

end
