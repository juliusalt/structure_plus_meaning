theory Finite_Relation_Reader_Assessments
  imports Finite_Assessment_Reports
begin

definition finite_reader_inspect where
  "finite_reader_inspect report (f::nat)=(case report of (result,reference) \<Rightarrow>
    if f=0 then fBall result (\<lambda>x. x |\<in>| reference)
    else if f=1 then fBall reference (\<lambda>x. x |\<in>| result) else False)"

definition relation_reader_condition where
  "relation_reader_condition relation (f::nat) result=(if f=0 then
      (\<forall>x. x |\<in>| result \<longrightarrow> relation x)
    else if f=1 then (\<forall>x. relation x \<longrightarrow> x |\<in>| result) else False)"

theorem finite_reader_inspect_exact:
  assumes reference: "\<And>x. x |\<in>| expected \<longleftrightarrow> relation x"
  shows "finite_reader_inspect (result,expected) f=relation_reader_condition relation f result"
  using reference by (auto simp: finite_reader_inspect_def relation_reader_condition_def Ball_def)

text \<open>
  The complete reference reader must have an exact relation for every possible
  result. Its computed values then determine soundness and completeness of an
  actual candidate result. A supplied satisfaction table supplies no premise.
\<close>

end
