theory Optional_Result_Invariants
  imports Main
begin

lemma optional_result_invariant:
  assumes every: "\<And>y. result=Some y \<Longrightarrow> P y"
  shows "pred_option P result"
  by (cases result) (auto intro: every)

end
