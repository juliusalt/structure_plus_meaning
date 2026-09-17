theory Finite_Partial_Result_Inspection
  imports "HOL-Library.FSet"
begin

lemma partial_source_result_available:
  assumes reading: "\<And>P A. result=Some (P,A) \<longleftrightarrow> source P \<and> meaning P A"
    and total: "\<And>P. source P \<Longrightarrow> \<exists>A. result=Some (P,A)"
  shows "result\<noteq>None \<longleftrightarrow> (\<exists>P. source P)"
  using reading total by (cases result) auto

type_synonym 'a finite_partial_result_assessment =
  "bool\<times>('a fset\<times>'a fset) option\<times>bool\<times>bool"

definition finite_partial_result_inspect :: "'a finite_partial_result_assessment\<Rightarrow>nat\<Rightarrow>bool" where
  "finite_partial_result_inspect A f=(case A of (ready,terms,retained,rejected) \<Rightarrow>
    if f=3 then (\<not>ready \<longrightarrow> rejected)
    else if f<3 then (ready \<longrightarrow>
      (if f=2 then retained else case terms of None \<Rightarrow> False | Some (extra,missing) \<Rightarrow>
        (if f=0 then extra={||} else missing={||}))) else False)"

end
