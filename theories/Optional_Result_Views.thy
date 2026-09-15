theory Optional_Result_Views
  imports Main
begin

theorem optional_result_view_projection:
  assumes projection: "map_option project result=original"
    and each: "\<And>value. result=Some value \<Longrightarrow> read value=original_read (project value)"
  shows "map_option read result=map_option original_read original"
  by (cases result) (simp_all add: projection[symmetric] each)

theorem optional_single_result_projection:
  assumes domain: "result\<noteq>None \<longleftrightarrow> available"
    and each: "\<And>value. result=Some value \<Longrightarrow> read value=original"
  shows "map_option read result=(if available then Some original else None)"
  using domain by (cases result) (simp_all add: each)

text \<open>
  Complete views compose through an established optional projection. An exact
  availability condition and the whole view of each actual result likewise
  determine an optional singleton result. Both statements retain every failure
  and require the caller's actual operation equations.
\<close>

end
