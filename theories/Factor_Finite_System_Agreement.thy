theory Factor_Finite_System_Agreement
  imports Factor_Finite_System_Fields Factor_Positive_Locality
begin

section \<open>Agreement checks every actual interface and clause in either program\<close>

definition finite_system_agrees_on where
  "finite_system_agrees_on P Q U \<longleftrightarrow>
    fBall (finite_system_interfaces P |\<union>| finite_system_interfaces Q) (\<lambda>(d,p).
      d |\<in>| U \<longrightarrow> ((d,p) |\<in>| finite_system_interfaces P \<longleftrightarrow> (d,p) |\<in>| finite_system_interfaces Q)) \<and>
    fBall (finite_system_clauses P |\<union>| finite_system_clauses Q) (\<lambda>((d,c),S).
      d |\<in>| U \<longrightarrow> (((d,c),S) |\<in>| finite_system_clauses P \<longleftrightarrow> ((d,c),S) |\<in>| finite_system_clauses Q))"

theorem finite_system_agrees_on_correct:
  "finite_system_agrees_on P Q U \<longleftrightarrow>
    systems_agree_on (decode_finite_system P) (decode_finite_system Q) (fset U)"
  by (auto simp: finite_system_agrees_on_def systems_agree_on_def map_relation_values_def
    Ball_def split_paired_All; force)

export_code finite_system_agrees_on checking SML

end
