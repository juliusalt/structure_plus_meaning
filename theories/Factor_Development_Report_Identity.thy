theory Factor_Development_Report_Identity
  imports Factor_Development_Cycle Projected_Identity_Execution
begin

definition development_execution_shape where
  "development_execution_shape execution=(case execution of (S,P,D,A,T,ys) \<Rightarrow>
    (T={||},length ys))"

definition development_report_shape where
  "development_report_shape report=(
    map_option (\<lambda>(P,D,A,rows). length rows) (development_generation report),
    map_option (map (\<lambda>S. S\<noteq>None)) (development_compiled_conditions report),
    map_option (map (map_option development_execution_shape)) (development_observed_conditions report),
    map_option development_execution_shape (development_scope_review report),
    development_comparison report\<noteq>None,development_revision report\<noteq>None)"

definition development_report_contents where
  "development_report_contents report=(development_generation report,
    development_compiled_conditions report,development_observed_conditions report,
    development_scope_review report,development_comparison report,development_revision report,
    native_development_report.more report)"

lemma development_report_contents_injective:
  "development_report_contents x=development_report_contents y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: development_report_contents_def)

lemma native_development_report_equal_shape_code [code]:
  "HOL.equal (x::'a::equal native_development_report_scheme) y=
    observed_identity development_report_shape development_report_contents x y"
  by (simp only: equal_eq observed_identity_exact[OF development_report_contents_injective])

text \<open>Missing phases, lost ordered generation rows and omitted certificates
  are visible before comparing large source, term and proof structures. These
  observations are computed from the actual reports, not from a producer number.
  Every agreeing shape still receives the complete field comparison, including
  arbitrary record extensions. No positive verdict follows from shape alone.\<close>

end
