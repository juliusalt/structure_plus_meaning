theory Finite_Optional_Report_Observations
  imports Main
begin

definition optional_report_observation where
  "optional_report_observation enabled evaluation values=(if enabled then
    (case evaluation of None \<Rightarrow> None | Some (source,answer) \<Rightarrow>
      map_option (Pair source) values) else None)"

theorem optional_report_observation_map:
  "optional_report_observation enabled evaluation (map_option (\<lambda>(source,answer). f answer) evaluation)=
    (if enabled then map_option (\<lambda>(source,answer). (source,f answer)) evaluation else None)"
  by (cases evaluation) (simp_all add: optional_report_observation_def split: prod.splits)

text \<open>
  A supported observation reuses the actual evaluation's source and computed
  projection. A missing evaluation or missing projection remains unavailable.
  The exact equation requires that the projection came from that evaluation;
  arbitrary supplied report fields acquire no observation contract.
\<close>

end
