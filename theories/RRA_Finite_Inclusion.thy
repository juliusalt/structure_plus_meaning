theory RRA_Finite_Inclusion
  imports RRA_Finite_Environments
begin

section \<open>Inclusion compares both complete finite environment tables\<close>

definition finite_environment_included ::
  "'u finite_artifact_environment \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> bool" where
  "finite_environment_included C D \<longleftrightarrow>
    finite_environment_artifacts C |\<subseteq>| finite_environment_artifacts D \<and>
    finite_environment_bindings C |\<subseteq>| finite_environment_bindings D"

theorem finite_environment_included_correct:
  "finite_environment_included C D \<longleftrightarrow>
    environment_included (decode_finite_environment C) (decode_finite_environment D)"
  by (auto simp: finite_environment_included_def environment_included_def map_relation_values_def)

export_code finite_environment_included checking SML

text \<open>
  Complete artifact equality includes every carrier, incidence, and data row.
  Inclusion also retains every outgoing binding. Formation is a separate
  condition on each environment, just as in the original relation.
\<close>

end
