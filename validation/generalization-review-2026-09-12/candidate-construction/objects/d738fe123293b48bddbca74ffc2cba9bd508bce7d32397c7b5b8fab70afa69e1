theory Factor_Binding_Observation_Programs
  imports Factor_Binding_Observation_Contracts
begin

section \<open>The complete conversion has one fixed native program\<close>

theorem fixed_native_binding_observations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and> inj_on g {347::nat} \<and>
    (\<forall>d\<in>{347::nat}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> binding_observation_result t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
  by (rule compiled_exact_operations[OF binding_observation_program_formed])
    (auto simp: binding_observation_call binding_observation_exact)

text \<open>
  The general compilation contract places the operation before every later
  input, with the same retained scope and original artifacts and bindings.
  The operation checks row-prefix equality and preserves both components.
  Actual use admission, complete functional bindings, and pattern admission
  belong to the surrounding native readers of a symbolic argument.
\<close>

end
