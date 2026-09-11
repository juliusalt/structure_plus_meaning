theory Factor_Admission_Plan_Realization
  imports Factor_Admission_Plan_Contracts Factor_Admission_Plan_Exact
begin

corollary native_admission_plan_installed:
  assumes native: "(341,z)\<in>positive_meaning admission_plan_system"
    and shape: "z=admission_plan_argument (admission_goal_value g) (admission_counter n)
      (admission_counter d) (admission_counter k) (data_list_term (map admission_instruction_value cs))"
    and source: "admission_source P n"
    and supported: "admission_goal_sites g\<subseteq>system_definitions P"
  shows "schema_system_formed (install_admission_plan P cs) \<and>
    systems_agree_on P (install_admission_plan P cs) (system_definitions P) \<and>
    (\<forall>t. (d,t)\<in>positive_meaning (install_admission_plan P cs) \<longleftrightarrow>
      admission_goal_holds (positive_meaning P) g t)"
proof -
  have mapped: "map admission_instruction_value xs=map admission_instruction_value ys \<longleftrightarrow> xs=ys" for xs ys
    by (induction xs arbitrary: ys) (case_tac ys; auto)+
  obtain h m r l xs where computation: "admission_plan h m=(r,l,xs)"
    and frame: "z=admission_plan_argument (admission_goal_value h) (admission_counter m)
      (admission_counter r) (admission_counter l) (data_list_term (map admission_instruction_value xs))"
    using admission_plan_sound[OF native] by (auto simp: admission_plan_result_def)
  have fields: "h=g" "m=n" "r=d" "l=k" "xs=cs"
    using frame shape by (auto simp: data_list_term_injective mapped)
  have plan: "admission_plan g n=(d,k,cs)" using computation by (simp add: fields)
  show ?thesis using admission_plan_installed[OF source supported plan]
    by (auto simp: admission_source_def admission_extension_def)
qed

end
