theory Factor_Native_Certificate_Input_Development
  imports Factor_Native_Certificate_Scope_Repair Factor_Native_Certificate_Development
begin

definition native_certificate_expanded_inputs where
  "native_certificate_expanded_inputs=certificate_scope_repair_method 2 native_certificate_original_inputs"

definition native_certificate_input_indices :: "nat list" where
  "native_certificate_input_indices=[0..<length native_certificate_expanded_inputs]"

definition native_certificate_input_problem where
  "native_certificate_input_problem w=(if w<length native_certificate_expanded_inputs
    then native_certificate_expanded_inputs!w else Native_Certificate_Query None)"

definition native_certificate_input_assess where
  "native_certificate_input_assess m w=native_certificate_input_assessment (native_certificate_input_problem w)
    (native_certificate_input_method m (native_certificate_input_problem w))"

definition native_certificate_input_quality where
  "native_certificate_input_quality m w f=native_certificate_inspect (native_certificate_input_assess m w) f"

lemma native_certificate_input_quality_exact:
  "native_certificate_input_quality m w f=native_certificate_input_condition f
    (native_certificate_input_method m) (native_certificate_input_problem w)"
  by (simp only: native_certificate_input_quality_def native_certificate_input_assess_def native_certificate_input_assessment_exact)

interpretation certificate_input: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]"
    "[0,1,2,3,4,5,6]" ws native_certificate_input_method native_certificate_input_condition
    native_certificate_input_problem native_certificate_input_quality for ws
  by (unfold_locales) (rule native_certificate_input_quality_exact)

definition native_certificate_input_investigation where
  "native_certificate_input_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
    [0,1,2,3,4,5,6] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_input_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_input_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_certificate_input_investigation_def},
   equation = @{thm certificate_input.observations_derived},
   formation = @{thm certificate_input.maps_formed},
   observation = @{thm certificate_input.observation_at_subject},
   comparison = @{thm certificate_input.comparison_at_subject}}\<close>

definition native_certificate_input_context where
  "native_certificate_input_context w=(let X=native_certificate_input_problem w;
    original=native_certificate_input_original X in (X,original,native_certificate_base_from original))"

lemma native_certificate_input_cell_at:
  "native_certificate_cell m (native_certificate_input_context w)=
    (native_certificate_input_method m (native_certificate_input_problem w),native_certificate_input_assess m w)"
  by (simp only: native_certificate_cell_def native_certificate_input_context_def native_certificate_input_method_def
    native_certificate_input_assess_def native_certificate_input_assessment_def Let_def case_prod_conv)

definition native_certificate_input_criticism_condition where
  "native_certificate_input_criticism_condition ws=(\<forall>f\<in>{0,1,2}. \<exists>w\<in>set ws.
    native_certificate_family_coverage_condition f (native_certificate_input_original (native_certificate_input_problem w)))"

theorem native_certificate_input_criticism_exact:
  "native_certificate_criticism_accept (native_certificate_criticism
    (context_assessment_table native_certificate_methods ws native_certificate_input_context native_certificate_cell))=
    native_certificate_input_criticism_condition ws"
  by (simp only: native_certificate_input_context_def[abs_def] Let_def native_certificate_criticism_originals
    native_certificate_input_criticism_condition_def)

definition native_certificate_input_cycle where
  "native_certificate_input_cycle ws selected=context_subject_cycle native_certificate_methods [0,1,2,3,4,5,6] ws
    native_certificate_input_method native_certificate_input_context native_certificate_cell
    (\<lambda>(result,A). native_certificate_inspect A) native_certificate_criticism native_certificate_criticism_accept selected"

definition native_certificate_input_admissions where
  "native_certificate_input_admissions ws selected=map fst (snd (snd (snd (snd (native_certificate_input_cycle ws selected)))))"

theorem native_certificate_input_admissions_exact:
  "m\<in>set (native_certificate_input_admissions ws selected) \<longleftrightarrow>
    subject_cycle_admissible [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws
      native_certificate_input_method native_certificate_input_condition native_certificate_input_problem
      (native_certificate_input_criticism_condition ws) selected m"
proof -
  have observed: "(\<lambda>(result,A). native_certificate_inspect A)
      (native_certificate_cell c (native_certificate_input_context w)) f=
    native_certificate_input_condition f (native_certificate_input_method c) (native_certificate_input_problem w)" for c w f
    by (simp only: native_certificate_input_cell_at case_prod_conv native_certificate_input_quality_def[symmetric]
      native_certificate_input_quality_exact)
  show ?thesis
    by (simp only: native_certificate_input_admissions_def native_certificate_input_cycle_def
      native_certificate_input_criticism_exact[symmetric] native_certificate_methods_def[symmetric];
      rule context_subject_cycle_indices_exact; rule observed)
qed

definition native_certificate_input_packet where
  "native_certificate_input_packet ws selected=(case native_certificate_input_cycle ws selected of
    (table,criticism,result,cycle,admissions) \<Rightarrow>
      (map (\<lambda>(w,(X,original,base),cells). (w,X,original,cells)) table,criticism,result,cycle,map fst admissions))"

text \<open>
  This proposed expanded cycle instantiates the same complete context, cell,
  criticism and admission operations. The input embedding preserves every old
  query. The scoped admission theorem retains all original subject conditions,
  basis readiness and the independent criticism condition. Executing it on the
  proposed expanded scope is conditional on reviewing the actual scope repair
  comparison first. Admission here remains distinct from complete workflow
  enforcement, candidate-language adequacy, historical permission and genesis.
\<close>

end
