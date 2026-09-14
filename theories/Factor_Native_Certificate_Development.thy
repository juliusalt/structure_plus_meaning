theory Factor_Native_Certificate_Development
  imports Factor_Native_Certificate_Investigation Factor_Native_Certificate_Coverage Finite_Subject_Cycles
begin

definition native_certificate_criticism where
  "native_certificate_criticism table=map (\<lambda>(w,(X,original,base),cells).
    (w,native_certificate_family_coverage original)) table"

definition native_certificate_criticism_accept :: "(nat\<times>native_certificate_family_coverage_report) list\<Rightarrow>bool" where
  "native_certificate_criticism_accept criticism=list_all (\<lambda>f.
    list_ex (\<lambda>(w,A). native_certificate_family_coverage_inspect A f) criticism) [0,1,2]"

definition native_certificate_criticism_condition where
  "native_certificate_criticism_condition ws=(\<forall>f\<in>{0,1,2}. \<exists>w\<in>set ws.
    native_certificate_family_coverage_condition f (native_certificate_original (native_certificate_problem w)))"

theorem native_certificate_criticism_originals:
  "native_certificate_criticism_accept (native_certificate_criticism
    (context_assessment_table cs ws (\<lambda>w. (input w,original w,base w)) cell))=
    (\<forall>f\<in>{0,1,2}. \<exists>w\<in>set ws. native_certificate_family_coverage_condition f (original w))"
  by (auto simp: native_certificate_criticism_accept_def native_certificate_criticism_def
    context_assessment_table_def native_certificate_family_coverage_exact list_all_iff list_ex_iff Let_def)

theorem native_certificate_criticism_exact:
  "native_certificate_criticism_accept (native_certificate_criticism
    (context_assessment_table native_certificate_methods ws native_certificate_context native_certificate_cell))=
    native_certificate_criticism_condition ws"
  by (simp only: native_certificate_context_def[abs_def] Let_def native_certificate_criticism_originals
    native_certificate_criticism_condition_def)

definition native_certificate_development_cycle where
  "native_certificate_development_cycle ws selected=context_subject_cycle native_certificate_methods [0,1,2,3,4,5,6] ws
    native_certificate_method native_certificate_context native_certificate_cell (\<lambda>(result,A). native_certificate_inspect A)
    native_certificate_criticism native_certificate_criticism_accept selected"

definition native_certificate_development_admissions where
  "native_certificate_development_admissions ws selected=map fst
    (snd (snd (snd (snd (native_certificate_development_cycle ws selected)))))"

theorem native_certificate_development_admissions_exact:
  "m\<in>set (native_certificate_development_admissions ws selected) \<longleftrightarrow>
    subject_cycle_admissible [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws
      native_certificate_method native_certificate_condition native_certificate_problem
      (native_certificate_criticism_condition ws) selected m"
proof -
  have observed: "(\<lambda>(result,A). native_certificate_inspect A)
      (native_certificate_cell c (native_certificate_context w)) f=
    native_certificate_condition f (native_certificate_method c) (native_certificate_problem w)" for c w f
    by (simp only: native_certificate_cell_at case_prod_conv native_certificate_quality_def[symmetric]
      native_certificate_quality_exact)
  show ?thesis
    by (simp only: native_certificate_development_admissions_def native_certificate_development_cycle_def
      native_certificate_criticism_exact[symmetric] native_certificate_methods_def[symmetric];
      rule context_subject_cycle_indices_exact; rule observed)
qed

theorem native_certificate_development_keeps_conditions:
  assumes admitted: "m\<in>set (native_certificate_development_admissions ws selected)"
    and facet: "f<7" and workload: "w\<in>set ws"
  shows "native_certificate_condition f (native_certificate_method m) (native_certificate_problem w)"
proof -
  have conditions: "\<forall>f\<in>set [0,1,2,3,4,5,6]. \<forall>w\<in>set ws.
    native_certificate_condition f (native_certificate_method m) (native_certificate_problem w)"
    using admitted by (simp only: native_certificate_development_admissions_exact subject_cycle_admissible_def; blast)
  have member: "f\<in>set [0,1,2,3,4,5,6]" using facet by (auto; arith)
  show ?thesis using conditions member workload by blast
qed

theorem native_certificate_coverage_failure_prevents_admission:
  "\<not>native_certificate_criticism_condition ws \<Longrightarrow>
    native_certificate_development_admissions ws selected=[]"
  by (simp only: native_certificate_development_admissions_def native_certificate_development_cycle_def
    context_subject_cycle_admissions native_certificate_criticism_exact subject_cycle_admissions_def; simp)

definition native_certificate_development_packet where
  "native_certificate_development_packet ws selected=(case native_certificate_development_cycle ws selected of
    (table,criticism,result,cycle,admissions) \<Rightarrow>
      (map (\<lambda>(w,(X,original,base),cells). (w,X,original,cells)) table,
        criticism,result,cycle,map fst admissions))"

export_code native_certificate_development_packet checking SML

text \<open>
  The pending certificate construction is the first development-cycle subject.
  Its actual comparison remains unchanged. Independent scope criticism reads
  the original programs and certificates from the full constructed contexts,
  regardless of any candidate output. Missing proof, call or sharing witnesses
  prevent admission even when methods are selected by the comparison.

  This is a scoped gate under explicit bootstrap contracts. It does not yet
  represent or enforce every workflow requirement, admit native mathematical
  proofs, establish historical permission, justify the candidate language or
  settle the complete cost and retention accounts. Those conditions remain
  required by the six-condition development milestone.
\<close>

end
