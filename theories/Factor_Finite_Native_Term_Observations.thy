theory Factor_Finite_Native_Term_Observations
  imports Factor_Finite_Term_Demands
begin

section \<open>Filter supplied terms using one evaluation of their actual source\<close>

definition finite_native_term_observation where
  "finite_native_term_observation supported test E u r T=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> if supported P then
      map_option (\<lambda>(Q,A). (Q,ffilter (test A) T))
        (finite_native_program_evaluation E u r (finite_program_term_demand P T)) else None)"

theorem finite_native_term_observation_conditions:
  "finite_native_term_observation supported test E u r T=Some (P,M) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and> supported P \<and>
    (\<exists>A. finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A) \<and>
      M=ffilter (test A) T)"
  by (auto simp: finite_native_term_observation_def finite_native_program_evaluation_def
    split: option.splits prod.splits if_splits)

theorem finite_native_term_observation_ready:
  "(\<exists>M. finite_native_term_observation supported test E u r T=Some (P,M)) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and> supported P \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A)"
  by (auto simp: finite_native_term_observation_conditions finite_native_program_evaluation_def)

theorem finite_native_term_observation_semantics:
  assumes exact: "\<And>A. finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A) \<Longrightarrow>
    supported P \<Longrightarrow> fset (ffilter (test A) T)={t\<in>fset T. expected t}"
  shows "finite_native_term_observation supported test E u r T=Some (P,M) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    supported P \<and> (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T. expected t}"
proof
  assume result: "finite_native_term_observation supported test E u r T=Some (P,M)"
  have source: "finite_native_source E u r=Some P" and supported: "supported P"
    using result by (simp only: finite_native_term_observation_conditions; blast)+
  obtain A where evaluated: "finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A)"
    and mask: "M=ffilter (test A) T"
    using result by (simp only: finite_native_term_observation_conditions; blast)
  have available: "\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A"
    using finite_native_term_observation_ready[of supported test E u r T P] result by blast
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    supported P \<and> (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T. expected t}"
    using source supported available exact[OF evaluated supported]
    by (simp only: finite_native_source_correct mask; blast)
next
  assume facts: "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    supported P \<and> (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T. expected t}"
  have source: "finite_native_source E u r=Some P" and supported: "supported P"
    using facts by (simp only: finite_native_source_correct; blast)+
  obtain A where evaluation: "finite_program_evaluation P (finite_program_term_demand P T)=Some A"
    using facts by blast
  have evaluated: "finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A)"
    by (simp add: finite_native_program_evaluation_def source evaluation)
  have mask: "M=ffilter (test A) T"
    using exact[OF evaluated supported] facts by (simp only: fset_inject[symmetric]; blast)
  show "finite_native_term_observation supported test E u r T=Some (P,M)"
    by (simp only: finite_native_term_observation_conditions; use source supported evaluated mask in blast)
qed

export_code finite_native_term_observation checking SML

end
