theory Factor_Native_Certificate_Scope_Repair
  imports Factor_Native_Certificate_Identity_Cases Factor_Native_Certificate_Coverage Finite_Subject_Cycles
begin

definition certificate_scope_repair_method :: "nat\<Rightarrow>native_certificate_input list\<Rightarrow>native_certificate_input list" where
  "certificate_scope_repair_method m Xs=(if m=0 then Xs else if m=2 then Xs@native_certificate_identity_inputs else [])"

definition certificate_scope_repair_condition where
  "certificate_scope_repair_condition (f::nat) method Xs=(if f=0 then set Xs\<subseteq>set (method Xs)
    else if f<4 then native_certificate_scope_coverage_condition (f-1)
      (map native_certificate_input_original (method Xs)) else False)"

definition certificate_scope_repair_assessment where
  "certificate_scope_repair_assessment Xs Ys=(let originals=map native_certificate_input_original Ys in
    (set Xs\<subseteq>set Ys,originals,native_certificate_scope_coverage originals))"

definition certificate_scope_repair_inspect :: "bool\<times>native_derivation_result list\<times>
    native_certificate_family_coverage_report list\<Rightarrow>nat\<Rightarrow>bool" where
  "certificate_scope_repair_inspect A f=(case A of (retained,originals,coverage) \<Rightarrow>
    if f=0 then retained else if f<4 then native_certificate_scope_coverage_inspect coverage (f-1) else False)"

theorem certificate_scope_repair_assessment_exact:
  "certificate_scope_repair_inspect (certificate_scope_repair_assessment Xs (method Xs)) f=
    certificate_scope_repair_condition f method Xs"
  by (simp only: certificate_scope_repair_assessment_def certificate_scope_repair_inspect_def
    certificate_scope_repair_condition_def Let_def case_prod_conv native_certificate_scope_coverage_exact)

definition certificate_scope_repair_problem where
  "certificate_scope_repair_problem (w::nat)=native_certificate_original_inputs"

definition certificate_scope_repair_assess where
  "certificate_scope_repair_assess m w=certificate_scope_repair_assessment (certificate_scope_repair_problem w)
    (certificate_scope_repair_method m (certificate_scope_repair_problem w))"

definition certificate_scope_repair_quality where
  "certificate_scope_repair_quality m w f=certificate_scope_repair_inspect (certificate_scope_repair_assess m w) f"

lemma certificate_scope_repair_quality_exact:
  "certificate_scope_repair_quality m w f=certificate_scope_repair_condition f
    (certificate_scope_repair_method m) (certificate_scope_repair_problem w)"
  by (simp only: certificate_scope_repair_quality_def certificate_scope_repair_assess_def
    certificate_scope_repair_assessment_exact)

interpretation certificate_scope_repair: finite_subject_investigation "[0,1,2]" "[0,1,2,3]" ws
    certificate_scope_repair_method certificate_scope_repair_condition certificate_scope_repair_problem
    certificate_scope_repair_quality for ws
  by (unfold_locales) (rule certificate_scope_repair_quality_exact)

definition certificate_scope_repair_investigation where
  "certificate_scope_repair_investigation ws selected=investigation_basis [0,1,2] [0,1,2,3] selected
    (subject_investigation_observations [0,1,2] [0,1,2,3] ws certificate_scope_repair_quality)
    (subject_investigation_relation [0,1,2] [0,1,2,3] ws certificate_scope_repair_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm certificate_scope_repair_investigation_def},
   equation = @{thm certificate_scope_repair.observations_derived},
   formation = @{thm certificate_scope_repair.maps_formed},
   observation = @{thm certificate_scope_repair.observation_at_subject},
   comparison = @{thm certificate_scope_repair.comparison_at_subject}}\<close>

definition certificate_scope_repair_cell where
  "certificate_scope_repair_cell m Xs=(let Ys=certificate_scope_repair_method m Xs in
    (Ys,certificate_scope_repair_assessment Xs Ys))"

definition certificate_scope_repair_packet where
  "certificate_scope_repair_packet selections=(let
    table=context_assessment_table [0,1,2] [0] certificate_scope_repair_problem certificate_scope_repair_cell;
    compared=context_assessment_investigation [0,1,2] [0,1,2,3] [0] table
      (\<lambda>(Ys,A). certificate_scope_repair_inspect A)
    in (table,compared,map (investigation_cycle_report [0,1,2] [0,1,2,3]
      (fst compared) (fst (snd compared))) selections))"

theorem certificate_scope_repair_packet_comparison:
  "fst (snd (certificate_scope_repair_packet selections))=
    assessed_subject_investigation [0,1,2] [0,1,2,3] [0]
      certificate_scope_repair_assess certificate_scope_repair_inspect"
  by (simp only: certificate_scope_repair_packet_def Let_def fst_conv snd_conv
    context_assessment_investigation_exact; rule assessed_subject_investigation_cong)
    (simp only: certificate_scope_repair_cell_def certificate_scope_repair_assess_def Let_def case_prod_conv)

text \<open>
  The original scope consists of full native inputs, including unavailable and
  rejected requests. Candidates retain it, erase it, or append the proposed
  actual identity subjects. Retention compares those complete inputs. Coverage
  reads and independently checks the actual resulting certificate families and
  retains every proof, call and shared-path witness. The shared investigation
  supplies all maps, observations, comparison and revision reasons directly.
  This scope correction does not by itself admit a development operation.
\<close>

end
