theory Factor_Native_Replay_Investigation
  imports Factor_Native_Replay_Correctness Factor_Native_Replay_Caches Finite_Assessment_Reports
begin

definition native_replay_family_condition where
  "native_replay_family_condition f method Xs=(\<forall>X\<in>fset Xs. native_replay_condition f method X)"

definition native_replay_context where
  "native_replay_context w=(let Xs=native_replay_problem w in
    (Xs,fimage (\<lambda>X. let original=native_replay_original X; base=native_replay_base X;
      results=map (\<lambda>m. native_replay_apply m X base) native_replay_methods in
      (X,native_replay_reference X,original,base,native_replay_caches X (if original=None then [] else results))) Xs))"

definition native_replay_cell where
  "native_replay_cell m C=(case C of (Xs,prepared) \<Rightarrow>
    fimage (\<lambda>(X,reference,original,base,caches). let result=native_replay_apply m X base in
      (X,reference,result,native_replay_cached_assessment_from caches X original result)) prepared)"

definition native_replay_family_inspect where
  "native_replay_family_inspect rows (f::nat)=fBall rows (\<lambda>(X,reference,result,A). native_replay_inspect A f)"

definition native_replay_family_assess where
  "native_replay_family_assess m w=native_replay_cell m (native_replay_context w)"

definition native_replay_quality where
  "native_replay_quality m w f=native_replay_family_inspect (native_replay_family_assess m w) f"

theorem native_replay_cell_exact:
  "native_replay_cell m (native_replay_context w)=fimage (\<lambda>X.
    (X,native_replay_reference X,native_replay_method m X,native_replay_assessment X (native_replay_method m X)))
    (native_replay_problem w)"
  by (simp add: native_replay_cell_def native_replay_context_def native_replay_method_def
    native_replay_assessment_def native_replay_cached_assessment_from_exact fimage_fimage comp_def Let_def)

theorem native_replay_quality_exact:
  "native_replay_quality m w f=native_replay_family_condition f (native_replay_method m) (native_replay_problem w)"
  by (simp only: native_replay_quality_def native_replay_family_assess_def native_replay_cell_exact
    native_replay_family_inspect_def native_replay_family_condition_def;
    auto simp: fimage.rep_eq native_replay_assessment_exact)

interpretation native_replay: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13]"
    "[0,1,2,3,4,5,6,7,8,9]" ws native_replay_method native_replay_family_condition native_replay_problem native_replay_quality for ws
  by (unfold_locales) (rule native_replay_quality_exact)

definition native_replay_investigation where
  "native_replay_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13]
    [0,1,2,3,4,5,6,7,8,9] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1,2,3,4,5,6,7,8,9] ws native_replay_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1,2,3,4,5,6,7,8,9] ws native_replay_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_replay_investigation_def},
   equation = @{thm native_replay.observations_derived},
   formation = @{thm native_replay.maps_formed},
   observation = @{thm native_replay.observation_at_subject},
   comparison = @{thm native_replay.comparison_at_subject}}\<close>

definition native_replay_packet where
  "native_replay_packet ws selections=(let
    table=context_assessment_table native_replay_methods ws native_replay_context native_replay_cell;
    compared=context_assessment_investigation native_replay_methods [0,1,2,3,4,5,6,7,8,9] ws table native_replay_family_inspect
    in (map (\<lambda>(w,(Xs,prepared),cells). (w,Xs,cells)) table,compared,
      map (investigation_cycle_report native_replay_methods [0,1,2,3,4,5,6,7,8,9]
        (fst compared) (fst (snd compared))) selections))"

theorem native_replay_packet_comparison:
  "fst (snd (native_replay_packet ws selections))=assessed_subject_investigation
    native_replay_methods [0,1,2,3,4,5,6,7,8,9] ws native_replay_family_assess native_replay_family_inspect"
  by (simp only: native_replay_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact
    native_replay_family_assess_def[abs_def])

export_code native_replay_packet native_replay_indices native_replay_inspect native_replay_family_inspect checking SML

text \<open>
  Complete finite subject families retain actual certificates without assigning
  an order to proof values. Each family member has one shared base construction;
  every candidate retains its whole result and all original-subject assessments.
  Independent conditions quantify over every complete family member. The common
  subject investigation supplies the maps, observations and comparison directly.
  The scope includes actual equality and variable sources, recursive branches,
  independently checked identity/sharing examples, corrupted certificates, an
  unavailable source and an unrelated original artifact. Complete native output
  review and independent coverage criticism remain required before adoption.
\<close>

end
