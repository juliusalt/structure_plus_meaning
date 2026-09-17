theory RRA_Generation_Record_Assessment
  imports RRA_Finite_Generation_Record_Cases RRA_Finite_Generation_References
    RRA_Finite_Generation_Projections
begin

definition generation_record_original_ready :: "generation_record_problem\<Rightarrow>bool" where
  "generation_record_original_ready X=(case X of (E,l,p,c,rows) \<Rightarrow>
    environment_formed (decode_finite_environment E) \<and>
    target_formed (decode_finite_target l) \<and> target_formed (decode_finite_target p) \<and>
    target_formed (decode_finite_target c) \<and> distinct (map snd rows) \<and>
    (\<forall>(d,G)\<in>set rows. generation_at (decode_finite_environment E) (fst d) (snd d)
      (decode_finite_generation G)))"

definition generation_record_reference where
  "generation_record_reference X=(case X of (E,l,p,c,rows) \<Rightarrow>
    finite_generation_record_ready E l p c rows)"

lemma generation_record_reference_exact:
  "generation_record_reference X=generation_record_original_ready X"
  by (auto simp: generation_record_reference_def generation_record_original_ready_def
    finite_generation_record_ready_def finite_environment_formed_correct finite_target_formed_correct
    finite_check_generation_exact list_all_iff split: prod.splits)

definition generation_record_result_condition ::
  "nat\<Rightarrow>generation_record_problem\<Rightarrow>generation_record_result option\<Rightarrow>bool" where
  "generation_record_result_condition f X result=(case X of (E,l,p,c,rows) \<Rightarrow>
    case result of None \<Rightarrow> False | Some (F,u,G) \<Rightarrow>
      if f=1 then generation_locus (decode_finite_generation G)=decode_finite_target l
      else if f=2 then generation_payload (decode_finite_generation G)=decode_finite_target p
      else if f=3 then generation_cause (decode_finite_generation G)=decode_finite_target c
      else if f=4 then generation_predecessors (decode_finite_generation G)=
        fimage decode_finite_generation (fset_of_list (map snd rows))
      else if f=5 then environment_formed (decode_finite_environment F)
      else if f=6 then generation_at (decode_finite_environment F) u [] (decode_finite_generation G)
      else if f=7 then
        (\<forall>v\<in>environment_uses (decode_finite_environment E). \<forall>R.
          artifact_at (decode_finite_environment E) v R \<longleftrightarrow> artifact_at (decode_finite_environment F) v R) \<and>
        (\<forall>v\<in>environment_uses (decode_finite_environment E). \<forall>k w.
          binds_slot (decode_finite_environment E) v k w \<longleftrightarrow> binds_slot (decode_finite_environment F) v k w)
      else if f=8 then generation_predecessor_references (decode_finite_environment F) u []
        (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)=set (map fst rows)
      else False)"

definition generation_record_condition where
  "generation_record_condition (f::nat) method X=(if f=0 then
    (method X\<noteq>None)=generation_record_original_ready X
    else if f<9 then (generation_record_original_ready X \<longrightarrow>
      generation_record_result_condition f X (method X)) else False)"

definition generation_record_result_assessment where
  "generation_record_result_assessment X result=(case X of (E,l,p,c,rows) \<Rightarrow>
    map_option (\<lambda>(F,u,G). let
      field_readings=finite_generation_field_readings F u [];
      refs=finite_generation_predecessor_references F u [] l p c
      in (field_readings,refs,
        generation_locus G=l,generation_payload G=p,generation_cause G=c,
        generation_predecessors G=fset_of_list (map snd rows),
        finite_environment_formed F,finite_check_generation G F u [],
        finite_environment_agrees_on E F (finite_environment_uses E),
        refs=fset_of_list (map fst rows))) result)"

definition generation_record_result_inspect where
  "generation_record_result_inspect assessment (f::nat)=(case assessment of None \<Rightarrow> False
    | Some (field_readings,refs,locus,payload,cause,predecessors,formed,native,preserved,original_refs) \<Rightarrow>
      if f=1 then locus else if f=2 then payload else if f=3 then cause
      else if f=4 then predecessors else if f=5 then formed else if f=6 then native
      else if f=7 then preserved else if f=8 then original_refs else False)"

theorem generation_record_result_assessment_exact:
  "generation_record_result_inspect (generation_record_result_assessment X result) f=
    generation_record_result_condition f X result"
proof -
  have references: "finite_generation_predecessor_references F u [] l p c=fset_of_list ds \<longleftrightarrow>
    generation_predecessor_references (decode_finite_environment F) u []
      (decode_finite_target l) (decode_finite_target p) (decode_finite_target c)=set ds"
    for F u l p c ds
    by (simp only: fset_inject[symmetric] finite_generation_predecessor_references_correct fset_of_list.rep_eq)
  obtain E l p c rows where input: "X=(E,l,p,c,rows)" by (cases X) auto
  show ?thesis
  proof (cases result)
    case None
    show ?thesis by (simp only: input None generation_record_result_assessment_def
      generation_record_result_inspect_def generation_record_result_condition_def
      case_prod_conv option.map option.case)
  next
    case (Some y)
    obtain F u G where result_fields: "y=(F,u,G)" by (cases y) auto
    show ?thesis by (simp only: input Some result_fields generation_record_result_assessment_def
      generation_record_result_inspect_def generation_record_result_condition_def
      case_prod_conv option.map option.case Let_def decode_finite_generation_selectors
      decode_finite_target_injective fset_image_equality[OF decode_finite_generation_inj]
      finite_environment_formed_correct finite_check_generation_exact
      finite_environment_agrees_on_correct finite_environment_uses_correct references)
  qed
qed

definition generation_record_assessment where
  "generation_record_assessment X result=(generation_record_reference X,result\<noteq>None,
    generation_record_result_assessment X result)"

definition generation_record_inspect where
  "generation_record_inspect assessment (f::nat)=(case assessment of (ready,available,body) \<Rightarrow>
    if f=0 then available=ready else if f<9 then (ready \<longrightarrow> generation_record_result_inspect body f)
    else False)"

theorem generation_record_assessment_exact:
  "generation_record_inspect (generation_record_assessment X (method X)) f=
    generation_record_condition f method X"
  by (simp only: generation_record_assessment_def generation_record_inspect_def case_prod_conv
    generation_record_condition_def generation_record_reference_exact generation_record_result_assessment_exact)

text \<open>
  The independent conditions concern actual original targets, every original
  predecessor reading, the whole old environment, and each actual cited use and
  address. Availability is required on every ready input and refusal on every
  unready input. A recovered core alone does not discharge reference identity.
  Complete field readings and reference sets accompany the actual input and
  result; the observations are derived through their all-input equations.
  Cause truth and historical permission are separate requirements.
\<close>

end
