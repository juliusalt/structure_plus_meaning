theory Factor_Program_Evaluation_Investigation
  imports Factor_Finite_Program_Evaluation Factor_Finite_Native_Controls Factor_Finite_Material_Arguments Finite_Subject_Investigation
begin

section \<open>Actual programs criticize proposed evaluation operations\<close>

type_synonym finite_evaluation_subject =
  "(nat,nat,nat,nat) finite_schema_system\<times>(nat\<times>finite_factor_term) fset"
type_synonym finite_evaluation_operation =
  "finite_evaluation_subject\<Rightarrow>(nat\<times>finite_factor_term) fset option"

definition program_evaluation_terms where
  "program_evaluation_terms={|Finite_Payload [],Finite_Payload [1],
    Finite_Pair (Finite_Payload []) (Finite_Payload []),
    Finite_Pair (Finite_Payload []) (Finite_Payload [1]),
    Finite_Target (Finite_Whole (finite_payload_syntax [42])),
    Finite_Target (Finite_Anchor (finite_payload_syntax [42]) [])|}"

definition program_evaluation_material where
  "program_evaluation_material i=(let C=(if i<19 then finite_empty_artifact else
      if i=19 then finite_payload_syntax [42] else
        finite_enumerated_artifact [[],[0],[1]] [([],[0],[1])] [([0],[7]),([0],[7])] [([1],[42])]);
    M=finite_literal_material C;
    N=(if i=18 then M\<lparr>finite_material_atoms:=Finite_Pattern_Payload []\<rparr>
      else if i=21 then M\<lparr>finite_material_edges:=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)\<rparr>
      else M)
    in \<lparr>finite_schema_conclusion=Finite_Variable (0::nat),finite_schema_premises={||},
      finite_schema_materials={|(0::nat,N)|}\<rparr>)"

definition program_evaluation_workload_indices :: "nat list" where
  "program_evaluation_workload_indices=[0..<22]"

definition program_evaluation_subject :: "nat\<Rightarrow>finite_evaluation_subject" where
  "program_evaluation_subject i=(let
    source=finite_nat_guard_source_model False;
    hidden=finite_add_view_definition source 1 (Finite_Variable 0)
      {|(0,finite_control_rule (Finite_Variable 0) {|(0,0,Finite_Variable 1)|})|};
    growing=finite_add_view_definition source 1 (Finite_Variable 0)
      {|(0,finite_control_rule (Finite_Variable 0)
        {|(0,0,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 0))|})|};
    P=(if 17\<le>i then finite_add_view_definition source 1 (Finite_Variable 0) {|(0,program_evaluation_material i)|}
      else if i=8 then finite_native_control_candidate 4 else if i=9 \<or> i=14 then hidden
      else if i=10 then finite_native_control_candidate 11 else if i=11 then finite_native_control_candidate 12
      else if i=12 \<or> i=13 then growing else if i=15 \<or> i=16 then finite_native_control_candidate 6
      else finite_native_control_candidate i);
    D=(if i=8 \<or> i=12 then {|(1,Finite_Payload [])|}
      else if i=13 then {|(1,Finite_Payload []),(0,Finite_Pair (Finite_Payload []) (Finite_Payload []))|}
      else if i=14 then fimage (\<lambda>t. (0,t)) program_evaluation_terms
      else if i=15 then {|(1,Finite_Payload [256])|}
      else if i=16 then {|(255,Finite_Payload [])|}
      else ffUnion (fimage (\<lambda>d. fimage (\<lambda>t. (d,t)) program_evaluation_terms) (finite_system_definitions P)))
    in (P,D))"

definition program_evaluation_method :: "nat\<Rightarrow>finite_evaluation_operation" where
  "program_evaluation_method m X=(case X of (P,D) \<Rightarrow>
    let F=finite_program_rule_table P D in
    if m=0 then Some (fimage fst F)
    else if m=1 then Some (ffilter (\<lambda>q. q\<in>finite_inference_round F {||} {}) D)
    else if m=2 then finite_program_evaluation P D
    else if m=3 then Some D else None)"

definition program_evaluation_ready where
  "program_evaluation_ready P D \<longleftrightarrow>
    schema_system_formed (decode_finite_system P) \<and> finite_program_head_covered P D \<and>
    program_demand_closed (decode_finite_system P) (decode_finite_call_term ` fset D)"

lemma program_evaluation_ready_exact:
  "program_evaluation_ready P D \<longleftrightarrow> (\<exists>A. finite_program_evaluation P D=Some A)"
  by (auto simp only: program_evaluation_ready_def finite_program_evaluation_conditions
    finite_system_formed_correct finite_program_demand_closed_correct)

definition program_evaluation_condition :: "nat\<Rightarrow>finite_evaluation_operation\<Rightarrow>finite_evaluation_subject\<Rightarrow>bool" where
  "program_evaluation_condition f method X=(case X of (P,D) \<Rightarrow>
    let ready=program_evaluation_ready P D;
      original={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}
    in if f=0 then (ready \<longrightarrow> (\<exists>A. method X=Some A \<and> fset A\<subseteq>original))
      else if f=1 then (ready \<longrightarrow> (\<exists>A. method X=Some A \<and> original\<subseteq>fset A \<and> A |\<subseteq>| D))
      else f=2 \<and> (\<not>ready \<longrightarrow> method X=None))"

definition program_evaluation_quality :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>bool" where
  "program_evaluation_quality m w f=(let X=program_evaluation_subject w in case X of (P,D) \<Rightarrow>
    (case finite_program_evaluation P D of None \<Rightarrow>
      (if f=0 \<or> f=1 then True else f=2 \<and> program_evaluation_method m X=None)
    | Some A \<Rightarrow> if f=2 then True else
      (case program_evaluation_method m X of None \<Rightarrow> False
       | Some B \<Rightarrow> if f=0 then B |\<subseteq>| A else f=1 \<and> A |\<subseteq>| B \<and> B |\<subseteq>| D)))"

lemma program_evaluation_quality_exact:
  "program_evaluation_quality m w f=
    program_evaluation_condition f (program_evaluation_method m) (program_evaluation_subject w)"
proof -
  obtain P D where subject: "program_evaluation_subject w=(P,D)"
    by (cases "program_evaluation_subject w") auto
  show ?thesis
  proof (cases "finite_program_evaluation P D")
    case None
    have absent: "\<not>program_evaluation_ready P D"
      by (simp only: program_evaluation_ready_exact None; simp)
    show ?thesis by (auto simp: program_evaluation_quality_def program_evaluation_condition_def
      subject None absent Let_def split: if_splits)
  next
    case (Some A)
    have ready: "program_evaluation_ready P D"
      by (simp only: program_evaluation_ready_exact; use Some in blast)
    have original: "{q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}=fset A"
      by (rule finite_program_evaluation_exact(2)[OF Some, symmetric])
    show ?thesis by (auto simp: program_evaluation_quality_def program_evaluation_condition_def
      subject Some ready original Let_def less_eq_fset.rep_eq split: option.splits if_splits)
  qed
qed

interpretation program_evaluation: finite_subject_investigation "[0,1,2,3,4]" "[0,1,2]"
    program_evaluation_workload_indices program_evaluation_method program_evaluation_condition
    program_evaluation_subject program_evaluation_quality
  by (unfold_locales) (rule program_evaluation_quality_exact)

definition program_evaluation_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "program_evaluation_investigation_observations=subject_investigation_observations
    [0,1,2,3,4] [0,1,2] program_evaluation_workload_indices program_evaluation_quality"

definition program_evaluation_investigation_relation :: "(nat\<times>nat) list" where
  "program_evaluation_investigation_relation=subject_investigation_relation
    [0,1,2,3,4] [0,1,2] program_evaluation_workload_indices program_evaluation_quality"

definition program_evaluation_investigation where
  "program_evaluation_investigation selected=investigation_basis [0,1,2,3,4] [0,1,2] selected
    program_evaluation_investigation_observations program_evaluation_investigation_relation"

definition program_evaluation_candidates where
  "program_evaluation_candidates=fimage (\<lambda>m. (m,program_evaluation_method m)) (fset_of_list [0,1,2,3,4])"
definition program_evaluation_conditions where
  "program_evaluation_conditions=fimage (\<lambda>f. (f,program_evaluation_condition f)) (fset_of_list [0,1,2])"
definition program_evaluation_workloads where
  "program_evaluation_workloads=fimage (\<lambda>w. (w,program_evaluation_subject w)) (fset_of_list program_evaluation_workload_indices)"

lemma program_evaluation_subject_maps:
  "finite_observation_subjects_formed program_evaluation_candidates program_evaluation_conditions program_evaluation_workloads"
  by (simp only: program_evaluation_candidates_def program_evaluation_conditions_def program_evaluation_workloads_def;
    rule program_evaluation.maps_formed)

lemma program_evaluation_observations_derived:
  "fset_of_list program_evaluation_investigation_observations=finite_derived_observations
    program_evaluation_candidates program_evaluation_conditions program_evaluation_workloads
      (\<lambda>condition method problem. condition method problem)"
  by (simp only: program_evaluation_investigation_observations_def program_evaluation_candidates_def
    program_evaluation_conditions_def program_evaluation_workloads_def;
    rule program_evaluation.observations_derived)

theorem program_evaluation_observation_at_subject:
  assumes "(m,method) |\<in>| program_evaluation_candidates"
    "(f,condition) |\<in>| program_evaluation_conditions"
    "(w,problem) |\<in>| program_evaluation_workloads"
  shows "(f,m,w)\<in>set program_evaluation_investigation_observations \<longleftrightarrow> condition method problem"
  by (simp only: program_evaluation_investigation_observations_def;
    rule program_evaluation.observation_at_subject)
    (use assms in \<open>simp_all only: program_evaluation_candidates_def program_evaluation_conditions_def
      program_evaluation_workloads_def\<close>)

definition program_evaluation_comparison where
  "program_evaluation_comparison method other=finite_subject_comparison
    program_evaluation_conditions program_evaluation_workloads method other"

theorem program_evaluation_comparison_at_subject:
  assumes "(m,method) |\<in>| program_evaluation_candidates"
    "(n,other) |\<in>| program_evaluation_candidates"
  shows "(m,n)\<in>set program_evaluation_investigation_relation \<longleftrightarrow> program_evaluation_comparison method other"
  by (simp only: program_evaluation_investigation_relation_def program_evaluation_comparison_def
    program_evaluation_conditions_def program_evaluation_workloads_def;
    rule program_evaluation.comparison_at_subject)
    (use assms in \<open>simp_all only: program_evaluation_candidates_def\<close>)

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm program_evaluation_investigation_def},
   equation = @{thm program_evaluation_observations_derived},
   formation = @{thm program_evaluation_subject_maps},
   observation = @{thm program_evaluation_observation_at_subject},
   comparison = @{thm program_evaluation_comparison_at_subject}}\<close>

definition program_evaluation_selected where
  "program_evaluation_selected=subject_investigation_selected
    [0,1,2,3,4] [0,1,2] program_evaluation_workload_indices program_evaluation_quality"

theorem program_evaluation_selection_at_subject:
  assumes "(m,method) |\<in>| program_evaluation_candidates"
  shows "m\<in>set program_evaluation_selected \<longleftrightarrow>
    (\<forall>(n,other)\<in>fset program_evaluation_candidates. program_evaluation_comparison other method)"
  by (simp only: program_evaluation_selected_def program_evaluation_candidates_def
    program_evaluation_comparison_def program_evaluation_conditions_def program_evaluation_workloads_def;
    rule program_evaluation.selection_at_subject)
    (use assms in \<open>simp_all only: program_evaluation_candidates_def\<close>)

definition program_evaluation_report where
  "program_evaluation_report w=(let X=program_evaluation_subject w in case X of (P,D) \<Rightarrow>
    (P,D,finite_system_formed P,finite_program_head_covered P D,finite_program_demand_closed P D,
      finite_program_applications P D,finite_program_rule_table P D,finite_program_evaluation P D,
      map (\<lambda>m. (m,program_evaluation_method m X,map (\<lambda>f. (f,program_evaluation_quality m w f)) [0,1,2])) [0,1,2,3,4]))"

text \<open>
  The independent criteria concern sound answers, complete answers, and no
  answer when the exact finite decision prerequisites are missing. They use
  the original positive meaning of each complete program. The proved finite
  evaluator supplies executable equations for that unchanged condition.

  The five proposed operations return all possible rule heads, only one
  inference round, checked least closure, every requested call, or no answer.
  Workloads include unsupported and seeded recursion, literal identity,
  two rejected material encodings, omitted callee demand, hidden binding values,
  malformed programs, a larger constructed argument, its complete demand,
  an irrelevant hidden-variable clause, a malformed term and an absent callee.
  The malformed term and absent callee are valid negative judgments; missing coverage is not.
  Independent criticism of the first execution found no successful material
  case: both older operands used a data-list terminator. Five further subjects keep those failures and add complete generated material
  operands for the empty artifact, a payload artifact, and an artifact with
  incidence and repeated counted attachments. Two variants alter an atom
  enumeration or omit actual incidence. Their operands are computed from each
  complete artifact under the shared universal material-construction contract.

  Every observation and comparison is derived from these actual subjects.
  Selection retains every method dominating the other supplied operations
  under those computed conditions. No order or score on identifiers chooses
  an operation. Coverage beyond this workload family and enforcement of the
  complete development cycle remain separate questions.
\<close>

end
