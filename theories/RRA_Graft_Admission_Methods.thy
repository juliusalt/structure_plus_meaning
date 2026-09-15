theory RRA_Graft_Admission_Methods
  imports RRA_Compact_Graft_Admission RRA_Graft_Methods Finite_Relation_Reader_Assessments
begin

definition finite_compact_graft_full_ready where
  "finite_compact_graft_full_ready E u F \<longleftrightarrow> finite_environment_formed E \<and>
    finite_environment_formed F \<and> finite_shared_graft_artifact E u F \<and>
    finite_environment_formed (finite_compact_graft E u F)"

lemma finite_compact_graft_full_ready_exact:
  "finite_compact_graft_full_ready E u F=finite_compact_graft_ready E u F"
  by (simp only: finite_compact_graft_full_ready_def finite_compact_graft_ready_exact
    original_graft_ready_by_result[OF finite_compact_boundary_embedding]
    finite_environment_formed_correct finite_shared_graft_artifact_exact
    finite_compact_graft_def finite_embedded_graft_exact)

type_synonym graft_admission_value = "local_address option finite_artifact_environment option"

definition graft_admission_relation :: "graft_subject\<Rightarrow>graft_admission_value\<Rightarrow>bool" where
  "graft_admission_relation X result=(case X of (E,u,F) \<Rightarrow>
    original_graft_result (finite_compact_use_map (finite_environment_uses E) u)
      (decode_finite_environment E) u (decode_finite_environment F) (map_option decode_finite_environment result))"

definition graft_admission_reference where
  "graft_admission_reference X=(case X of (E,u,F) \<Rightarrow> {|guarded_compact_graft E u F|})"

lemma graft_admission_reference_exact:
  "result |\<in>| graft_admission_reference X \<longleftrightarrow> graft_admission_relation X result"
  by (cases X) (simp only: graft_admission_reference_def graft_admission_relation_def case_prod_conv
    fset_simps singleton_iff guarded_compact_graft_exact)

definition graft_admission_variant where
  "graft_admission_variant (m::nat) E u F=(let G=finite_compact_graft E u F;
    ready=finite_compact_graft_ready E u F;
    common=finite_environment_formed E \<and> finite_environment_formed F \<and> finite_shared_graft_artifact E u F;
    admit=(if m=1 then finite_compact_graft_full_ready E u F
      else if m=2 then common else if m=3 then finite_environment_formed G
      else if m=4 then finite_shared_graft_artifact E u F else if m=5 then True
      else if m=10 then ready \<and> fBall (finite_environment_bindings F) (\<lambda>((v,k),w). v\<noteq>None)
      else ready);
    output=(if m=6 then G\<lparr>finite_environment_bindings:={||}\<rparr>
      else if m=7 then E else if m=11 then finite_graft_environment E u F
      else if m=12 then finite_add_artifact_use G (Some [999]) (finite_payload_syntax [9]) else G)
    in if m=8 then None else if admit then Some output else None)"

definition graft_admission_method :: "nat\<Rightarrow>graft_subject\<Rightarrow>graft_admission_value fset" where
  "graft_admission_method m X=(if m=9 then {||} else case X of (E,u,F) \<Rightarrow>
    {|if m=0 then guarded_compact_graft E u F else graft_admission_variant m E u F|})"

lemma graft_admission_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> graft_admission_method m X=graft_admission_reference X"
  by (cases X) (auto simp: graft_admission_method_def graft_admission_reference_def
    graft_admission_variant_def guarded_compact_graft_def finite_compact_graft_full_ready_exact Let_def)

definition graft_admission_condition where
  "graft_admission_condition f method X=relation_reader_condition (graft_admission_relation X) f (method X)"

definition graft_admission_context where
  "graft_admission_context X=(X,graft_admission_reference X)"

definition graft_admission_assessment where
  "graft_admission_assessment m context=(case context of (X,reference) \<Rightarrow> (graft_admission_method m X,reference))"

definition graft_admission_inspect :: "(graft_admission_value fset\<times>graft_admission_value fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "graft_admission_inspect=finite_reader_inspect"

theorem graft_admission_assessment_exact:
  "graft_admission_inspect (graft_admission_assessment m (graft_admission_context X)) f=
    graft_admission_condition f (graft_admission_method m) X"
  by (simp only: graft_admission_inspect_def graft_admission_assessment_def graft_admission_context_def
    case_prod_conv graft_admission_condition_def finite_reader_inspect_exact[OF graft_admission_reference_exact])

definition graft_admission_case :: "nat\<Rightarrow>graft_subject" where
  "graft_admission_case w=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    E=finite_enumerated_environment [(None,R)] [] in
    if w<16 then graft_case w
    else if w=16 then (finite_enumerated_environment [(None,R)] [((None,[]),None)],None,
      finite_enumerated_environment [(None,R)] [((None,[]),None)])
    else if w=17 then (E,Some [99],finite_enumerated_environment [(None,R)] [])
    else if w=18 then (E,None,finite_enumerated_environment [(Some [],R)] [])
    else if w=19 then (finite_enumerated_environment [(None,R),(None,T)] [],None,E)
    else if w=20 then (E,None,finite_enumerated_environment [(None,R)] [((None,[256]),None)])
    else (E,None,finite_enumerated_environment [(None,R)] [((None,[]),Some [])]))"

lemma graft_admission_previous_cases:
  "w<16 \<Longrightarrow> graft_admission_case w=graft_case w"
  by (simp add: graft_admission_case_def Let_def)

definition graft_admission_requirements where
  "graft_admission_requirements X=(case X of (E,u,F) \<Rightarrow>
    let h=finite_compact_use_map (finite_environment_uses E) u in
    (finite_environment_formed E,finite_environment_formed F,finite_shared_graft_artifact E u F,
      finite_boundary_bindings_compatible h E u F,finite_compact_graft_ready E u F,
      finite_map_rows (graft_input_uses X) h,finite_compact_graft E u F))"

text \<open>
  The same original complete compact graft relation evaluates each actual
  operation. One alternative checks formation of the full merge; the general
  compatibility theorem proves its equality with boundary admission. Controls
  omit premises, drop bindings, return incomplete or unsupported material,
  change the constructor, or refuse successful and failed result rows.
\<close>

end
