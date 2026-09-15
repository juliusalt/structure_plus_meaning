theory RRA_Graft_Methods
  imports RRA_Graft_Observations RRA_Finite_Syntax_Construction
begin

definition graft_method :: "nat\<Rightarrow>graft_subject\<Rightarrow>graft_result" where
  "graft_method m X=(case X of (E,u,F) \<Rightarrow>
    let U=finite_environment_uses E;head=finite_compact_use_head U u;
      h=(if m=0 then finite_fresh_use_map U u
        else if m=2 then prefix_use_map [0] u
        else if m=3 then prefix_use_map [head] None
        else if m=4 then (\<lambda>x. case x of None \<Rightarrow> u | Some a \<Rightarrow> Some [head])
        else if m=8 then (\<lambda>x. case x of None \<Rightarrow> u | Some a \<Rightarrow> Some (head#rev a))
        else finite_compact_use_map U u);
      G=finite_embedded_graft h E F;
      output=(if m=5 then E else if m=6 then G\<lparr>finite_environment_bindings:={||}\<rparr>
        else if m=7 then finite_rename_environment h F
        else if m=9 then finite_add_artifact_use G (Some [999]) (finite_payload_syntax [9]) else G)
    in (h,output))"

definition graft_case :: "nat\<Rightarrow>graft_subject" where
  "graft_case w=(let R=finite_payload_syntax [7];T=finite_payload_syntax [8];
    E=finite_enumerated_environment [(None,R)] [];
    F=finite_enumerated_environment [(None,R),(Some [],T)] []
    in if w=0 then (E,None,E)
    else if w=1 then (finite_enumerated_environment [(Some [7],R)] [],Some [7],F)
    else if w=2 then (finite_enumerated_environment [(None,R),(Some [0],T)] [],None,
      finite_enumerated_environment [(None,R),(Some [],T)] [((Some [],[]),None)])
    else if w=3 then (finite_enumerated_environment [(None,R),(Some [0],T)] [],None,F)
    else if w=4 then (finite_enumerated_environment [(None,R),(Some [1],T)] [],None,
      finite_enumerated_environment [(None,R),(Some [0],T)] [((Some [0],[]),Some [0])])
    else if w=5 then (finite_enumerated_environment [(Some [300],R)] [],Some [300],F)
    else if w=6 then (finite_enumerated_environment [(None,R),(Some (replicate 128 0),T)] [],None,F)
    else if w=7 then (finite_enumerated_environment [(None,R)] [((None,[]),None)],None,
      finite_enumerated_environment [(None,R),(Some [],T)] [((Some [],[]),None)])
    else if w=8 then (E,None,finite_enumerated_environment [(None,R),(Some [],T)] [((None,[]),Some [])])
    else if w=9 then (finite_enumerated_environment [(None,R)] [((None,[]),None)],None,
      finite_enumerated_environment [(None,R),(Some [],T)] [((None,[]),Some [])])
    else if w=10 then (E,None,finite_enumerated_environment [(None,R),(Some [],R),(Some [],T)] [])
    else if w=11 then (E,None,finite_enumerated_environment [(None,T),(Some [],T)] [])
    else if w=12 then (finite_enumerated_environment [] [],None,finite_enumerated_environment [] [])
    else if w=13 then (finite_enumerated_environment
      (map (\<lambda>i. (Some [i,1],T)) [0..<64]@[(None,R)]) [],None,F)
    else if w=14 then (E,None,finite_enumerated_environment [(None,R),(Some [300],T)] [((None,[]),Some [300])])
    else (E,None,finite_enumerated_environment [(None,R),(Some [1,2],T),(Some [2,1],T)] []))"

lemma graft_method_original:
  "graft_method 0 (E,u,F)=(finite_fresh_use_map (finite_environment_uses E) u,finite_graft_environment E u F)"
  by (simp add: graft_method_def Let_def finite_original_graft_instance)

lemma graft_method_compact:
  "graft_method 1 (E,u,F)=(finite_compact_use_map (finite_environment_uses E) u,finite_compact_graft E u F)"
  by (simp add: graft_method_def Let_def finite_compact_graft_def)


theorem graft_original_semantics:
  assumes facet: "f\<in>{0,1,2,3}"
  shows "graft_condition f (graft_method 0) X"
proof -
  obtain E u F where X: "X=(E,u,F)" by (cases X) auto
  have embedding: "boundary_use_embedding (environment_uses (decode_finite_environment E)) u
      (finite_fresh_use_map (finite_environment_uses E) u)"
    by (simp only: finite_fresh_use_map_exact finite_environment_uses_correct[symmetric];
      rule original_boundary_embedding; simp)
  have whole: "decode_finite_environment (finite_graft_environment E u F)=
    embedded_graft_environment (finite_fresh_use_map (finite_environment_uses E) u)
      (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: finite_original_graft_instance finite_embedded_graft_exact)
  show ?thesis unfolding X
    by (rule graft_condition_from_embedding[where method="graft_method 0", OF graft_method_original[of E u F] embedding whole facet])
qed

theorem graft_compact_semantics:
  assumes facet: "f\<in>{0,1,2,3}"
  shows "graft_condition f (graft_method 1) X"
proof -
  obtain E u F where X: "X=(E,u,F)" by (cases X) auto
  have embedding: "boundary_use_embedding (environment_uses (decode_finite_environment E)) u
      (finite_compact_use_map (finite_environment_uses E) u)"
    by (simp only: finite_compact_use_map_exact finite_environment_uses_correct[symmetric];
      rule compact_boundary_embedding; simp)
  have whole: "decode_finite_environment (finite_compact_graft E u F)=
    embedded_graft_environment (finite_compact_use_map (finite_environment_uses E) u)
      (decode_finite_environment E) (decode_finite_environment F)"
    by (simp only: finite_compact_graft_def finite_embedded_graft_exact)
  show ?thesis unfolding X
    by (rule graft_condition_from_embedding[where method="graft_method 1", OF graft_method_compact[of E u F] embedding whole facet])
qed

theorem graft_compact_growth:
  "graft_condition 4 (graft_method 1) X"
  by (cases X)
    (auto simp: graft_condition_def graft_method_compact[unfolded One_nat_def]
      graft_mapping_condition_def finite_compact_use_map_exact compact_use_word_length split: option.splits)

end
