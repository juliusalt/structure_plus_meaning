theory Factor_Literal_Replay_Cases
  imports Factor_Finite_Literal_Replay Factor_Finite_Requirement_Decision_Replay
    Factor_Finite_Source_Extension_Cases Finite_Singleton_Selection Finite_Optional_Relation_Predicates
begin

type_synonym literal_replay_subject =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    local_address option\<times>local_address\<times>local_address option definition_site\<times>finite_exact_artifact"

definition literal_replay_holds :: "literal_replay_subject\<Rightarrow>bool" where
  "literal_replay_holds X=(case X of (E,pu,pr,au,ar,root,R) \<Rightarrow>
    native_replay_at (decode_finite_environment E) pu pr au ar root {} \<and>
    (\<exists>d I K. native_application_at (decode_finite_environment E) au ar d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I K))"

definition literal_replay_report where
  "literal_replay_report X=(case X of (E,pu,pr,au,ar,root,R) \<Rightarrow>
    (finite_native_package_readings E pu pr,finite_application_readings E au ar,
      finite_native_replay_readings E pu pr au ar root,R))"

definition literal_replay_decide where
  "literal_replay_decide (m::nat) report=(case report of (programs,apps,replays,R) \<Rightarrow>
    let closed={||} |\<in>| replays;
      literal=fBex apps (\<lambda>((d,t),I,K). t=Finite_Target (Finite_Whole R))
    in if m=0 then closed \<and> literal
      else if m=1 then literal else if m=2 then closed
      else if m=3 then True else if m=4 then False
      else if m=5 then programs\<noteq>{||}
      else if m=6 then closed \<and>
        finite_singleton_option (fimage (\<lambda>((d,t),I,K). t) apps)=Some (Finite_Target (Finite_Whole R))
      else False)"

definition literal_replay_method where
  "literal_replay_method (m::nat) X=literal_replay_decide m (literal_replay_report X)"

lemma literal_replay_method_original:
  "literal_replay_method 0 (E,pu,pr,au,ar,root,R)=finite_literal_replay_ready E pu pr au ar root R"
  by (simp add: literal_replay_method_def literal_replay_decide_def literal_replay_report_def
    finite_literal_replay_ready_def finite_literal_application_ready_def finite_native_replay_proves_def Let_def)

lemma literal_replay_original_exact:
  "literal_replay_method 0 X=literal_replay_holds X"
  by (cases X) (simp add: literal_replay_holds_def literal_replay_method_original
    finite_literal_replay_ready_at split: prod.splits)

definition literal_replay_seed where
  "literal_replay_seed=map_option (\<lambda>(E,u,r). let R=finite_payload_syntax [61] in
    (E,u,r,R,finite_requirement_decision_replay E u r [] {|Finite_Target (Finite_Whole R)|}))
      (finite_source_extension_seed 9)"

definition literal_replay_variant :: "nat\<Rightarrow>local_address option finite_artifact_environment\<Rightarrow>
    local_address option\<Rightarrow>local_address option\<Rightarrow>local_address option definition_site\<Rightarrow>
    finite_exact_artifact\<Rightarrow>literal_replay_subject" where
  "literal_replay_variant w E pu au root R=(let h=map_option (Cons 300) in
    if w=1 then (finite_native_judgment_environment E pu [] au [],pu,[],au,[],root,R)
    else if w=2 then (E,pu,[],au,[],root,finite_payload_syntax [62])
    else if w=3 then (E,pu,[],au,[],(fst root,[255]),R)
    else if w=4 then (finite_enumerated_environment [] [],pu,[],au,[],root,R)
    else if w=5 then (finite_add_artifact_use E (Some [255]) (finite_payload_syntax [256]),pu,[],au,[],root,R)
    else if w=6 then (finite_rename_environment h E,h pu,[],h au,[],(h (fst root),snd root),R)
    else (E,pu,[],au,[],root,R))"

definition literal_replay_family where
  "literal_replay_family seed w=(case seed of None \<Rightarrow> {||}
    | Some (E,u,r,R,decision) \<Rightarrow> case decision of None \<Rightarrow> {||}
      | Some ((entry,F,pu,Q,D,A,T,Ys),replays) \<Rightarrow>
        fimage (\<lambda>(c,result). (c,map_option (\<lambda>(B,M,root,G,au,I,K,H).
          literal_replay_variant w H pu au root R) result)) replays)"

definition literal_replay_covered where
  "literal_replay_covered seed=fBex (literal_replay_family seed 0) (\<lambda>(c,X).
    case X of None \<Rightarrow> False | Some x \<Rightarrow> literal_replay_method 0 x)"

lemma literal_replay_covered_exact:
  "literal_replay_covered seed \<longleftrightarrow>
    (\<exists>c X. (c,Some X) |\<in>| literal_replay_family seed 0 \<and> literal_replay_holds X)"
  by (simp only: literal_replay_covered_def literal_replay_original_exact finite_optional_relation_exists)

text \<open>
  The seed is an actual empty native package extended by an explicitly empty
  test requirement family, followed by its actual certificate and native replay
  constructors. Every returned certificate remains a family key; an unavailable
  replay remains unavailable. Coverage requires an actually valid original
  literal replay, preventing an empty or failed fixture family from selecting
  a method vacuously. This test policy does not establish adequate requirements
  for a development workflow.
\<close>

end
