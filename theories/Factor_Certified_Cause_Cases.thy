theory Factor_Certified_Cause_Cases
  imports Factor_Finite_Certified_Causes Factor_Finite_Generation_Replay_Completion Factor_Literal_Replay_Cases
begin

type_synonym certified_cause_subject =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    finite_generation\<times>local_address option finite_artifact_environment\<times>
    local_address option definition_site\<times>finite_exact_artifact"

definition certified_cause_holds :: "certified_cause_subject \<Rightarrow> bool" where
  "certified_cause_holds X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    certified_base_cause_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R))"

definition certified_cause_direct :: "certified_cause_subject \<Rightarrow> bool" where
  "certified_cause_direct X=(case X of (E,gu,gr,G,H,root,R) \<Rightarrow>
    finite_certified_base_cause E gu gr G H root R)"

lemma certified_cause_direct_exact:
  "certified_cause_direct X=certified_cause_holds X"
  by (cases X) (simp add: certified_cause_direct_def certified_cause_holds_def
    finite_certified_base_cause_exact split: prod.splits)

definition certified_cause_seed_record where
  "certified_cause_seed_record X=(case X of (E,pu,pr,au,ar,root,R) \<Rightarrow>
    finite_record_native_replay (finite_enumerated_environment [] [])
      (Finite_Whole (finite_payload_syntax [60])) [] E pu pr au ar root R)"

definition certified_cause_seed_family where
  "certified_cause_seed_family seed w=fimage (\<lambda>(c,result).
    (c,map_option (\<lambda>X. (X,certified_cause_seed_record X)) result)) (literal_replay_family seed w)"

text \<open>
  The original literal replay fixture supplies complete source, decision,
  certificate and replay evidence. Its actual result enters the joined record
  constructor with an explicitly empty test history and no predecessors.
  The test requirement family remains explicitly empty. Unavailable original
  replays and unavailable joined records retain their failure positions.
\<close>

end
