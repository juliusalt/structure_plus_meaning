theory RRA_Bounded_Environment_Updates
  imports RRA_Bounded_Environment_States
begin

definition bounded_environment_allocate where
  "bounded_environment_allocate q R=(if finite_exact_formed R then
    Some (Suc (fst q),indexed_insert_artifact (snd q) (bounded_environment_next_use q) R) else None)"

lemma bounded_environment_allocate_indexed:
  "bounded_environment_valid q \<Longrightarrow>
    bounded_environment_allocate q R=map_option (\<lambda>I. (Suc (fst q),I))
      (indexed_add_artifact (snd q) (bounded_environment_next_use q) R)"
  by (simp add: bounded_environment_allocate_def indexed_add_artifact_def indexed_artifact_ready_def
    bounded_environment_next_fresh)

lemma bounded_environment_allocate_valid:
  assumes valid: "bounded_environment_valid q" and result: "bounded_environment_allocate q R=Some following"
  shows "bounded_environment_valid following"
proof -
  have formed: "finite_exact_formed R"
    and following: "following=(Suc (fst q),indexed_insert_artifact (snd q) (bounded_environment_next_use q) R)"
    using result by (auto simp: bounded_environment_allocate_def split: if_splits)
  have added: "indexed_add_artifact (snd q) (bounded_environment_next_use q) R=
      Some (indexed_insert_artifact (snd q) (bounded_environment_next_use q) R)"
    using formed bounded_environment_next_fresh[OF valid]
    by (simp add: indexed_add_artifact_def indexed_artifact_ready_def)
  have original: "indexed_environment_valid (snd q)"
    using valid by (simp add: bounded_environment_valid_def)
  have new_valid: "indexed_environment_valid (indexed_insert_artifact (snd q) (bounded_environment_next_use q) R)"
    by (rule indexed_add_artifact_valid[OF original added])
  show ?thesis using valid new_valid
    by (auto simp: following bounded_environment_valid_def bounded_environment_next_use_def)
qed

definition bounded_environment_add_binding where
  "bounded_environment_add_binding q u k v=map_option (\<lambda>I. (fst q,I))
    (indexed_add_binding (snd q) u k v)"

lemma bounded_environment_add_binding_valid:
  assumes valid: "bounded_environment_valid q"
    and result: "bounded_environment_add_binding q u k v=Some following"
  shows "bounded_environment_valid following"
proof -
  obtain I where added: "indexed_add_binding (snd q) u k v=Some I"
    and following: "following=(fst q,I)"
    using result by (auto simp: bounded_environment_add_binding_def split: option.splits)
  have original: "indexed_environment_valid (snd q)"
    using valid by (simp add: bounded_environment_valid_def)
  have new_valid: "indexed_environment_valid I" by (rule indexed_add_binding_valid[OF original added])
  have I: "I=indexed_insert_binding (snd q) u k v"
    using added by (auto simp: indexed_add_binding_def split: if_splits)
  show ?thesis using valid new_valid by (simp add: following I bounded_environment_valid_def)
qed

theorem bounded_environment_allocate_view:
  assumes valid: "bounded_environment_valid q"
    and result: "bounded_environment_allocate q R=Some following"
  shows "indexed_environment_view (snd following)=
    finite_add_artifact_use (indexed_environment_view (snd q)) (bounded_environment_next_use q) R"
    "fst following=Suc (fst q)"
proof -
  have following: "following=(Suc (fst q),indexed_insert_artifact (snd q) (bounded_environment_next_use q) R)"
    using result by (auto simp: bounded_environment_allocate_def split: if_splits)
  show "indexed_environment_view (snd following)=
    finite_add_artifact_use (indexed_environment_view (snd q)) (bounded_environment_next_use q) R"
    by (simp only: following snd_conv; rule indexed_environment_view_representation;
      rule indexed_insert_artifact_exact; rule indexed_environment_view_exact)
  show "fst following=Suc (fst q)" by (simp only: following fst_conv)
qed

text \<open>
  Allocation uses the actual stored bound, checks the new artifact, inserts it
  through the persistent index and advances the bound. Its complete environment
  equals the original artifact constructor, with the original fresh-use guard
  established from the state invariant. No old-row scan occurs in this operation.
  Binding insertion keeps its original local checks and leaves every artifact
  and the head bound unchanged. Natural arithmetic and path cost remain explicit
  further cost requirements.
\<close>

end
