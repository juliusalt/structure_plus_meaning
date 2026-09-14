theory RRA_Included_Artifacts
  imports RRA_Environment
begin

theorem included_existing_artifact:
  assumes included: "environment_included E F" and formed: "environment_formed F"
    and existing: "v\<in>environment_uses E"
  shows "artifact_at F v R \<longleftrightarrow> artifact_at E v R"
proof
  assume actual: "artifact_at F v R"
  obtain S where original: "artifact_at E v S"
    using existing by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  have kept: "artifact_at F v S" by (rule included_artifact[OF included original])
  have same: "R=S" by (rule environment_artifact_unique[OF formed actual kept])
  show "artifact_at E v R" using original same by simp
next
  show "artifact_at E v R \<Longrightarrow> artifact_at F v R"
    by (rule included_artifact[OF included])
qed

text \<open>
  Inclusion into a formed environment preserves the exact artifact value at
  every original use. This does not rule out new bindings at previously empty
  slots; exact binding preservation needs its own construction property.
\<close>

end
