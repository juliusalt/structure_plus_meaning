theory Factor_Predecessor_Assembly
  imports Factor_Current_Companions Factor_Current_Construction_Certificates Factor_Generation_Replay_Causes
begin

section \<open>The construction role belongs to the actual predecessor\<close>

definition predecessor_assembly_certificate ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> local_address \<Rightarrow>
    exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "predecessor_assembly_certificate C q D r R s H xs B W Z \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d. current_entry_scope_quoted_at C q A l G p E pu pr P d) \<and>
    current_companion C q D r \<and> current_construction_certificate D r R s xs B W Z \<and>
    generation_replay_scope H R s \<and> generation_payload H=Whole_Artifact Z"

theorem predecessor_assembly_certificate_program:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "predecessor_assembly_certificate C q D r R s H xs B W Z"
  shows "\<exists>z e F au ar root t I K.
    current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    current_companion C q D r \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    environment_formed F \<and> environment_included E F \<and> native_package_at F pu pr P \<and>
    native_package_environment F pu pr=E \<and> native_application_at F au ar e t I K \<and>
    current_constructs_at D r F au ar xs B W Z \<and>
    certified_construction_at F pu pr au ar root xs B W Z \<and>
    generation_replay_scope H R s \<and> generation_payload H=Whole_Artifact Z"
proof -
  have companion: "current_companion C q D r"
    and certified: "current_construction_certificate D r R s xs B W Z"
    and fields: "generation_replay_scope H R s" "generation_payload H=Whole_Artifact Z"
    using certificate by (auto simp: predecessor_assembly_certificate_def)
  obtain A' l' G' z E' qu qr Q e where actual:
    "current_entry_scope_quoted_at D r A' l' G' z E' qu qr Q e"
    using certified unfolding current_construction_certificate_def by blast
  have same: "A=A' \<and> l=l' \<and> G=G' \<and> E=E' \<and> pu=qu \<and> pr=qr \<and> P=Q"
    by (rule current_companion_program[OF companion current actual])
  have selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e" using actual same by simp
  show ?thesis using selected companion current_construction_certificate_program[OF selected certified] fields by blast
qed

theorem predecessor_assembly_certificate_derivation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "predecessor_assembly_certificate C q D r R s H xs B W Z"
  shows "\<exists>z e F au ar root t I K J.
    current_entry_scope_quoted_at D r A l G z E pu pr P e \<and>
    replay_scope_quoted_at R s F pu pr au ar root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_at F pu pr P \<and>
    native_application_at F au ar e t I K \<and>
    native_schema_graph_at F root J \<and> schema_graph_derives (positioned_program P) J root e t {} \<and>
    construction_claim_presents xs B W Z t \<and> construction_permission_invariant P e \<and>
    source_constructs xs B W Z \<and> construction_coordinates_formed B W"
proof -
  obtain z e where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    using predecessor_assembly_certificate_program[OF current certificate] by blast
  have certified: "current_construction_certificate D r R s xs B W Z"
    using certificate by (simp add: predecessor_assembly_certificate_def)
  show ?thesis using selected current_construction_certificate_derivation[OF selected certified] by blast
qed

theorem predecessor_assembly_certificate_recorded_cause:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and certificate: "predecessor_assembly_certificate C q D r R s H xs B W Z"
    and gen: "generation_at N hu hr H"
  shows "\<exists>F au ar root.
    replay_scope_quoted_at R s F pu pr au ar root {} \<and> native_package_environment F pu pr=E \<and>
    certified_recorded_cause_at N hu hr H F root xs B W Z"
proof -
  obtain z e F au ar root where selected: "current_entry_scope_quoted_at D r A l G z E pu pr P e"
    and scope: "replay_scope_quoted_at R s F pu pr au ar root {}"
    and fixed: "native_package_environment F pu pr=E"
    and allowed: "current_constructs_at D r F au ar xs B W Z"
    and fields: "generation_replay_scope H R s" "generation_payload H=Whole_Artifact Z"
    using predecessor_assembly_certificate_program[OF current certificate] by blast
  have judged: "construction_judgment_at F pu pr au ar xs B W Z"
    using current_construction_program_scope[OF selected allowed] by blast
  have complete: "certified_recorded_cause_at N hu hr H F root xs B W Z"
    by (rule generation_replay_construction[OF fields(1) scope judged fields(2) gen])
  show ?thesis using scope fixed complete by blast
qed

theorem predecessor_assembly_certificate_account:
  assumes certificate: "predecessor_assembly_certificate C q D r R s H xs B W Z"
  shows "generation_formed H \<and> generation_payload H=Whole_Artifact Z \<and>
    source_constructs xs B W Z \<and> construction_coordinates_formed B W \<and>
    K2 (construction_assembly xs B W) \<and> Z=assembly_output (construction_assembly xs B W)"
proof -
  obtain A l G p E pu pr P d where current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    using certificate unfolding predecessor_assembly_certificate_def by blast
  obtain z e F au ar root t I K where package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar e t I K"
    and certified: "certified_construction_at F pu pr au ar root xs B W Z"
    and fields: "generation_replay_scope H R s" "generation_payload H=Whole_Artifact Z"
    using predecessor_assembly_certificate_program[OF current certificate] by blast
  have permitted: "factor_constructs P e xs B W Z"
    by (rule certified_construction_permission[OF package app certified])
  show ?thesis using permitted factor_construction_assembly[OF permitted] fields
    by (auto simp: generation_replay_scope_def factor_constructs_def)
qed

theorem predecessor_assembly_certificate_account_unique:
  assumes first: "predecessor_assembly_certificate C q D r R s G xs B W Z"
    and second: "predecessor_assembly_certificate C' q' D' r' R a H ys B' W' Z'"
  shows "s=a \<and> xs=ys \<and> B=B' \<and> W=W' \<and> Z=Z'"
proof -
  have certificates: "current_construction_certificate D r R s xs B W Z"
    "current_construction_certificate D' r' R a ys B' W' Z'"
    using first second by (auto simp: predecessor_assembly_certificate_def)
  show ?thesis by (rule current_construction_certificate_account_unique[OF certificates])
qed

section \<open>Admitted construction evidence precedes the candidate's history\<close>

theorem predecessor_assembly_candidate_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and companion: "current_companion C q D r"
    and certified: "current_construction_certificate D r R s xs B W Z"
    and locus: "target_formed m" and predecessors: "\<forall>J\<in>fset V. generation_formed J"
  shows "\<exists>H. \<exists>N :: local_address option artifact_environment. \<exists>u.
    predecessor_assembly_certificate C q D r R s H xs B W Z \<and>
    generation_locus H=m \<and> generation_predecessors H=V \<and> generation_payload H=Whole_Artifact Z \<and>
    generation_at N u [] H \<and> generation_environment_closed N {(u,[])}"
proof -
  obtain A' l' G' z E' qu qr Q e F au ar root where recorded:
    "current_entry_scope_quoted_at D r A' l' G' z E' qu qr Q e"
    "replay_scope_quoted_at R s F qu qr au ar root {}" "current_constructs_at D r F au ar xs B W Z"
    using certified unfolding current_construction_certificate_def by blast
  have judged: "construction_judgment_at F qu qr au ar xs B W Z"
    using current_construction_program_scope[OF recorded(1,3)] by blast
  have built: "source_constructs xs B W Z"
    using judged unfolding construction_judgment_at_def factor_constructs_def by blast
  have zf: "exact_formed Z" by (rule source_construction_finite(7)[OF built])
  obtain H and N :: "local_address option artifact_environment" and u where fields:
    "generation_replay_scope H R s" "generation_locus H=m" "generation_predecessors H=V"
    "generation_payload H=Whole_Artifact Z" "generation_at N u [] H" "generation_environment_closed N {(u,[])}"
    using generation_replay_scope_total[OF recorded(2) zf locus predecessors] by blast
  have complete: "predecessor_assembly_certificate C q D r R s H xs B W Z"
    using current companion certified fields(1,4) unfolding predecessor_assembly_certificate_def by blast
  show ?thesis using complete fields(2-6) by blast
qed

text \<open>
  The construction purpose is separately adopted under the predecessor's
  original adoption policy. Its selected entry belongs to the predecessor's
  exact program scope. The construction derivation and recorded cause are
  checked against that same program and exact call; the successor's clauses
  do not become rules of this derivation.

  The account recovers all reused and introduced pieces and their complete
  origins through the existing construction relation. Its output is exactly
  the candidate's payload. The cause retains its minimal call scope, and the
  proof remains separate. Every outer generation presentation recovers the
  same existing certified recorded cause.

  Historical membership is deliberately not part of this component. One
  construction certificate can accompany different proposed predecessor
  families. Succession must separately require the actual predecessor and
  judge the complete submitted material. Assembly alone supplies no successor
  authority, dependency evidence, continuation, or amendment acceptance.
\<close>

end
