theory Factor_Executable_Replay_Retention
  imports Factor_Executable_Dependencies Factor_Executable_Realization Factor_Replay_Retention
begin

section \<open>Application and proof metadata determine their external slots\<close>

definition finite_native_application_demands ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_application_demands E u r =
    fimage (Pair u) (finite_reading_slots (finite_application_readings E u r))"

theorem finite_native_application_demands_correct:
  "fset (finite_native_application_demands E u r) = native_application_demands (decode_finite_environment E) u r"
proof -
  have projected: "fset (finite_reading_slots (finite_application_readings E u r)) =
      {k. \<exists>q I K. native_application_at (decode_finite_environment E) u r (fst q) (snd q) I K \<and> k \<in> K}"
  proof (rule finite_reading_slots_correct[where D=decode_finite_call_term])
    show "(q,I,K) |\<in>| finite_application_readings E u r \<longleftrightarrow>
        native_application_at (decode_finite_environment E) u r
          (fst (decode_finite_call_term q)) (snd (decode_finite_call_term q)) (fset I) (fset K)" for q I K
      by (cases q) (simp add: finite_application_readings_correct)
    fix q I K assume read: "native_application_at (decode_finite_environment E) u r (fst q) (snd q) I K"
    show "\<exists>p J A. (p,J,A) |\<in>| finite_application_readings E u r \<and> fset A=K"
      using finite_application_readings_complete[OF read] by blast
  qed
  show ?thesis by (auto simp: finite_native_application_demands_def native_application_demands_def
      fimage.rep_eq projected split: prod.splits; force)
qed

definition finite_native_node_slots ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow>
    ('u definition_site,'u definition_site) finite_schema_graph_node \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) fset \<Rightarrow> local_address fset" where
  "finite_native_node_slots E n N D = finite_reading_slots
    (ffilter (\<lambda>((M,F),I,K). M=N \<and> F=D) (finite_proof_node_readings E (fst n) (snd n)))"

lemma finite_native_node_slots_member:
  "k |\<in>| finite_native_node_slots E n N D \<longleftrightarrow>
    (\<exists>I K. ((N,D),I,K) |\<in>| finite_proof_node_readings E (fst n) (snd n) \<and> k |\<in>| K)"
  by (simp only: finite_native_node_slots_def finite_reading_slots_member ffmember_filter
      split_paired_Ex prod.case; blast)

lemma finite_native_node_slots_correct:
  "fset (finite_native_node_slots E n N D) =
    {k. \<exists>I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) I K \<and> k \<in> K}"
proof (rule set_eqI)
  fix k
  show "k \<in> fset (finite_native_node_slots E n N D) \<longleftrightarrow>
      k \<in> {k. \<exists>I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        (decode_finite_graph_node N) (fset D) I K \<and> k \<in> K}"
  proof
    assume "k \<in> fset (finite_native_node_slots E n N D)"
    then obtain I K where member: "((N,D),I,K) |\<in>| finite_proof_node_readings E (fst n) (snd n)"
      and slot: "k |\<in>| K" by (simp only: finite_native_node_slots_member; blast)
    have read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
      using member by (simp add: finite_proof_node_readings_correct)
    show "k \<in> {k. \<exists>I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        (decode_finite_graph_node N) (fset D) I K \<and> k \<in> K}" using read slot by blast
  next
    assume "k \<in> {k. \<exists>I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) I K \<and> k \<in> K}"
    then obtain I K where read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        (decode_finite_graph_node N) (fset D) I K" and slot: "k \<in> K" by blast
    obtain M F J A where member: "((M,F),J,A) |\<in>| finite_proof_node_readings E (fst n) (snd n)"
      and decoded: "decode_finite_graph_node M=decode_finite_graph_node N" "fset F=fset D" "fset A=K"
      using finite_proof_node_readings_complete[OF read] by blast
    have same: "M=N" "F=D" using decoded by (simp_all add: fset_inject)
    show "k \<in> fset (finite_native_node_slots E n N D)"
      unfolding finite_native_node_slots_member
      apply (rule exI[of _ J], rule exI[of _ A])
      using member decoded slot same by simp
  qed
qed

definition finite_native_graph_sources :: "'u finite_native_derivation_graph \<Rightarrow> 'u fset" where
  "finite_native_graph_sources G = fimage fst (finite_graph_nodes G)"

lemma finite_native_graph_sources_correct:
  "fset (finite_native_graph_sources G) = native_graph_sources (decode_finite_graph G)"
  by (simp add: finite_native_graph_sources_def native_graph_sources_def fimage.rep_eq finite_graph_nodes_correct)

definition finite_native_graph_demands ::
  "'u finite_artifact_environment \<Rightarrow> 'u finite_native_derivation_graph \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_graph_demands E G = ffUnion (fimage (\<lambda>(n,N).
    fimage (Pair (fst n)) (finite_native_node_slots E n N (finite_graph_premises G n))) (finite_graph_inferences G))"

lemma finite_native_graph_demands_member:
  "(u,k) |\<in>| finite_native_graph_demands E G \<longleftrightarrow>
    (\<exists>n N. (n,N) |\<in>| finite_graph_inferences G \<and> u=fst n \<and>
      k |\<in>| finite_native_node_slots E n N (finite_graph_premises G n))"
  by (simp only: finite_native_graph_demands_def finite_union_image_member finite_image_member
      split_paired_Ex prod.case fst_conv prod.inject; blast)

theorem finite_native_graph_demands_correct:
  "fset (finite_native_graph_demands E G) = native_graph_demands (decode_finite_environment E) (decode_finite_graph G)"
proof -
  have member: "(u,k) |\<in>| finite_native_graph_demands E G \<longleftrightarrow>
      (u,k) \<in> native_graph_demands (decode_finite_environment E) (decode_finite_graph G)" for u k
    by (simp only: finite_native_graph_demands_member finite_native_node_slots_correct mem_Collect_eq
        finite_graph_premises_correct native_graph_demand_member decode_finite_graph_fields
        map_relation_values_member; blast)
  show ?thesis using member by (auto split: prod.splits)
qed

section \<open>One computed boundary retains all three native readings\<close>

definition finite_native_replay_sources ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow>
    'u finite_native_derivation_graph \<Rightarrow> 'u fset" where
  "finite_native_replay_sources E pu pr au G =
    finite_native_package_sources E pu pr |\<union>| {|au|} |\<union>| finite_native_graph_sources G"

lemma finite_native_replay_sources_correct:
  "fset (finite_native_replay_sources E pu pr au G) =
    native_replay_sources (decode_finite_environment E) pu pr au (decode_finite_graph G)"
  by (simp add: finite_native_replay_sources_def native_replay_sources_def
      finite_native_package_sources_correct finite_native_graph_sources_correct)

definition finite_native_replay_demands ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_derivation_graph \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_replay_demands E pu pr au ar G =
    finite_native_package_demands E pu pr |\<union>| finite_native_application_demands E au ar |\<union>| finite_native_graph_demands E G"

lemma finite_native_replay_demands_correct:
  "fset (finite_native_replay_demands E pu pr au ar G) =
    native_replay_demands (decode_finite_environment E) pu pr au ar (decode_finite_graph G)"
  by (simp add: finite_native_replay_demands_def native_replay_demands_def
      finite_native_package_demands_correct finite_native_application_demands_correct finite_native_graph_demands_correct)

definition finite_native_replay_environment ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_derivation_graph \<Rightarrow> 'u finite_artifact_environment" where
  "finite_native_replay_environment E pu pr au ar G =
    finite_read_environment E (finite_native_replay_sources E pu pr au G) (finite_native_replay_demands E pu pr au ar G)"

theorem finite_native_replay_environment_correct:
  "decode_finite_environment (finite_native_replay_environment E pu pr au ar G) =
    native_replay_environment (decode_finite_environment E) pu pr au ar (decode_finite_graph G)"
  by (simp add: finite_native_replay_environment_def native_replay_environment_def finite_read_environment_correct
      finite_native_replay_sources_correct finite_native_replay_demands_correct)

theorem finite_native_replay_environment_recovers:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    and graph: "G |\<in>| finite_native_graph_readings E root"
  shows "P |\<in>| finite_native_package_readings (finite_native_replay_environment E pu pr au ar G) pu pr"
    "((d,t),I,K) |\<in>| finite_application_readings (finite_native_replay_environment E pu pr au ar G) au ar"
    "G |\<in>| finite_native_graph_readings (finite_native_replay_environment E pu pr au ar G) root"
    "finite_environment_formed (finite_native_replay_environment E pu pr au ar G)"
proof -
  have program: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using package by (simp add: finite_native_package_readings_correct)
  have application: "native_application_at (decode_finite_environment E) au ar d (decode_finite_term t) (fset I) (fset K)"
    using app by (simp add: finite_application_readings_correct)
  have realization: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    using graph by (simp add: finite_native_graph_readings_correct)
  show "P |\<in>| finite_native_package_readings (finite_native_replay_environment E pu pr au ar G) pu pr"
    "((d,t),I,K) |\<in>| finite_application_readings (finite_native_replay_environment E pu pr au ar G) au ar"
    "G |\<in>| finite_native_graph_readings (finite_native_replay_environment E pu pr au ar G) root"
    "finite_environment_formed (finite_native_replay_environment E pu pr au ar G)"
    using native_replay_environment_recovers[OF program application realization]
    by (simp_all add: finite_native_package_readings_correct finite_application_readings_correct
        finite_native_graph_readings_correct finite_environment_formed_correct finite_native_replay_environment_correct)
qed

theorem finite_native_replay_environment_closed:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    and graph: "G |\<in>| finite_native_graph_readings E root"
  shows "finite_environment_closed (finite_native_replay_environment E pu pr au ar G) {|pu,au,fst root|}
    (finite_native_replay_demands (finite_native_replay_environment E pu pr au ar G) pu pr au ar G)"
proof -
  have program: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using package by (simp add: finite_native_package_readings_correct)
  have application: "native_application_at (decode_finite_environment E) au ar d (decode_finite_term t) (fset I) (fset K)"
    using app by (simp add: finite_application_readings_correct)
  have realization: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    using graph by (simp add: finite_native_graph_readings_correct)
  show ?thesis using native_replay_environment_closed[OF program application realization]
    by (simp add: finite_environment_closed_correct finite_native_replay_demands_correct finite_native_replay_environment_correct)
qed

theorem finite_native_replay_environment_least:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    and graph: "G |\<in>| finite_native_graph_readings E root"
    and included: "environment_included F (decode_finite_environment E)"
    and retained_package: "native_package_at F pu pr (decode_finite_system P)"
    and retained_app: "native_application_at F au ar d (decode_finite_term t) J L"
    and retained_graph: "native_schema_graph_at F root (decode_finite_graph G)"
  shows "environment_included (decode_finite_environment (finite_native_replay_environment E pu pr au ar G)) F"
proof -
  have program: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using package by (simp add: finite_native_package_readings_correct)
  have application: "native_application_at (decode_finite_environment E) au ar d (decode_finite_term t) (fset I) (fset K)"
    using app by (simp add: finite_application_readings_correct)
  have realization: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    using graph by (simp add: finite_native_graph_readings_correct)
  show ?thesis using native_replay_environment_least[
      OF program application realization included retained_package retained_app retained_graph]
    by (simp add: finite_native_replay_environment_correct)
qed

export_code finite_native_application_demands finite_native_graph_demands
  finite_native_replay_sources finite_native_replay_demands finite_native_replay_environment checking SML

text \<open>
  The actual program, application, and proof grammars determine one complete
  source-and-slot boundary. At each proof node, demanded slots come from the
  exact metadata and premise table in the supplied graph. The computed retained
  environment preserves all three readings, is closed from their roots, and is
  included in every included environment preserving those readings. No truth or
  derivation assumption is needed to compute or minimize this retention.
\<close>

end
