theory Factor_Proof_Retention
  imports Factor_Proof_Restriction
begin

section \<open>The graph grammar determines its retained sources and references\<close>

definition native_graph_sources :: "'u native_derivation_graph \<Rightarrow> 'u set" where
  "native_graph_sources G = fst ` schema_graph_nodes G"

definition native_graph_demands ::
  "'u artifact_environment \<Rightarrow> 'u native_derivation_graph \<Rightarrow> ('u \<times> local_address) set" where
  "native_graph_demands E G = {(fst n,k) |n A I K k.
    (n,A) \<in> fset (graph_inferences G) \<and>
    native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K \<and> k \<in> K}"

lemma native_graph_demand_member:
  "(u,k) \<in> native_graph_demands E G \<longleftrightarrow>
    (\<exists>n A I K. (n,A) \<in> fset (graph_inferences G) \<and> u=fst n \<and>
      native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K \<and> k \<in> K)"
  by (auto simp: native_graph_demands_def)

lemma native_graph_demandI:
  assumes member: "(n,A) \<in> fset (graph_inferences G)"
    and node: "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K"
    and slot: "k \<in> K"
  shows "(fst n,k) \<in> native_graph_demands E G"
  unfolding native_graph_demand_member
  by (rule exI[of _ n], rule exI[of _ A], rule exI[of _ I], rule exI[of _ K]) (use assms in simp)

theorem native_graph_read_boundary:
  assumes graph: "native_schema_graph_at E root G"
  shows "read_boundary_formed E (native_graph_sources G) (native_graph_demands E G)"
proof -
  have ef: "environment_formed E" by (rule native_schema_graph_environment[OF graph])
  have sources: "native_graph_sources G \<subseteq> environment_uses E"
  proof
    fix u assume member: "u \<in> native_graph_sources G"
    obtain n where node: "n \<in> schema_graph_nodes G" and same: "u=fst n"
      using member by (auto simp: native_graph_sources_def)
    have position: "n \<in> environment_positions E"
      by (rule subsetD[OF native_schema_graph_positions[OF graph] node])
    obtain R where art: "artifact_at E (fst n) R" using position by (cases n) auto
    show "u \<in> environment_uses E" using art same
      by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  qed
  have demands: "native_graph_demands E G \<subseteq> rel_dom (environment_bindings E)"
  proof
    fix x assume member: "x \<in> native_graph_demands E G"
    obtain n A I K k where parts: "x=(fst n,k)"
      "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K" "k \<in> K"
      using member by (auto simp: native_graph_demands_def)
    show "x \<in> rel_dom (environment_bindings E)" using native_proof_node_slots_bound[OF parts(2,3)] parts(1) by simp
  qed
  have scope: "fst ` native_graph_demands E G \<subseteq> native_graph_sources G"
    by (auto simp: native_graph_demands_def native_graph_sources_def schema_graph_nodes_def rel_dom_def intro: rev_image_eqI; blast)
  show ?thesis using ef sources demands scope by (simp add: read_boundary_formed_def)
qed

theorem native_schema_graph_read_environment:
  assumes graph: "native_schema_graph_at E root G" and boundary: "read_boundary_formed E U D"
    and sources: "native_graph_sources G \<subseteq> U" and demands: "native_graph_demands E G \<subseteq> D"
  shows "native_schema_graph_at (read_environment E U D) root G"
proof -
  have formed: "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  have nodes: "\<forall>n A. (n,A) \<in> fset (graph_inferences G) \<longrightarrow>
    (\<exists>I K. native_proof_node_at (read_environment E U D) (fst n) (snd n) A (schema_graph_premises G n) I K)"
  proof (intro allI impI)
    fix n A assume member: "(n,A) \<in> fset (graph_inferences G)"
    obtain I K where node: "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K"
      using native_schema_graph_entry[OF graph member] by blast
    have source: "fst n \<in> U"
      using sources member by (auto simp: native_graph_sources_def schema_graph_nodes_def rel_dom_def)
    have slots: "\<forall>k\<in>K. (fst n,k) \<in> D"
      using demands native_graph_demandI[OF member node] by blast
    show "\<exists>I K. native_proof_node_at (read_environment E U D) (fst n) (snd n) A (schema_graph_premises G n) I K"
      using native_proof_node_read_environment[OF node boundary source slots] by blast
  qed
  show ?thesis using formed nodes by (simp add: native_schema_graph_at_def)
qed

lemma native_graph_demands_preserved:
  assumes graph: "native_schema_graph_at E root G"
    and copy: "\<And>n A I K. (n,A)\<in>fset (graph_inferences G) \<Longrightarrow>
      native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K \<Longrightarrow>
      native_proof_node_at F (fst n) (snd n) A (schema_graph_premises G n) I K"
  shows "native_graph_demands F G=native_graph_demands E G"
proof -
  have forward: "native_graph_demands E G \<subseteq> native_graph_demands F G"
  proof
    fix x assume member: "x \<in> native_graph_demands E G"
    obtain n A I K k where parts: "x=(fst n,k)" "(n,A) \<in> fset (graph_inferences G)"
      "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K" "k \<in> K"
      using member by (auto simp: native_graph_demands_def)
    have node: "native_proof_node_at F (fst n) (snd n) A (schema_graph_premises G n) I K"
      by (rule copy[OF parts(2,3)])
    show "x \<in> native_graph_demands F G" using native_graph_demandI[OF parts(2) node parts(4)] parts(1) by simp
  qed
  have reverse: "native_graph_demands F G \<subseteq> native_graph_demands E G"
  proof
    fix x assume member: "x \<in> native_graph_demands F G"
    obtain n A I K k where parts: "x=(fst n,k)" "(n,A) \<in> fset (graph_inferences G)"
      "native_proof_node_at F (fst n) (snd n) A (schema_graph_premises G n) I K" "k \<in> K"
      using member by (auto simp: native_graph_demands_def)
    obtain J W where old: "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) J W"
      using native_schema_graph_entry[OF graph parts(2)] by blast
    have new: "native_proof_node_at F (fst n) (snd n) A (schema_graph_premises G n) J W"
      by (rule copy[OF parts(2) old])
    have same: "K=W" using native_proof_node_unique[OF parts(3) new] by blast
    have slot: "k \<in> W" using parts(4) same by simp
    show "x \<in> native_graph_demands E G" using native_graph_demandI[OF parts(2) old slot] parts(1) by simp
  qed
  show ?thesis using forward reverse by blast
qed

lemma native_graph_demands_stable:
  assumes graph: "native_schema_graph_at E root G" and boundary: "read_boundary_formed E U D"
    and sources: "native_graph_sources G \<subseteq> U" and demands: "native_graph_demands E G \<subseteq> D"
  shows "native_graph_demands (read_environment E U D) G=native_graph_demands E G"
proof -
  let ?F = "read_environment E U D"
  have copy: "\<And>n A I K. (n,A) \<in> fset (graph_inferences G) \<Longrightarrow>
    native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K \<Longrightarrow>
    native_proof_node_at ?F (fst n) (snd n) A (schema_graph_premises G n) I K"
  proof -
    fix n A I K assume member: "(n,A) \<in> fset (graph_inferences G)"
      and node: "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) I K"
    have source: "fst n \<in> U"
      using sources member by (auto simp: native_graph_sources_def schema_graph_nodes_def rel_dom_def)
    have slots: "\<forall>k\<in>K. (fst n,k) \<in> D" using demands native_graph_demandI[OF member node] by blast
    show "native_proof_node_at ?F (fst n) (snd n) A (schema_graph_premises G n) I K"
      by (rule native_proof_node_read_environment[OF node boundary source slots])
  qed
  show ?thesis by (rule native_graph_demands_preserved[OF graph copy])
qed

definition native_proof_environment ::
  "'u artifact_environment \<Rightarrow> 'u native_derivation_graph \<Rightarrow> 'u artifact_environment" where
  "native_proof_environment E G = read_environment E (native_graph_sources G) (native_graph_demands E G)"

theorem native_proof_environment_recovers:
  assumes graph: "native_schema_graph_at E root G"
  shows "native_schema_graph_at (native_proof_environment E G) root G"
  unfolding native_proof_environment_def
  by (rule native_schema_graph_read_environment[OF graph native_graph_read_boundary[OF graph]]) simp_all

theorem native_proof_environment_closed:
  assumes graph: "native_schema_graph_at E root G"
  shows "environment_closed (native_proof_environment E G) (native_graph_sources G) (native_graph_demands E G)"
  unfolding native_proof_environment_def by (rule read_environment_closed[OF native_graph_read_boundary[OF graph]])

theorem native_proof_environment_demands:
  assumes graph: "native_schema_graph_at E root G"
  shows "native_graph_demands (native_proof_environment E G) G=native_graph_demands E G"
  unfolding native_proof_environment_def
  by (rule native_graph_demands_stable[OF graph native_graph_read_boundary[OF graph]]) simp_all

lemma native_proof_environment_included:
  "environment_included (native_proof_environment E G) E"
  unfolding native_proof_environment_def by (rule read_environment_included)

theorem native_proof_environment_idempotent:
  assumes graph: "native_schema_graph_at E root G"
  shows "native_proof_environment (native_proof_environment E G) G=native_proof_environment E G"
proof -
  have demands: "native_graph_demands (native_proof_environment E G) G=native_graph_demands E G"
    by (rule native_proof_environment_demands[OF graph])
  show ?thesis using demands by (simp add: native_proof_environment_def read_environment_idempotent)
qed

text \<open>
  The proof grammar determines its complete source uses and outgoing slots.
  Restricting to that boundary preserves the entire native graph and recovers
  the same demands on rereading. Literal targets retain their exact artifact
  values; location references retain their target uses and addresses. This is
  the proof's retention boundary. A replay must additionally retain its
  independently selected program and root call.
\<close>

end
