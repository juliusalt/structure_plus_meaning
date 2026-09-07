theory Factor_Retention_Observations
  imports Factor_Proof_Node_Reading Factor_Slot_Observations
    Factor_Replay_Retention Factor_Judgment_Retention Factor_Replay_Values
begin

section \<open>Complete row coverage characterizes the retained environment\<close>

lemma read_environment_fixed_coverage:
  "read_environment E U D=E \<longleftrightarrow>
    rel_dom (environment_bindings E)\<subseteq>D \<and>
    environment_uses E\<subseteq>U\<union>rel_ran (environment_bindings E)"
proof
  assume fixed: "read_environment E U D=E"
  have bindings: "environment_bindings (read_environment E U D)=environment_bindings E"
    by (simp only: fixed)
  have domain: "rel_dom (environment_bindings E)\<subseteq>D"
  proof
    fix x assume "x\<in>rel_dom (environment_bindings E)"
    then obtain v where row: "(x,v)\<in>environment_bindings E" by (auto simp: rel_dom_def)
    have kept: "(x,v)\<in>environment_bindings (read_environment E U D)" using row by (simp only: bindings)
    show "x\<in>D" using kept by (simp add: read_environment_def)
  qed
  have uses: "environment_uses E\<subseteq>read_environment_uses E U D"
  proof
    fix u assume "u\<in>environment_uses E"
    then obtain R where art: "artifact_at E u R" by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
    have kept: "artifact_at (read_environment E U D) u R" by (simp only: fixed; rule art)
    show "u\<in>read_environment_uses E U D" using kept by simp
  qed
  have targets: "read_environment_uses E U D\<subseteq>U\<union>rel_ran (environment_bindings E)"
    by (auto simp: read_environment_uses_def binds_slot_def rel_ran_def; blast)
  have covered: "environment_uses E\<subseteq>U\<union>rel_ran (environment_bindings E)"
    by (rule subset_trans[OF uses targets])
  show "rel_dom (environment_bindings E)\<subseteq>D \<and>
    environment_uses E\<subseteq>U\<union>rel_ran (environment_bindings E)"
    using domain covered by blast
next
  assume coverage: "rel_dom (environment_bindings E)\<subseteq>D \<and>
    environment_uses E\<subseteq>U\<union>rel_ran (environment_bindings E)"
  have uses: "U\<union>rel_ran (environment_bindings E)\<subseteq>read_environment_uses E U D"
    using coverage by (auto simp: read_environment_uses_def rel_dom_def rel_ran_def binds_slot_def)
  have all_uses: "environment_uses E\<subseteq>read_environment_uses E U D"
    by (rule subset_trans[OF conjunct2[OF coverage] uses])
  have keep_artifact: "fst z\<in>read_environment_uses E U D" if row: "z\<in>environment_artifacts E" for z
  proof -
    have source: "fst z\<in>environment_uses E" using row by (cases z) (auto simp: environment_uses_def rel_dom_def)
    show ?thesis by (rule subsetD[OF all_uses source])
  qed
  have artifacts: "environment_artifacts (read_environment E U D)=environment_artifacts E"
    using keep_artifact by (auto simp: read_environment_def)
  have keep_binding: "fst z\<in>D" if row: "z\<in>environment_bindings E" for z
  proof -
    have domain: "fst z\<in>rel_dom (environment_bindings E)" using row by (cases z) (auto simp: rel_dom_def)
    show ?thesis by (rule subsetD[OF conjunct1[OF coverage] domain])
  qed
  have bindings: "environment_bindings (read_environment E U D)=environment_bindings E"
    using keep_binding by (auto simp: read_environment_def)
  show "read_environment E U D=E" by (rule artifact_environment.equality[OF artifacts bindings]) simp
qed

lemma native_replay_closed_coverage:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G) \<longleftrightarrow>
    rel_dom (environment_bindings E)\<subseteq>native_replay_demands E pu pr au ar G \<and>
    environment_uses E\<subseteq>native_replay_sources E pu pr au G\<union>rel_ran (environment_bindings E)"
proof -
  have boundary: "read_boundary_formed E (native_replay_sources E pu pr au G) (native_replay_demands E pu pr au ar G)"
    by (rule native_replay_read_boundary[OF package app graph])
  have root: "root\<in>schema_graph_nodes G" using graph
    by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  have roots: "{pu,au,fst root}\<subseteq>native_replay_sources E pu pr au G"
    using root by (auto simp: native_replay_sources_def native_package_sources_def native_graph_sources_def)
  have fixed: "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G) \<longleftrightarrow>
    native_replay_environment E pu pr au ar G=E"
  proof
    assume closed: "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
    show "native_replay_environment E pu pr au ar G=E"
      unfolding native_replay_environment_def by (rule read_environment_closed_fixed[OF boundary closed roots])
  next
    assume same: "native_replay_environment E pu pr au ar G=E"
    show "environment_closed E {pu,au,fst root} (native_replay_demands E pu pr au ar G)"
      using native_replay_environment_closed[OF package app graph] by (simp only: same)
  qed
  show ?thesis by (simp only: fixed native_replay_environment_def read_environment_fixed_coverage)
qed

abbreviation replay_context_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "replay_context_term e pu pr au ar ru rr \<equiv>
    Pair_Term (Pair_Term e (Pair_Term (Pair_Term pu pr) (Pair_Term au ar))) (Pair_Term ru rr)"

abbreviation replay_context_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "replay_context_pattern e pu pr au ar ru rr \<equiv>
    Pattern_Pair (Pattern_Pair e (Pattern_Pair (Pattern_Pair pu pr) (Pattern_Pair au ar))) (Pattern_Pair ru rr)"

lemma replay_context_presents:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K" and graph: "native_schema_graph_at E (ru,rr) G"
  shows "replay_value_presents E pu pr au ar (ru,rr)
    (replay_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)
      (use_data_term ru) (Payload_Term rr))"
proof -
  have sites: "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    by (rule native_judgment_positions[OF package app])+
  have member: "(ru,rr)\<in>schema_graph_nodes G" using graph
    by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  have root: "(ru,rr)\<in>environment_positions E"
    by (rule subsetD[OF native_schema_graph_positions[OF graph] member])
  show ?thesis using source sites root
    by (auto simp: replay_value_presents_def judgment_value_presents_def site_data_term_def)
qed

lemma replay_context_formed:
  assumes "environment_value_presents E e" "native_package_at E pu pr P"
    "native_application_at E au ar d t I K" "native_schema_graph_at E (ru,rr) G"
  shows "term_formed (replay_context_term e (use_data_term pu) (Payload_Term pr)
    (use_data_term au) (Payload_Term ar) (use_data_term ru) (Payload_Term rr))"
  using replay_value_presents_formed[OF replay_context_presents[OF assms]] by blast

lemma native_graph_demands_at_nodes:
  assumes graph: "native_schema_graph_at E root G"
  shows "(u,k)\<in>native_graph_demands E G \<longleftrightarrow>
    (\<exists>a N D I K. (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D I K \<and> k\<in>K)"
proof
  assume "(u,k)\<in>native_graph_demands E G"
  then obtain n N I K where parts: "u=fst n" "(n,N)\<in>fset (graph_inferences G)"
    "native_proof_node_at E (fst n) (snd n) N (schema_graph_premises G n) I K" "k\<in>K"
    by (auto simp: native_graph_demand_member)
  have member: "n\<in>schema_graph_nodes G" using parts(2) by (auto simp: schema_graph_nodes_def rel_dom_def)
  have typed: "(u,snd n)\<in>schema_graph_nodes G" using member parts(1) by simp
  show "\<exists>a N D I K. (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D I K \<and> k\<in>K"
    by (rule exI[of _ "snd n"], rule exI[of _ N], rule exI[of _ "schema_graph_premises G n"],
      rule exI[of _ I], rule exI[of _ K]) (use typed parts(3,4) in \<open>simp add: parts(1)\<close>)
next
  assume "\<exists>a N D I K. (u,a)\<in>schema_graph_nodes G \<and> native_proof_node_at E u a N D I K \<and> k\<in>K"
  then obtain a N D I K where parts: "(u,a)\<in>schema_graph_nodes G" "native_proof_node_at E u a N D I K" "k\<in>K" by blast
  obtain A J L where actual: "((u,a),A)\<in>fset (graph_inferences G)"
    "native_proof_node_at E u a A (schema_graph_premises G (u,a)) J L"
    using native_schema_graph_node[OF graph parts(1)] by auto
  have same: "K=L" using native_proof_node_unique[OF parts(2) actual(2)] by blast
  show "(u,k)\<in>native_graph_demands E G"
    using native_graph_demandI[OF actual(1), of E J L k] actual(2) parts(3) same by simp
qed

section \<open>Observed slot lists come from the actual readers\<close>

lemma citation_slot_observation:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>s a i. (42,citation_reading_argument e (use_data_term u) (Payload_Term r) (Pair_Term s a) i)
      \<in>positive_meaning citation_reading_system \<and> selected_data_member x s) \<longleftrightarrow>
    (\<exists>k R c I. x=Payload_Term k \<and> artifact_at E u R \<and> citation_at R r c I \<and> k\<in>citation_slots c)"
proof
  assume "\<exists>s a i. (42,citation_reading_argument e (use_data_term u) (Payload_Term r) (Pair_Term s a) i)
    \<in>positive_meaning citation_reading_system \<and> selected_data_member x s"
  then obtain s a i where read: "(42,citation_reading_argument e (use_data_term u) (Payload_Term r) (Pair_Term s a) i)
    \<in>positive_meaning citation_reading_system" and selected: "selected_data_member x s" by blast
  obtain R c Is where raw: "artifact_at E u R" "citation_at R r c (set Is)" "citation_data_term c=Pair_Term s a"
    using read by (auto simp: citation_reading_at_source[OF source] inj_eq[OF use_data_term_injective])
  obtain Ss where slots: "s=data_list_term (map Payload_Term Ss)" "set Ss=citation_slots c"
    using citation_data_slot_fields[OF raw(3)] by blast
  have formed: "term_formed s" using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  obtain k where member: "x=Payload_Term k" "k\<in>citation_slots c"
    using selected by (simp only: slots(1) selected_payload_list[OF formed[unfolded slots(1)]]; use slots(2) in blast)
  show "\<exists>k R c I. x=Payload_Term k \<and> artifact_at E u R \<and> citation_at R r c I \<and> k\<in>citation_slots c"
    using raw member by blast
next
  assume "\<exists>k R c I. x=Payload_Term k \<and> artifact_at E u R \<and> citation_at R r c I \<and> k\<in>citation_slots c"
  then obtain k R c I where raw: "x=Payload_Term k" "artifact_at E u R" "citation_at R r c I" "k\<in>citation_slots c" by blast
  have finite: "finite I" using raw_citation_interior(1) raw(3) by (auto simp: citation_at_def)
  obtain Is where order: "distinct Is" "set Is=I" using finite_distinct_list[OF finite] by blast
  obtain Ss a where shape: "citation_data_term c=Pair_Term (data_list_term (map Payload_Term Ss)) a"
    and slots: "set Ss=citation_slots c" using citation_data_slot_shape[of c] by blast
  have read: "(42,citation_reading_argument e (use_data_term u) (Payload_Term r) (citation_data_term c)
    (data_list_term (map Payload_Term Is)))\<in>positive_meaning citation_reading_system"
    by (rule citation_reading_complete[OF source raw(2) order(1)]) (simp only: order(2); rule raw(3))
  have formed: "term_formed (data_list_term (map Payload_Term Ss))"
    using citation_data_formed_at[OF raw(3)] by (simp only: shape; simp)
  have selected: "selected_data_member x (data_list_term (map Payload_Term Ss))"
    using raw(1,4) slots by (simp add: selected_payload_list[OF formed])
  show "\<exists>s a i. (42,citation_reading_argument e (use_data_term u) (Payload_Term r) (Pair_Term s a) i)
    \<in>positive_meaning citation_reading_system \<and> selected_data_member x s"
    using read[unfolded shape] selected by blast
qed

lemma application_reading_value:
  assumes source: "environment_value_presents E e" and app: "native_application_at E u r d t I K"
  shows "\<exists>i k. (58,application_reading_argument e (use_data_term u) (Payload_Term r)
    (definition_site_value d) t i k)\<in>positive_meaning application_reading_system"
proof -
  obtain Is Ks where lists: "distinct Is" "distinct Ks" "set Is=I" "set Ks=K"
    using native_application_properties[OF app] finite_distinct_list[of I] finite_distinct_list[of K] by blast
  have actual: "native_application_at E u r (fst d,snd d) t (set Is) (set Ks)" using app lists by simp
  show ?thesis using application_reading_complete[OF source lists(1,2) actual] by blast
qed

lemma application_slot_observation:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>d t i ks. (58,application_reading_argument e (use_data_term u) (Payload_Term r) d t i ks)
      \<in>positive_meaning application_reading_system \<and> selected_data_member x ks) \<longleftrightarrow>
    (\<exists>k d t I K. x=Payload_Term k \<and> native_application_at E u r d t I K \<and> k\<in>K)"
proof
  assume "\<exists>d t i ks. (58,application_reading_argument e (use_data_term u) (Payload_Term r) d t i ks)
    \<in>positive_meaning application_reading_system \<and> selected_data_member x ks"
  then obtain d t i ks where read: "(58,application_reading_argument e (use_data_term u) (Payload_Term r) d t i ks)
    \<in>positive_meaning application_reading_system" and selected: "selected_data_member x ks" by blast
  obtain du da Is Ks where raw: "ks=data_list_term (map Payload_Term Ks)"
    "native_application_at E u r (du,da) t (set Is) (set Ks)"
    using read by (auto simp: application_reading_at_source[OF source] inj_eq[OF use_data_term_injective])
  have formed: "term_formed ks" using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  show "\<exists>k d t I K. x=Payload_Term k \<and> native_application_at E u r d t I K \<and> k\<in>K"
    using selected raw(2) by (simp only: raw(1) selected_payload_list[OF formed[unfolded raw(1)]]; blast)
next
  assume "\<exists>k d t I K. x=Payload_Term k \<and> native_application_at E u r d t I K \<and> k\<in>K"
  then obtain k d t I K where raw: "x=Payload_Term k" "native_application_at E u r d t I K" "k\<in>K" by blast
  obtain i ks where read: "(58,application_reading_argument e (use_data_term u) (Payload_Term r)
    (definition_site_value d) t i ks)\<in>positive_meaning application_reading_system"
    using application_reading_value[OF source raw(2)] by blast
  obtain Is Ks where lists: "ks=data_list_term (map Payload_Term Ks)"
    "native_application_at E u r d t (set Is) (set Ks)"
    using read by (auto simp: application_reading_at_source[OF source] inj_eq[OF use_data_term_injective] site_data_term_def)
  have same: "set Ks=K" using native_application_unique[OF lists(2) raw(2)] by blast
  have formed: "term_formed ks" using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  have selected: "selected_data_member x ks"
    by (simp only: lists(1) selected_payload_list[OF formed[unfolded lists(1)]]; use raw(1,3) same in blast)
  show "\<exists>d t i ks. (58,application_reading_argument e (use_data_term u) (Payload_Term r) d t i ks)
    \<in>positive_meaning application_reading_system \<and> selected_data_member x ks" using read selected by blast
qed

lemma proof_slot_observation:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>n i ks. (94,term_quotation_argument e (use_data_term u) (Payload_Term r) n i ks)
      \<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks) \<longleftrightarrow>
    (\<exists>k N D I K. x=Payload_Term k \<and> native_proof_node_at E u r N D I K \<and> k\<in>K)"
proof
  assume "\<exists>n i ks. (94,term_quotation_argument e (use_data_term u) (Payload_Term r) n i ks)
    \<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks"
  then obtain n i ks where read: "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n i ks)
    \<in>positive_meaning proof_node_reading_system" and selected: "selected_data_member x ks" by blast
  obtain N D Is Ks where raw: "ks=data_list_term (map Payload_Term Ks)"
    "native_proof_node_at E u r N D (set Is) (set Ks)"
    using read by (auto simp: proof_node_reading_at_source[OF source] inj_eq[OF use_data_term_injective])
  have formed: "term_formed ks" using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  show "\<exists>k N D I K. x=Payload_Term k \<and> native_proof_node_at E u r N D I K \<and> k\<in>K"
    using selected raw(2) by (simp only: raw(1) selected_payload_list[OF formed[unfolded raw(1)]]; blast)
next
  assume "\<exists>k N D I K. x=Payload_Term k \<and> native_proof_node_at E u r N D I K \<and> k\<in>K"
  then obtain k N D I K where raw: "x=Payload_Term k" "native_proof_node_at E u r N D I K" "k\<in>K" by blast
  obtain Is Ks where lists: "distinct Is" "distinct Ks" "set Is=I" "set Ks=K"
    using native_proof_node_properties(6,7)[OF raw(2)] finite_distinct_list[of I] finite_distinct_list[of K] by blast
  obtain n where presented: "proof_node_value_presents N D n" using proof_node_value_total[OF raw(2)] by blast
  have actual: "native_proof_node_at E u r N D (set Is) (set Ks)" using raw(2) lists by simp
  have read: "(94,term_quotation_argument e (use_data_term u) (Payload_Term r) n
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning proof_node_reading_system"
    by (rule proof_node_reading_complete[OF source lists(1,2) actual presented])
  have formed: "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  have selected: "selected_data_member x (data_list_term (map Payload_Term Ks))"
    using raw(1,3) lists(4) by (simp add: selected_payload_list[OF formed])
  show "\<exists>n i ks. (94,term_quotation_argument e (use_data_term u) (Payload_Term r) n i ks)
    \<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks" using read selected by blast
qed

lemma application_slot_observation_fields:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>d t i ks. (58,application_reading_argument e u r d t i ks)\<in>positive_meaning application_reading_system \<and> selected_data_member x ks)
    \<longleftrightarrow> (\<exists>v a k d t I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_application_at E v a d t I K \<and> k\<in>K)"
proof
  assume "\<exists>d t i ks. (58,application_reading_argument e u r d t i ks)\<in>positive_meaning application_reading_system \<and> selected_data_member x ks"
  then obtain d t i ks where read: "(58,application_reading_argument e u r d t i ks)\<in>positive_meaning application_reading_system"
    and selected: "selected_data_member x ks" by blast
  obtain v a where fields: "u=use_data_term v" "r=Payload_Term a"
    using read by (auto simp: application_reading_at_source[OF source])
  have observed: "\<exists>d t i ks. (58,application_reading_argument e (use_data_term v) (Payload_Term a) d t i ks)
    \<in>positive_meaning application_reading_system \<and> selected_data_member x ks"
    using read selected by (simp only: fields; blast)
  show "\<exists>v a k d t I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_application_at E v a d t I K \<and> k\<in>K"
    using fields observed by (simp only: application_slot_observation[OF source]) blast
next
  assume "\<exists>v a k d t I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_application_at E v a d t I K \<and> k\<in>K"
  then obtain v a k d t I K where fields: "u=use_data_term v" "r=Payload_Term a"
    and raw: "x=Payload_Term k" "native_application_at E v a d t I K" "k\<in>K" by blast
  show "\<exists>d t i ks. (58,application_reading_argument e u r d t i ks)\<in>positive_meaning application_reading_system \<and> selected_data_member x ks"
    by (simp only: fields application_slot_observation[OF source]) (use raw in blast)
qed

lemma proof_slot_observation_fields:
  assumes source: "environment_value_presents E e"
  shows "(\<exists>n i ks. (94,term_quotation_argument e u r n i ks)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks)
    \<longleftrightarrow> (\<exists>v a k N D I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_proof_node_at E v a N D I K \<and> k\<in>K)"
proof
  assume "\<exists>n i ks. (94,term_quotation_argument e u r n i ks)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks"
  then obtain n i ks where read: "(94,term_quotation_argument e u r n i ks)\<in>positive_meaning proof_node_reading_system"
    and selected: "selected_data_member x ks" by blast
  obtain v a where fields: "u=use_data_term v" "r=Payload_Term a"
    using read by (auto simp: proof_node_reading_at_source[OF source])
  have observed: "\<exists>n i ks. (94,term_quotation_argument e (use_data_term v) (Payload_Term a) n i ks)
    \<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks"
    using read selected by (simp only: fields; blast)
  show "\<exists>v a k N D I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_proof_node_at E v a N D I K \<and> k\<in>K"
    using fields observed by (simp only: proof_slot_observation[OF source]) blast
next
  assume "\<exists>v a k N D I K. u=use_data_term v \<and> r=Payload_Term a \<and> x=Payload_Term k \<and>
      native_proof_node_at E v a N D I K \<and> k\<in>K"
  then obtain v a k N D I K where fields: "u=use_data_term v" "r=Payload_Term a"
    and raw: "x=Payload_Term k" "native_proof_node_at E v a N D I K" "k\<in>K" by blast
  show "\<exists>n i ks. (94,term_quotation_argument e u r n i ks)\<in>positive_meaning proof_node_reading_system \<and> selected_data_member x ks"
    by (simp only: fields proof_slot_observation[OF source]) (use raw in blast)
qed

section \<open>Projection follows every stored environment row\<close>

lemma collection_pair_keys_total:
  assumes collection: "data_collection_presents read A a" and formed: "term_formed a"
    and pairs: "\<And>z v. z\<in>A \<Longrightarrow> read z v \<Longrightarrow> \<exists>x y. v=Pair_Term x y"
  shows "\<exists>keys. (51,Pair_Term a keys)\<in>positive_meaning row_keys_system"
proof -
  have represented: "\<exists>ts. a=data_list_term ts \<and> (\<forall>v\<in>set ts. \<exists>x y. v=Pair_Term x y)"
    by (rule data_collection_presents_elements[OF collection]) (rule pairs; assumption)
  obtain ts where shape: "a=data_list_term ts" and each: "\<forall>v\<in>set ts. \<exists>x y. v=Pair_Term x y"
    using represented by blast
  have range: "\<forall>v\<in>set ts. \<exists>z. v=(case z of (x,y) \<Rightarrow> Pair_Term x y)" using each by auto
  obtain xs where rows: "ts=map (\<lambda>(x,y). Pair_Term x y) xs"
    using list_range_witnesses[of ts "\<lambda>(x,y). Pair_Term x y"] range by blast
  have at: "a=pair_list_term xs" by (simp only: shape rows)
  show ?thesis using row_keys_complete[OF formed[unfolded at]] by (simp only: at; blast)
qed

lemma row_keys_selected:
  assumes keys: "(51,Pair_Term a k)\<in>positive_meaning row_keys_system" and data: "self_contained_term a"
  shows "\<exists>xs. k=data_list_term xs \<and> (\<forall>x. x\<in>set xs \<longleftrightarrow> (\<exists>y. selected_data_member (Pair_Term x y) a))"
proof -
  obtain ys where rows: "a=pair_list_term ys" "k=data_list_term (map fst ys)" "term_formed (pair_list_term ys)"
    using keys by (auto simp: row_keys_exact)
  have formed: "data_elements (map (\<lambda>(x,y). Pair_Term x y) ys)"
    using rows(3) data by (simp only: rows(1) data_list_term_formed data_list_term_self_contained; blast)
  have selected: "selected_data_member (Pair_Term x y) a \<longleftrightarrow> (x,y)\<in>set ys" for x y
    by (simp only: rows(1) selected_data_member_exact data_list_term_injective; use formed in auto)
  show ?thesis by (rule exI[of _ "map fst ys"]) (simp add: rows(2) selected; force)
qed

lemma environment_keys_total:
  assumes source: "environment_value_presents E (Pair_Term a b)"
  shows "\<exists>us ks. (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
proof -
  have af: "term_formed a" and bf: "term_formed b" using environment_value_presents_formed[OF source] by auto
  have artifacts: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    and bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E) b"
    using source by (auto simp: environment_value_presents_def)
  have left: "\<exists>us. (51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    by (rule collection_pair_keys_total[OF artifacts af]) (auto simp: environment_artifact_entry_presents_def)
  have right: "\<exists>ks. (51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    by (rule collection_pair_keys_total[OF bindings bf]) (auto simp: binding_data_def)
  show ?thesis using left right by blast
qed

lemma environment_artifact_keys:
  assumes source: "environment_value_presents E (Pair_Term a b)"
    and keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
  shows "\<exists>xs. us=data_list_term xs \<and> set xs=image use_data_term (environment_uses E)"
proof -
  have data: "self_contained_term a" using environment_value_presents_formed[OF source] by auto
  obtain xs where rows: "us=data_list_term xs"
    "\<forall>x. x\<in>set xs \<longleftrightarrow> (\<exists>y. selected_data_member (Pair_Term x y) a)"
    using row_keys_selected[OF keys data] by blast
  have range: "set xs=image use_data_term (environment_uses E)"
    using rows(2) environment_artifact_selection[OF source]
    by (auto simp: environment_uses_def rel_dom_def artifact_at_def; blast)
  show ?thesis using rows(1) range by blast
qed

lemma environment_binding_keys:
  assumes source: "environment_value_presents E (Pair_Term a b)"
    and keys: "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
  shows "\<exists>xs. ks=data_list_term xs \<and> set xs=image definition_site_value (rel_dom (environment_bindings E))"
proof -
  have data: "self_contained_term b" using environment_value_presents_formed[OF source] by auto
  obtain xs where rows: "ks=data_list_term xs"
    "\<forall>x. x\<in>set xs \<longleftrightarrow> (\<exists>y. selected_data_member (Pair_Term x y) b)"
    using row_keys_selected[OF keys data] by blast
  have key: "x\<in>set xs \<longleftrightarrow>
    (\<exists>u k v. x=Pair_Term (use_data_term u) (Payload_Term k) \<and> binds_slot E u k v)" for x
    by (simp only: rows(2)[rule_format] environment_binding_selection[OF source]
      binding_data_def fst_conv snd_conv factor_term.inject; blast)
  have range: "set xs=image definition_site_value (rel_dom (environment_bindings E))"
  proof (rule set_eqI)
    fix x
    show "x\<in>set xs \<longleftrightarrow> x\<in>image definition_site_value (rel_dom (environment_bindings E))"
    proof
      assume "x\<in>set xs"
      then obtain u k v where parts: "x=Pair_Term (use_data_term u) (Payload_Term k)" "binds_slot E u k v"
        by (simp only: key) blast
      have domain: "(u,k)\<in>rel_dom (environment_bindings E)" using parts(2) by (auto simp: binds_slot_def rel_dom_def)
      have encoded: "x=definition_site_value (u,k)" using parts(1) by (simp add: site_data_term_def)
      show "x\<in>image definition_site_value (rel_dom (environment_bindings E))"
        by (simp only: encoded; rule imageI; rule domain)
    next
      assume "x\<in>image definition_site_value (rel_dom (environment_bindings E))"
      then obtain q where row: "x=definition_site_value q" "q\<in>rel_dom (environment_bindings E)" by blast
      obtain u k where coords: "q=(u,k)" by (cases q)
      obtain v where binding: "binds_slot E u k v" using row(2) by (auto simp: coords rel_dom_def binds_slot_def)
      show "x\<in>set xs" by (simp only: key) (use row(1) coords binding in \<open>auto simp: site_data_term_def\<close>)
    qed
  qed
  show ?thesis using rows(1) range by blast
qed

text \<open>
  Coverage reads the complete stored artifact and binding lists. The two finite
  inclusions characterize exactly the existing closed replay environment once
  the package, application, and graph have been read. No derivation or truth
  premise is used. Whole artifact values remain the unit of retention.

  The context abbreviation expands to the existing replay value: one complete
  environment and three actual sites. It adds no field to that value. Slot
  observations select actual reader outputs; an unused optional citation slot
  contributes nothing.
\<close>

end
