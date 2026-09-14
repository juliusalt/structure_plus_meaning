theory Factor_Graph_Construction
  imports Factor_Rooted_Proof_Families Factor_Reference_Packages
begin

section \<open>One complete artifact for each fresh proof-node use\<close>

theorem native_graph_placement_total:
  fixes E :: "local_address option artifact_environment" and G :: "local_address option native_derivation_graph"
  assumes ef: "environment_formed E" and formed: "schema_graph_formed G root"
    and metadata: "graph_metadata_at E G"
    and roots: "\<forall>n\<in>schema_graph_nodes G. snd n=[]"
    and fresh: "image fst (schema_graph_nodes G)\<inter>environment_uses E={}"
  shows "\<exists>F. environment_formed F \<and> environment_included E F \<and> native_schema_graph_at F root G \<and>
    (\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v)"
proof -
  let ?U = "image fst (schema_graph_nodes G)"
  let ?N = "\<lambda>u. rel_value (fset (graph_inferences G)) (u,[])"
  let ?D = "\<lambda>u. schema_graph_premises G (u,[])"
  have fin: "finite ?U" by simp
  have at_root: "\<And>u. u\<in>?U \<Longrightarrow> (u,[])\<in>schema_graph_nodes G"
    by (rule fixed_second_image_member[OF roots])
  have row: "\<And>u. u\<in>?U \<Longrightarrow> ((u,[]),?N u)\<in>fset (graph_inferences G)"
    by (rule schema_graph_node_value[OF formed at_root]; assumption)
  have inputs: "\<And>u. u\<in>?U \<Longrightarrow> graph_node_inputs_at E (?D u) (?N u)"
    using metadata row by (auto simp: graph_metadata_at_def)
  have each: "\<forall>u\<in>?U. \<exists>z. case z of (R,L,C,I,K) \<Rightarrow> proof_node_code_for (?N u) (?D u) R L C I K"
  proof (intro ballI)
    fix u assume member: "u\<in>?U"
    have target_addresses: "\<forall>s n. (s,n)\<in>?D u \<longrightarrow> octets_formed (snd n)"
    proof (intro allI impI)
      fix s n assume premise: "(s,n)\<in>?D u"
      have inside: "n\<in>schema_graph_nodes G"
        by (rule subsetD[OF schema_graph_premises_targets[OF formed] rel_ranI[OF premise]])
      show "octets_formed (snd n)" using roots inside by (simp add: octets_formed_def)
    qed
    obtain R L C I K where code: "proof_node_code_for (?N u) (?D u) R L C I K"
      using proof_node_code_total[OF ef inputs[OF member] schema_graph_premises_finite
        schema_graph_premises_functional[OF formed] target_addresses] by blast
    show "\<exists>z. case z of (R,L,C,I,K) \<Rightarrow> proof_node_code_for (?N u) (?D u) R L C I K"
      by (rule exI[of _ "(R,L,C,I,K)"]) (use code in simp)
  qed
  obtain code where selected: "\<forall>u\<in>?U.
    case code u of (R,L,C,I,K) \<Rightarrow> proof_node_code_for (?N u) (?D u) R L C I K"
    using bchoice[OF each] by blast
  let ?R = "\<lambda>u. fst (code u)"
  let ?L = "\<lambda>u. fst (snd (code u))"
  let ?C = "\<lambda>u. fst (snd (snd (code u)))"
  let ?I = "\<lambda>u. fst (snd (snd (snd (code u))))"
  let ?K = "\<lambda>u. snd (snd (snd (snd (code u))))"
  have codes: "\<And>u. u\<in>?U \<Longrightarrow> proof_node_code_for (?N u) (?D u) (?R u) (?L u) (?C u) (?I u) (?K u)"
  proof -
    fix u assume member: "u\<in>?U"
    obtain R L C I K where shape: "code u=(R,L,C,I,K)" by (cases "code u") auto
    show "proof_node_code_for (?N u) (?D u) (?R u) (?L u) (?C u) (?I u) (?K u)"
      using selected[rule_format, OF member] by (simp add: shape)
  qed
  have family_codes: "\<forall>n N. (n,N)\<in>fset (graph_inferences G) \<longrightarrow>
    proof_node_code_for N (schema_graph_premises G n) (?R (fst n)) (?L (fst n)) (?C (fst n)) (?I (fst n)) (?K (fst n))"
  proof (intro allI impI)
    fix n N assume row: "(n,N)\<in>fset (graph_inferences G)"
    have inside: "n\<in>schema_graph_nodes G" using row by (auto simp: schema_graph_nodes_def rel_dom_def)
    have use: "fst n\<in>?U" by (rule imageI[OF inside])
    have site: "(fst n,[])=n" by (rule fixed_second_shape[OF roots inside])
    have functional: "single_valued (fset (graph_inferences G))"
      using formed by (simp only: schema_graph_formed_def; blast)
    have node: "rel_value (fset (graph_inferences G)) n=N" by (rule rel_value_eq[OF functional row])
    show "proof_node_code_for N (schema_graph_premises G n)
      (?R (fst n)) (?L (fst n)) (?C (fst n)) (?I (fst n)) (?K (fst n))"
      using codes[OF use] by (simp only: site node)
  qed
  interpret family: rooted_proof_code_family E G root ?R ?L ?C ?I ?K
    by (rule rooted_proof_code_family.intro[OF ef formed metadata roots family_codes])
  obtain F where installed: "environment_formed F" "environment_included E F"
    "\<forall>u\<in>?U. artifact_at F u (?R u) \<and> syntax_references F u (?L u) (?C u)"
    "\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T"
    "\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
    using fresh_reference_environment[OF ef family.finite_uses fresh family.artifact_formation
      family.profiles family.bounds family.targets] by blast
  have native: "native_schema_graph_at F root G" by (rule family.installed[OF installed(1,3)])
  show ?thesis by (rule exI[of _ F]) (use installed native in blast)
qed

section \<open>Every finite source graph has fresh native proof-node coordinates\<close>

theorem native_graph_construction_total:
  fixes E :: "local_address option artifact_environment"
    and G :: "(local_address option definition_site,local_address option definition_site,
      local_address option definition_site,'n) schema_derivation_graph"
  assumes ef: "environment_formed E" and formed: "schema_graph_formed G root" and metadata: "graph_metadata_at E G"
  shows "\<exists>F h. environment_formed F \<and> environment_included E F \<and> inj_on h (schema_graph_nodes G) \<and>
    native_schema_graph_at F (h root) (rename_schema_graph h G) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T) \<and>
    (\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v)"
proof -
  obtain f where addressing: "finite_addressing (schema_graph_nodes G) f"
    using finite_addressing_exists[OF schema_graph_nodes_finite, of G] by blast
  have fin: "finite (environment_uses E)" by (rule environment_uses_finite[OF ef])
  let ?g = "\<lambda>n. fresh_use_map (environment_uses E) None (Some (f n))"
  let ?h = "\<lambda>n. (?g n,[] :: local_address)"
  let ?H = "rename_schema_graph ?h G"
  have injective: "inj_on ?h (schema_graph_nodes G)"
  proof (rule inj_onI)
    fix n m assume n: "n\<in>schema_graph_nodes G" and m: "m\<in>schema_graph_nodes G"
      and equal: "?h n=?h m"
    have use_eq: "fresh_use_map (environment_uses E) None (Some (f n))=
      fresh_use_map (environment_uses E) None (Some (f m))" using equal by simp
    have same: "f n=f m" using injD[OF fresh_use_map_injective[OF fin] use_eq] by simp
    have finj: "inj_on f (schema_graph_nodes G)" using addressing by (simp add: finite_addressing_def)
    show "n=m" by (rule inj_onD[OF finj same n m])
  qed
  have hf: "schema_graph_formed ?H (?h root)" by (rule renamed_schema_graph_formed[OF formed injective])
  have inputs: "graph_metadata_at E ?H" by (rule graph_metadata_rename[OF metadata formed injective])
  have roots: "\<forall>n\<in>schema_graph_nodes ?H. snd n=[]" by (simp add: schema_graph_renamed_nodes)
  have outside: "\<And>n. ?g n\<notin>environment_uses E"
    using fresh_use_map_outside[OF fin, where u=None] by blast
  have fresh: "image fst (schema_graph_nodes ?H)\<inter>environment_uses E={}"
    using outside by (auto simp: schema_graph_renamed_nodes)
  obtain F where final:
    "environment_formed F" "environment_included E F" "native_schema_graph_at F (?h root) ?H"
    "\<forall>u\<in>environment_uses E. \<forall>T. artifact_at F u T \<longleftrightarrow> artifact_at E u T"
    "\<forall>u\<in>environment_uses E. \<forall>k v. binds_slot F u k v \<longleftrightarrow> binds_slot E u k v"
    using native_graph_placement_total[OF ef hf inputs roots fresh] by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ ?h]) (use final injective in blast)
qed

text \<open>
  Every source node is placed once, with all premise links installed after the
  complete finite family of node artifacts exists. Repeated links to a proved
  node preserve sharing. The injective coordinate map preserves every source
  occurrence and does not change program clauses, bindings, or premise sockets.
  All previous artifacts and bindings remain exact. Native graph recovery
  then fixes the complete root-reachable graph, not merely a selected subset.
\<close>

end
