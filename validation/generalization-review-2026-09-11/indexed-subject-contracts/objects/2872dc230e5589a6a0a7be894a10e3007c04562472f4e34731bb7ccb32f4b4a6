theory Factor_Executable_Realization
  imports Factor_Executable_Metadata Factor_Executable_Packages Factor_Realization
begin

type_synonym 'u finite_native_derivation_graph =
  "('u definition_site,'u definition_site,'u definition_site,'u definition_site) finite_derivation_graph"

section \<open>Every node reading comes from an actual environment position\<close>

definition finite_proof_node_rows ::
  "'u finite_artifact_environment \<Rightarrow>
    ('u definition_site \<times> 'u finite_native_node_metadata finite_syntax_reading) fset" where
  "finite_proof_node_rows E = ffUnion (fimage (\<lambda>n.
    fimage (Pair n) (finite_proof_node_readings E (fst n) (snd n))) (finite_environment_positions E))"

lemma finite_proof_node_rows_step:
  "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<longleftrightarrow>
    n |\<in>| finite_environment_positions E \<and>
    ((N,D),I,K) |\<in>| finite_proof_node_readings E (fst n) (snd n)"
  by (simp only: finite_proof_node_rows_def finite_union_image_member finite_image_member prod.inject; blast)

lemma finite_proof_node_rows_correct:
  "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<longleftrightarrow>
    native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
proof -
  have position: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) (fset I) (fset K) \<Longrightarrow>
      n \<in> environment_positions (decode_finite_environment E)"
    using native_proof_node_properties(2)[of "decode_finite_environment E" "fst n" "snd n"] by simp
  show ?thesis using position
    by (auto simp: finite_proof_node_rows_step finite_environment_positions_correct finite_proof_node_readings_correct)
qed

lemma finite_proof_node_rows_complete:
  assumes read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K"
  shows "\<exists>M F J A. (n,(M,F),J,A) |\<in>| finite_proof_node_rows E \<and>
    decode_finite_graph_node M=N \<and> fset F=D \<and> fset J=I \<and> fset A=K"
proof -
  obtain M F J A where member: "((M,F),J,A) |\<in>| finite_proof_node_readings E (fst n) (snd n)"
    and decoded: "decode_finite_graph_node M=N" "fset F=D" "fset J=I" "fset A=K"
    using finite_proof_node_readings_complete[OF read] by blast
  have row: "(n,(M,F),J,A) |\<in>| finite_proof_node_rows E"
    using read decoded by (simp add: finite_proof_node_rows_correct)
  show ?thesis using row decoded by blast
qed

definition finite_native_proof_edges ::
  "'u finite_artifact_environment \<Rightarrow> ('u definition_site \<times> 'u definition_site) fset" where
  "finite_native_proof_edges E = ffUnion (fimage (\<lambda>(n,(N,D),I,K).
    fimage (\<lambda>(s,m). (m,n)) D) (finite_proof_node_rows E))"

lemma finite_native_proof_edges_step:
  "(m,n) |\<in>| finite_native_proof_edges E \<longleftrightarrow>
    (\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D)"
proof
  assume member: "(m,n) |\<in>| finite_native_proof_edges E"
  have raw: "\<exists>q. q |\<in>| finite_proof_node_rows E \<and>
      (m,n) |\<in>| (case q of (a,(N,D),I,K) \<Rightarrow> fimage (\<lambda>(s,t). (t,a)) D)"
    using member by (simp only: finite_native_proof_edges_def finite_union_image_member case_prod_unfold)
  obtain q where actual: "q |\<in>| finite_proof_node_rows E"
    and target: "(m,n) |\<in>| (case q of (a,(N,D),I,K) \<Rightarrow> fimage (\<lambda>(s,t). (t,a)) D)"
    using raw by blast
  obtain a N D I K where shape: "q=(a,(N,D),I,K)" by (cases q) auto
  obtain z where premise: "z |\<in>| D" and mapped: "(m,n)=(case z of (s,t) \<Rightarrow> (t,a))"
    using target by (simp only: shape prod.case finite_image_member; blast)
  obtain s t where pair: "z=(s,t)" by (cases z)
  have same: "t=m" "a=n" using mapped by (simp_all add: pair)
  show "\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D"
    by (rule exI[of _ N], rule exI[of _ D], rule exI[of _ I], rule exI[of _ K], rule exI[of _ s])
       (use actual premise in \<open>simp add: shape pair same\<close>)
next
  assume "\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D"
  then obtain N D I K s where row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
    and premise: "(s,m) |\<in>| D" by blast
  show "(m,n) |\<in>| finite_native_proof_edges E"
    unfolding finite_native_proof_edges_def finite_union_image_member
    apply (rule exI[of _ "(n,(N,D),I,K)"], rule conjI[OF row])
    apply (simp only: prod.case finite_image_member)
    apply (rule exI[of _ "(s,m)"])
    using premise by simp
qed

theorem finite_native_proof_edges_correct:
  "fset (finite_native_proof_edges E) = native_proof_edges (decode_finite_environment E)"
proof -
  have member: "(m,n) |\<in>| finite_native_proof_edges E \<longleftrightarrow>
      (m,n) \<in> native_proof_edges (decode_finite_environment E)" for m n
  proof
    assume "(m,n) |\<in>| finite_native_proof_edges E"
    then obtain N D I K s where row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
      and premise: "(s,m) |\<in>| D" by (auto simp: finite_native_proof_edges_step)
    have read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
      using row by (simp add: finite_proof_node_rows_correct)
    show "(m,n) \<in> native_proof_edges (decode_finite_environment E)"
      using read premise by (simp only: native_proof_edges_def mem_Collect_eq prod.case; blast)
  next
    assume "(m,n) \<in> native_proof_edges (decode_finite_environment E)"
    then obtain N D I K s where read: "native_proof_node_at (decode_finite_environment E)
        (fst n) (snd n) N D I K" and premise: "(s,m) \<in> D"
      by (auto simp: native_proof_edges_def)
    obtain M F J A where row: "(n,(M,F),J,A) |\<in>| finite_proof_node_rows E"
      and decoded: "fset F=D" using finite_proof_node_rows_complete[OF read] by blast
    show "(m,n) |\<in>| finite_native_proof_edges E"
      unfolding finite_native_proof_edges_step
      apply (rule exI[of _ M], rule exI[of _ F], rule exI[of _ J], rule exI[of _ A], rule exI[of _ s])
      using row premise decoded by simp
  qed
  show ?thesis using member by (auto split: prod.splits)
qed

definition finite_native_proof_sites ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow> 'u definition_site fset" where
  "finite_native_proof_sites E root = finsert root (fimage fst
    (ffilter (\<lambda>(m,n). n=root) (finite_edge_closure (finite_native_proof_edges E))))"

theorem finite_native_proof_sites_correct:
  "fset (finite_native_proof_sites E root) = native_proof_sites (decode_finite_environment E) root"
proof -
  let ?A = "(native_proof_edges (decode_finite_environment E))\<^sup>+"
  have project: "n \<in> fst ` ({(m,r). r=root} \<inter> ?A) \<longleftrightarrow> (n,root) \<in> ?A" for n
  proof
    assume "n \<in> fst ` ({(m,r). r=root} \<inter> ?A)"
    then show "(n,root) \<in> ?A" by auto
  next
    assume "(n,root) \<in> ?A"
    then have pair: "(n,root) \<in> {(m,r). r=root} \<inter> ?A" by simp
    show "n \<in> fst ` ({(m,r). r=root} \<inter> ?A)" by (rule rev_image_eqI[OF pair]) simp
  qed
  show ?thesis by (auto simp: finite_native_proof_sites_def fimage.rep_eq finite_edge_closure_correct
      finite_native_proof_edges_correct native_proof_sites_def rtrancl_eq_or_trancl project)
qed

section \<open>The recovered graph retains complete metadata at every reached site\<close>

definition finite_recovered_graph ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow> 'u finite_native_derivation_graph" where
  "finite_recovered_graph E root =
    (let R=ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| finite_native_proof_sites E root) (finite_proof_node_rows E)
     in \<lparr>finite_graph_inferences=fimage (\<lambda>(n,(N,D),I,K). (n,N)) R,
         finite_graph_discharges=ffUnion (fimage (\<lambda>(n,(N,D),I,K).
           fimage (\<lambda>(s,m). ((n,s),m)) D) R)\<rparr>)"

lemma finite_recovered_graph_inference_step:
  "(n,N) |\<in>| finite_graph_inferences (finite_recovered_graph E root) \<longleftrightarrow>
    n |\<in>| finite_native_proof_sites E root \<and>
    (\<exists>D I K. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E)"
  by (auto simp: finite_recovered_graph_def Let_def finite_image_member split: prod.splits; force)

lemma finite_recovered_graph_discharge_step:
  "((n,s),m) |\<in>| finite_graph_discharges (finite_recovered_graph E root) \<longleftrightarrow>
    n |\<in>| finite_native_proof_sites E root \<and>
    (\<exists>N D I K. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D)"
proof
  let ?R = "ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| finite_native_proof_sites E root) (finite_proof_node_rows E)"
  assume member: "((n,s),m) |\<in>| finite_graph_discharges (finite_recovered_graph E root)"
  have raw: "\<exists>q. q |\<in>| ?R \<and>
      ((n,s),m) |\<in>| (case q of (a,(N,D),I,K) \<Rightarrow> fimage (\<lambda>(t,p). ((a,t),p)) D)"
    using member by (simp only: finite_recovered_graph_def Let_def finite_derivation_graph.select_convs
        finite_union_image_member case_prod_unfold)
  obtain q where actual: "q |\<in>| ?R"
    and target: "((n,s),m) |\<in>| (case q of (a,(N,D),I,K) \<Rightarrow> fimage (\<lambda>(t,p). ((a,t),p)) D)"
    using raw by blast
  obtain a N D I K where shape: "q=(a,(N,D),I,K)" by (cases q) auto
  obtain z where premise: "z |\<in>| D" and mapped: "((n,s),m)=(case z of (t,p) \<Rightarrow> ((a,t),p))"
    using target by (simp only: shape prod.case finite_image_member; blast)
  obtain t p where pair: "z=(t,p)" by (cases z)
  have same: "a=n" "t=s" "p=m" using mapped by (simp_all add: pair)
  have row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
    and inside: "n |\<in>| finite_native_proof_sites E root"
    using actual by (simp_all add: shape same)
  show "n |\<in>| finite_native_proof_sites E root \<and>
      (\<exists>N D I K. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D)"
    by (rule conjI[OF inside], rule exI[of _ N], rule exI[of _ D], rule exI[of _ I], rule exI[of _ K])
       (use row premise in \<open>simp add: pair same\<close>)
next
  assume "n |\<in>| finite_native_proof_sites E root \<and>
    (\<exists>N D I K. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D)"
  then obtain N D I K where row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
    and inside: "n |\<in>| finite_native_proof_sites E root" and premise: "(s,m) |\<in>| D" by blast
  have actual: "(n,(N,D),I,K) |\<in>| ffilter
      (\<lambda>(n,(N,D),I,K). n |\<in>| finite_native_proof_sites E root) (finite_proof_node_rows E)"
    using row inside by simp
  show "((n,s),m) |\<in>| finite_graph_discharges (finite_recovered_graph E root)"
    unfolding finite_recovered_graph_def Let_def finite_derivation_graph.select_convs finite_union_image_member
    apply (rule exI[of _ "(n,(N,D),I,K)"], rule conjI[OF actual])
    apply (simp only: prod.case finite_image_member)
    apply (rule exI[of _ "(s,m)"])
    using premise by simp
qed

lemma finite_recovered_graph_inference:
  "(n,N) \<in> fset (graph_inferences (decode_finite_graph (finite_recovered_graph E root))) \<longleftrightarrow>
    n \<in> native_proof_sites (decode_finite_environment E) root \<and>
    (\<exists>D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K)"
proof
  assume member: "(n,N) \<in> fset (graph_inferences (decode_finite_graph (finite_recovered_graph E root)))"
  obtain M where row: "(n,M) |\<in>| finite_graph_inferences (finite_recovered_graph E root)"
    and decoded: "N=decode_finite_graph_node M"
    using member by (auto simp: map_relation_values_member)
  obtain D I K where actual: "(n,(M,D),I,K) |\<in>| finite_proof_node_rows E"
    and inside: "n |\<in>| finite_native_proof_sites E root"
    using row by (auto simp: finite_recovered_graph_inference_step)
  have read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      N (fset D) (fset I) (fset K)"
    using actual decoded by (simp add: finite_proof_node_rows_correct)
  show "n \<in> native_proof_sites (decode_finite_environment E) root \<and>
      (\<exists>D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K)"
    using inside read by (auto simp: finite_native_proof_sites_correct)
next
  assume "n \<in> native_proof_sites (decode_finite_environment E) root \<and>
    (\<exists>D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K)"
  then obtain D I K where inside: "n \<in> native_proof_sites (decode_finite_environment E) root"
    and read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K" by blast
  obtain M F J A where actual: "(n,(M,F),J,A) |\<in>| finite_proof_node_rows E"
    and decoded: "decode_finite_graph_node M=N" using finite_proof_node_rows_complete[OF read] by blast
  have row: "(n,M) |\<in>| finite_graph_inferences (finite_recovered_graph E root)"
    using actual inside by (auto simp: finite_recovered_graph_inference_step finite_native_proof_sites_correct)
  show "(n,N) \<in> fset (graph_inferences (decode_finite_graph (finite_recovered_graph E root)))"
    using row decoded by (auto simp: map_relation_values_member)
qed

lemma finite_recovered_graph_discharge:
  "((n,s),m) \<in> fset (graph_discharges (decode_finite_graph (finite_recovered_graph E root))) \<longleftrightarrow>
    n \<in> native_proof_sites (decode_finite_environment E) root \<and>
    (\<exists>N D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K \<and> (s,m) \<in> D)"
proof
  assume member: "((n,s),m) \<in> fset (graph_discharges (decode_finite_graph (finite_recovered_graph E root)))"
  obtain N D I K where row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
    and inside: "n |\<in>| finite_native_proof_sites E root" and premise: "(s,m) |\<in>| D"
    using member by (auto simp: finite_recovered_graph_discharge_step)
  have read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
    using row by (simp add: finite_proof_node_rows_correct)
  show "n \<in> native_proof_sites (decode_finite_environment E) root \<and>
      (\<exists>N D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K \<and> (s,m) \<in> D)"
    using read inside premise by (auto simp: finite_native_proof_sites_correct)
next
  assume "n \<in> native_proof_sites (decode_finite_environment E) root \<and>
    (\<exists>N D I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K \<and> (s,m) \<in> D)"
  then obtain N D I K where inside: "n \<in> native_proof_sites (decode_finite_environment E) root"
    and read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K"
    and premise: "(s,m) \<in> D" by blast
  obtain M F J A where row: "(n,(M,F),J,A) |\<in>| finite_proof_node_rows E"
    and decoded: "fset F=D" using finite_proof_node_rows_complete[OF read] by blast
  show "((n,s),m) \<in> fset (graph_discharges (decode_finite_graph (finite_recovered_graph E root)))"
    using row inside premise decoded
    by (auto simp: finite_recovered_graph_discharge_step finite_native_proof_sites_correct)
qed

lemma finite_recovered_graph_premises:
  assumes inside: "n \<in> native_proof_sites (decode_finite_environment E) root"
    and read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K"
  shows "schema_graph_premises (decode_finite_graph (finite_recovered_graph E root)) n=D"
proof -
  have member: "(s,m) \<in> schema_graph_premises (decode_finite_graph (finite_recovered_graph E root)) n
      \<longleftrightarrow> (s,m) \<in> D" for s m
  proof
    assume "(s,m) \<in> schema_graph_premises (decode_finite_graph (finite_recovered_graph E root)) n"
    then obtain M F J A where other: "native_proof_node_at (decode_finite_environment E)
        (fst n) (snd n) M F J A" and premise: "(s,m) \<in> F"
      by (simp only: schema_graph_premises_def mem_Collect_eq prod.case finite_recovered_graph_discharge; blast)
    have same: "F=D" using native_proof_node_unique[OF other read] by blast
    show "(s,m) \<in> D" using premise same by simp
  next
    assume "(s,m) \<in> D"
    then show "(s,m) \<in> schema_graph_premises (decode_finite_graph (finite_recovered_graph E root)) n"
      using inside read
      by (simp only: schema_graph_premises_def mem_Collect_eq prod.case finite_recovered_graph_discharge; blast)
  qed
  show ?thesis using member by (auto split: prod.splits)
qed

theorem finite_recovered_graph_exact:
  assumes graph: "native_schema_graph_at (decode_finite_environment E) root G"
  shows "decode_finite_graph (finite_recovered_graph E root)=G"
proof -
  let ?H = "decode_finite_graph (finite_recovered_graph E root)"
  have formed: "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  have sites: "schema_graph_nodes G=native_proof_sites (decode_finite_environment E) root"
    by (rule native_schema_graph_exact_sites[OF graph])
  have nodes: "(n,N) \<in> fset (graph_inferences ?H) \<longleftrightarrow> (n,N) \<in> fset (graph_inferences G)" for n N
  proof
    assume "(n,N) \<in> fset (graph_inferences ?H)"
    then obtain D I K where inside: "n \<in> schema_graph_nodes G"
      and read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K"
      by (simp only: finite_recovered_graph_inference sites; blast)
    obtain M J A where row: "(n,M) \<in> fset (graph_inferences G)"
      and other: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        M (schema_graph_premises G n) J A"
      using native_schema_graph_node[OF graph inside] by blast
    have same: "N=M" using native_proof_node_unique[OF read other] by blast
    show "(n,N) \<in> fset (graph_inferences G)" using row same by simp
  next
    assume row: "(n,N) \<in> fset (graph_inferences G)"
    have inside: "n \<in> schema_graph_nodes G" using row by (auto simp: schema_graph_nodes_def rel_dom_def)
    obtain I K where read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        N (schema_graph_premises G n) I K"
      using native_schema_graph_entry[OF graph row] by blast
    show "(n,N) \<in> fset (graph_inferences ?H)"
      using inside read by (simp only: finite_recovered_graph_inference sites; blast)
  qed
  have premise_tables: "schema_graph_premises ?H n=schema_graph_premises G n" if inside: "n \<in> schema_graph_nodes G" for n
  proof -
    obtain N I K where read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
        N (schema_graph_premises G n) I K"
      using native_schema_graph_node[OF graph inside] by blast
    show ?thesis by (rule finite_recovered_graph_premises[OF _ read]) (use inside sites in simp)
  qed
  have discharges: "((n,s),m) \<in> fset (graph_discharges ?H) \<longleftrightarrow>
      ((n,s),m) \<in> fset (graph_discharges G)" for n s m
  proof
    assume row: "((n,s),m) \<in> fset (graph_discharges ?H)"
    have inside: "n \<in> schema_graph_nodes G" using row
      by (simp only: finite_recovered_graph_discharge sites; blast)
    show "((n,s),m) \<in> fset (graph_discharges G)"
      using row premise_tables[OF inside] by (auto simp: schema_graph_premises_def)
  next
    assume row: "((n,s),m) \<in> fset (graph_discharges G)"
    have edge: "(m,n) \<in> schema_graph_edges G"
      using row by (simp only: schema_graph_edges_def mem_Collect_eq prod.case; blast)
    have inside: "n \<in> schema_graph_nodes G" by (rule schema_graph_edge_nodes(2)[OF formed edge])
    show "((n,s),m) \<in> fset (graph_discharges ?H)"
      using row premise_tables[OF inside] by (auto simp: schema_graph_premises_def)
  qed
  have node_field: "graph_inferences ?H=graph_inferences G"
    using nodes by (auto simp: fset_inject[symmetric] split: prod.splits)
  have discharge_field: "graph_discharges ?H=graph_discharges G"
    using discharges by (auto simp: fset_inject[symmetric] split: prod.splits)
  show ?thesis using node_field discharge_field by (cases G; cases ?H) simp
qed

section \<open>Graph formation selects exactly the native realization\<close>

definition finite_native_graph_readings ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow> 'u finite_native_derivation_graph fset" where
  "finite_native_graph_readings E root =
    (let G=finite_recovered_graph E root in if finite_graph_formed G root then {|G|} else {||})"

theorem finite_native_graph_readings_sound:
  assumes member: "G |\<in>| finite_native_graph_readings E root"
  shows "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
proof -
  have represented: "G=finite_recovered_graph E root" and formed: "schema_graph_formed (decode_finite_graph G) root"
    using member by (auto simp: finite_native_graph_readings_def Let_def finite_graph_formed_correct split: if_splits)
  have node: "\<exists>I K. native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      N (schema_graph_premises (decode_finite_graph G) n) I K"
    if row: "(n,N) \<in> fset (graph_inferences (decode_finite_graph G))" for n N
  proof -
    obtain D I K where inside: "n \<in> native_proof_sites (decode_finite_environment E) root"
      and read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n) N D I K"
      using row by (simp only: represented finite_recovered_graph_inference; blast)
    have same: "schema_graph_premises (decode_finite_graph G) n=D"
      using finite_recovered_graph_premises[OF inside read] represented by simp
    show ?thesis using read same by blast
  qed
  show ?thesis using formed node by (simp add: native_schema_graph_at_def)
qed

theorem finite_native_graph_readings_complete:
  assumes graph: "native_schema_graph_at (decode_finite_environment E) root G"
  shows "\<exists>H. H |\<in>| finite_native_graph_readings E root \<and> decode_finite_graph H=G"
proof -
  have represented: "decode_finite_graph (finite_recovered_graph E root)=G"
    by (rule finite_recovered_graph_exact[OF graph])
  have formed: "finite_graph_formed (finite_recovered_graph E root) root"
    using graph by (simp add: finite_graph_formed_correct represented native_schema_graph_at_def)
  show ?thesis by (rule exI[of _ "finite_recovered_graph E root"])
    (use formed represented in \<open>simp add: finite_native_graph_readings_def Let_def\<close>)
qed

theorem finite_native_graph_readings_correct:
  "G |\<in>| finite_native_graph_readings E root \<longleftrightarrow>
    native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
proof
  assume "G |\<in>| finite_native_graph_readings E root"
  then show "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    by (rule finite_native_graph_readings_sound)
next
  assume graph: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
  show "G |\<in>| finite_native_graph_readings E root"
    using finite_native_graph_readings_complete[OF graph] by auto
qed

corollary finite_native_graph_readings_unique:
  assumes "G |\<in>| finite_native_graph_readings E root" "H |\<in>| finite_native_graph_readings E root"
  shows "G=H"
proof -
  have first: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph G)"
    and second: "native_schema_graph_at (decode_finite_environment E) root (decode_finite_graph H)"
    using assms by (simp_all add: finite_native_graph_readings_correct)
  show ?thesis using native_schema_graph_unique[OF first second] by simp
qed

export_code finite_proof_node_rows finite_native_proof_edges finite_native_proof_sites
  finite_native_graph_readings checking SML

text \<open>
  Recovery follows every premise reference back from the chosen root and retains
  each reached site's full metadata and all its discharge occurrences. It then
  applies exactly the existing graph-formation check. Shared inferences remain
  shared, distinct assertion sites remain distinct, and omitted premise nodes or
  cycles cannot yield an accepted graph. The correspondence and coverage results
  include every graph admitted by native realization. Checking the program's
  rules and the root claim is the separate derivation step.
\<close>

end
