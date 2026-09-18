theory Factor_Demanded_Graph_Readings
  imports Finite_Demanded_Closures Factor_Recovered_Graph_Sharing
begin

section \<open>A recovered proof graph reads a node only where its root demands one\<close>

text \<open>
  A recovered proof graph is the proof nodes its root reaches through the premises they
  discharge. Its sites and rows were computed from the rows of the whole environment: a proof
  node was read at every position of every artifact, including every address of every literal
  target, so replaying a judgment whose argument is a whole artifact cost the square of that
  artifact. This is the second instance of the demanded reading of Finite_Demanded_Closures,
  after the definitions of a package: a node is read only at a site the root reaches, its
  successors being the children its premises cite. The premise of the traversal is again the
  reading's own boundary: a proof node is read from a record of the artifact at its use, so its
  site is a position of the environment. The recovered graph keeps its original value.
\<close>

definition finite_proof_site_reading ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_site_reading E n=finite_proof_node_readings E (fst n) (snd n)"

definition finite_proof_children ::
  "'u finite_native_node_metadata finite_syntax_reading \<Rightarrow> 'u definition_site fset" where
  "finite_proof_children q=(case q of ((N,D),I,K) \<Rightarrow> fimage snd D)"

lemma finite_proof_children_member:
  "m |\<in>| finite_proof_children ((N,D),I,K) \<longleftrightarrow> (\<exists>s. (s,m) |\<in>| D)"
proof
  assume "m |\<in>| finite_proof_children ((N,D),I,K)"
  then obtain z where member: "z |\<in>| D" and second: "m=snd z"
    by (simp only: finite_proof_children_def prod.case finite_image_member; blast)
  have "(fst z,m) |\<in>| D" using member second by simp
  then show "\<exists>s. (s,m) |\<in>| D" by blast
next
  assume "\<exists>s. (s,m) |\<in>| D"
  then obtain s where member: "(s,m) |\<in>| D" by blast
  have "\<exists>z. z |\<in>| D \<and> m=snd z" using member by (intro exI[of _ "(s,m)"]) simp
  then show "m |\<in>| finite_proof_children ((N,D),I,K)"
    by (simp only: finite_proof_children_def prod.case finite_image_member)
qed

lemma finite_proof_reading_position:
  assumes reading: "x |\<in>| finite_proof_site_reading E n"
  shows "n |\<in>| finite_environment_positions E"
proof -
  obtain M I K where shape: "x=(M,I,K)" by (cases x rule: prod_cases3)
  obtain N D where node: "M=(N,D)" by (cases M)
  have read: "native_proof_node_at (decode_finite_environment E) (fst n) (snd n)
      (decode_finite_graph_node N) (fset D) (fset I) (fset K)"
    using reading shape node by (simp add: finite_proof_site_reading_def finite_proof_node_readings_correct)
  have position: "(fst n,snd n) \<in> environment_positions (decode_finite_environment E)"
    by (rule native_proof_node_properties(2)[OF read])
  show ?thesis using position by (simp add: finite_environment_positions_correct)
qed

lemma finite_proof_reading_universe:
  "finite_proof_site_reading E n \<noteq> {||} \<Longrightarrow> n |\<in>| finite_environment_positions E"
  using finite_proof_reading_position by (metis all_not_fin_conv)

lemma finite_proof_node_rows_site_rows:
  "finite_proof_node_rows E=finite_site_rows (finite_proof_site_reading E) (finite_environment_positions E)"
  by (simp only: finite_proof_node_rows_def finite_site_rows_def finite_proof_site_reading_def)

lemma finite_native_proof_edges_converse:
  fixes E :: "'u finite_artifact_environment"
  shows "fset (finite_native_proof_edges E)=
    (fset (finite_row_edges (finite_proof_site_reading E) finite_proof_children (finite_environment_positions E)))\<inverse>"
proof (rule set_eqI)
  fix z :: "'u definition_site \<times> 'u definition_site"
  obtain m n where shape: "z=(m,n)" by (cases z) auto
  have left: "(m,n) |\<in>| finite_native_proof_edges E \<longleftrightarrow>
      (\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D)"
    by (rule finite_native_proof_edges_step)
  have right: "(n,m) |\<in>| finite_row_edges (finite_proof_site_reading E) finite_proof_children
        (finite_environment_positions E) \<longleftrightarrow>
      (\<exists>x. n |\<in>| finite_environment_positions E \<and> x |\<in>| finite_proof_site_reading E n \<and>
        m |\<in>| finite_proof_children x)"
    by (rule finite_row_edges_member)
  have rows: "(n,x) |\<in>| finite_proof_node_rows E \<longleftrightarrow>
      n |\<in>| finite_environment_positions E \<and> x |\<in>| finite_proof_site_reading E n" for x
    by (simp only: finite_proof_node_rows_site_rows finite_site_rows_member)
  have "(\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D) \<longleftrightarrow>
      (\<exists>x. n |\<in>| finite_environment_positions E \<and> x |\<in>| finite_proof_site_reading E n \<and>
        m |\<in>| finite_proof_children x)"
  proof
    assume "\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D"
    then obtain N D I K s where row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
      and premise: "(s,m) |\<in>| D" by blast
    have child: "m |\<in>| finite_proof_children ((N,D),I,K)"
      using premise by (simp only: finite_proof_children_member; blast)
    show "\<exists>x. n |\<in>| finite_environment_positions E \<and> x |\<in>| finite_proof_site_reading E n \<and>
        m |\<in>| finite_proof_children x"
      using row child by (simp only: rows; blast)
  next
    assume "\<exists>x. n |\<in>| finite_environment_positions E \<and> x |\<in>| finite_proof_site_reading E n \<and>
        m |\<in>| finite_proof_children x"
    then obtain x where position: "n |\<in>| finite_environment_positions E"
      and reading: "x |\<in>| finite_proof_site_reading E n" and child: "m |\<in>| finite_proof_children x"
      by blast
    obtain M I K where shape: "x=(M,I,K)" by (cases x rule: prod_cases3)
    obtain N D where node: "M=(N,D)" by (cases M)
    have row: "(n,(N,D),I,K) |\<in>| finite_proof_node_rows E"
      using position reading shape node by (simp only: rows; blast)
    obtain s where premise: "(s,m) |\<in>| D"
      using child shape node by (simp only: finite_proof_children_member; blast)
    show "\<exists>N D I K s. (n,(N,D),I,K) |\<in>| finite_proof_node_rows E \<and> (s,m) |\<in>| D"
      using row premise by blast
  qed
  then show "z\<in>fset (finite_native_proof_edges E) \<longleftrightarrow>
      z\<in>(fset (finite_row_edges (finite_proof_site_reading E) finite_proof_children (finite_environment_positions E)))\<inverse>"
    by (simp only: shape converse_iff left[symmetric] right[symmetric])
qed

lemma finite_native_proof_sites_rooted:
  fixes E :: "'u finite_artifact_environment"
  shows "finite_native_proof_sites E root=
    finite_rooted_sites (finite_proof_site_reading E) finite_proof_children (finite_environment_positions E) {|root|}"
proof (rule fset_eqI)
  fix m :: "'u definition_site"
  let ?R="fset (finite_row_edges (finite_proof_site_reading E) finite_proof_children (finite_environment_positions E))"
  have proof_site: "m |\<in>| finite_native_proof_sites E root \<longleftrightarrow> (m,root)\<in>(fset (finite_native_proof_edges E))\<^sup>*"
    by (simp only: finite_native_proof_sites_correct native_proof_sites_def mem_Collect_eq
        finite_native_proof_edges_correct)
  have rooted: "m |\<in>| finite_rooted_sites (finite_proof_site_reading E) finite_proof_children
      (finite_environment_positions E) {|root|} \<longleftrightarrow> (root,m)\<in>?R\<^sup>*"
    by (simp only: finite_rooted_sites_member; simp)
  have turned: "(m,root)\<in>(?R\<inverse>)\<^sup>* \<longleftrightarrow> (root,m)\<in>?R\<^sup>*"
    by (simp only: rtrancl_converse converse_iff)
  show "m |\<in>| finite_native_proof_sites E root \<longleftrightarrow>
      m |\<in>| finite_rooted_sites (finite_proof_site_reading E) finite_proof_children
        (finite_environment_positions E) {|root|}"
    by (simp only: proof_site rooted finite_native_proof_edges_converse turned)
qed

lemma finite_proof_rows_at_sites:
  fixes E :: "'u finite_artifact_environment"
  shows "ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| sites) (finite_proof_node_rows E)=
    finite_site_rows (finite_proof_site_reading E) sites"
proof (rule fset_eqI)
  fix z :: "'u definition_site \<times> 'u finite_native_node_metadata finite_syntax_reading"
  obtain n x where shape: "z=(n,x)" by (cases z) auto
  obtain M I K where parts: "x=(M,I,K)" by (cases x rule: prod_cases3)
  obtain N D where node: "M=(N,D)" by (cases M)
  have position: "n |\<in>| finite_environment_positions E"
    if "x |\<in>| finite_proof_site_reading E n"
    by (rule finite_proof_reading_position[OF that])
  show "z |\<in>| ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| sites) (finite_proof_node_rows E) \<longleftrightarrow>
      z |\<in>| finite_site_rows (finite_proof_site_reading E) sites"
    using position
    by (auto simp: shape parts node finite_proof_node_rows_site_rows finite_site_rows_member)
qed

section \<open>The demanded traversal returns the recovered graph unchanged\<close>

lemma finite_demanded_proof_readings:
  "finite_demanded_readings (finite_proof_site_reading E) finite_proof_children {|root|}=
    Some (finite_native_proof_sites E root,
      ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| finite_native_proof_sites E root) (finite_proof_node_rows E))"
proof -
  let ?read="finite_proof_site_reading E"
  let ?U="finite_environment_positions E"
  have run: "finite_demanded_readings ?read finite_proof_children {|root|}=
      Some (finite_rooted_sites ?read finite_proof_children ?U {|root|},
        finite_site_rows ?read (finite_rooted_sites ?read finite_proof_children ?U {|root|}))"
    by (rule finite_demanded_readings_exact[OF finite_proof_reading_universe])
  show ?thesis using run by (simp only: finite_native_proof_sites_rooted finite_proof_rows_at_sites)
qed

text \<open>
  A formed environment has formed artifacts, so the traversal reads the formation-free node
  bodies of Factor_Recovered_Graph_Sharing and checks the environment once, as the universe
  formulation did for its whole row table. An unformed environment reads no node, so its
  recovered graph is empty.
\<close>

definition finite_proof_site_reading_formed ::
  "'u finite_artifact_environment \<Rightarrow> 'u definition_site \<Rightarrow>
    'u finite_native_node_metadata finite_syntax_reading fset" where
  "finite_proof_site_reading_formed E n=finite_proof_node_readings_formed E (fst n) (snd n)"

lemma finite_proof_site_reading_formed_exact:
  assumes formed: "finite_environment_formed E"
  shows "finite_proof_site_reading_formed E=finite_proof_site_reading E"
  by (rule ext)
    (simp add: finite_proof_site_reading_formed_def finite_proof_site_reading_def
      finite_proof_node_readings_formed_guard formed)

lemma finite_proof_node_rows_unformed:
  assumes unformed: "\<not> finite_environment_formed E"
  shows "finite_proof_node_rows E={||}"
  using unformed by (simp add: finite_proof_node_rows_formed_once_code)

declare Factor_Recovered_Graph_Sharing.finite_recovered_graph_shared_code[code del]

lemma finite_recovered_graph_demanded_code [code]:
  "finite_recovered_graph E root=(let R=(if finite_environment_formed E
       then snd (the (finite_demanded_readings (finite_proof_site_reading_formed E) finite_proof_children {|root|}))
       else {||}) in
     \<lparr>finite_graph_inferences=fimage (\<lambda>(n,(N,D),I,K). (n,N)) R,
      finite_graph_discharges=ffUnion (fimage (\<lambda>(n,(N,D),I,K). fimage (\<lambda>(s,m). ((n,s),m)) D) R)\<rparr>)"
proof (cases "finite_environment_formed E")
  case True
  show ?thesis
    by (simp add: True finite_proof_site_reading_formed_exact[OF True] finite_demanded_proof_readings
        finite_recovered_graph_def)
next
  case False
  have empty: "ffilter (\<lambda>(n,(N,D),I,K). n |\<in>| finite_native_proof_sites E root) (finite_proof_node_rows E)={||}"
    by (auto simp: finite_proof_node_rows_unformed[OF False] fset_eq_iff ffilter.rep_eq bot_fset.rep_eq)
  show ?thesis by (simp only: finite_recovered_graph_def Let_def empty False if_False)
qed

text \<open>
  The equation returns the original graph: the nodes a root reaches through the premises they
  discharge and the rows at exactly those sites. A position that carries no proof node is no
  longer read, so replaying a judgment costs the proof it reads and not the literal material
  beside it; graph formation, the replay environment and every judgment built on them keep
  their values.
\<close>

end
