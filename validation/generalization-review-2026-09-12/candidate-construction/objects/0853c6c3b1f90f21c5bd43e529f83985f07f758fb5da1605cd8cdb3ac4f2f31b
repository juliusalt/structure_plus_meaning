theory Factor_Proof_Graph_Bounds
  imports Factor_Realization Factor_Finite_Graph_Order
begin

section \<open>Complete native nodes and their actual assertion origins\<close>

definition native_assertion_origins ::
  "'u artifact_environment \<Rightarrow> 'u definition_site set \<Rightarrow>
    ('u definition_site\<times>('u definition_site\<times>'u definition_site)) set" where
  "native_assertion_origins E A = {(n,(p,s)). p\<in>A \<and>
    (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K) \<and>
    (\<exists>N D I K. native_proof_node_at E (fst p) (snd p) N D I K \<and> (s,n)\<in>D)}"

lemma native_proof_edges_at_node:
  assumes raw: "native_proof_node_at E (fst n) (snd n) N D I K"
  shows "(m,n)\<in>native_proof_edges E \<longleftrightarrow> m\<in>rel_ran D"
proof
  assume edge: "(m,n)\<in>native_proof_edges E"
  obtain M F J L s where other: "native_proof_node_at E (fst n) (snd n) M F J L"
    and row: "(s,m)\<in>F" using edge by (auto simp: native_proof_edges_def)
  have same: "F=D" using native_proof_node_unique[OF other raw] by blast
  show "m\<in>rel_ran D" by (rule rel_ranI) (use row same in simp)
next
  assume member: "m\<in>rel_ran D"
  obtain s where row: "(s,m)\<in>D" using member by (auto simp: rel_ran_def)
  show "(m,n)\<in>native_proof_edges E"
    unfolding native_proof_edges_def
    by (simp only: mem_Collect_eq case_prod_conv;
        rule exI[of _ N], rule exI[of _ D], rule exI[of _ I], rule exI[of _ K], rule exI[of _ s])
      (use raw row in blast)
qed

lemma native_assertion_root_sites:
  assumes raw: "native_proof_node_at E (fst root) (snd root) Schema_Assertion {} I K"
  shows "native_proof_sites E root={root}"
proof -
  have no_edge: "(n,root)\<notin>native_proof_edges E" for n
    by (simp only: native_proof_edges_at_node[OF raw]) (simp add: rel_ran_def)
  show ?thesis using no_edge by (auto simp: native_proof_sites_def elim: rtranclE)
qed

lemma native_assertion_origins_at_node:
  assumes raw: "native_proof_node_at E (fst p) (snd p) N D I K"
  shows "(n,(p,s))\<in>native_assertion_origins E A \<longleftrightarrow>
    p\<in>A \<and> (s,n)\<in>D \<and> (\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L)"
proof
  assume member: "(n,(p,s))\<in>native_assertion_origins E A"
  obtain M F U V where parent: "p\<in>A"
    and assertion: "\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L"
    and other: "native_proof_node_at E (fst p) (snd p) M F U V" and row: "(s,n)\<in>F"
    using member by (auto simp: native_assertion_origins_def)
  have same: "F=D" using native_proof_node_unique[OF other raw] by blast
  show "p\<in>A \<and> (s,n)\<in>D \<and> (\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L)"
    using parent row same assertion by simp
next
  assume parts: "p\<in>A \<and> (s,n)\<in>D \<and> (\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L)"
  show "(n,(p,s))\<in>native_assertion_origins E A"
    using parts raw by (auto simp: native_assertion_origins_def)
qed

lemma graph_native_assertion_origins:
  fixes E :: "'u artifact_environment"
  assumes closed: "schema_graph_edges G\<subseteq>schema_graph_nodes G\<times>schema_graph_nodes G"
    and reads: "\<And>n N. (n,N)\<in>fset (graph_inferences G) \<Longrightarrow>
      \<exists>I K. native_proof_node_at E (fst n) (snd n) N (schema_graph_premises G n) I K"
  shows "schema_assertion_uses G=native_assertion_origins E (schema_graph_nodes G)"
proof (rule set_eqI)
  fix row :: "'u definition_site \<times> ('u definition_site \<times> 'u definition_site)"
  obtain n p s where row: "row=(n,(p,s))" by (cases row) auto
  show "row\<in>schema_assertion_uses G \<longleftrightarrow> row\<in>native_assertion_origins E (schema_graph_nodes G)"
  proof
    assume member: "row\<in>schema_assertion_uses G"
    have assertion: "(n,Schema_Assertion)\<in>fset (graph_inferences G)"
      and link: "(s,n)\<in>schema_graph_premises G p"
      using member by (auto simp: row schema_assertion_use_member schema_graph_premises_def)
    have parent: "p\<in>schema_graph_nodes G" using closed schema_graph_edge[OF link] by blast
    obtain N where entry: "(p,N)\<in>fset (graph_inferences G)"
      using parent by (auto simp: schema_graph_nodes_def rel_dom_def)
    obtain I K where raw_assertion:
      "native_proof_node_at E (fst n) (snd n) Schema_Assertion (schema_graph_premises G n) I K"
      using reads[OF assertion] by blast
    have empty: "schema_graph_premises G n={}" using native_proof_node_assertion[OF raw_assertion] by blast
    show "row\<in>native_assertion_origins E (schema_graph_nodes G)"
      using parent link reads[OF entry] raw_assertion empty by (auto simp: row native_assertion_origins_def)
  next
    assume member: "row\<in>native_assertion_origins E (schema_graph_nodes G)"
    obtain N D I K J L where parent: "p\<in>schema_graph_nodes G"
      and raw: "native_proof_node_at E (fst p) (snd p) N D I K" and link: "(s,n)\<in>D"
      and assertion: "native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L"
      using member by (auto simp: row native_assertion_origins_def)
    obtain M where entry: "(p,M)\<in>fset (graph_inferences G)"
      using parent by (auto simp: schema_graph_nodes_def rel_dom_def)
    obtain U V where actual: "native_proof_node_at E (fst p) (snd p) M (schema_graph_premises G p) U V"
      using reads[OF entry] by blast
    have same: "D=schema_graph_premises G p" using native_proof_node_unique[OF raw actual] by blast
    have premise: "(s,n)\<in>schema_graph_premises G p" using link same by simp
    have child: "n\<in>schema_graph_nodes G" using closed schema_graph_edge[OF premise] by blast
    obtain A where child_entry: "(n,A)\<in>fset (graph_inferences G)"
      using child by (auto simp: schema_graph_nodes_def rel_dom_def)
    obtain X Y where child_raw: "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) X Y"
      using reads[OF child_entry] by blast
    have kind: "A=Schema_Assertion" using native_proof_node_unique[OF child_raw assertion] by blast
    show "row\<in>schema_assertion_uses G"
      using child_entry kind premise by (auto simp: row schema_assertion_use_member schema_graph_premises_def)
  qed
qed

corollary native_schema_graph_assertion_origins:
  assumes graph: "native_schema_graph_at E root G"
  shows "schema_assertion_uses G=native_assertion_origins E (schema_graph_nodes G)"
  by (rule graph_native_assertion_origins)
    (use graph in \<open>auto simp: native_schema_graph_at_def schema_graph_formed_def\<close>)

fun native_node_bound :: "'u artifact_environment \<Rightarrow> 'u definition_site list \<Rightarrow> bool" where
  "native_node_bound E [] \<longleftrightarrow> True"
| "native_node_bound E (n#ns) \<longleftrightarrow> n\<notin>set ns \<and> native_node_bound E ns \<and>
    (\<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K \<and> rel_ran D\<subseteq>set ns)"

lemma native_node_bound_reads:
  assumes bound: "native_node_bound E ns" and member: "n\<in>set ns"
  shows "\<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K"
  using bound member by (induction ns) auto

lemma native_node_bound_order:
  assumes bound: "native_node_bound E ns"
  shows "children_follow (native_proof_edges E) ns"
  using bound
proof (induction ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  obtain N D I K where raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    and children: "rel_ran D\<subseteq>set ns" using Cons.prems by auto
  show ?case using Cons children by (auto simp: native_proof_edges_at_node[OF raw])
qed

lemma native_node_bound_from_order:
  assumes order: "children_follow (native_proof_edges E) ns"
    and reads: "\<And>n. n\<in>set ns \<Longrightarrow> \<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K"
  shows "native_node_bound E ns"
  using order reads
proof (induction ns)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  obtain N D I K where raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    using Cons.prems(2)[of n] by auto
  have children: "rel_ran D\<subseteq>set ns"
    using Cons.prems(1) by (auto simp: native_proof_edges_at_node[OF raw, symmetric])
  have tail: "native_node_bound E ns" by (rule Cons.IH) (use Cons.prems in auto)
  show ?case using Cons.prems(1) tail raw children by auto
qed

section \<open>The actual predecessor closure has a complete finite projection\<close>

lemma native_graph_from_closed_nodes:
  fixes E :: "'u artifact_environment"
  assumes finite: "finite A" and root: "root\<in>A"
    and reads: "\<And>n. n\<in>A \<Longrightarrow> \<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K"
    and closed: "\<And>n m. n\<in>A \<Longrightarrow> (m,n)\<in>native_proof_edges E \<Longrightarrow> m\<in>A"
    and paths: "\<And>n. n\<in>A \<Longrightarrow> (n,root)\<in>(native_proof_edges E \<inter> (A\<times>A))\<^sup>*"
    and descent: "wf (native_proof_edges E \<inter> (A\<times>A))"
    and origins: "single_valued (native_assertion_origins E A)"
  shows "\<exists>G. native_schema_graph_at E root G \<and> schema_graph_nodes G=A"
proof -
  have witnesses: "\<forall>n\<in>A. \<exists>q. \<exists>I K. native_proof_node_at E (fst n) (snd n) (fst q) (snd q) I K"
    using reads by (metis fst_conv snd_conv)
  obtain f where chosen: "\<forall>n\<in>A. \<exists>I K. native_proof_node_at E (fst n) (snd n) (fst (f n)) (snd (f n)) I K"
    using bchoice[OF witnesses] by blast
  have local_read: "\<exists>I K. native_proof_node_at E (fst n) (snd n) (fst (f n)) (snd (f n)) I K"
    if "n\<in>A" for n using chosen that by blast
  let ?N="image (\<lambda>n. (n,fst (f n))) A"
  let ?D="\<Union>n\<in>A. image (\<lambda>(s,m). ((n,s),m)) (snd (f n))"
  let ?G="\<lparr>graph_inferences=Abs_fset ?N, graph_discharges=Abs_fset ?D\<rparr>"
  have local_finite: "finite (snd (f n))" if member: "n\<in>A" for n
  proof -
    obtain I K where raw: "native_proof_node_at E (fst n) (snd n) (fst (f n)) (snd (f n)) I K"
      using local_read[OF member] by blast
    show ?thesis by (rule native_proof_node_properties(3)[OF raw])
  qed
  have nf: "finite ?N" using finite by simp
  have df: "finite ?D" by (rule finite_UN_I[OF finite]) (use local_finite in auto)
  have inferences: "fset (graph_inferences ?G)=?N" and discharges: "fset (graph_discharges ?G)=?D"
    by (simp_all add: Abs_fset_inverse nf df)
  have nodes: "schema_graph_nodes ?G=A"
    by (simp only: schema_graph_nodes_def inferences; auto simp: rel_dom_def)
  have premise_rows: "schema_graph_premises ?G n=snd (f n)" if "n\<in>A" for n
    using that by (simp only: schema_graph_premises_def discharges; auto)
  have actual: "\<exists>I K. native_proof_node_at E (fst n) (snd n) N (schema_graph_premises ?G n) I K"
    if "(n,N)\<in>fset (graph_inferences ?G)" for n N
    using that local_read by (simp only: inferences; auto simp: premise_rows)
  have edge_at: "(m,n)\<in>native_proof_edges E \<longleftrightarrow> m\<in>rel_ran (snd (f n))"
    if member: "n\<in>A" for m n
  proof -
    obtain I K where raw: "native_proof_node_at E (fst n) (snd n) (fst (f n)) (snd (f n)) I K"
      using local_read[OF member] by blast
    show ?thesis by (rule native_proof_edges_at_node[OF raw])
  qed
  have discharge_parent: "n\<in>A" if "((n,s),m)\<in>fset (graph_discharges ?G)" for n s m
    using that by (simp only: discharges; auto)
  have edges: "schema_graph_edges ?G=native_proof_edges E \<inter> (A\<times>A)"
  proof (rule set_eqI)
    fix z :: "'u definition_site\<times>'u definition_site"
    obtain m n where shape: "z=(m,n)" by (cases z)
    show "z\<in>schema_graph_edges ?G \<longleftrightarrow> z\<in>native_proof_edges E \<inter> (A\<times>A)"
    proof
      assume member: "z\<in>schema_graph_edges ?G"
      obtain s where discharge: "((n,s),m)\<in>fset (graph_discharges ?G)"
        using member by (simp only: shape schema_graph_edges_def mem_Collect_eq case_prod_conv; blast)
      have parent: "n\<in>A" by (rule discharge_parent[OF discharge])
      have projected: "(s,m)\<in>schema_graph_premises ?G n"
        using discharge by (simp only: schema_graph_premises_def mem_Collect_eq case_prod_conv)
      have premise: "(s,m)\<in>snd (f n)"
        using projected by (simp only: premise_rows[OF parent])
      have child: "m\<in>rel_ran (snd (f n))" by (rule rel_ranI[OF premise])
      have actual_edge: "(m,n)\<in>native_proof_edges E" using edge_at[OF parent] child by blast
      have target: "m\<in>A" by (rule closed[OF parent actual_edge])
      show "z\<in>native_proof_edges E \<inter> (A\<times>A)" using actual_edge parent target by (simp add: shape)
    next
      assume member: "z\<in>native_proof_edges E \<inter> (A\<times>A)"
      have parent: "n\<in>A" and actual_edge: "(m,n)\<in>native_proof_edges E"
        using member by (simp_all add: shape)
      have child: "m\<in>rel_ran (snd (f n))" using edge_at[OF parent] actual_edge by blast
      obtain s where premise: "(s,m)\<in>snd (f n)"
        using child by (simp only: rel_ran_def mem_Collect_eq; blast)
      have projected: "(s,m)\<in>schema_graph_premises ?G n"
        using premise by (simp only: premise_rows[OF parent])
      have graph_edge: "(m,n)\<in>schema_graph_edges ?G" by (rule schema_graph_edge[OF projected])
      show "z\<in>schema_graph_edges ?G" using graph_edge by (simp only: shape)
    qed
  qed
  have bounded: "schema_graph_edges ?G\<subseteq>schema_graph_nodes ?G\<times>schema_graph_nodes ?G"
    by (simp add: edges nodes)
  have node_sv: "single_valued (fset (graph_inferences ?G))"
    by (simp only: inferences; auto simp: single_valued_def)
  have local_sv: "single_valued (snd (f n))" if member: "n\<in>A" for n
  proof -
    obtain I K where raw: "native_proof_node_at E (fst n) (snd n) (fst (f n)) (snd (f n)) I K"
      using local_read[OF member] by blast
    show ?thesis by (rule native_proof_node_properties(4)[OF raw])
  qed
  have discharge_sv: "single_valued (fset (graph_discharges ?G))"
    using local_sv by (simp only: discharges; auto simp: single_valued_def)
  have uses: "schema_assertion_uses ?G=native_assertion_origins E A"
    using graph_native_assertion_origins[OF bounded actual] by (simp only: nodes)
  have formed: "schema_graph_formed ?G root"
    using node_sv discharge_sv origins root bounded paths descent
    by (auto simp: schema_graph_formed_def nodes edges uses)
  have graph: "native_schema_graph_at E root ?G"
    using formed actual by (auto simp: native_schema_graph_at_def)
  show ?thesis by (rule exI[of _ ?G]) (use graph nodes in simp)
qed

theorem native_graph_finite_bound:
  "(\<exists>G. native_schema_graph_at E root G) \<longleftrightarrow>
    (\<exists>ns. native_node_bound E ns \<and> root\<in>set ns \<and> single_valued (native_assertion_origins E (set ns)))"
proof
  assume "\<exists>G. native_schema_graph_at E root G"
  then obtain G where graph: "native_schema_graph_at E root G" by blast
  let ?A="schema_graph_nodes G"
  have formed: "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  have root: "root\<in>?A" and descent: "wf (schema_graph_edges G)"
    and bounded: "schema_graph_edges G\<subseteq>?A\<times>?A"
    using formed by (auto simp: schema_graph_formed_def)
  have closed: "m\<in>?A" if "n\<in>?A" "(m,n)\<in>native_proof_edges E" for m n
    using native_schema_graph_edge_at[OF graph that(1)] that(2) bounded by blast
  have edges: "native_proof_edges E \<inter> (?A\<times>?A)=schema_graph_edges G"
    using native_schema_graph_edge_at[OF graph] bounded by auto
  have restricted_wf: "wf (native_proof_edges E \<inter> (?A\<times>?A))"
    by (subst edges) (rule descent)
  have finite_order: "\<exists>ns. set ns=?A \<and> children_follow (native_proof_edges E) ns"
    by (rule finite_closed_graph_order[OF schema_graph_nodes_finite closed restricted_wf])
  obtain ns where order: "set ns=?A" "children_follow (native_proof_edges E) ns" using finite_order by blast
  have bound: "native_node_bound E ns"
    by (rule native_node_bound_from_order[OF order(2)])
      (use native_schema_graph_node[OF graph] order(1) in blast)
  have origins: "single_valued (native_assertion_origins E (set ns))"
    using formed native_schema_graph_assertion_origins[OF graph] order(1)
    by (auto simp: schema_graph_formed_def)
  show "\<exists>ns. native_node_bound E ns \<and> root\<in>set ns \<and> single_valued (native_assertion_origins E (set ns))"
    using bound root order(1) origins by blast
next
  assume "\<exists>ns. native_node_bound E ns \<and> root\<in>set ns \<and> single_valued (native_assertion_origins E (set ns))"
  then obtain ns where bound: "native_node_bound E ns" and root: "root\<in>set ns"
    and origins: "single_valued (native_assertion_origins E (set ns))" by blast
  let ?A="native_proof_sites E root"
  have order: "children_follow (native_proof_edges E) ns" by (rule native_node_bound_order[OF bound])
  have closed_bound: "m\<in>set ns" if "n\<in>set ns" "(m,n)\<in>native_proof_edges E" for m n
    by (rule children_follow_closed[OF order that])
  have subset: "?A\<subseteq>set ns"
    using root_predecessors_least[OF root closed_bound] by (simp only: native_proof_sites_def)
  have finite: "finite ?A" by (rule finite_subset[OF subset]) simp
  have reads: "\<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K" if "n\<in>?A" for n
    by (rule native_node_bound_reads[OF bound]) (use subset that in blast)
  have closed: "m\<in>?A" if "n\<in>?A" "(m,n)\<in>native_proof_edges E" for m n
    using root_predecessors_closed[of n root "native_proof_edges E" m] that
    by (simp add: native_proof_sites_def)
  have paths: "(n,root)\<in>(native_proof_edges E \<inter> (?A\<times>?A))\<^sup>*" if "n\<in>?A" for n
    using root_predecessors_path[of n root "native_proof_edges E"] that
    by (simp add: native_proof_sites_def)
  have descent: "wf (native_proof_edges E \<inter> (?A\<times>?A))"
    by (rule wf_subset[OF children_follow_wellfounded[OF order]]) (use subset in auto)
  have uses_subset: "native_assertion_origins E ?A\<subseteq>native_assertion_origins E (set ns)"
    using subset by (auto simp: native_assertion_origins_def)
  have unique: "single_valued (native_assertion_origins E ?A)"
    using origins uses_subset unfolding single_valued_def by blast
  have member: "root\<in>?A" by (simp add: native_proof_sites_def)
  have constructed: "\<exists>G. native_schema_graph_at E root G \<and> schema_graph_nodes G=?A"
  proof (rule native_graph_from_closed_nodes[where E=E and A="?A" and root=root, OF finite member])
    fix n assume inside: "n\<in>?A"
    show "\<exists>N D I K. native_proof_node_at E (fst n) (snd n) N D I K" by (rule reads[OF inside])
  next
    fix n m assume inside: "n\<in>?A" and edge: "(m,n)\<in>native_proof_edges E"
    show "m\<in>?A" by (rule closed[OF inside edge])
  next
    fix n assume inside: "n\<in>?A"
    show "(n,root)\<in>(native_proof_edges E \<inter> (?A\<times>?A))\<^sup>*" by (rule paths[OF inside])
  next
    show "wf (native_proof_edges E \<inter> (?A\<times>?A))" by (rule descent)
    show "single_valued (native_assertion_origins E ?A)" by (rule unique)
  qed
  show "\<exists>G. native_schema_graph_at E root G" using constructed by blast
qed

text \<open>
  A checked bound reads every listed native node and places every premise
  target in the strict remaining tail. It need not identify the graph's node
  set. The semantic graph is obtained from the actual root closure, with every
  complete node and premise relation retained. Shared inference nodes remain
  shared, while assertion origins must be functional. A root assertion may
  have no origin; every other assertion in a formed rooted graph has one.
  No global separation condition is imposed on different nodes' syntax.
\<close>

end
