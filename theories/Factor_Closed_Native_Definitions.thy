theory Factor_Closed_Native_Definitions
  imports Factor_Packages
begin

section \<open>An actual reading determines every outgoing definition edge\<close>

lemma native_definition_edges_at:
  assumes read: "native_definition_at E u r p C"
  shows "((u,r),e)\<in>native_definition_edges E \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>C \<and> e\<in>schema_dependencies S)"
proof
  assume edge: "((u,r),e)\<in>native_definition_edges E"
  obtain q D c S where actual: "native_definition_at E u r q D"
    "(c,S)\<in>D" "e\<in>schema_dependencies S"
    using edge by (auto simp: native_definition_edges_def)
  have same: "q=p \<and> D=C" by (rule native_definition_unique[OF actual(1) read])
  show "\<exists>c S. (c,S)\<in>C \<and> e\<in>schema_dependencies S"
    using actual same by blast
next
  assume "\<exists>c S. (c,S)\<in>C \<and> e\<in>schema_dependencies S"
  then show "((u,r),e)\<in>native_definition_edges E"
    using read by (auto simp: native_definition_edges_def)
qed

section \<open>A complete closed reading graph is the exact selected graph\<close>

theorem native_closed_definition_graph:
  assumes formed: "environment_formed E"
    and reads: "\<And>d p C. (d,p,C)\<in>G \<Longrightarrow> native_definition_at E (fst d) (snd d) p C"
    and closed: "\<And>d p C c S. (d,p,C)\<in>G \<Longrightarrow> (c,S)\<in>C \<Longrightarrow>
      schema_dependencies S\<subseteq>rel_dom G"
  shows "native_definition_sites E (rel_dom G)=rel_dom G"
    and "native_package_formed E (rel_dom G)"
    and "native_definition_graph E (rel_dom G)=G"
proof -
  have outgoing: "e\<in>rel_dom G"
    if at: "d\<in>rel_dom G" and edge: "(d,e)\<in>native_definition_edges E" for d e
  proof -
    obtain p C where row: "(d,p,C)\<in>G" using at by (auto simp: rel_dom_def)
    have read: "native_definition_at E (fst d) (snd d) p C" by (rule reads[OF row])
    obtain c S where callee: "(c,S)\<in>C" "e\<in>schema_dependencies S"
      using native_definition_edges_at[OF read, of e] edge by auto
    show ?thesis by (rule subsetD[OF closed[OF row callee(1)] callee(2)])
  qed
  have upper: "native_definition_sites E (rel_dom G)\<subseteq>rel_dom G"
    by (rule native_definition_sites_least[OF subset_refl outgoing])
  have sites: "native_definition_sites E (rel_dom G)=rel_dom G"
    using upper native_definition_roots[of "rel_dom G" E] by blast
  show "native_definition_sites E (rel_dom G)=rel_dom G" by (rule sites)
  have defined: "\<forall>d\<in>rel_dom G. \<exists>p C. native_definition_at E (fst d) (snd d) p C"
  proof (intro ballI)
    fix d assume "d\<in>rel_dom G"
    then obtain p C where row: "(d,p,C)\<in>G" by (auto simp: rel_dom_def)
    show "\<exists>p C. native_definition_at E (fst d) (snd d) p C"
      by (rule exI[of _ p], rule exI[of _ C], rule reads[OF row])
  qed
  show "native_package_formed E (rel_dom G)"
    using formed defined by (simp only: native_package_formed_def sites)
  have exact: "native_definition_at E (fst d) (snd d) p C \<longleftrightarrow> (d,p,C)\<in>G"
    if at: "d\<in>rel_dom G" for d p C
  proof -
    obtain q D where row: "(d,q,D)\<in>G" using at by (auto simp: rel_dom_def)
    have read: "native_definition_at E (fst d) (snd d) q D" by (rule reads[OF row])
    show ?thesis
    proof
      assume actual: "native_definition_at E (fst d) (snd d) p C"
      have "p=q \<and> C=D" by (rule native_definition_unique[OF actual read])
      then show "(d,p,C)\<in>G" using row by simp
    next
      assume "(d,p,C)\<in>G"
      then show "native_definition_at E (fst d) (snd d) p C" by (rule reads)
    qed
  qed
  show "native_definition_graph E (rel_dom G)=G"
  proof (rule subset_antisym)
    show "native_definition_graph E (rel_dom G)\<subseteq>G"
    proof (rule subsetI)
      fix x assume member: "x\<in>native_definition_graph E (rel_dom G)"
      obtain d p C where x: "x=(d,p,C)" by (cases x) auto
      have at: "d\<in>rel_dom G"
        and read: "native_definition_at E (fst d) (snd d) p C"
        using member by (auto simp: native_definition_graph_def sites x)
      show "x\<in>G" using exact[OF at] read by (simp add: x)
    qed
    show "G\<subseteq>native_definition_graph E (rel_dom G)"
    proof (rule subsetI)
      fix x assume member: "x\<in>G"
      obtain d p C where x: "x=(d,p,C)" by (cases x) auto
      have row: "(d,p,C)\<in>G" using member by (simp add: x)
      have at: "d\<in>rel_dom G" using row by (auto simp: rel_dom_def)
      have read: "native_definition_at E (fst d) (snd d) p C" by (rule reads[OF row])
      show "x\<in>native_definition_graph E (rel_dom G)"
        using at read by (simp add: native_definition_graph_def sites x)
    qed
  qed
qed

lemma native_complete_definition_family:
  assumes ef: "environment_formed E"
    and definitions: "\<forall>d\<in>D. native_definition_at E (fst d) (snd d) (p d) (Cs d)"
    and closed: "\<forall>d\<in>D. (\<Union>S\<in>rel_ran (Cs d). schema_dependencies S)\<subseteq>D"
  shows "native_definition_sites E D=D" "native_package_formed E D"
proof -
  let ?G="{(d,p d,Cs d) |d. d\<in>D}"
  have domain: "rel_dom ?G=D" by (auto simp: rel_dom_def)
  have reads: "native_definition_at E (fst d) (snd d) q C" if "(d,q,C)\<in>?G" for d q C
    using definitions that by auto
  have dependencies: "schema_dependencies S\<subseteq>rel_dom ?G"
    if row: "(d,q,C)\<in>?G" and clause: "(c,S)\<in>C" for d q C c S
  proof -
    have member: "d\<in>D" and family: "C=Cs d" using row by auto
    have schema: "S\<in>rel_ran (Cs d)" using clause family by (auto simp: rel_ran_def)
    show ?thesis using closed member schema by (simp only: domain; blast)
  qed
  show "native_definition_sites E D=D" "native_package_formed E D"
    using native_closed_definition_graph(1,2)[OF ef reads dependencies] by (simp_all only: domain)
qed

text \<open>
  The supplied graph contains actual complete definition readings. Closure
  concerns their prospective definition calls and permits mutually referring
  definitions. It does not erase other artifacts, bindings or literal
  references in the environment, and it makes no claim about proof validity.
\<close>

end
