theory Factor_Selected_Definition_Graphs
  imports Factor_Closed_Native_Definitions
begin

section \<open>The actual roots reach the complete independently read graph\<close>

theorem native_selected_definition_graph:
  assumes formed: "environment_formed E"
    and reads: "\<And>d p C. (d,p,C)\<in>G \<Longrightarrow> native_definition_at E (fst d) (snd d) p C"
    and closed: "\<And>d p C c S. (d,p,C)\<in>G \<Longrightarrow> (c,S)\<in>C \<Longrightarrow>
      schema_dependencies S\<subseteq>rel_dom G"
    and roots: "U\<subseteq>rel_dom G" and coverage: "rel_dom G\<subseteq>native_definition_sites E U"
  shows "native_definition_sites E U=rel_dom G"
    and "native_package_formed E U"
    and "native_definition_graph E U=G"
proof -
  have full_sites: "native_definition_sites E (rel_dom G)=rel_dom G"
    by (rule native_closed_definition_graph(1)[OF formed reads closed])
  have full_package: "native_package_formed E (rel_dom G)"
    by (rule native_closed_definition_graph(2)[OF formed reads closed])
  have full_graph: "native_definition_graph E (rel_dom G)=G"
    by (rule native_closed_definition_graph(3)[OF formed reads closed])
  have upper: "native_definition_sites E U\<subseteq>native_definition_sites E (rel_dom G)"
    using roots by (auto simp: native_definition_sites_def)
  show sites: "native_definition_sites E U=rel_dom G" using upper coverage full_sites by blast
  show "native_package_formed E U" using full_package
    by (simp only: native_package_formed_def sites full_sites; blast)
  show "native_definition_graph E U=G" using full_graph
    by (simp only: native_definition_graph_def sites full_sites; blast)
qed

end
