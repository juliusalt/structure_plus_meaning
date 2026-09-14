theory Factor_Finite_Graph_Correspondence
  imports Factor_Finite_Graph_Construction Factor_Finite_Graph_Mappings
begin

theorem finite_extend_native_graph_correspondence:
  assumes extended: "finite_extend_native_graph E G root=Some (F,M,r,H)"
  shows "finite_graph_mapping M G root H r"
    "single_valued ((fset M)\<inverse>)"
proof -
  have facts: "finite_graph_construction_ready E G root"
    "M=fimage (\<lambda>n. (n,finite_graph_coordinates E G n)) (finite_graph_nodes G)"
    "r=finite_graph_coordinates E G root"
    "H=finite_rename_graph (finite_graph_coordinates E G) G"
    "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    by (rule finite_extend_native_graph_correct[OF extended])+
  have formed: "finite_graph_formed G root"
    using facts(1) by (simp only: finite_graph_construction_ready_def; blast)
  show "finite_graph_mapping M G root H r"
    by (simp only: facts(2,3,4); rule finite_graph_mapping_rename[OF formed])
  show "single_valued ((fset M)\<inverse>)"
    using facts(5) by (simp only: facts(2) finite_function_graph graph_map_converse_functional)
qed

text \<open>
  Every successful native placement retains the complete original graph through
  its actual returned map. The converse is functional on that complete map.
  Both facts are available to direct placement and to composed constructions.
\<close>

end
