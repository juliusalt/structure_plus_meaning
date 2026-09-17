theory Factor_Finite_Graph_Reindexing
  imports Factor_Graph_Reindexing Factor_Executable_Graphs
begin

definition finite_reindex_graph ::
    "('n\<Rightarrow>('a,'c) finite_schema_graph_node\<Rightarrow>('b,'e) finite_schema_graph_node)\<Rightarrow>
      ('n\<Rightarrow>'s\<Rightarrow>'t)\<Rightarrow>('a,'s,'c,'n) finite_derivation_graph\<Rightarrow>
      ('b,'t,'e,'n) finite_derivation_graph" where
  "finite_reindex_graph K S G=\<lparr>
    finite_graph_inferences=fimage (indexed_pair_map K) (finite_graph_inferences G),
    finite_graph_discharges=fimage (map_prod (indexed_pair_map S) id) (finite_graph_discharges G)\<rparr>"

theorem finite_reindex_graph_correct:
  assumes rows: "\<And>n A. decode_finite_graph_node (K n A)=L n (decode_finite_graph_node A)"
  shows "decode_finite_graph (finite_reindex_graph K S G)=reindex_schema_graph L S (decode_finite_graph G)"
proof -
  have commute: "map_prod id decode_finite_graph_node \<circ> indexed_pair_map K=
      indexed_pair_map L \<circ> map_prod id decode_finite_graph_node"
    by (rule ext) (auto simp: comp_def indexed_pair_map_def map_prod_def rows)
  show ?thesis
    by (simp add: decode_finite_graph_def finite_reindex_graph_def reindex_schema_graph_def fimage_fimage commute)
qed

end
