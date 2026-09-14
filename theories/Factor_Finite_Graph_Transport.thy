theory Factor_Finite_Graph_Transport
  imports Factor_Executable_Graphs Factor_Graph_Transport
begin

definition finite_rename_graph :: "('n\<Rightarrow>'m)\<Rightarrow>('a,'s,'c,'n) finite_derivation_graph\<Rightarrow>
    ('a,'s,'c,'m) finite_derivation_graph" where
  "finite_rename_graph h G=\<lparr>
    finite_graph_inferences=fimage (map_prod h id) (finite_graph_inferences G),
    finite_graph_discharges=fimage (map_prod (map_prod h id) h) (finite_graph_discharges G)\<rparr>"

theorem finite_rename_graph_exact:
  "decode_finite_graph (finite_rename_graph h G)=rename_schema_graph h (decode_finite_graph G)"
  by (simp add: finite_rename_graph_def decode_finite_graph_def rename_schema_graph_def
    fimage_fimage comp_def map_prod_def case_prod_unfold)

lemma finite_graph_renamed_nodes:
  "finite_graph_nodes (finite_rename_graph h G)=fimage h (finite_graph_nodes G)"
  by (rule fset_inject[THEN iffD1])
    (simp only: finite_graph_nodes_correct finite_rename_graph_exact schema_graph_renamed_nodes fimage.rep_eq)

theorem finite_graph_renamed_formed:
  assumes formed: "finite_graph_formed G root" and injective: "inj_on h (fset (finite_graph_nodes G))"
  shows "finite_graph_formed (finite_rename_graph h G) (h root)"
  using renamed_schema_graph_formed[of "decode_finite_graph G" root h] formed injective
  by (simp only: finite_graph_formed_correct finite_rename_graph_exact finite_graph_nodes_correct)

theorem finite_graph_renamed_premises:
  assumes formed: "finite_graph_formed G root" and injective: "inj_on h (fset (finite_graph_nodes G))"
    and member: "n |\<in>| finite_graph_nodes G"
  shows "finite_graph_premises (finite_rename_graph h G) (h n)=fimage (map_prod id h) (finite_graph_premises G n)"
proof -
  have gf: "schema_graph_formed (decode_finite_graph G) root" using formed by (simp only: finite_graph_formed_correct)
  have inj: "inj_on h (schema_graph_nodes (decode_finite_graph G))"
    using injective by (simp only: finite_graph_nodes_correct)
  have inside: "n\<in>schema_graph_nodes (decode_finite_graph G)"
    using member by (simp only: finite_graph_nodes_correct)
  show ?thesis by (rule fset_inject[THEN iffD1])
    (simp only: finite_graph_premises_correct finite_rename_graph_exact
      schema_graph_renamed_premises[OF gf inj inside] fimage.rep_eq)
qed

export_code finite_rename_graph checking SML

text \<open>
  The operation moves every node occurrence and both endpoints of every
  indexed discharge. Its exact decoding is the original graph renaming.
  Injectivity on the complete node family preserves graph formation and
  every original premise relation, including explicit inference sharing.
\<close>

end
