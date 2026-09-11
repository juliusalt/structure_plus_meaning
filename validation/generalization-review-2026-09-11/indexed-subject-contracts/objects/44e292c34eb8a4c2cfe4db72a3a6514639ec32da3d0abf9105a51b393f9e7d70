theory Factor_Construction_Reuse
  imports Factor_Construction_Claims RRA_Assembly_Reuse
begin

section \<open>Exact reuse from one supplied input occurrence\<close>

definition whole_source_construction :: "exact_artifact \<Rightarrow> addressed_construction" where
  "whole_source_construction R=
    \<lparr>construction_selections={([],Inl 0,rra_carrier (object_structure R))},
     construction_origins=graph_map ({[]}\<times>rra_carrier (object_structure R)) snd\<rparr>"

theorem whole_source_constructs:
  assumes formed: "exact_formed R"
  shows "source_constructs [R] {} (whole_source_construction R) R"
proof -
  let ?W="whole_source_construction R"
  have finite: "finite (rra_carrier (object_structure R))"
    using formed by (simp add: exact_formed_def object_formed_def rra_formed_def)
  have selected: "construction_selection_formed [R] {} ?W"
    using formed finite
    by (simp add: construction_selection_formed_def construction_sources_formed_def
      whole_source_construction_def source_selection_valid_def single_valued_def)
  have graph: "piece_graph (construction_pieces [R] {} ?W)={([],R)}"
    by (simp add: construction_pieces_def whole_source_construction_def construction_fragment_def
      fragment_material_def whole_artifact_restriction[OF formed])
  have assembly: "assembly_relation (construction_pieces [R] {} ?W)
      (construction_origins ?W) R"
    using single_piece_assembly[OF formed graph]
    by (simp add: whole_source_construction_def)
  show ?thesis using selected assembly by (simp add: source_constructs_def)
qed

lemma whole_source_coordinates:
  "construction_coordinates_formed {} (whole_source_construction R)"
  by (simp add: construction_coordinates_formed_def whole_source_construction_def octets_formed_def)

lemma whole_source_selected_atoms:
  "construction_selected_atoms (whole_source_construction R) j=
    (if j=Inl 0 then rra_carrier (object_structure R) else {})"
  by (auto simp: construction_selected_atoms_def whole_source_construction_def)

lemma whole_source_origin:
  "((s,a),b)\<in>construction_origins (whole_source_construction R)\<longleftrightarrow>
    s=[] \<and> a\<in>rra_carrier (object_structure R) \<and> b=a"
  by (auto simp: whole_source_construction_def graph_map_member)

text \<open>
  The input list contains the whole source once, the base boundary is empty,
  and one piece selects every source atom. Its origin map explains the exact
  output without changing any address or data. The empty word is a formed
  coordinate chosen for this witness, with no role discriminator.

  Reuse requires an already supplied formed source. It supplies no semantic
  permission, no origin before that boundary, and no adequacy of a policy that
  permits the account. A program payload can use this account as ordinary
  material without becoming a rule of the program judging its construction.
\<close>

end
