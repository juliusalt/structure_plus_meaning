theory Factor_Construction_Omissions
  imports Factor_Construction
begin

section \<open>Source incidence omitted by all selected pieces\<close>

lemma construction_selected_piece_at:
  assumes wf: "construction_selection_formed xs B W"
    and selected: "(s,j,A) \<in> construction_selections W"
  shows "piece_at (construction_pieces xs B W) s =
    fragment_material (construction_fragment xs B j A)"
proof -
  have pf: "piece_family_formed (construction_pieces xs B W)"
    by (rule construction_pieces_formed[OF wf])
  have member: "(s,fragment_material (construction_fragment xs B j A)) \<in>
    piece_graph (construction_pieces xs B W)"
    unfolding construction_piece_member
    by (rule exI[of _ j], rule exI[of _ A]) (use selected in simp)
  have sv: "single_valued (piece_graph (construction_pieces xs B W))"
    using pf by (simp add: piece_family_formed_def)
  show ?thesis unfolding piece_at_def by (rule rel_value_eq[OF sv member])
qed

lemma construction_selected_piece_incidence:
  assumes wf: "construction_selection_formed xs B W"
    and selected: "(s,j,A) \<in> construction_selections W"
  shows "((s,r),(s,p),(s,x)) \<in> copied_incidence (construction_pieces xs B W) \<longleftrightarrow>
    (r,p,x) \<in> rra_incidence (object_structure (fragment_material (construction_fragment xs B j A)))"
proof -
  have slot: "s \<in> piece_slots (construction_pieces xs B W)"
    using selected by (auto simp: construction_piece_slots rel_dom_def)
  show ?thesis using slot construction_selected_piece_at[OF wf selected]
    by (auto simp: copied_incidence_def)
qed

definition construction_selected_incidence ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> nat + 'b \<Rightarrow>
    (local_address \<times> local_address \<times> local_address) set" where
  "construction_selected_incidence xs B W j =
    {e. \<exists>s A. (s,j,A) \<in> construction_selections W \<and>
      e \<in> rra_incidence (object_structure (fragment_material (construction_fragment xs B j A)))}"

definition construction_omitted_incidence ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> nat + 'b \<Rightarrow>
    (local_address \<times> local_address \<times> local_address) set" where
  "construction_omitted_incidence xs B W j =
    rra_incidence (object_structure (construction_source_value xs B j)) -
      construction_selected_incidence xs B W j"

lemma construction_selected_incidence_subset:
  "construction_selected_incidence xs B W j \<subseteq>
    rra_incidence (object_structure (construction_source_value xs B j))"
  by (auto simp: construction_selected_incidence_def fragment_material_def construction_fragment_def
    restrict_object_def restrict_structure_def internal_incidence_def)

theorem construction_source_incidence_partition:
  "rra_incidence (object_structure (construction_source_value xs B j)) =
    construction_selected_incidence xs B W j \<union> construction_omitted_incidence xs B W j"
  "construction_selected_incidence xs B W j \<inter> construction_omitted_incidence xs B W j = {}"
  using construction_selected_incidence_subset[of xs B W j]
  by (auto simp: construction_omitted_incidence_def)

theorem construction_omitted_incidence_exact:
  assumes wf: "construction_selection_formed xs B W"
  shows "(r,p,x) \<in> construction_omitted_incidence xs B W j \<longleftrightarrow>
    (r,p,x) \<in> rra_incidence (object_structure (construction_source_value xs B j)) \<and>
    (\<forall>s A. (s,j,A) \<in> construction_selections W \<longrightarrow>
      ((s,r),(s,p),(s,x)) \<notin> copied_incidence (construction_pieces xs B W))"
  using construction_selected_piece_incidence[OF wf]
  by (auto simp: construction_omitted_incidence_def construction_selected_incidence_def)

theorem full_atom_selection_can_omit_incidence:
  "\<exists>S :: exact_artifact. \<exists>W :: (unit,local_address) source_construction. \<exists>R.
    source_constructs [S] {} W R \<and>
    construction_selected_atoms W (Inl 0) = rra_carrier (object_structure S) \<and>
    construction_selected_incidence [S] {} W (Inl 0) = {} \<and>
    rra_incidence (object_structure S) \<noteq> {}"
proof -
  let ?S = "\<lparr>object_structure =
    \<lparr>rra_carrier = {[],[0],[1]}, rra_incidence = {([],[0],[1])}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  let ?W0 = "\<lparr>construction_selections =
    {([2],Inl 0,{[]}),([3],Inl 0,{[0]}),([4],Inl 0,{[1]})},
    construction_origins = {}\<rparr> :: (unit,local_address) source_construction"
  have sf: "exact_formed ?S"
    by (auto simp: exact_formed_def object_formed_def rra_formed_def octets_formed_def)
  have wf: "construction_selection_formed [?S] {} ?W0"
    using sf by (auto simp: construction_selection_formed_def construction_sources_formed_def
      source_selection_valid_def single_valued_def)
  obtain A where assembly: "assembly_pieces A = construction_pieces [?S] {} ?W0" "K2 A"
    using piece_family_has_assembly[OF construction_pieces_formed[OF wf]] by blast
  let ?W = "?W0\<lparr>construction_origins := assembly_origin A\<rparr>"
  have wf': "construction_selection_formed [?S] {} ?W"
    using wf by (simp add: construction_selection_formed_def)
  have pieces: "construction_pieces [?S] {} ?W = construction_pieces [?S] {} ?W0"
    by (simp add: construction_pieces_def)
  have same: "construction_assembly [?S] {} ?W = A"
    using pieces assembly(1) by (cases A) (simp add: construction_assembly_def construction_pieces_def)
  have built: "source_constructs [?S] {} ?W (assembly_output A)"
    using wf' same assembly(2) by (simp add: source_constructs_iff_K2)
  have atoms: "construction_selected_atoms ?W (Inl 0) = rra_carrier (object_structure ?S)"
    by (auto simp: construction_selected_atoms_def)
  have omitted: "construction_selected_incidence [?S] {} ?W (Inl 0) = {}"
    by (auto simp: construction_selected_incidence_def construction_fragment_def fragment_material_def
      restrict_object_def restrict_structure_def internal_incidence_def)
  show ?thesis
    by (rule exI[of _ ?S], rule exI[of _ ?W], rule exI[of _ "assembly_output A"])
       (use built atoms omitted in simp)
qed

text \<open>
  The union of selected carriers does not determine which source incidences are
  copied. An incidence may cross different pieces even when every source atom
  occurs somewhere. The omission relation therefore tracks complete source
  incidence separately and characterizes exactly the absence of a copy from
  that source occurrence. The complete source value remains available in the
  construction argument.
\<close>

end
