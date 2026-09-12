theory RRA_Assembly_Reuse
  imports RRA_Assembly
begin

section \<open>Whole selection retains the exact artifact\<close>

lemma whole_artifact_restriction:
  assumes formed: "exact_formed R"
  shows "restrict_object R (rra_carrier (object_structure R))=R"
  using formed
  by (auto simp: exact_identity_iff rra_identity basis_identity restrict_object_def
    restrict_structure_def internal_incidence_def restrict_basis_def exact_formed_def object_formed_def
    rra_formed_def basis_formed_def bag_support_def fun_eq_iff)

section \<open>One complete piece can retain every original address\<close>

theorem single_piece_assembly:
  assumes formed: "exact_formed R" and graph: "piece_graph P={(s,R)}"
  shows "assembly_relation P
    (graph_map ({s}\<times>rra_carrier (object_structure R)) snd) R"
proof -
  let ?U="rra_carrier (object_structure R)"
  let ?q="graph_map ({s}\<times>?U) snd"
  have finite: "finite ?U" and basis: "basis_formed ?U (object_data R)"
    using formed by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have endpoints: "\<And>a b c. (a,b,c)\<in>rra_incidence (object_structure R) \<Longrightarrow>
    a\<in>?U \<and> b\<in>?U \<and> c\<in>?U"
    using formed by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have slots: "piece_slots P={s}" by (simp add: piece_slots_def graph rel_dom_def)
  have at: "piece_at P s=R"
    using rel_value_eq[where R="{(s,R)}" and x=s and y=R]
    by (simp add: piece_at_def graph single_valued_def)
  have pieces: "piece_family_formed P"
    using formed by (simp add: piece_family_formed_def graph single_valued_def)
  have carrier: "copied_carrier P={s}\<times>?U"
    by (auto simp: copied_carrier_def slots at)
  have carrier_image: "copied_carrier P=image (Pair s) ?U"
    by (auto simp: carrier)
  have projection: "\<And>a. a\<in>?U \<Longrightarrow> rel_value ?q (s,a)=a"
    by (simp add: rel_value_graph_map)
  have mapping: "exact_map (copied_carrier P) ?U ?q"
    using graph_map_exact[of "{s}\<times>?U" snd] finite
    by (simp add: carrier)
  have incidence: "rra_incidence (object_structure R)=expected_incidence P ?q"
  proof (rule set_eqI)
    fix t :: "local_address\<times>local_address\<times>local_address"
    show "t\<in>rra_incidence (object_structure R)\<longleftrightarrow>t\<in>expected_incidence P ?q"
    proof
      assume arc: "t\<in>rra_incidence (object_structure R)"
      obtain a b c where shape: "t=(a,b,c)" by (cases t) auto
      have addresses: "a\<in>?U" "b\<in>?U" "c\<in>?U" using endpoints arc shape by auto
      have original: "((s,a),(s,b),(s,c))\<in>copied_incidence P"
        using arc shape by (auto simp: copied_incidence_def slots at)
      have image: "(rel_value ?q (s,a),rel_value ?q (s,b),rel_value ?q (s,c))\<in>expected_incidence P ?q"
        unfolding expected_incidence_def ternary_image_def
        by (rule CollectI, rule exI[of _ "(s,a)"], rule exI[of _ "(s,b)"], rule exI[of _ "(s,c)"])
           (use original in simp)
      show "t\<in>expected_incidence P ?q"
        using image addresses by (simp add: shape projection)
    next
      assume image: "t\<in>expected_incidence P ?q"
      obtain a b c where arc: "(a,b,c)\<in>rra_incidence (object_structure R)"
        and shape: "t=(rel_value ?q (s,a),rel_value ?q (s,b),rel_value ?q (s,c))"
        using image by (auto simp: expected_incidence_def ternary_image_def copied_incidence_def slots at)
      have addresses: "a\<in>?U" "b\<in>?U" "c\<in>?U" using endpoints[OF arc] by auto
      show "t\<in>rra_incidence (object_structure R)"
        using arc addresses by (simp add: shape projection)
    qed
  qed
  have agree: "\<forall>x\<in>copied_carrier P. rel_value ?q x=snd x"
    using projection by (auto simp: carrier)
  have same_push: "push_basis (copied_carrier P) (rel_value ?q) (copied_basis P)=
      push_basis (copied_carrier P) snd (copied_basis P)"
    by (rule push_basis_cong[OF copied_basis_formed[OF pieces] agree])
  have injective: "inj_on (Pair s) ?U" by (auto simp: inj_on_def)
  have counts: "bag_count (push_basis (copied_carrier P) snd (copied_basis P))=
      bag_count (object_data R)"
  proof (rule ext)
    fix av :: "local_address\<times>octets"
    obtain a v where shape: "av=(a,v)" by (cases av) auto
    show "bag_count (push_basis (copied_carrier P) snd (copied_basis P)) av=
        bag_count (object_data R) av"
      using finite count_outside_carrier[OF basis, of a v]
      by (simp add: shape carrier_image push_basis_def pushed_count_def
        sum.reindex[OF injective] copied_basis_def slots at o_def)
  qed
  have bindings: "functional_bindings (push_basis (copied_carrier P) snd (copied_basis P))=
      functional_bindings (object_data R)"
    by (auto simp: push_basis_def copied_functional_bindings slots at image_image split_def)
  have data: "assembled_data P ?q (object_data R)"
    using counts bindings same_push by (simp add: assembled_data_def basis_identity)
  show ?thesis using pieces formed mapping incidence data by (simp add: assembly_relation_def)
qed

text \<open>
  A single piece occurrence has an explicit origin for every output atom.
  Projecting its copied coordinates back to their original addresses preserves
  the entire incidence relation, every anonymous attachment count, and every
  functional binding. This is exact artifact equality, including empty
  artifacts. The piece key separates the occurrence; it has no semantic role.
\<close>

end
