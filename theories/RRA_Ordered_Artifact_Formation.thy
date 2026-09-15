theory RRA_Ordered_Artifact_Formation
  imports Finite_Ordered_Relation_Checks
begin

definition ordered_object_formed ::
  "('a::linorder,'v::linorder) finite_structured_object \<Rightarrow> bool" where
  "ordered_object_formed C=(
    let S=finite_structure C; D=finite_data C;
        incidence=sorted_list_of_fset (finite_incidence S);
        counted=sorted_list_of_multiset (finite_bag D);
        bindings=sorted_list_of_fset (finite_bindings D);
        used=concat (map (\<lambda>(r,p,x). [r,p,x]) incidence) @ map fst counted @ map fst bindings
    in ordered_relation_functional (finite_bindings D) \<and>
      ordered_fset_subset (fset_of_list used) (finite_carrier S))"

theorem ordered_object_formed_exact:
  "ordered_object_formed C=finite_object_formed C"
  by (auto simp: ordered_object_formed_def Let_def ordered_relation_functional_exact
      ordered_fset_subset_exact finite_object_formed_def finite_structure_formed_def
      finite_basis_formed_def fsubset_iff fset_of_list_elem split: prod.splits; blast)

declare finite_exact_formed_def[code del]

theorem finite_exact_formed_ordered_code [code]:
  "finite_exact_formed C=(ordered_object_formed C \<and>
    fBall (finite_carrier (finite_structure C)) octets_formed \<and>
    (\<forall>x\<in>set_mset (finite_bag (finite_data C)). octets_formed (snd x)) \<and>
    fBall (finite_bindings (finite_data C)) (\<lambda>x. octets_formed (snd x)))"
  by (simp only: finite_exact_formed_def ordered_object_formed_exact)

text \<open>Every original incidence endpoint and data address must still belong
  to the carrier, and functional bindings must still be functional. All original
  byte conditions remain. The exact Boolean equation applies to arbitrary
  complete artifacts, including malformed objects and repeated counted data;
  the artifact and every count remain unchanged.\<close>

end
