theory Factor_Finite_Proof_Coordinates
  imports Factor_Finite_Proof_Paths Finite_Ordered_Representatives "HOL-Library.List_Lexorder"
begin

definition finite_schema_proof_coordinates ::
    "('a,'s::linorder,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node\<Rightarrow>
      (('a,'s,'d,'c) finite_instantiated_proof_node\<times>'s list) fset" where
  "finite_schema_proof_coordinates P root=(case root of (p,d,t) \<Rightarrow>
    finite_representative_map (finite_schema_proof_paths P p d t))"

lemma finite_schema_proof_coordinates_member:
  "(n,ss) |\<in>| finite_schema_proof_coordinates P (p,d,t) \<longleftrightarrow>
    (ss,n) |\<in>| finite_schema_proof_paths P p d t \<and>
    (\<forall>tt. (tt,n) |\<in>| finite_schema_proof_paths P p d t \<longrightarrow> ss\<le>tt)"
  by (simp only: finite_schema_proof_coordinates_def case_prod_conv
    finite_representative_map_member finite_relation_least_key_some)

theorem finite_schema_proof_coordinates_domain:
  "fimage fst (finite_schema_proof_coordinates P (p,d,t))=finite_schema_proof_positions P p d t"
  by (simp only: finite_schema_proof_coordinates_def case_prod_conv
    finite_representative_map_domain finite_schema_proof_paths_projection)

theorem finite_schema_proof_coordinates_functional:
  "finite_relation_functional (finite_schema_proof_coordinates P root)"
  by (cases root) (simp only: finite_schema_proof_coordinates_def case_prod_conv finite_representative_map_functional)

theorem finite_schema_proof_coordinates_injective:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "single_valued ((fset (finite_schema_proof_coordinates P (p,d,t)))\<inverse>)"
  by (simp only: finite_schema_proof_coordinates_def case_prod_conv;
    rule finite_representative_map_injective[OF finite_schema_proof_paths_functional[OF checked]])

lemma finite_schema_proof_coordinates_root:
  "((p,d,t),[]) |\<in>| finite_schema_proof_coordinates P (p,d,t)"
  by (simp add: finite_schema_proof_coordinates_member finite_schema_proof_paths_root)

export_code finite_schema_proof_coordinates checking SML

text \<open>
  Each complete certificate-and-call node receives one of its actual source
  socket paths. The complete map covers exactly the existing position family.
  It is functional on all inputs and injective for a checked certificate.
  Multiple paths to a shared node remain present in the path family while
  supplying one representative in the coordinate map. Only source sockets
  are ordered; certificate values receive no imposed ordering.
\<close>

end
