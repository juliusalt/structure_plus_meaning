theory Factor_Finite_Derivations
  imports Factor_Executable_Readings Finite_Functional_Selections
begin

type_synonym ('a,'s,'c) finite_schema_proof = "('a,'s,'c,finite_factor_term) inference_proof"

definition decode_finite_proof :: "('a,'s,'c) finite_schema_proof\<Rightarrow>('a,'s,'c) schema_proof" where
  "decode_finite_proof=map_inference_proof id id id decode_finite_term"

lemma decode_finite_proof_node:
  "decode_finite_proof (Schema_Proof c V B)=Schema_Proof c (decode_finite_binding_set V)
    (fimage (map_prod id decode_finite_proof) B)"
  by (simp add: decode_finite_proof_def decode_finite_binding_set_def)

lemma finite_proof_of_decode:
  "map_inference_proof id id id finite_term_of (decode_finite_proof p)=p"
  by (simp add: decode_finite_proof_def inference_proof.map_comp comp_def inference_proof.map_ident)

lemma decode_finite_proof_injective [simp]:
  "decode_finite_proof p=decode_finite_proof q \<longleftrightarrow> p=q"
  using finite_proof_of_decode[of p] finite_proof_of_decode[of q] by metis

lemma decoded_proof_family_values:
  "fset (fimage (map_prod id decode_finite_proof) B)=map_relation_values decode_finite_proof (fset B)"
  by (auto simp: map_relation_values_def map_prod_def)

lemma decoded_proof_family_all:
  "(\<forall>s q. (s,q)\<in>fset (fimage (map_prod id decode_finite_proof) B) \<longrightarrow> R s q) \<longleftrightarrow>
    (\<forall>s p. (s,p) |\<in>| B \<longrightarrow> R s (decode_finite_proof p))"
  by (simp only: decoded_proof_family_values map_relation_values_member; blast)

lemma decoded_proof_family_functional:
  "single_valued (fset (fimage (map_prod id decode_finite_proof) B)) \<longleftrightarrow>
    finite_relation_functional B"
proof -
  have injective: "inj decode_finite_proof" by (auto simp: inj_def)
  show ?thesis by (simp only: decoded_proof_family_values map_relation_values_functional[OF injective] finite_relation_functional_correct)
qed

lemma decoded_proof_family_domain:
  "rel_dom (fset (fimage (map_prod id decode_finite_proof) B))=fset (fimage fst B)"
  apply (simp only: decoded_proof_family_values map_relation_values_domain)
  by (simp only: rel_dom_image fimage.rep_eq)

text \<open>
  Finite and semantic certificates instantiate the same inference-proof
  structure. Every binding value is decoded, recursively through the complete
  socket-to-child family. The original proof checker remains the independent
  validity condition.
\<close>

end
