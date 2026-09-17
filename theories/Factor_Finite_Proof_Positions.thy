theory Factor_Finite_Proof_Positions
  imports Factor_Finite_Proof_Children
begin

primrec finite_schema_proof_positions ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'c) finite_schema_proof\<Rightarrow>'d\<Rightarrow>
      finite_factor_term\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node fset" where
  "finite_schema_proof_positions P (Schema_Proof c V B) d t=finsert (Schema_Proof c V B,d,t)
    (ffUnion (fimage (\<lambda>H. ffUnion (fimage (\<lambda>(s,F).
      ffUnion (fimage (\<lambda>(r,e,x). if r=s then F e x else {||}) H))
        (fimage (map_prod id (finite_schema_proof_positions P)) B)))
      (finite_admitted_premise_readings P d c V t)))"

lemma finite_schema_proof_positions_unfold:
  "finite_schema_proof_positions P p d t=finsert (p,d,t)
    (ffUnion (fimage (\<lambda>(s,q,e,x). finite_schema_proof_positions P q e x)
      (finite_schema_proof_children P (p,d,t))))"
proof -
  obtain c V B where tree: "p=Schema_Proof c V B" by (cases p) auto
  have joined:
    "ffUnion (fimage (\<lambda>(s,F). ffUnion (fimage (\<lambda>(r,e,x). if r=s then F e x else {||}) H))
      (fimage (map_prod id (finite_schema_proof_positions P)) B))=
      ffUnion (fimage (\<lambda>(s,q,e,x). finite_schema_proof_positions P q e x) (finite_keyed_product B H))" for H
    using finite_keyed_product_union_values[where R=B and S=H
      and f="finite_schema_proof_positions P" and F="\<lambda>s F y. F (fst y) (snd y)"]
    by (simp only: case_prod_unfold fst_conv snd_conv)
  show ?thesis
    unfolding tree finite_schema_proof_positions.simps
    by (simp only: finite_schema_proof_children.simps finite_union_image_flatten
      joined)
qed

theorem finite_schema_proof_positions_correct:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
    and p :: "('a,'s,'c) finite_schema_proof"
  shows
  "fset (fimage decode_finite_instantiated_node (finite_schema_proof_positions P p d t))=
    schema_proof_positions (decode_finite_system P) (decode_finite_instantiated_node (p,d,t))"
proof (induction p arbitrary: d t rule: measure_induct_rule[of size])
  case (less p)
  let ?C = "finite_schema_proof_children P (p,d,t)"
  let ?D = decode_finite_instantiated_node
  let ?P = "decode_finite_system P"
  have recursive:
    "?D ` fset (finite_schema_proof_positions P q e x)=schema_proof_positions ?P (?D (q,e,x))"
    if "(s,q,e,x) |\<in>| ?C" for s q e x
  proof -
    have smaller: "size q<size p"
      using finite_schema_proof_child_size[OF that] by (simp only: fst_conv)
    have exact:
      "fset (fimage ?D (finite_schema_proof_positions P q e x))=schema_proof_positions ?P (?D (q,e,x))"
      by (rule less.IH[OF smaller])
    show ?thesis using exact by (simp only: fimage.rep_eq)
  qed
  have children:
    "schema_proof_children ?P (?D (p,d,t))=map_prod id ?D ` fset ?C"
    using finite_schema_proof_children_correct[of P "(p,d,t)"]
    by (simp only: fimage.rep_eq)
  have ranges:
    "rel_ran (schema_proof_children ?P (?D (p,d,t)))=?D ` rel_ran (fset ?C)"
    by (simp only: children map_prod_def pair_image_range)
  have indexed:
    "(\<Union>(s,q,e,x)\<in>fset ?C. ?D ` fset (finite_schema_proof_positions P q e x))=
      (\<Union>(s,q,e,x)\<in>fset ?C. schema_proof_positions ?P (?D (q,e,x)))"
  proof (rule arg_cong[where f=Union], rule image_cong[OF refl])
    fix z :: "'s\<times>('a,'s,'d,'c) finite_instantiated_proof_node"
    assume inside: "z\<in>fset ?C"
    obtain s q e x where shape: "z=(s,q,e,x)" by (cases z) auto
    show "(case z of (s,q,e,x) \<Rightarrow> ?D ` fset (finite_schema_proof_positions P q e x))=
      (case z of (s,q,e,x) \<Rightarrow> schema_proof_positions ?P (?D (q,e,x)))"
      by (simp only: shape case_prod_conv; rule recursive; use inside in \<open>simp only: shape\<close>)
  qed
  have descendants:
    "?D ` (\<Union>(s,q,e,x)\<in>fset ?C. fset (finite_schema_proof_positions P q e x))=
      (\<Union>n\<in>rel_ran (schema_proof_children ?P (?D (p,d,t))). schema_proof_positions ?P n)"
    unfolding ranges image_UN UN_simps(10)
    using indexed by (simp only: relation_range_union[symmetric] case_prod_unfold prod.collapse)
  show ?case
    apply (subst finite_schema_proof_positions_unfold)
    apply (subst schema_proof_positions_unfold)
    using descendants by (simp only: fimage.rep_eq finsert.rep_eq ffUnion.rep_eq image_insert
      image_UN image_image case_prod_unfold prod.collapse)
qed

text \<open>
  Structural recursion retains the root and every descendant generated from
  the actual source premise relation. Every position pairs a complete
  certificate with its required call. Exact decoding recovers the original
  reachable-position relation on every finite input, including an unchecked
  root with no admitted children.
\<close>

end
