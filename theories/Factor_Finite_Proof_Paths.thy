theory Factor_Finite_Proof_Paths
  imports Factor_Finite_Proof_Positions Indexed_Relation_Paths
begin

primrec finite_schema_proof_paths ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'c) finite_schema_proof\<Rightarrow>'d\<Rightarrow>
      finite_factor_term\<Rightarrow>('s list\<times>('a,'s,'d,'c) finite_instantiated_proof_node) fset" where
  "finite_schema_proof_paths P (Schema_Proof c V B) d t=finsert ([],(Schema_Proof c V B,d,t))
    (ffUnion (fimage (\<lambda>H. ffUnion (fimage (\<lambda>(s,F).
      ffUnion (fimage (\<lambda>(r,e,x). if r=s then fimage (map_prod (Cons s) id) (F e x) else {||}) H))
        (fimage (map_prod id (finite_schema_proof_paths P)) B)))
      (finite_admitted_premise_readings P d c V t)))"

lemma finite_schema_proof_paths_unfold:
  "finite_schema_proof_paths P p d t=finsert ([],(p,d,t))
    (ffUnion (fimage (\<lambda>(s,q,e,x). fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x))
      (finite_schema_proof_children P (p,d,t))))"
proof -
  obtain c V B where tree: "p=Schema_Proof c V B" by (cases p) auto
  have joined:
    "ffUnion (fimage (\<lambda>(s,F). ffUnion
      (fimage (\<lambda>(r,e,x). if r=s then fimage (map_prod (Cons s) id) (F e x) else {||}) H))
      (fimage (map_prod id (finite_schema_proof_paths P)) B))=
      ffUnion (fimage (\<lambda>(s,q,e,x). fimage (map_prod (Cons s) id) (finite_schema_proof_paths P q e x))
        (finite_keyed_product B H))" for H
    using finite_keyed_product_union_values[where R=B and S=H
      and f="finite_schema_proof_paths P" and F="\<lambda>s F y. fimage (map_prod (Cons s) id) (F (fst y) (snd y))"]
    by (simp only: case_prod_unfold fst_conv snd_conv)
  show ?thesis
    unfolding tree finite_schema_proof_paths.simps
    by (simp only: finite_schema_proof_children.simps finite_union_image_flatten
      joined)
qed

lemma finite_schema_proof_empty_path:
  "([],n) |\<in>| finite_schema_proof_paths P p d t \<longleftrightarrow> n=(p,d,t)"
  by (subst finite_schema_proof_paths_unfold)
    (auto simp: finite_union_image_member finite_image_member map_prod_def split: prod.splits)

lemma finite_schema_proof_paths_root:
  "([],(p,d,t)) |\<in>| finite_schema_proof_paths P p d t"
  by (simp only: finite_schema_proof_empty_path)

theorem finite_schema_proof_paths_family:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
    and p :: "('a,'s,'c) finite_schema_proof"
  shows "fset (finite_schema_proof_paths P p d t)=
    indexed_path_family (\<lambda>n. fset (finite_schema_proof_children P n)) (p,d,t)"
proof (induction p arbitrary: d t rule: measure_induct_rule[of size])
  case (less p)
  let ?C = "\<lambda>n. fset (finite_schema_proof_children P n)"
  have recursive: "fset (finite_schema_proof_paths P q e x)=indexed_path_family ?C (q,e,x)"
    if child: "(s,q,e,x)\<in>?C (p,d,t)" for s q e x
  proof -
    have smaller: "size q<size p"
      using finite_schema_proof_child_size[OF child] by (simp only: fst_conv)
    show ?thesis by (rule less.IH[OF smaller])
  qed
  have tails:
    "(\<Union>(s,q,e,x)\<in>?C (p,d,t). map_prod (Cons s) id ` fset (finite_schema_proof_paths P q e x))=
      (\<Union>(s,n)\<in>?C (p,d,t). map_prod (Cons s) id ` indexed_path_family ?C n)"
  proof (rule arg_cong[where f=Union], rule image_cong[OF refl])
    fix z :: "'s\<times>('a,'s,'d,'c) finite_instantiated_proof_node"
    assume member: "z\<in>?C (p,d,t)"
    obtain s q e x where shape: "z=(s,q,e,x)" by (cases z) auto
    have child: "(s,q,e,x)\<in>?C (p,d,t)" using member by (simp only: shape)
    show "(case z of (s,q,e,x) \<Rightarrow> map_prod (Cons s) id ` fset (finite_schema_proof_paths P q e x))=
      (case z of (s,n) \<Rightarrow> map_prod (Cons s) id ` indexed_path_family ?C n)"
      by (simp only: shape case_prod_conv recursive[OF child])
  qed
  show ?case
    apply (subst finite_schema_proof_paths_unfold)
    apply (subst indexed_path_family_unfold)
    using tails by (simp only: finsert.rep_eq ffUnion.rep_eq fimage.rep_eq image_image case_prod_unfold)
qed

theorem finite_schema_proof_paths_correct:
  "fset (fimage (map_prod id decode_finite_instantiated_node) (finite_schema_proof_paths P p d t))=
    indexed_path_family (schema_proof_children (decode_finite_system P))
      (decode_finite_instantiated_node (p,d,t))"
proof -
  have rows: "schema_proof_children (decode_finite_system P) (decode_finite_instantiated_node n)=
    map_prod id decode_finite_instantiated_node ` fset (finite_schema_proof_children P n)" for n
    by (simp only: finite_schema_proof_children_correct[symmetric] fimage.rep_eq)
  show ?thesis
    by (simp only: fimage.rep_eq finite_schema_proof_paths_family;
      rule indexed_path_family_image[symmetric]; rule rows)
qed

lemma finite_schema_proof_paths_decoded_member:
  "(ss,decode_finite_instantiated_node n)\<in>
    indexed_path_family (schema_proof_children (decode_finite_system P)) (decode_finite_instantiated_node (p,d,t))
    \<longleftrightarrow> (ss,n) |\<in>| finite_schema_proof_paths P p d t"
  by (simp only: finite_schema_proof_paths_correct[symmetric] finite_value_image_member
    decode_finite_instantiated_node_injective; blast)

lemma finite_schema_proof_paths_equal:
  "fset (fimage (map_prod id decode_finite_instantiated_node) R)=
    indexed_path_family (schema_proof_children (decode_finite_system P)) (decode_finite_instantiated_node (p,d,t))
    \<longleftrightarrow> R=finite_schema_proof_paths P p d t"
proof -
  have injective: "inj (map_prod id decode_finite_instantiated_node)"
    by (auto simp: inj_def)
  show ?thesis by (simp only: finite_schema_proof_paths_correct[symmetric]
    fimage.rep_eq inj_image_eq_iff[OF injective] fset_inject)
qed

theorem finite_schema_proof_paths_projection:
  "fimage snd (finite_schema_proof_paths P p d t)=finite_schema_proof_positions P p d t"
proof -
  let ?D = decode_finite_instantiated_node
  let ?P = "decode_finite_system P"
  let ?R = "finite_schema_proof_paths P p d t"
  have original_range:
    "rel_ran (indexed_path_family (schema_proof_children ?P) (?D (p,d,t)))=
      schema_proof_positions ?P (?D (p,d,t))"
    unfolding schema_proof_positions_def
    by (rule indexed_path_family_range) (auto simp: schema_proof_edges_def)
  have native_range: "?D ` rel_ran (fset ?R)=schema_proof_positions ?P (?D (p,d,t))"
    using original_range
    by (simp only: finite_schema_proof_paths_correct[symmetric] fimage.rep_eq map_prod_def id_apply pair_image_range)
  have same_image:
    "?D ` fset (fimage snd ?R)=?D ` fset (finite_schema_proof_positions P p d t)"
    using native_range finite_schema_proof_positions_correct[of P p d t]
    by (simp only: fimage.rep_eq rel_ran_image)
  have injective: "inj ?D" by (auto simp: inj_def)
  show ?thesis by (rule fset_inject[THEN iffD1], rule inj_image_eq_iff[OF injective, THEN iffD1], rule same_image)
qed

theorem finite_schema_proof_paths_functional:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "finite_relation_functional (finite_schema_proof_paths P p d t)"
proof -
  let ?D = decode_finite_instantiated_node
  let ?P = "decode_finite_system P"
  let ?R = "finite_schema_proof_paths P p d t"
  have root: "instantiated_node_checked ?P (?D (p,d,t))"
    using checked by (simp only: instantiated_node_checked_def decode_finite_instantiated_node_pair
      fst_conv snd_conv finite_checks_schema_proof_exact)
  have original: "single_valued (indexed_path_family (schema_proof_children ?P) (?D (p,d,t)))"
    by (rule indexed_path_family_functional[where Q="instantiated_node_checked ?P"])
      (rule root, rule schema_proof_children_checked, assumption, assumption,
        rule schema_proof_children_single_valued, assumption)
  have injective: "inj ?D" by (auto simp: inj_def)
  have reflected: "single_valued (map_prod id ?D ` fset ?R) \<longleftrightarrow> single_valued (fset ?R)"
    using map_relation_values_functional[OF injective, of "fset ?R"]
    by (simp only: map_relation_values_def map_prod_def id_apply)
  show ?thesis using original reflected
    by (simp only: finite_relation_functional_correct finite_schema_proof_paths_correct[symmetric] fimage.rep_eq)
qed

text \<open>
  The actual source reader supplies every socket and required child call.
  The operation retains all complete paths and the full certificate-and-call
  node at each endpoint. Exact correspondence to the independent path family,
  full position projection, checked-path functionality and actual representative
  coordinates remain required before this construction is adopted.
\<close>

end
