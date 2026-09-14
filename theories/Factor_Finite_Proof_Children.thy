theory Factor_Finite_Proof_Children
  imports Factor_Finite_Proof_Checking Factor_Proof_Positions Finite_Keyed_Products
begin

type_synonym ('a,'s,'d,'c) finite_instantiated_proof_node =
  "('a,'s,'c) finite_schema_proof\<times>'d\<times>finite_factor_term"

definition decode_finite_instantiated_node ::
    "('a,'s,'d,'c) finite_instantiated_proof_node\<Rightarrow>('a,'s,'d,'c) instantiated_proof_node" where
  "decode_finite_instantiated_node n=(decode_finite_proof (fst n),
    decode_finite_call_term (snd n))"

lemma decode_finite_instantiated_node_pair [simp]:
  "decode_finite_instantiated_node (p,d,t)=(decode_finite_proof p,d,decode_finite_term t)"
  by (simp only: decode_finite_instantiated_node_def fst_conv snd_conv decode_finite_call_pair)

lemma decode_finite_instantiated_node_proof [simp]:
  "fst (decode_finite_instantiated_node n)=decode_finite_proof (fst n)"
  by (simp only: decode_finite_instantiated_node_def fst_conv)

lemma decode_finite_instantiated_node_injective [simp]:
  "decode_finite_instantiated_node n=decode_finite_instantiated_node m \<longleftrightarrow> n=m"
  by (cases n; cases m) auto

fun finite_schema_proof_children ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node\<Rightarrow>
      ('s\<times>('a,'s,'d,'c) finite_instantiated_proof_node) fset" where
  "finite_schema_proof_children P (Schema_Proof c V B,d,t)=
    ffUnion (fimage (finite_keyed_product B) (finite_admitted_premise_readings P d c V t))"

declare finite_schema_proof_children.simps [simp del]

lemma finite_schema_proof_children_member:
  "(s,p,e,x) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t) \<longleftrightarrow>
    (s,p) |\<in>| B \<and> (\<exists>H. H |\<in>| finite_admitted_premise_readings P d c V t \<and> (s,e,x) |\<in>| H)"
  by (simp only: finite_schema_proof_children.simps finite_union_image_member finite_keyed_product_member; blast)

theorem finite_schema_proof_children_correct:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
    and n :: "('a,'s,'d,'c) finite_instantiated_proof_node"
  shows
  "fset (fimage (map_prod id decode_finite_instantiated_node) (finite_schema_proof_children P n))=
    schema_proof_children (decode_finite_system P) (decode_finite_instantiated_node n)"
proof -
  obtain p d t where node: "n=(p,d,t)" by (cases n) auto
  obtain c V B where tree: "p=Schema_Proof c V B" by (cases p) auto
  have member:
    "(s,q)\<in>schema_proof_children (decode_finite_system P)
      (decode_finite_instantiated_node (Schema_Proof c V B,d,t)) \<longleftrightarrow>
      (\<exists>v e x. (s,v,e,x) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t) \<and>
        q=decode_finite_instantiated_node (v,e,x))" for s q
  proof -
    obtain z e x where result: "q=(z,e,x)" by (cases q) auto
    show ?thesis
    proof
      assume child: "(s,q)\<in>schema_proof_children (decode_finite_system P)
        (decode_finite_instantiated_node (Schema_Proof c V B,d,t))"
      obtain Q where stored: "(s,z)\<in>fset (fimage (map_prod id decode_finite_proof) B)"
        and inst: "admitted_schema_instance (decode_finite_system P) d c
          (decode_finite_term_bindings V) (decode_finite_term t) Q"
        and premise: "(s,e,x)\<in>Q"
        using child by (auto simp: result decode_finite_proof_node schema_proof_children.simps)
      obtain v where row: "(s,v) |\<in>| B" and decoded_tree: "z=decode_finite_proof v"
        using stored by (simp only: decoded_proof_family_values map_relation_values_member; blast)
      obtain H where reading: "H |\<in>| finite_admitted_premise_readings P d c V t"
        and decoded: "Q=decode_finite_premises H"
        using inst by (simp only: finite_admitted_premise_readings_correct; blast)
      obtain y where call: "(s,e,y) |\<in>| H" and decoded_term: "x=decode_finite_term y"
        using premise by (simp only: decoded decode_finite_premises_value_member; blast)
      have actual: "(s,v,e,y) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t)"
        using row reading call by (simp only: finite_schema_proof_children_member; blast)
      show "\<exists>v e x. (s,v,e,x) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t) \<and>
        q=decode_finite_instantiated_node (v,e,x)"
        by (rule exI[of _ v], rule exI[of _ e], rule exI[of _ y])
          (use actual result decoded_tree decoded_term in simp)
    next
      assume "\<exists>v e x. (s,v,e,x) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t) \<and>
        q=decode_finite_instantiated_node (v,e,x)"
      then obtain v k y where child: "(s,v,k,y) |\<in>| finite_schema_proof_children P (Schema_Proof c V B,d,t)"
        and decoded_result: "q=decode_finite_instantiated_node (v,k,y)" by blast
      obtain H where row: "(s,v) |\<in>| B" and reading: "H |\<in>| finite_admitted_premise_readings P d c V t"
        and call: "(s,k,y) |\<in>| H"
        using child by (simp only: finite_schema_proof_children_member; blast)
      have inst: "admitted_schema_instance (decode_finite_system P) d c
        (decode_finite_term_bindings V) (decode_finite_term t) (decode_finite_premises H)"
        by (simp only: finite_admitted_premise_readings_correct; rule exI[of _ H]; use reading in simp)
      have stored: "(s,decode_finite_proof v)\<in>fset (fimage (map_prod id decode_finite_proof) B)"
        by (simp only: decoded_proof_family_values map_relation_values_member; use row in blast)
      have premise: "(s,k,decode_finite_term y)\<in>decode_finite_premises H"
        by (simp only: decode_finite_premises_value_member; use call in blast)
      show "(s,q)\<in>schema_proof_children (decode_finite_system P)
        (decode_finite_instantiated_node (Schema_Proof c V B,d,t))"
        using stored inst premise by (auto simp: decoded_result decode_finite_proof_node schema_proof_children.simps)
    qed
  qed
  show ?thesis
  proof (rule set_eqI)
    fix z :: "'s\<times>('a,'s,'d,'c) instantiated_proof_node"
    obtain s q where shape: "z=(s,q)" by (cases z) auto
    show "(z\<in>fset (fimage (map_prod id decode_finite_instantiated_node) (finite_schema_proof_children P n))) =
      (z\<in>schema_proof_children (decode_finite_system P) (decode_finite_instantiated_node n))"
      using member[of s q]
      by (simp only: node tree shape finite_value_image_member split_paired_Ex; blast)
  qed
qed

lemma finite_schema_proof_children_decoded_member:
  "(s,q)\<in>schema_proof_children (decode_finite_system P) (decode_finite_instantiated_node n) \<longleftrightarrow>
    (\<exists>m. (s,m) |\<in>| finite_schema_proof_children P n \<and> q=decode_finite_instantiated_node m)"
  by (simp only: finite_schema_proof_children_correct[symmetric] finite_value_image_member)

lemma finite_schema_proof_child_size:
  assumes child: "(s,m) |\<in>| finite_schema_proof_children P n"
  shows "size (fst m)<size (fst n)"
proof -
  obtain p d t where node: "n=(p,d,t)" by (cases n) auto
  obtain c V B where tree: "p=Schema_Proof c V B" by (cases p) auto
  obtain q e x where result: "m=(q,e,x)" by (cases m) auto
  have member: "(s,q) |\<in>| B"
    using child by (simp only: node tree result finite_schema_proof_children_member; blast)
  show ?thesis using schema_proof_child_size[OF member, of c V]
    by (simp only: node tree result fst_conv)
qed

export_code finite_schema_proof_children checking SML

text \<open>
  Every child retains its complete certificate and actual required call.
  The original source reader supplies that call through the same indexed
  premise socket. Exact decoding recovers the existing child relation on all
  finite inputs, and each actual edge strictly decreases certificate size.
\<close>

end
