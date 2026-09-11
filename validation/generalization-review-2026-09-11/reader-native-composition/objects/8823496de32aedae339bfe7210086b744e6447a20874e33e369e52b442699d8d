theory Factor_Proof_Positions
  imports Factor_Derivation
begin

section \<open>Finite predecessors in a well-founded relation\<close>

lemma finite_well_founded_predecessors:
  assumes well_founded: "wf r" and branching: "\<And>a. finite {b. (b,a) \<in> r}"
  shows "finite {b. (b,a) \<in> r\<^sup>*}"
proof (induction a rule: wf_induct[OF well_founded])
  case (1 a)
  have decomposition: "{b. (b,a) \<in> r\<^sup>*} =
    insert a (\<Union>c\<in>{c. (c,a) \<in> r}. {b. (b,c) \<in> r\<^sup>*})"
    by (auto elim: rtrancl.cases intro: rtrancl_into_rtrancl)
  have finite: "finite (\<Union>c\<in>{c. (c,a) \<in> r}. {b. (b,c) \<in> r\<^sup>*})"
    by (rule finite_UN_I[OF branching]) (use "1.IH" in blast)
  show ?case using finite decomposition by simp
qed

section \<open>Private coordinates for a tree and its required call\<close>

type_synonym ('a,'s,'d,'c) instantiated_proof_node =
  "('a,'s,'c) schema_proof \<times> ('d \<times> factor_term)"

fun schema_proof_children ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) instantiated_proof_node \<Rightarrow>
    ('s \<times> ('a,'s,'d,'c) instantiated_proof_node) set" where
  "schema_proof_children P (Schema_Proof c V B,d,t) =
    {(s,(p,e,x)). (s,p) \<in> fset B \<and>
      (\<exists>Q. admitted_schema_instance P d c (fset V) t Q \<and> (s,e,x) \<in> Q)}"

declare schema_proof_children.simps [simp del]

definition instantiated_node_checked ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) instantiated_proof_node \<Rightarrow> bool" where
  "instantiated_node_checked P n \<longleftrightarrow>
    checks_schema_proof P (fst n) (fst (snd n)) (snd (snd n))"

lemma schema_proof_children_at_instance:
  assumes inst: "admitted_schema_instance P d c (fset V) t Q"
  shows "schema_proof_children P (Schema_Proof c V B,d,t) =
    {(s,(p,e,x)). (s,p) \<in> fset B \<and> (s,e,x) \<in> Q}"
proof -
  have unique: "\<And>W. admitted_schema_instance P d c (fset V) t W \<Longrightarrow> W=Q"
  proof -
    fix W assume other: "admitted_schema_instance P d c (fset V) t W"
    show "W=Q" using admitted_instance_unique[OF inst other] by simp
  qed
  have exact: "\<And>s e x. (\<exists>W. admitted_schema_instance P d c (fset V) t W \<and> (s,e,x) \<in> W)
    \<longleftrightarrow> (s,e,x) \<in> Q"
  proof -
    fix s e x
    show "(\<exists>W. admitted_schema_instance P d c (fset V) t W \<and> (s,e,x) \<in> W)
      \<longleftrightarrow> (s,e,x) \<in> Q"
    proof
      assume "\<exists>W. admitted_schema_instance P d c (fset V) t W \<and> (s,e,x) \<in> W"
      then obtain W where other: "admitted_schema_instance P d c (fset V) t W" "(s,e,x) \<in> W" by blast
      show "(s,e,x) \<in> Q" using unique[OF other(1)] other(2) by simp
    next
      assume member: "(s,e,x) \<in> Q"
      show "\<exists>W. admitted_schema_instance P d c (fset V) t W \<and> (s,e,x) \<in> W"
        by (rule exI[of _ Q]) (use inst member in simp)
    qed
  qed
  show ?thesis by (simp only: schema_proof_children.simps exact)
qed

lemma schema_proof_children_finite:
  "finite (schema_proof_children P n)"
proof -
  obtain tree d t where np: "n=(tree,d,t)" by (cases n) auto
  obtain c V B where tp: "tree=Schema_Proof c V B" by (cases tree) auto
  show ?thesis
  proof (cases "\<exists>Q. admitted_schema_instance P d c (fset V) t Q")
    case True
    then obtain Q where inst: "admitted_schema_instance P d c (fset V) t Q" by blast
    have qf: "finite Q" using admitted_instance_formed[OF inst] by blast
    have subset: "schema_proof_children P n \<subseteq>
      rel_dom (fset B) \<times> (rel_ran (fset B) \<times> rel_ran Q)"
      unfolding np tp schema_proof_children_at_instance[OF inst]
      by (auto simp: rel_dom_def rel_ran_def)
    show ?thesis
      by (rule finite_subset[OF subset])
         (simp add: finite_rel_dom finite_rel_ran qf)
  next
    case False
    then have "schema_proof_children P n = {}" by (simp add: np tp schema_proof_children.simps)
    then show ?thesis by simp
  qed
qed

lemma schema_proof_children_checked:
  assumes parent: "instantiated_node_checked P n"
    and child: "(s,m) \<in> schema_proof_children P n"
  shows "instantiated_node_checked P m"
proof -
  obtain tree d t where np: "n=(tree,d,t)" by (cases n) auto
  obtain c V B where tp: "tree=Schema_Proof c V B" by (cases tree) auto
  have checked: "checks_schema_proof P (Schema_Proof c V B) d t"
    using parent by (simp add: instantiated_node_checked_def np tp)
  obtain Q where inst: "admitted_schema_instance P d c (fset V) t Q"
    and domain: "rel_dom (fset B)=rel_dom Q"
    and sv: "single_valued (fset B)"
    and supplied: "\<forall>s p. (s,p) \<in> fset B \<longrightarrow>
      (\<exists>e x. (s,e,x) \<in> Q \<and> checks_schema_proof P p e x)"
    using checked by (auto simp only: checks_schema_proof_node)
  obtain p e x where mp: "m=(p,e,x)" and branch: "(s,p) \<in> fset B" "(s,e,x) \<in> Q"
    using child by (auto simp: np tp schema_proof_children_at_instance[OF inst])
  obtain q where support: "(s,q) \<in> fset B" "checks_schema_proof P q e x"
    using proof_premise_supported[OF inst domain supplied branch(2)] by blast
  have same: "p=q" by (rule single_valued_outputs[OF sv branch(1) support(1)])
  show ?thesis using support(2) same mp by (simp add: instantiated_node_checked_def)
qed

lemma schema_proof_children_single_valued:
  assumes parent: "instantiated_node_checked P n"
  shows "single_valued (schema_proof_children P n)"
proof -
  obtain tree d t where np: "n=(tree,d,t)" by (cases n) auto
  obtain c V B where tp: "tree=Schema_Proof c V B" by (cases tree) auto
  obtain Q where inst: "admitted_schema_instance P d c (fset V) t Q"
    and sv: "single_valued (fset B)"
    using parent by (auto simp: instantiated_node_checked_def np tp checks_schema_proof_node)
  have qsv: "single_valued Q" using admitted_instance_formed[OF inst] by blast
  show ?thesis using sv qsv
    by (auto simp: np tp schema_proof_children_at_instance[OF inst] single_valued_def; blast)
qed

lemma schema_proof_children_domain:
  assumes checked: "checks_schema_proof P (Schema_Proof c V B) d t"
    and inst: "admitted_schema_instance P d c (fset V) t Q"
  shows "rel_dom (schema_proof_children P (Schema_Proof c V B,d,t)) = rel_dom Q"
proof -
  obtain W where inst_other: "admitted_schema_instance P d c (fset V) t W"
    and domain: "rel_dom (fset B)=rel_dom W"
    using checked by (auto simp only: checks_schema_proof_node)
  have same: "W=Q" using admitted_instance_unique[OF inst inst_other] by simp
  have bd: "rel_dom (fset B)=rel_dom Q" using domain same by simp
  show ?thesis
  proof (rule set_eqI)
    fix s
    show "s \<in> rel_dom (schema_proof_children P (Schema_Proof c V B,d,t)) \<longleftrightarrow> s \<in> rel_dom Q"
    proof
      assume "s \<in> rel_dom (schema_proof_children P (Schema_Proof c V B,d,t))"
      then show "s \<in> rel_dom Q"
        by (auto simp: schema_proof_children_at_instance[OF inst] rel_dom_def)
    next
      assume key: "s \<in> rel_dom Q"
      have bk: "s \<in> rel_dom (fset B)" using key bd by simp
      obtain p where entry: "(s,p) \<in> fset B" using bk by (auto simp: rel_dom_def)
      obtain e x where premise: "(s,e,x) \<in> Q" using key by (auto simp: rel_dom_def)
      have child: "(s,p,e,x) \<in> schema_proof_children P (Schema_Proof c V B,d,t)"
        using entry premise by (simp add: schema_proof_children_at_instance[OF inst])
      show "s \<in> rel_dom (schema_proof_children P (Schema_Proof c V B,d,t))" by (rule rel_domI[OF child])
    qed
  qed
qed

section \<open>Exactly the reachable instantiated proof positions\<close>

definition schema_proof_edges ::
  "('a,'s,'d,'c) schema_system \<Rightarrow>
    (('a,'s,'d,'c) instantiated_proof_node \<times> ('a,'s,'d,'c) instantiated_proof_node) set" where
  "schema_proof_edges P = {(m,n). \<exists>s. (s,m) \<in> schema_proof_children P n}"

lemma schema_proof_edge_decreases:
  assumes "(m,n) \<in> schema_proof_edges P"
  shows "size (fst m) < size (fst n)"
proof -
  obtain tree d t where np: "n=(tree,d,t)" by (cases n) auto
  obtain c V B where tp: "tree=Schema_Proof c V B" by (cases tree) auto
  obtain s p e x where mp: "m=(p,e,x)" and member: "(s,p) \<in> fset B"
    using assms by (auto simp: schema_proof_edges_def np tp schema_proof_children.simps)
  show ?thesis using schema_proof_child_size[OF member, of c V] by (simp add: np tp mp)
qed

lemma schema_proof_edges_well_founded:
  "wf (schema_proof_edges P)"
proof -
  have subset: "schema_proof_edges P \<subseteq> measure (size \<circ> fst)"
    using schema_proof_edge_decreases[of _ _ P] by auto
  show ?thesis by (rule wf_subset[OF wf_measure subset])
qed

lemma schema_proof_edges_finitely_branching:
  "finite {m. (m,n) \<in> schema_proof_edges P}"
proof -
  have same: "{m. (m,n) \<in> schema_proof_edges P} = rel_ran (schema_proof_children P n)"
    by (auto simp: schema_proof_edges_def rel_ran_def)
  show ?thesis unfolding same by (rule finite_rel_ran[OF schema_proof_children_finite])
qed

definition schema_proof_positions ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) instantiated_proof_node \<Rightarrow>
    ('a,'s,'d,'c) instantiated_proof_node set" where
  "schema_proof_positions P root = {n. (n,root) \<in> (schema_proof_edges P)\<^sup>*}"

lemma schema_proof_positions_finite:
  "finite (schema_proof_positions P root)"
  unfolding schema_proof_positions_def
  by (rule finite_well_founded_predecessors[OF schema_proof_edges_well_founded
      schema_proof_edges_finitely_branching])

lemma schema_proof_positions_root [simp]:
  "root \<in> schema_proof_positions P root"
  by (simp add: schema_proof_positions_def)

lemma schema_proof_positions_closed:
  assumes inside: "n \<in> schema_proof_positions P root"
    and child: "(s,m) \<in> schema_proof_children P n"
  shows "m \<in> schema_proof_positions P root"
proof -
  have edge: "(m,n) \<in> schema_proof_edges P"
    using child by (auto simp: schema_proof_edges_def)
  have path: "(n,root) \<in> (schema_proof_edges P)\<^sup>*"
    using inside by (simp add: schema_proof_positions_def)
  have "(m,root) \<in> (schema_proof_edges P)\<^sup>*"
    by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] path])
  then show ?thesis by (simp add: schema_proof_positions_def)
qed

lemma schema_proof_positions_checked:
  assumes root: "instantiated_node_checked P r" and member: "n \<in> schema_proof_positions P r"
  shows "instantiated_node_checked P n"
proof -
  have path: "(n,r) \<in> (schema_proof_edges P)\<^sup>*"
    using member by (simp add: schema_proof_positions_def)
  have descent: "\<And>m k. (m,k) \<in> schema_proof_edges P \<Longrightarrow>
    instantiated_node_checked P k \<Longrightarrow> instantiated_node_checked P m"
    using schema_proof_children_checked[of P] by (auto simp: schema_proof_edges_def)
  have "instantiated_node_checked P r \<longrightarrow> instantiated_node_checked P n"
    using path by (induction rule: rtrancl_induct) (use descent in blast)+
  then show ?thesis using root by blast
qed

text \<open>
  These positions are construction coordinates for flattening an existing
  certificate. Including the required call keeps identical certificate values
  used at different calls from being accidentally shared. The graph validator
  never inspects a position's representation. A subsequent injective finite
  readdressing can replace all such private coordinates.

  The child relation uses only the selected finite rule instance and premise
  sockets. Strict certificate-size descent and finite branching prove that its
  entire root closure is finite; no truth search or retention premise is used.
\<close>

end
