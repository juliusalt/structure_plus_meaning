theory Factor_Graph_Transport
  imports Factor_Graph_Renaming Factor_Proof_Flattening
begin

section \<open>The complete claim assignment moves with its private nodes\<close>

lemma schema_graph_renamed_claims:
  assumes read: "schema_graph_reading P G root d t J"
    and injective: "inj_on f (schema_graph_nodes G)"
  shows "single_valued (map_prod f id ` J)"
    and "rel_dom (map_prod f id ` J) = f ` schema_graph_nodes G"
proof -
  have sv: "single_valued J" and domain: "rel_dom J = schema_graph_nodes G"
    using read by (auto simp: schema_graph_reading_def)
  have inj: "inj_on f (rel_dom J)" using injective domain by simp
  show "single_valued (map_prod f id ` J)"
    using single_valued_pair_image[OF sv inj, where g=id] by (simp add: map_prod_def)
  show "rel_dom (map_prod f id ` J) = f ` schema_graph_nodes G"
    using pair_image_domain[where R=J and f=f and g=id] domain by (simp add: map_prod_def)
qed

lemma schema_graph_renamed_claim_value:
  assumes read: "schema_graph_reading P G root d t J"
    and injective: "inj_on f (schema_graph_nodes G)" and inside: "n \<in> schema_graph_nodes G"
  shows "rel_value (map_prod f id ` J) (f n) = rel_value J n"
proof -
  have source: "(n,rel_value J n) \<in> J" by (rule schema_graph_reading_value[OF read inside])
  have copied: "(f n,rel_value J n) \<in> map_prod f id ` J"
    using imageI[OF source, of "map_prod f id"] by simp
  show ?thesis by (rule rel_value_eq[OF schema_graph_renamed_claims(1)[OF read injective] copied])
qed

lemma checks_schema_graph_node_rename:
  assumes read: "schema_graph_reading P G root d t J"
    and injective: "inj_on f (schema_graph_nodes G)" and inside: "n \<in> schema_graph_nodes G"
    and checked: "checks_schema_graph_node P G J n A"
  shows "checks_schema_graph_node P (rename_schema_graph f G) (map_prod f id ` J) (f n) A"
proof -
  let ?F = "rename_schema_graph f G"
  let ?L = "map_prod f id ` J"
  have formed: "schema_graph_formed G root" using read by (simp add: schema_graph_reading_def)
  have rv: "rel_value ?L (f n)=rel_value J n"
    by (rule schema_graph_renamed_claim_value[OF read injective inside])
  have edges: "schema_graph_premises ?F (f n) = map_prod id f ` schema_graph_premises G n"
    by (rule schema_graph_renamed_premises[OF formed injective inside])
  show ?thesis
  proof (cases A)
    case Schema_Assertion
    then show ?thesis using checked rv edges by simp
  next
    case (Schema_Inference c V)
    obtain Q where inst: "admitted_schema_instance P (fst (rel_value J n)) c (fset V) (snd (rel_value J n)) Q"
      and domain: "rel_dom (schema_graph_premises G n)=rel_dom Q"
      and supplied: "\<forall>s m. (s,m) \<in> schema_graph_premises G n \<longrightarrow> (m,rel_value Q s) \<in> J"
      using checked Schema_Inference by auto
    have mapped_domain: "rel_dom (schema_graph_premises ?F (f n))=rel_dom Q"
      using pair_image_domain[where R="schema_graph_premises G n" and f=id and g=f] domain edges
      by (simp add: map_prod_def)
    have children: "\<forall>s m. (s,m) \<in> schema_graph_premises ?F (f n) \<longrightarrow> (m,rel_value Q s) \<in> ?L"
    proof (intro allI impI)
      fix s m assume member: "(s,m) \<in> schema_graph_premises ?F (f n)"
      obtain k where old: "(s,k) \<in> schema_graph_premises G n" "m=f k"
        using member edges by (auto simp: map_prod_def)
      have source: "(k,rel_value Q s) \<in> J" using supplied old(1) by blast
      have "(f k,rel_value Q s) \<in> ?L" using imageI[OF source, of "map_prod f id"] by simp
      then show "(m,rel_value Q s) \<in> ?L" using old(2) by simp
    qed
    show ?thesis unfolding Schema_Inference checks_schema_graph_node.simps
      by (rule exI[of _ Q]) (use inst rv mapped_domain children in simp)
  qed
qed

theorem schema_graph_reading_rename:
  assumes read: "schema_graph_reading P G root d t J"
    and injective: "inj_on f (schema_graph_nodes G)"
  shows "schema_graph_reading P (rename_schema_graph f G) (f root) d t (map_prod f id ` J)"
proof -
  let ?F = "rename_schema_graph f G"
  let ?L = "map_prod f id ` J"
  have formed: "schema_graph_formed G root" and root: "(root,d,t) \<in> J"
    using read by (auto simp: schema_graph_reading_def)
  have ff: "schema_graph_formed ?F (f root)" by (rule renamed_schema_graph_formed[OF formed injective])
  have copied_root: "(f root,d,t) \<in> ?L"
    using imageI[OF root, of "map_prod f id"] by simp
  have nodes: "\<forall>n A. (n,A) \<in> fset (graph_inferences ?F) \<longrightarrow> checks_schema_graph_node P ?F ?L n A"
  proof (intro allI impI)
    fix n A assume member: "(n,A) \<in> fset (graph_inferences ?F)"
    obtain m where source: "(m,A) \<in> fset (graph_inferences G)" and np: "n=f m"
      using member by (auto simp: schema_graph_renamed_node)
    have inside: "m \<in> schema_graph_nodes G"
      using rel_domI[OF source] by (simp add: schema_graph_nodes_def)
    have checked: "checks_schema_graph_node P G J m A"
      using read source unfolding schema_graph_reading_def by blast
    show "checks_schema_graph_node P ?F ?L n A"
      using checks_schema_graph_node_rename[OF read injective inside checked] np by simp
  qed
  show ?thesis using ff copied_root nodes schema_graph_renamed_claims[OF read injective]
    by (simp add: schema_graph_reading_def schema_graph_renamed_nodes)
qed

theorem schema_graph_assumptions_rename:
  assumes read: "schema_graph_reading P G root d t J"
    and injective: "inj_on f (schema_graph_nodes G)"
  shows "schema_graph_assumptions (rename_schema_graph f G) (map_prod f id ` J) =
    map_prod f id ` schema_graph_assumptions G J"
proof
  let ?F = "rename_schema_graph f G"
  let ?L = "map_prod f id ` J"
  show "schema_graph_assumptions ?F ?L \<subseteq> map_prod f id ` schema_graph_assumptions G J"
  proof
    fix z assume member: "z \<in> schema_graph_assumptions ?F ?L"
    obtain n q where zp: "z=(n,q)" by (cases z) auto
    have node: "(n,Schema_Assertion) \<in> fset (graph_inferences ?F)" and entry: "(n,q) \<in> ?L"
      using member zp by (auto simp: schema_graph_assumptions_def)
    obtain a where old_node: "(a,Schema_Assertion) \<in> fset (graph_inferences G)" and na: "n=f a"
      using node by (auto simp: schema_graph_renamed_node)
    obtain b where old_claim: "(b,q) \<in> J" and nb: "n=f b"
      using entry by (simp only: key_image_member) blast
    have a: "a \<in> schema_graph_nodes G"
      using rel_domI[OF old_node] by (simp add: schema_graph_nodes_def)
    have b: "b \<in> schema_graph_nodes G"
      using rel_domI[OF old_claim] read by (simp add: schema_graph_reading_def)
    have eq: "f a=f b" using na nb by simp
    have same: "a=b" by (rule inj_onD[OF injective eq a b])
    have assertion: "(a,q) \<in> schema_graph_assumptions G J"
      using old_node old_claim same by (simp add: schema_graph_assumptions_def)
    show "z \<in> map_prod f id ` schema_graph_assumptions G J"
      by (rule rev_image_eqI[OF assertion]) (use zp na in simp)
  qed
  show "map_prod f id ` schema_graph_assumptions G J \<subseteq> schema_graph_assumptions ?F ?L"
    by (auto simp: map_prod_def schema_graph_assumptions_def schema_graph_renamed_node key_image_member; blast)
qed

theorem schema_graph_derives_rename:
  assumes derived: "schema_graph_derives P G root d t H"
    and injective: "inj_on f (schema_graph_nodes G)"
  shows "schema_graph_derives P (rename_schema_graph f G) (f root) d t (map_prod f id ` H)"
proof -
  obtain J where read: "schema_graph_reading P G root d t J"
    and boundary: "H=schema_graph_assumptions G J"
    using derived unfolding schema_graph_derives_def by blast
  have copied: "schema_graph_reading P (rename_schema_graph f G) (f root) d t (map_prod f id ` J)"
    by (rule schema_graph_reading_rename[OF read injective])
  have exact: "map_prod f id ` H = schema_graph_assumptions (rename_schema_graph f G) (map_prod f id ` J)"
    using schema_graph_assumptions_rename[OF read injective] boundary by simp
  show ?thesis unfolding schema_graph_derives_def
    by (rule exI[of _ "map_prod f id ` J"]) (use copied exact in simp)
qed

section \<open>Every positive judgment has an addressed closed proof graph\<close>

theorem addressed_schema_graph_complete:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes meaning: "(d,t) \<in> positive_meaning P"
  shows "\<exists>G :: ('a,'s,'c,local_address) schema_derivation_graph. \<exists>root.
    schema_graph_derives P G root d t {} \<and>
    (\<forall>n\<in>schema_graph_nodes G. octets_formed n)"
proof -
  obtain G :: "('a,'s,'c,('a,'s,'d,'c) instantiated_proof_node) schema_derivation_graph"
    and root where derived: "schema_graph_derives P G root d t {}"
    using schema_graph_complete[OF meaning] by blast
  obtain f where addressing: "finite_addressing (schema_graph_nodes G) f"
    using finite_addressing_exists[OF schema_graph_nodes_finite, of G] by blast
  have injective: "inj_on f (schema_graph_nodes G)"
    using addressing by (simp add: finite_addressing_def)
  have copied: "schema_graph_derives P (rename_schema_graph f G) (f root) d t {}"
    using schema_graph_derives_rename[OF derived injective] by simp
  show ?thesis
    by (rule exI[of _ "rename_schema_graph f G"], rule exI[of _ "f root"])
       (use copied addressing in \<open>auto simp: schema_graph_renamed_nodes finite_addressing_def\<close>)
qed

text \<open>
  The exact recovered claim and assumption graphs move only through the declared
  injective node map. Definitions, complete arguments, clauses, variable
  bindings, and premise sockets stay fixed. Every positive judgment therefore
  has a finite closed graph whose node coordinates are formed local addresses,
  ready for a separate structural realization.
\<close>

end
