theory Factor_Proof_Schemes
  imports Factor_Inference_Value_Maps Factor_Pattern_Bindings
begin

section \<open>Symbolic bindings use the existing graph geometry\<close>

type_synonym ('a,'s,'c,'n,'b) schema_proof_scheme =
  "('a,'s,'c,'n,'b term_pattern) inference_graph"

fun checks_schema_scheme_node ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow> 'n \<Rightarrow>
    ('a,'c,'b term_pattern) inference_node \<Rightarrow> bool" where
  "checks_schema_scheme_node P G J n Schema_Assertion \<longleftrightarrow> schema_graph_premises G n={}"
| "checks_schema_scheme_node P G J n (Schema_Inference c V) \<longleftrightarrow>
    (\<exists>S. ((fst (rel_value J n),c),S)\<in>system_clauses P \<and>
      pattern_bindings_formed (schema_variables S) (fset V) \<and>
      snd (rel_value J n)=pattern_substitute (rel_value (fset V)) (schema_conclusion S) \<and>
      rel_dom (schema_graph_premises G n)=rel_dom (schema_premises S) \<and>
      (\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
        (m,fst (rel_value (schema_premises S) s),
          pattern_substitute (rel_value (fset V)) (snd (rel_value (schema_premises S) s)))\<in>J))"

definition schema_scheme_reading ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> 'b term_pattern \<Rightarrow>
    ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow> bool" where
  "schema_scheme_reading P G root d p J \<longleftrightarrow>
    schema_system_formed P \<and> schema_graph_formed G root \<and>
    single_valued J \<and> rel_dom J=schema_graph_nodes G \<and> (root,d,p)\<in>J \<and>
    (\<forall>n e q. (n,e,q)\<in>J \<longrightarrow> schema_pattern_call P e q) \<and>
    (\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> checks_schema_scheme_node P G J n A)"

lemma schema_scheme_reading_finite:
  "schema_scheme_reading P G root d p J \<Longrightarrow> finite J"
  using finite_single_valued[of J] by (auto simp: schema_scheme_reading_def)

lemma schema_scheme_reading_value:
  assumes read: "schema_scheme_reading P G root d p J" and key: "n\<in>schema_graph_nodes G"
  shows "(n,rel_value J n)\<in>J"
proof -
  have domain: "n\<in>rel_dom J" using read key by (auto simp: schema_scheme_reading_def)
  obtain q where row: "(n,q)\<in>J" using domain by (auto simp: rel_dom_def)
  have sv: "single_valued J" using read by (simp add: schema_scheme_reading_def)
  show ?thesis using row rel_value_eq[OF sv row] by simp
qed

fun scheme_node_variables :: "('a,'c,'b term_pattern) inference_node \<Rightarrow> 'b set" where
  "scheme_node_variables Schema_Assertion={}"
| "scheme_node_variables (Schema_Inference c V)=pattern_binding_variables (fset V)"

definition schema_scheme_variables ::
  "('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow> 'b set" where
  "schema_scheme_variables G J=(\<Union>(n,A)\<in>fset (graph_inferences G). scheme_node_variables A) \<union>
    (\<Union>(n,d,p)\<in>J. pattern_variables p)"

lemma schema_scheme_variables_finite:
  assumes "schema_scheme_reading P G root d p J"
  shows "finite (schema_scheme_variables G J)"
proof -
  have nodes: "finite (scheme_node_variables A)" for A
    by (cases A) (auto intro: pattern_binding_variables_finite)
  show ?thesis using schema_scheme_reading_finite[OF assms]
    by (auto simp: schema_scheme_variables_def nodes intro: finite_UN_I split: prod.splits)
qed

lemma schema_scheme_binding_scope:
  "(n,Schema_Inference c V)\<in>fset (graph_inferences G) \<Longrightarrow>
    pattern_binding_variables (fset V)\<subseteq>schema_scheme_variables G J"
  by (auto simp: schema_scheme_variables_def)

lemma schema_scheme_claim_scope:
  "(n,d,p)\<in>J \<Longrightarrow> pattern_variables p\<subseteq>schema_scheme_variables G J"
  by (auto simp: schema_scheme_variables_def)

section \<open>Material assumptions are derived from the actual inference occurrences\<close>

fun scheme_node_materials ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow>
    'n \<Rightarrow> ('a,'c,'b term_pattern) inference_node \<Rightarrow>
    (('n\<times>'s)\<times>'b material_pattern) set" where
  "scheme_node_materials P J n Schema_Assertion={}"
| "scheme_node_materials P J n (Schema_Inference c V)=
    (\<lambda>(s,M). ((n,s),material_pattern_substitute (rel_value (fset V)) M)) `
      schema_material_premises (rel_value (system_clauses P) (fst (rel_value J n),c))"

definition schema_scheme_materials ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c,'n,'b) schema_proof_scheme \<Rightarrow>
    ('n\<times>('d\<times>'b term_pattern)) set \<Rightarrow> (('n\<times>'s)\<times>'b material_pattern) set" where
  "schema_scheme_materials P G J=(\<Union>(n,A)\<in>fset (graph_inferences G). scheme_node_materials P J n A)"

lemma schema_scheme_material_member:
  assumes read: "schema_scheme_reading P G root d p J"
    and node: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
    and clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
    and material: "(s,M)\<in>schema_material_premises S"
  shows "((n,s),material_pattern_substitute (rel_value (fset V)) M)\<in>schema_scheme_materials P G J"
proof -
  have sv: "single_valued (system_clauses P)"
    using read by (simp add: schema_scheme_reading_def schema_system_formed_def)
  have source: "rel_value (system_clauses P) (fst (rel_value J n),c)=S"
    by (rule rel_value_eq[OF sv clause])
  show ?thesis unfolding schema_scheme_materials_def
    by (rule UN_I[OF node]) (use material in \<open>auto simp: source\<close>)
qed

lemma schema_scheme_materials_finite:
  assumes read: "schema_scheme_reading P G root d p J"
  shows "finite (schema_scheme_materials P G J)"
proof -
  have each: "finite (scheme_node_materials P J n A)"
    if node: "(n,A)\<in>fset (graph_inferences G)" for n A
  proof (cases A)
    case Schema_Assertion
    then show ?thesis by simp
  next
    case (Schema_Inference c V)
    have checked: "checks_schema_scheme_node P G J n (Schema_Inference c V)"
      using read node Schema_Inference unfolding schema_scheme_reading_def by blast
    obtain S where clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
      using checked by auto
    have sv: "single_valued (system_clauses P)" and sf: "schema_formed S"
      using read clause by (auto simp: schema_scheme_reading_def schema_system_formed_def)
    have source: "rel_value (system_clauses P) (fst (rel_value J n),c)=S"
      by (rule rel_value_eq[OF sv clause])
    show ?thesis using sf by (simp add: Schema_Inference source schema_formed_def)
  qed
  show ?thesis unfolding schema_scheme_materials_def by (rule finite_UN_I) (use each in auto)
qed

lemma schema_scheme_materials_functional:
  assumes read: "schema_scheme_reading P G root d p J"
  shows "single_valued (schema_scheme_materials P G J)"
proof -
  have nodes: "single_valued (fset (graph_inferences G))"
    and system: "schema_system_formed P"
    using read by (auto simp: schema_scheme_reading_def schema_graph_formed_def)
  have each: "single_valued (scheme_node_materials P J n A)"
    if node: "(n,A)\<in>fset (graph_inferences G)" for n A
  proof (cases A)
    case Schema_Assertion
    then show ?thesis by (simp add: single_valued_def)
  next
    case (Schema_Inference c V)
    have checked: "checks_schema_scheme_node P G J n (Schema_Inference c V)"
      using read node Schema_Inference unfolding schema_scheme_reading_def by blast
    obtain S where clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
      using checked by auto
    have sv: "single_valued (system_clauses P)" and mat: "single_valued (schema_material_premises S)"
      using system clause by (auto simp: schema_system_formed_def schema_formed_def)
    have source: "rel_value (system_clauses P) (fst (rel_value J n),c)=S"
      by (rule rel_value_eq[OF sv clause])
    show ?thesis using mat by (auto simp: Schema_Inference source single_valued_def; blast)
  qed
  have origin: "((k,s),M)\<in>scheme_node_materials P J n A \<Longrightarrow> k=n" for k s M n A
    by (cases A) auto
  show ?thesis using nodes each origin
    by (auto simp: single_valued_def schema_scheme_materials_def; metis)
qed

section \<open>Every admissible valuation produces an ordinary checked graph\<close>

lemma schema_scheme_valued_call:
  assumes read: "schema_scheme_reading P G root d p J"
    and valuation: "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    and row: "(n,e,q)\<in>J"
  shows "schema_call_formed P e (evaluate_pattern h q)"
  by (rule schema_pattern_call_evaluation)
    (use read valuation schema_scheme_claim_scope[OF row] row in \<open>auto simp: schema_scheme_reading_def\<close>)

lemma schema_scheme_node_evaluation:
  assumes read: "schema_scheme_reading P G root d p J"
    and valuation: "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    and materials: "\<forall>k M. (k,M)\<in>schema_scheme_materials P G J \<longrightarrow> evaluate_material_satisfaction h M"
    and node: "(n,A)\<in>fset (graph_inferences G)"
  shows "checks_schema_graph_node P (map_inference_values (evaluate_pattern h) G)
    (map_relation_values (map_prod id (evaluate_pattern h)) J) n (map_inference_node (evaluate_pattern h) A)"
proof -
  let ?K="map_relation_values (map_prod id (evaluate_pattern h)) J"
  let ?F="map_inference_values (evaluate_pattern h) G"
  have inside: "n\<in>schema_graph_nodes G" using node by (auto simp: schema_graph_nodes_def rel_dom_def)
  have jsv: "single_valued J" and keys: "rel_dom J=schema_graph_nodes G"
    and checked: "checks_schema_scheme_node P G J n A"
    using read node by (auto simp: schema_scheme_reading_def)
  have jrow: "(n,rel_value J n)\<in>J" by (rule schema_scheme_reading_value[OF read inside])
  have claim: "rel_value ?K n=(fst (rel_value J n),evaluate_pattern h (snd (rel_value J n)))"
    using map_relation_values_value[OF jsv, of n "map_prod id (evaluate_pattern h)"] inside keys
    by (simp add: map_prod_def split_def)
  have call: "schema_call_formed P (fst (rel_value J n)) (evaluate_pattern h (snd (rel_value J n)))"
    by (rule schema_scheme_valued_call[OF read valuation]) (use jrow in simp)
  show ?thesis
  proof (cases A)
    case Schema_Assertion
    show ?thesis using checked call by (simp add: Schema_Assertion claim)
  next
    case (Schema_Inference c V)
    let ?s="rel_value (fset V)"
    let ?g="\<lambda>a. evaluate_pattern h (?s a)"
    let ?W="fimage (map_prod id (evaluate_pattern h)) V"
    obtain S where clause: "((fst (rel_value J n),c),S)\<in>system_clauses P"
      and bindings: "pattern_bindings_formed (schema_variables S) (fset V)"
      and head: "snd (rel_value J n)=pattern_substitute ?s (schema_conclusion S)"
      and domain: "rel_dom (schema_graph_premises G n)=rel_dom (schema_premises S)"
      and children: "\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
        (m,fst (rel_value (schema_premises S) s),pattern_substitute ?s (snd (rel_value (schema_premises S) s)))\<in>J"
      using checked by (simp only: Schema_Inference checks_schema_scheme_node.simps) blast
    have sf: "schema_formed S" using read clause by (auto simp: schema_scheme_reading_def schema_system_formed_def)
    have scope: "pattern_binding_variables (fset V)\<subseteq>schema_scheme_variables G J"
      by (rule schema_scheme_binding_scope) (use node Schema_Inference in simp)
    have assignment: "\<forall>a\<in>schema_variables S. term_formed (?g a)"
    proof (intro ballI)
      fix a assume key: "a\<in>schema_variables S"
      show "term_formed (?g a)"
        by (rule evaluate_pattern_formed[OF pattern_binding_at(2)[OF bindings key]])
          (use valuation scope pattern_binding_at(3)[OF bindings key] in blast)
    qed
    have evaluated: "fset ?W=(\<lambda>a. (a,?g a)) ` schema_variables S"
      using pattern_bindings_evaluation_graph[OF bindings, of h]
      by (simp add: map_relation_values_def map_prod_def)
    let ?Q="evaluate_schema_premises ?g S"
    have inst: "schema_instance S (fset ?W) (evaluate_pattern h (snd (rel_value J n))) ?Q"
      using schema_evaluation_instance[OF sf assignment]
      by (simp only: evaluated head evaluate_pattern_substitute)
    have observed: "evaluate_material_satisfaction ?g M" if member: "(s,M)\<in>schema_material_premises S" for s M
    proof -
      have boundary: "((n,s),material_pattern_substitute ?s M)\<in>schema_scheme_materials P G J"
        by (rule schema_scheme_material_member[OF read _ clause member]) (use node Schema_Inference in simp)
      have target: "evaluate_material_satisfaction h (material_pattern_substitute ?s M)"
        using materials boundary by blast
      show ?thesis using target by simp
    qed
    have mat: "schema_material_satisfied S (fset ?W)"
      using schema_material_evaluation[OF inst, of ?g] observed by (simp only: evaluated) simp
    have psv: "single_valued (schema_premises S)" using sf by (simp add: schema_formed_def)
    have supplied: "(m,e,pattern_substitute ?s q)\<in>J"
      if original: "(s,e,q)\<in>schema_premises S" and discharge: "(s,m)\<in>schema_graph_premises G n" for s e q m
    proof -
      have rv: "rel_value (schema_premises S) s=(e,q)" by (rule rel_value_eq[OF psv original])
      have row: "(m,fst (rel_value (schema_premises S) s),
          pattern_substitute ?s (snd (rel_value (schema_premises S) s)))\<in>J"
        using children discharge by blast
      show ?thesis using row by (simp only: rv fst_conv snd_conv)
    qed
    have all_calls: "schema_call_formed P e x" if member: "(s,e,x)\<in>?Q" for s e x
    proof -
      obtain q where original: "(s,e,q)\<in>schema_premises S" and xp: "x=evaluate_pattern ?g q"
        using member by auto
      obtain m where discharge: "(s,m)\<in>schema_graph_premises G n"
        using domain original by (auto simp: rel_dom_def)
      have row: "(m,e,pattern_substitute ?s q)\<in>J" by (rule supplied[OF original discharge])
      show ?thesis using schema_scheme_valued_call[OF read valuation row] by (simp add: xp)
    qed
    have admitted: "admitted_schema_instance P (fst (rel_value J n)) c (fset ?W)
        (evaluate_pattern h (snd (rel_value J n))) ?Q"
      using call clause inst mat all_calls by (auto simp: admitted_schema_instance_def)
    have qdom: "rel_dom ?Q=rel_dom (schema_premises S)"
      using schema_instance_socket_boundary[OF inst] by blast
    have qsv: "single_valued ?Q" using schema_instance_socket_boundary[OF inst] by blast
    have joined: "(m,rel_value ?Q s)\<in>?K" if discharge: "(s,m)\<in>schema_graph_premises G n" for s m
    proof -
      obtain e q where original: "(s,e,q)\<in>schema_premises S"
        using domain discharge by (auto simp: rel_dom_def; blast)
      have ground: "(s,e,evaluate_pattern ?g q)\<in>?Q" using original by auto
      have rv: "rel_value ?Q s=(e,evaluate_pattern ?g q)" by (rule rel_value_eq[OF qsv ground])
      have row: "(m,e,pattern_substitute ?s q)\<in>J" by (rule supplied[OF original discharge])
      show ?thesis using row by (auto simp: rv map_prod_def)
    qed
    show ?thesis unfolding Schema_Inference map_inference_node.simps checks_schema_graph_node.simps claim
      by (rule exI[of _ ?Q]) (use admitted domain qdom joined in auto)
  qed
qed

theorem schema_scheme_instantiates:
  assumes read: "schema_scheme_reading P G root d p J"
    and valuation: "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    and materials: "\<forall>k M. (k,M)\<in>schema_scheme_materials P G J \<longrightarrow> evaluate_material_satisfaction h M"
  shows "schema_graph_reading P (map_inference_values (evaluate_pattern h) G) root d (evaluate_pattern h p)
    (map_relation_values (map_prod id (evaluate_pattern h)) J)"
proof -
  have graph: "schema_graph_formed G root" and sv: "single_valued J"
    and keys: "rel_dom J=schema_graph_nodes G" and root: "(root,d,p)\<in>J"
    using read by (auto simp: schema_scheme_reading_def)
  have formed: "schema_graph_formed (map_inference_values (evaluate_pattern h) G) root"
    by (rule map_inference_values_formed[OF graph])
  have every: "checks_schema_graph_node P (map_inference_values (evaluate_pattern h) G)
      (map_relation_values (map_prod id (evaluate_pattern h)) J) n A"
    if "(n,A)\<in>fset (graph_inferences (map_inference_values (evaluate_pattern h) G))" for n A
    using that schema_scheme_node_evaluation[OF read valuation materials]
    by (auto simp: map_inference_values_node)
  show ?thesis using formed map_relation_values_preserves_functional[OF sv] keys root every
    by (auto simp: schema_graph_reading_def map_prod_def)
qed

theorem schema_scheme_derives:
  assumes read: "schema_scheme_reading P G root d p J"
    and valuation: "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    and materials: "\<forall>k M. (k,M)\<in>schema_scheme_materials P G J \<longrightarrow> evaluate_material_satisfaction h M"
  shows "schema_graph_derives P (map_inference_values (evaluate_pattern h) G) root d (evaluate_pattern h p)
    (map_relation_values (map_prod id (evaluate_pattern h)) (schema_graph_assumptions G J))"
  using schema_scheme_instantiates[OF read valuation materials]
  by (auto simp: schema_graph_derives_def map_inference_values_assumptions)

theorem schema_scheme_conditional_sound:
  assumes read: "schema_scheme_reading P G root d p J"
    and valuation: "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    and materials: "\<forall>k M. (k,M)\<in>schema_scheme_materials P G J \<longrightarrow> evaluate_material_satisfaction h M"
    and assertions: "\<And>n e q. (n,e,q)\<in>schema_graph_assumptions G J \<Longrightarrow>
      (e,evaluate_pattern h q)\<in>positive_meaning P"
  shows "(d,evaluate_pattern h p)\<in>positive_meaning P"
  by (rule schema_graph_conditional_sound[OF schema_scheme_derives[OF read valuation materials]])
    (use assertions in \<open>auto simp: map_prod_def\<close>)

corollary schema_scheme_closed_sound:
  assumes "schema_scheme_reading P G root d p J"
    "\<forall>a\<in>schema_scheme_variables G J. term_formed (h a)"
    "schema_scheme_materials P G J={}" "schema_graph_assumptions G J={}"
  shows "(d,evaluate_pattern h p)\<in>positive_meaning P"
  by (rule schema_scheme_conditional_sound[OF assms(1,2)]) (use assms(3,4) in auto)

text \<open>
  A scheme retains the actual clause occurrence at every inference and a
  complete finite pattern replacement for its binder. The existing graph
  rules retain every premise socket and every separate assertion occurrence.
  The complete claim reading checks each actual program interface with its
  independently scoped specialization witness.

  Both variable and material boundaries are derived. Material assumptions
  retain each inference-node and material-socket pair and all five substituted
  operands. They are not assertions of truth at marker valuations. For every
  formed valuation satisfying these material assumptions, evaluation gives
  an ordinary checked derivation graph with exactly the evaluated assertion
  boundary. Conditional soundness therefore follows from the existing graph
  theorem. A scheme with no material assumptions or assertion nodes proves
  every formed instance.

  This establishes a finite mathematical proof scheme for the existing
  positive system. Native presentation and checking of the symbolic scheme
  relation require their own exact construction and are not assumed here.
\<close>

end
