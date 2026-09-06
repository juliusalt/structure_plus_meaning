theory Factor_Executable_Recovery
  imports Factor_Executable_Propagation
begin

section \<open>The root call determines a finite candidate reading\<close>

definition finite_claim_key :: "('n \<times> ('d \<times> finite_factor_term)) \<Rightarrow> ('n \<times> 'd)" where
  "finite_claim_key q = (fst q,fst (snd q))"

lemma finite_claim_key_pair [simp]: "finite_claim_key (n,d,t)=(n,d)"
  by (simp add: finite_claim_key_def)

definition finite_graph_claims ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('n \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_graph_claims P G root d t =
    finite_reachable_outputs finite_claim_key (finite_graph_transitions P G) (root,d,t)"

lemma finite_graph_claims_member:
  "(n,e,u) |\<in>| finite_graph_claims P G root d t \<longleftrightarrow>
    (n,e,u)=(root,d,t) \<or>
    (\<exists>k. (k,(n,e,u)) |\<in>| finite_graph_transitions P G \<and>
      ((root,d),k) \<in> (fset (finite_transition_keys finite_claim_key (finite_graph_transitions P G)))\<^sup>*)"
  by (simp add: finite_graph_claims_def finite_reachable_outputs_member)

lemma finite_graph_keys_reachable:
  assumes read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G) root d t J"
    and inside: "n \<in> schema_graph_nodes (decode_finite_graph G)"
  shows "((root,d),(n,fst (rel_value J n))) \<in>
    (fset (finite_transition_keys finite_claim_key (finite_graph_transitions P G)))\<^sup>*"
proof -
  let ?E = "fset (finite_transition_keys finite_claim_key (finite_graph_transitions P G))"
  have edges: "\<And>a b. (a,b) \<in> schema_graph_edges (decode_finite_graph G) \<Longrightarrow>
      ((b,fst (rel_value J b)),(a,fst (rel_value J a))) \<in> ?E"
  proof -
    fix a b assume edge: "(a,b) \<in> schema_graph_edges (decode_finite_graph G)"
    obtain e u where trans: "((b,fst (rel_value J b)),(a,e,u)) |\<in>| finite_graph_transitions P G"
      and rv: "rel_value J a=(e,decode_finite_term u)"
      using finite_graph_edge_transition[OF read edge] by blast
    show "((b,fst (rel_value J b)),(a,fst (rel_value J a))) \<in> ?E"
      using trans rv by (auto simp: finite_transition_keys_member; force)
  qed
  have paths: "\<And>a b. (a,b) \<in> (schema_graph_edges (decode_finite_graph G))\<^sup>* \<Longrightarrow>
      ((b,fst (rel_value J b)),(a,fst (rel_value J a))) \<in> ?E\<^sup>*"
  proof -
    fix a b assume path: "(a,b) \<in> (schema_graph_edges (decode_finite_graph G))\<^sup>*"
    show "((b,fst (rel_value J b)),(a,fst (rel_value J a))) \<in> ?E\<^sup>*"
      using path
    proof (induction rule: rtrancl_induct)
      case base
      show ?case by simp
    next
      case (step b c)
      have edge: "((c,fst (rel_value J c)),(b,fst (rel_value J b))) \<in> ?E"
        by (rule edges[OF step.hyps(2)])
      show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF edge] step.IH])
    qed
  qed
  have sv: "single_valued J" and rr: "(root,d,t) \<in> J"
    and path: "(n,root) \<in> (schema_graph_edges (decode_finite_graph G))\<^sup>*"
    using read inside by (auto simp: schema_graph_reading_def schema_graph_formed_def)
  have rv: "rel_value J root=(d,t)" by (rule rel_value_eq[OF sv rr])
  show ?thesis using paths[OF path] rv by simp
qed

theorem finite_graph_claims_recovers:
  fixes P :: "('a,'s,'d,'c) finite_schema_system" and G :: "('a,'s,'c,'n) finite_derivation_graph"
  assumes read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
    root d (decode_finite_term t) J"
  shows "decode_finite_premises (finite_graph_claims P G root d t) = J"
proof -
  let ?decode = "map_prod id decode_finite_call_term"
  let ?A = "{q. ?decode q \<in> J}"
  have rr: "(root,d,decode_finite_term t) \<in> J" and sv: "single_valued J"
    and domain: "rel_dom J=schema_graph_nodes (decode_finite_graph G)"
    and gf: "schema_graph_formed (decode_finite_graph G) root"
    using read by (auto simp: schema_graph_reading_def)
  have bounded: "fset (finite_graph_claims P G root d t) \<subseteq> ?A"
    unfolding finite_graph_claims_def
  proof (rule finite_reachable_outputs_invariant)
    show "(root,d,t) \<in> ?A" using rr by simp
    fix a b :: "'n \<times> ('d \<times> finite_factor_term)"
    assume member: "a \<in> ?A" and transition: "(finite_claim_key a,b) |\<in>| finite_graph_transitions P G"
    obtain n e u where a: "a=(n,e,u)" by (cases a) auto
    obtain m f v where b: "b=(m,f,v)" by (cases b) auto
    have claim: "(n,e,decode_finite_term u) \<in> J" using member a by simp
    have trans: "((n,e),(m,f,v)) |\<in>| finite_graph_transitions P G" using transition a b by simp
    have actual: "(m,f,decode_finite_term v) \<in> J" by (rule finite_graph_transition_sound[OF read claim trans])
    show "b \<in> ?A" using actual b by simp
  qed
  have lower: "decode_finite_premises (finite_graph_claims P G root d t) \<subseteq> J"
    using bounded by (auto simp: decode_finite_premises_def map_relation_values_def map_prod_def)
  have upper: "J \<subseteq> decode_finite_premises (finite_graph_claims P G root d t)"
  proof
    fix q assume member: "q \<in> J"
    obtain n e x where shape: "q=(n,e,x)" using member by (cases q) auto
    have row: "(n,e,x) \<in> J" using member shape by simp
    have nr: "rel_value J n=(e,x)" by (rule rel_value_eq[OF sv row])
    have inside: "n \<in> schema_graph_nodes (decode_finite_graph G)"
      using rel_domI[OF row] domain by simp
    show "q \<in> decode_finite_premises (finite_graph_claims P G root d t)"
    proof (cases "n=root")
      case True
      have same: "(e,x)=(d,decode_finite_term t)"
        by (rule single_valued_outputs[OF sv _ rr]) (use row True in simp)
      have candidate: "(root,d,t) |\<in>| finite_graph_claims P G root d t"
        by (simp add: finite_graph_claims_member)
      show ?thesis using shape True same candidate by simp
    next
      case False
      have path: "(n,root) \<in> (schema_graph_edges (decode_finite_graph G))\<^sup>*"
        using gf inside unfolding schema_graph_formed_def by blast
      obtain p where edge: "(n,p) \<in> schema_graph_edges (decode_finite_graph G)"
        using path False by (auto elim: converse_rtranclE)
      obtain f u where trans: "((p,fst (rel_value J p)),(n,f,u)) |\<in>| finite_graph_transitions P G"
        and rv: "rel_value J n=(f,decode_finite_term u)"
        using finite_graph_edge_transition[OF read edge] by blast
      have parent: "p \<in> schema_graph_nodes (decode_finite_graph G)"
        by (rule schema_graph_edge_nodes(2)[OF gf edge])
      have reachable: "((root,d),(p,fst (rel_value J p))) \<in>
          (fset (finite_transition_keys finite_claim_key (finite_graph_transitions P G)))\<^sup>*"
        by (rule finite_graph_keys_reachable[OF read parent])
      have candidate: "(n,f,u) |\<in>| finite_graph_claims P G root d t"
        using trans reachable by (auto simp: finite_graph_claims_member)
      have decoded: "(n,f,decode_finite_term u) \<in> decode_finite_premises (finite_graph_claims P G root d t)"
        using candidate by simp
      show ?thesis using decoded shape nr rv by auto
    qed
  qed
  show ?thesis using lower upper by blast
qed

section \<open>Complete graph checking takes only the root call\<close>

definition finite_graph_valid ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_graph_valid P G root d t \<longleftrightarrow>
    finite_graph_reading P G root d t (finite_graph_claims P G root d t)"

theorem finite_graph_valid_correct:
  "finite_graph_valid P G root d t \<longleftrightarrow>
    (\<exists>J. schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J)"
proof
  assume "finite_graph_valid P G root d t"
  then show "\<exists>J. schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J"
    by (auto simp: finite_graph_valid_def finite_graph_reading_correct)
next
  assume "\<exists>J. schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J"
  then obtain J where read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J" by blast
  show "finite_graph_valid P G root d t"
    using read by (simp add: finite_graph_valid_def finite_graph_reading_correct
        finite_graph_claims_recovers[OF read])
qed

definition finite_graph_proves ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_graph_proves P G root d t \<longleftrightarrow> finite_graph_valid P G root d t \<and>
    finite_graph_assumptions G (finite_graph_claims P G root d t) = {||}"

theorem finite_graph_proves_correct:
  "finite_graph_proves P G root d t \<longleftrightarrow>
    schema_graph_derives (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) {}"
proof
  assume accepted: "finite_graph_proves P G root d t"
  have read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises (finite_graph_claims P G root d t))"
    using accepted by (simp add: finite_graph_proves_def finite_graph_valid_def finite_graph_reading_correct)
  have empty: "schema_graph_assumptions (decode_finite_graph G)
      (decode_finite_premises (finite_graph_claims P G root d t)) = {}"
  proof -
    have no_assertions: "finite_graph_assumptions G (finite_graph_claims P G root d t)={||}"
      using accepted by (simp add: finite_graph_proves_def)
    show ?thesis
      by (simp only: finite_graph_assumptions_correct[symmetric] no_assertions decode_finite_premises_empty)
  qed
  show "schema_graph_derives (decode_finite_system P) (decode_finite_graph G) root d (decode_finite_term t) {}"
    using read empty unfolding schema_graph_derives_def by blast
next
  assume derived: "schema_graph_derives (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) {}"
  obtain J where read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) J" and empty: "schema_graph_assumptions (decode_finite_graph G) J={}"
    using derived unfolding schema_graph_derives_def by blast
  have valid: "finite_graph_valid P G root d t" using read by (auto simp: finite_graph_valid_correct)
  have boundary: "decode_finite_premises (finite_graph_assumptions G (finite_graph_claims P G root d t))={}"
    by (simp only: finite_graph_assumptions_correct finite_graph_claims_recovers[OF read] empty)
  have no_assertions: "finite_graph_assumptions G (finite_graph_claims P G root d t)={||}"
    using boundary by simp
  show "finite_graph_proves P G root d t" using valid no_assertions by (simp add: finite_graph_proves_def)
qed

corollary finite_graph_proves_sound:
  assumes "finite_graph_proves P G root d t"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule schema_graph_closed_sound) (use assms in \<open>simp add: finite_graph_proves_correct\<close>)

export_code finite_graph_claims finite_graph_valid finite_graph_proves checking SML

text \<open>
  The program, supplied graph, and root call suffice. The finite transition
  closure computes candidate claims, and the complete graph-reading check
  decides their validity. Whenever a reading exists, recovery gives exactly
  that reading. Missing nodes, conflicting shared claims, invalid instances,
  cycles, and omitted assertions are therefore governed by the same existing
  judgments. The procedure checks a supplied proof graph; it does not search
  for a proof of an arbitrary positive judgment.
\<close>

end
