theory Factor_Executable_Readings
  imports Factor_Executable_Graphs
begin

section \<open>Finite claim relations and exact socket joins\<close>

lemma finite_relation_test:
  assumes sv: "finite_relation_functional J" and row: "(n,q) |\<in>| J"
  shows "fBex J (\<lambda>(m,v). m=n \<and> test v) \<longleftrightarrow> test q"
  using sv row by (auto simp: finite_relation_functional_correct single_valued_def
      Bex_def split: prod.splits; blast)

lemma decode_finite_premises_member [simp]:
  "(n,d,decode_finite_term t) \<in> decode_finite_premises J \<longleftrightarrow> (n,d,t) |\<in>| J"
  by (auto simp: decode_finite_premises_def decode_finite_call_term_def)

lemma decode_finite_premises_domain [simp]:
  "rel_dom (decode_finite_premises J) = fset (fimage fst J)"
  by (simp add: decode_finite_premises_def rel_dom_image fimage.rep_eq)

lemma decode_finite_premises_functional [simp]:
  "single_valued (decode_finite_premises J) \<longleftrightarrow> finite_relation_functional J"
  by (simp add: decode_finite_premises_def
      map_relation_values_functional[OF decode_finite_call_inj(2)] finite_relation_functional_correct)

lemma decode_finite_premises_injective [simp]:
  "decode_finite_premises J = decode_finite_premises K \<longleftrightarrow> J=K"
  by (simp add: decode_finite_premises_def
      map_relation_values_injective[OF decode_finite_call_inj(2)] fset_inject)

lemma decode_finite_premises_empty [simp]:
  "decode_finite_premises {||} = {}"
  by (simp add: decode_finite_premises_def map_relation_values_def)

lemma decode_finite_premises_eq_empty [simp]:
  "decode_finite_premises J = {} \<longleftrightarrow> J={||}"
  using decode_finite_premises_injective[of J "{||}"] by simp

definition finite_link_claims ::
  "('a,'s,'c,'n) finite_derivation_graph \<Rightarrow> ('n \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow>
    'n \<Rightarrow> ('s \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_link_claims G J n = finite_edge_compose (finite_graph_premises G n) J"

lemma finite_link_claims_correct:
  "decode_finite_premises (finite_link_claims G J n) =
    schema_graph_premises (decode_finite_graph G) n O decode_finite_premises J"
  by (simp add: finite_link_claims_def decode_finite_premises_def finite_edge_compose_correct
      map_relation_values_join finite_graph_premises_correct)

section \<open>Every supplied node claim is checked\<close>

fun finite_checks_graph_node ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    ('n \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> 'n \<Rightarrow>
    ('a,'c) finite_schema_graph_node \<Rightarrow> bool" where
  "finite_checks_graph_node P G J n Finite_Assertion \<longleftrightarrow>
    fBex J (\<lambda>(m,d,t). m=n \<and> finite_schema_call_formed P d t) \<and>
    finite_graph_premises G n = {||}"
| "finite_checks_graph_node P G J n (Finite_Inference c V) \<longleftrightarrow>
    fBex J (\<lambda>(m,d,t). m=n \<and>
      finite_admitted_schema_instance P d c V t (finite_link_claims G J n))"

lemma finite_checks_graph_node_correct:
  assumes formed: "finite_graph_formed G root" and jsv: "finite_relation_functional J"
    and domain: "fimage fst J=finite_graph_nodes G" and inside: "n |\<in>| finite_graph_nodes G"
  shows "finite_checks_graph_node P G J n A \<longleftrightarrow>
    checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
      (decode_finite_premises J) n (decode_finite_graph_node A)"
proof -
  have key: "n |\<in>| fimage fst J" using domain inside by simp
  obtain d t where row: "(n,d,t) |\<in>| J"
    using key by (auto simp: fimage_iff)
  have abstract_row: "(n,d,decode_finite_term t) \<in> decode_finite_premises J" using row by simp
  have sv: "single_valued (decode_finite_premises J)" using jsv by simp
  have formed': "schema_graph_formed (decode_finite_graph G) root"
    using formed by (simp add: finite_graph_formed_correct)
  have domain': "rel_dom (decode_finite_premises J)=schema_graph_nodes (decode_finite_graph G)"
    by (simp only: decode_finite_premises_domain domain finite_graph_nodes_correct)
  have rv: "rel_value (decode_finite_premises J) n=(d,decode_finite_term t)"
    by (rule rel_value_eq[OF sv abstract_row])
  show ?thesis
  proof (cases A)
    case Finite_Assertion
    show ?thesis
      by (simp add: Finite_Assertion finite_relation_test[OF jsv row]
          finite_schema_call_formed_correct rv
          fset_inject[symmetric] finite_graph_premises_correct)
  next
    case (Finite_Inference c V)
    have joined: "checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
        (decode_finite_premises J) n (Schema_Inference c (decode_finite_binding_set V)) \<longleftrightarrow>
        admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
          (decode_finite_term t) (schema_graph_premises (decode_finite_graph G) n O decode_finite_premises J)"
      using checks_schema_inference_by_join[OF formed' sv domain' abstract_row,
        where P="decode_finite_system P" and c=c and V="decode_finite_binding_set V"]
      by simp
    show ?thesis
      by (simp only: Finite_Inference finite_checks_graph_node.simps decode_finite_graph_node.simps joined)
         (simp add: finite_relation_test[OF jsv row]
           finite_admitted_schema_instance_correct finite_link_claims_correct)
  qed
qed

definition finite_graph_reading ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow>
    'n \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
    ('n \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_graph_reading P G root d t J \<longleftrightarrow>
    finite_graph_formed G root \<and> finite_relation_functional J \<and>
    fimage fst J=finite_graph_nodes G \<and> (root,d,t) |\<in>| J \<and>
    fBall (finite_graph_inferences G) (\<lambda>(n,A). finite_checks_graph_node P G J n A)"

theorem finite_graph_reading_correct:
  "finite_graph_reading P G root d t J \<longleftrightarrow>
    schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises J)"
proof -
  have domain: "rel_dom (decode_finite_premises J)=schema_graph_nodes (decode_finite_graph G) \<longleftrightarrow>
      fimage fst J=finite_graph_nodes G"
    by (simp only: decode_finite_premises_domain finite_graph_nodes_correct[symmetric] fset_inject)
  have checks: "\<And>n A. finite_graph_formed G root \<Longrightarrow> finite_relation_functional J \<Longrightarrow>
      fimage fst J=finite_graph_nodes G \<Longrightarrow> (n,A) |\<in>| finite_graph_inferences G \<Longrightarrow>
      finite_checks_graph_node P G J n A \<longleftrightarrow>
      checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
        (decode_finite_premises J) n (decode_finite_graph_node A)"
    by (rule finite_checks_graph_node_correct)
       (auto simp: finite_graph_nodes_def intro: rev_image_eqI)
  show ?thesis
  proof
    assume read: "finite_graph_reading P G root d t J"
    have gf: "finite_graph_formed G root" and sv: "finite_relation_functional J"
      and dom: "fimage fst J=finite_graph_nodes G" and rr: "(root,d,t) |\<in>| J"
      and all: "\<forall>n A. (n,A) |\<in>| finite_graph_inferences G \<longrightarrow> finite_checks_graph_node P G J n A"
      using read by (auto simp: finite_graph_reading_def Ball_def split_paired_All)
    have checked: "\<And>n A. (n,A) \<in> fset (graph_inferences (decode_finite_graph G)) \<Longrightarrow>
        checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
          (decode_finite_premises J) n A"
    proof -
      fix n A
      assume member: "(n,A) \<in> fset (graph_inferences (decode_finite_graph G))"
      obtain B where row: "(n,B) |\<in>| finite_graph_inferences G" and shape: "A=decode_finite_graph_node B"
        using member by auto
      show "checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
          (decode_finite_premises J) n A"
        using checks[OF gf sv dom row] all row shape by blast
    qed
    show "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
        root d (decode_finite_term t) (decode_finite_premises J)"
      using gf sv dom rr checked
      by (simp only: schema_graph_reading_def finite_graph_formed_correct[symmetric]
          decode_finite_premises_functional domain decode_finite_premises_member; blast)
  next
    assume read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
        root d (decode_finite_term t) (decode_finite_premises J)"
    have gf: "finite_graph_formed G root" and sv: "finite_relation_functional J"
      and dom: "fimage fst J=finite_graph_nodes G" and rr: "(root,d,t) |\<in>| J"
      using read
      by (simp only: schema_graph_reading_def finite_graph_formed_correct[symmetric]
          decode_finite_premises_functional domain decode_finite_premises_member; blast)+
    have checked: "\<And>n A. (n,A) |\<in>| finite_graph_inferences G \<Longrightarrow> finite_checks_graph_node P G J n A"
    proof -
      fix n A assume row: "(n,A) |\<in>| finite_graph_inferences G"
      have decoded: "(n,decode_finite_graph_node A) \<in> fset (graph_inferences (decode_finite_graph G))"
        using row by auto
      have abstract: "checks_schema_graph_node (decode_finite_system P) (decode_finite_graph G)
          (decode_finite_premises J) n (decode_finite_graph_node A)"
        using read decoded unfolding schema_graph_reading_def by blast
      show "finite_checks_graph_node P G J n A" using checks[OF gf sv dom row] abstract by blast
    qed
    show "finite_graph_reading P G root d t J"
      using gf sv dom rr checked by (auto simp: finite_graph_reading_def Ball_def split_paired_All)
  qed
qed

definition finite_graph_assumptions ::
  "('a,'s,'c,'n) finite_derivation_graph \<Rightarrow> ('n \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow>
    ('n \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_graph_assumptions G J =
    ffilter (\<lambda>(n,q). (n,Finite_Assertion) |\<in>| finite_graph_inferences G) J"

lemma finite_graph_assumptions_correct:
  "decode_finite_premises (finite_graph_assumptions G J) =
    schema_graph_assumptions (decode_finite_graph G) (decode_finite_premises J)"
  by (auto simp: finite_graph_assumptions_def schema_graph_assumptions_def
      decode_finite_premises_def split: prod.splits)

theorem finite_graph_reading_unique:
  assumes "finite_graph_reading P G root d t J" "finite_graph_reading P G root d t K"
  shows "J=K"
  using schema_graph_reading_unique[OF assms[unfolded finite_graph_reading_correct]]
  by simp

theorem finite_graph_reading_conditional_sound:
  assumes read: "finite_graph_reading P G root d t J"
    and support: "\<And>n e u. (n,e,u) |\<in>| finite_graph_assumptions G J \<Longrightarrow>
      (e,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  have abstract: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G)
      root d (decode_finite_term t) (decode_finite_premises J)"
    using read by (simp add: finite_graph_reading_correct)
  show ?thesis
  proof (rule schema_graph_reading_sound[OF abstract])
    fix n q
    assume member: "(n,q) \<in> schema_graph_assumptions (decode_finite_graph G) (decode_finite_premises J)"
    have decoded: "(n,q) \<in> decode_finite_premises (finite_graph_assumptions G J)"
      using member by (simp only: finite_graph_assumptions_correct)
    obtain e u where row: "(n,e,u) |\<in>| finite_graph_assumptions G J"
      and shape: "q=(e,decode_finite_term u)"
      using decoded by (auto simp: decode_finite_premises_def decode_finite_call_term_def)
    show "q \<in> positive_meaning (decode_finite_system P)" using support[OF row] shape by simp
  qed
qed

corollary finite_closed_graph_reading_sound:
  assumes "finite_graph_reading P G root d t J" "finite_graph_assumptions G J={||}"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_graph_reading_conditional_sound[OF assms(1)]) (use assms(2) in simp)

export_code finite_graph_reading finite_graph_assumptions checking SML

text \<open>
  Supplied claims are checked against every identified inference and assertion.
  Socket links and child claims determine the full premise relation. Exact
  domain equality rejects missing or extra claims; functionality rejects
  conflicting claims at a shared node. The assumption projection retains
  every assertion occurrence. Acceptance has exactly the existing graph-reading
  meaning, including for malformed finite inputs. Recovering this unique
  reading from the root call is the next computation.
\<close>

end
