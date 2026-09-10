theory Factor_Derivation
  imports Factor_Positive_Meaning "HOL-Library.FSet"
begin

section \<open>Finite derivation certificates\<close>

datatype ('a,'s,'c) schema_proof =
  Schema_Proof 'c "('a \<times> factor_term) fset" "('s \<times> ('a,'s,'c) schema_proof) fset"

primrec checks_schema_proof ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'c) schema_proof \<Rightarrow> 'd \<Rightarrow> factor_term \<Rightarrow> bool" where
  "checks_schema_proof P (Schema_Proof c V B) d t \<longleftrightarrow>
    (\<exists>Q. admitted_schema_instance P d c (fset V) t Q \<and>
      single_valued (fset B) \<and> rel_dom (fset B) = rel_dom Q \<and>
      (\<forall>(s,F)\<in>fset (fimage (map_prod id (checks_schema_proof P)) B).
        \<exists>e x. (s,e,x) \<in> Q \<and> F e x))"

lemma schema_proof_child_size:
  fixes B :: "('s \<times> ('a,'s,'c) schema_proof) fset"
  assumes member: "(s,p) \<in> fset B"
  shows "size p < size (Schema_Proof c V B)"
proof -
  let ?F = "map_prod (\<lambda>x. x) (\<lambda>p. (p,size p))"
  have mapped: "(s,p,size p) \<in> ?F ` fset B"
    using imageI[OF member, of ?F] by simp
  have bound: "Suc (size_prod (\<lambda>_. 0) snd (s,p,size p)) \<le>
    (\<Sum>q\<in>?F ` fset B. Suc (size_prod (\<lambda>_. 0) snd q))"
    using member_le_sum[OF mapped, where f="\<lambda>q. Suc (size_prod (\<lambda>_. 0) snd q)"] by simp
  show ?thesis using bound by (simp; linarith)
qed

lemma fimage_pair_forall:
  "(\<forall>(s,z)\<in>fset (fimage (map_prod id f) B). A s z) \<longleftrightarrow>
    (\<forall>s p. (s,p) \<in> fset B \<longrightarrow> A s (f p))"
  by (auto simp: Ball_def split: prod.splits; metis map_prod_imageI id_apply)

lemma checks_schema_proof_node:
  "checks_schema_proof P (Schema_Proof c V B) d t \<longleftrightarrow>
    (\<exists>Q. admitted_schema_instance P d c (fset V) t Q \<and>
      single_valued (fset B) \<and> rel_dom (fset B) = rel_dom Q \<and>
      (\<forall>s p. (s,p) \<in> fset B \<longrightarrow>
        (\<exists>e x. (s,e,x) \<in> Q \<and> checks_schema_proof P p e x)))"
  by (simp only: checks_schema_proof.simps fimage_pair_forall)

lemma proof_premise_supported:
  assumes inst: "admitted_schema_instance P d c V t Q"
    and domain: "rel_dom (fset B) = rel_dom Q"
    and children: "\<forall>s p. (s,p) \<in> fset B \<longrightarrow>
      (\<exists>e x. (s,e,x) \<in> Q \<and> checks_schema_proof P p e x)"
    and member: "(s,e,x) \<in> Q"
  shows "\<exists>p. (s,p) \<in> fset B \<and> checks_schema_proof P p e x"
proof -
  have key: "s \<in> rel_dom Q" using member by (auto simp: rel_dom_def)
  have bound: "s \<in> rel_dom (fset B)" using domain key by simp
  obtain p where child: "(s,p) \<in> fset B" using bound by (auto simp: rel_dom_def)
  obtain a y where claim: "(s,a,y) \<in> Q" "checks_schema_proof P p a y"
    using children child by blast
  have sv: "single_valued Q" using admitted_instance_formed[OF inst] by blast
  have same: "a = e \<and> y = x" using sv claim(1) member by (auto simp: single_valued_def)
  show ?thesis using child claim(2) same by blast
qed

theorem schema_proof_sound:
  assumes "checks_schema_proof P tree d t"
  shows "(d,t) \<in> positive_meaning P"
  using assms
proof (induction tree arbitrary: d t)
  case (Schema_Proof c V B)
  obtain Q where inst: "admitted_schema_instance P d c (fset V) t Q"
    and domain: "rel_dom (fset B) = rel_dom Q"
    and children: "\<forall>s p. (s,p) \<in> fset B \<longrightarrow>
      (\<exists>e x. (s,e,x) \<in> Q \<and> checks_schema_proof P p e x)"
    using Schema_Proof.prems by (auto simp only: checks_schema_proof_node)
  have support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> positive_meaning P"
  proof (intro allI impI)
    fix s e x assume member: "(s,e,x) \<in> Q"
    obtain p where child: "(s,p) \<in> fset B" and replay: "checks_schema_proof P p e x"
      using proof_premise_supported[OF inst domain children member] by blast
    show "(e,x) \<in> positive_meaning P"
      by (rule Schema_Proof.IH[OF child _ replay]) (simp add: Basic_BNFs.prod_set_defs)
  qed
  show ?case by (rule positive_meaning_step[OF inst support])
qed

lemma finite_set_fset_witness:
  assumes "finite A"
  shows "\<exists>B. fset B = A"
proof -
  have "fset (Abs_fset A) = A" by (rule Abs_fset_inverse) (use assms in simp)
  then show ?thesis by blast
qed

lemma proof_closed_under_consequences:
  "schema_consequences P {(d,t). \<exists>tree. checks_schema_proof P tree d t}
    \<subseteq> {(d,t). \<exists>tree. checks_schema_proof P tree d t}"
proof
  fix call
  assume member: "call \<in> schema_consequences P {(d,t). \<exists>tree. checks_schema_proof P tree d t}"
  obtain d t where shape: "call = (d,t)" by (cases call) auto
  obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
    and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (\<exists>tree. checks_schema_proof P tree e x)"
    using member shape by (auto simp: schema_consequences_def)
  let ?pick = "\<lambda>(e,x). SOME tree. checks_schema_proof P tree e x"
  let ?B = "(\<lambda>(s,call). (s,?pick call)) ` Q"
  have chosen: "\<And>s e x. (s,e,x) \<in> Q \<Longrightarrow> checks_schema_proof P (?pick (e,x)) e x"
  proof -
    fix s e x assume member: "(s,e,x) \<in> Q"
    have exists: "\<exists>tree. checks_schema_proof P tree e x" using support member by blast
    show "checks_schema_proof P (?pick (e,x)) e x" using someI_ex[OF exists] by simp
  qed
  have qfinite: "finite Q" and qsv: "single_valued Q"
    using admitted_instance_formed[OF inst] by auto
  have vfinite: "finite V"
    using inst by (auto simp: admitted_schema_instance_def schema_instance_def term_bindings_formed_def)
  have bfinite: "finite ?B" using qfinite by simp
  have bsv: "single_valued ?B"
    using single_valued_pair_image[OF qsv, where f=id and g="?pick"] by simp
  have domain: "rel_dom ?B = rel_dom Q"
    using pair_image_domain[where R=Q and f=id and g="?pick"] by simp
  have children: "\<forall>s p. (s,p) \<in> ?B \<longrightarrow>
    (\<exists>e x. (s,e,x) \<in> Q \<and> checks_schema_proof P p e x)"
    using chosen by (auto; blast)
  obtain VB where vb: "fset VB = V" using finite_set_fset_witness[OF vfinite] by blast
  obtain BB where bb: "fset BB = ?B" using finite_set_fset_witness[OF bfinite] by blast
  have replay: "checks_schema_proof P (Schema_Proof c VB BB) d t"
    unfolding checks_schema_proof_node
    by (rule exI[of _ Q]) (use inst bsv domain children vb bb in simp)
  show "call \<in> {(d,t). \<exists>tree. checks_schema_proof P tree d t}"
    using replay shape by blast
qed

theorem schema_proof_complete:
  assumes "(d,t) \<in> positive_meaning P"
  shows "\<exists>tree. checks_schema_proof P tree d t"
  using positive_meaning_least[OF proof_closed_under_consequences] assms by blast

theorem schema_proof_adequate:
  "(d,t) \<in> positive_meaning P \<longleftrightarrow> (\<exists>tree. checks_schema_proof P tree d t)"
proof
  assume "(d,t) \<in> positive_meaning P"
  then show "\<exists>tree. checks_schema_proof P tree d t" by (rule schema_proof_complete)
next
  assume "\<exists>tree. checks_schema_proof P tree d t"
  then obtain tree where replay: "checks_schema_proof P tree d t" by blast
  show "(d,t) \<in> positive_meaning P" by (rule schema_proof_sound[OF replay])
qed

lemma proof_socket_boundary:
  assumes replay: "checks_schema_proof P (Schema_Proof c V B) d t"
    and source: "((d,c),S) \<in> system_clauses P"
  shows "rel_dom (fset B) = rel_dom (schema_premises S)"
proof -
  obtain Q T where chosen: "((d,c),T) \<in> system_clauses P"
    and inst: "schema_instance T (fset V) t Q"
    and domain: "rel_dom (fset B) = rel_dom Q"
    using replay by (auto simp: checks_schema_proof_node admitted_schema_instance_def)
  have sv: "single_valued (system_clauses P)"
    using positive_meaning_has_formed_system[OF schema_proof_sound[OF replay]]
    by (simp add: schema_system_formed_def)
  have same: "T = S" using sv chosen source by (auto simp: single_valued_def)
  show ?thesis using schema_instance_socket_boundary[OF inst] domain same by simp
qed

lemma proof_has_no_missing_socket:
  assumes "((d,c),S) \<in> system_clauses P" "s \<in> rel_dom (schema_premises S)"
    "s \<notin> rel_dom (fset B)"
  shows "\<not> checks_schema_proof P (Schema_Proof c V B) d t"
proof
  assume replay: "checks_schema_proof P (Schema_Proof c V B) d t"
  have same: "rel_dom (fset B) = rel_dom (schema_premises S)"
    by (rule proof_socket_boundary[OF replay assms(1)])
  show False using same assms(2,3) by blast
qed

text \<open>
  The claimed call is a separate checking input. An inference certificate stores its
  clause occurrence, complete variable bindings, and complete socket-to-child
  graph. The selected schema determines every expected child call. Neither the
  conclusion nor those child calls are duplicated inside the certificate.

  Sharing one child value at two sockets is represented by two explicit graph
  entries. Soundness and completeness relate finite derivation trees to the
  independently defined positive meaning. This projection still needs its
  native artifact representation and the joins to evidence selection.
\<close>

end
