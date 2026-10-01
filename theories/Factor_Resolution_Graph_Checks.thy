theory Factor_Resolution_Graph_Checks
  imports Factor_Resolution_Commitments Shared_Term_Tables Finite_Sorted_Set_Execution Merge_Sort_Keys Listed_Set_Unions
begin

text \<open>
  The check of a found derivation (DECISIONS.md, task 495's entry, its addition "The resolver at the given's size",
  "The check of a found derivation"). With F3 a search makes each distinct subderivation once, but a found state's
  certificate (@{const finite_node_proof}) is the unfolded tree, a premise closed by reuse reading the whole derivation of
  the solved node that closed it; the tree checker (@{const finite_checks_schema_proof}) traverses it. Here the check is
  made on the found state's derivation graph by the existing finite graph reading (@{const finite_graph_reading}): its
  nodes are the state's nodes a certificate reads from its root, each inference the node's clause and values, a premise
  discharged to the node at the premise's position or to the solved node that closed it. Its acceptance gives the tree
  check on every input (@{text finite_state_graph_check_accepts}), and at every found state it holds
  (@{text finite_state_graph_check_found}), so the two agree there. Certificates are built once per node and shared, and
  code equations of @{const finite_state_proofs}, @{const finite_outcome_result} and @{const finite_program_resolution}
  make the check over the graph, each equal to the original on every input: the committed, registered and native forms,
  whose results are @{const finite_outcome_result}'s, take them as they stand.
\<close>

section \<open>The nodes a certificate reads\<close>

lemma finite_relation_functional_at:
  assumes F: "finite_relation_functional F" and y: "(x,y) |\<in>| F" and z: "(x,z) |\<in>| F"
  shows "y = z"
proof -
  from F y have "fBall F (\<lambda>b. fst (x,y) = fst b \<longrightarrow> snd (x,y) = snd b)" unfolding finite_relation_functional_def by blast
  then have "fst (x,y) = fst (x,z) \<longrightarrow> snd (x,y) = snd (x,z)" using z by blast
  then show ?thesis by simp
qed

lemma finite_relation_functional_intro:
  assumes "\<And>x y z. (x,y) |\<in>| F \<Longrightarrow> (x,z) |\<in>| F \<Longrightarrow> y = z"
  shows "finite_relation_functional F"
  unfolding finite_relation_functional_def
proof (intro ballI impI)
  fix a b assume "a |\<in>| F" "b |\<in>| F" "fst a = fst b"
  then show "snd a = snd b" using assms[of "fst a" "snd a" "snd b"] by (metis prod.collapse)
qed

lemma finite_premise_nodes_member:
  assumes "m |\<in>| finite_premise_nodes N nd s e p"
  shows "m |\<in>| N" "resolution_node_site m = e"
    "finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p"
    "resolution_node_position m = resolution_node_position nd@[s] \<or>
      finite_position_left (resolution_node_position m) (resolution_node_position nd@[s])"
  using assms by (auto simp: finite_premise_nodes_def finite_first_nodes_def Let_def split: if_splits)

lemma finite_premise_nodes_unique:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and first: "m1 |\<in>| finite_premise_nodes N nd s e p" and second: "m2 |\<in>| finite_premise_nodes N nd s e p"
  shows "m1=m2"
proof -
  let ?q = "resolution_node_position nd@[s]"
  let ?F = "ffilter (\<lambda>m. resolution_node_site m=e \<and>
    finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p) N"
  let ?C = "ffilter (\<lambda>m. resolution_node_position m=?q) ?F"
  let ?L = "ffilter (\<lambda>m. finite_position_left (resolution_node_position m) ?q) ?F"
  have nodes: "finite_premise_nodes N nd s e p = (if ?C\<noteq>{||} then ?C else finite_first_nodes ?L)"
    by (simp add: finite_premise_nodes_def Let_def)
  show ?thesis
  proof (cases "?C={||}")
    case False
    then have "m1 |\<in>| ?C" "m2 |\<in>| ?C" using first second nodes by simp_all
    then show ?thesis using distinct by auto
  next
    case True
    then have in1: "m1 |\<in>| finite_first_nodes ?L" and in2: "m2 |\<in>| finite_first_nodes ?L"
      using first second nodes by simp_all
    have "?L \<noteq> {||}" using in1 by (auto simp: finite_first_nodes_def)
    moreover have "\<And>m m'. m |\<in>| ?L \<Longrightarrow> m' |\<in>| ?L \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
      using distinct by auto
    ultimately obtain m where "finite_first_nodes ?L = {|m|}" using finite_first_nodes_single by blast
    then show ?thesis using in1 in2 by simp
  qed
qed

text \<open>
  The links of a node: at each premise socket, the nodes its certificate reads there. A certificate is its node's clause
  and values with the certificates of its links (@{text finite_node_proof_links}).
\<close>

definition finite_node_links ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_node_links N nd = ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,m)) (finite_premise_nodes N nd s e p))
    (finite_schema_premises (resolution_node_schema nd)))"

lemma finite_node_links_member:
  "(s,m) |\<in>| finite_node_links N nd \<longleftrightarrow>
    (\<exists>e p. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd) \<and> m |\<in>| finite_premise_nodes N nd s e p)"
  by (force simp: finite_node_links_def resolution_fset_simps)

text \<open>
  A node a certificate reads has a smaller reach than its reader in the state (F3's order,
  @{thm [source] resolution_reach_less}): every chain of reads decreases in it.
\<close>

lemma finite_node_links_reach:
  assumes l: "(s,m) |\<in>| finite_node_links N nd"
  shows "m |\<in>| N" "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N m) < fcard (resolution_reach N nd)"
proof -
  obtain e p where m: "m |\<in>| finite_premise_nodes N nd s e p" using l by (auto simp: finite_node_links_member)
  show "m |\<in>| N" by (rule finite_premise_nodes_member(1)[OF m])
  show "fcard (resolution_reach N m) < fcard (resolution_reach N nd)" if "nd |\<in>| N"
    by (rule resolution_reach_less[OF that finite_premise_nodes_member(4)[OF m]])
qed

lemma finite_reach_positive:
  assumes "nd |\<in>| N"
  shows "0 < fcard (resolution_reach N nd)"
proof -
  have m: "nd |\<in>| resolution_reach N nd" using assms by (simp add: resolution_ffilter_member)
  then have "{|nd|} |\<subseteq>| resolution_reach N nd" by (simp only: finsert_fsubset) simp
  from fcard_mono[OF this] show ?thesis by (simp add: fcard.rep_eq)
qed

lemma finite_node_links_functional:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and prem: "finite_relation_functional (finite_schema_premises (resolution_node_schema nd))"
  shows "finite_relation_functional (finite_node_links N nd)"
proof (rule finite_relation_functional_intro)
  fix s m m' assume "(s,m) |\<in>| finite_node_links N nd" "(s,m') |\<in>| finite_node_links N nd"
  then obtain e p e' p' where sp: "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd)"
      "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema nd)"
    and m: "m |\<in>| finite_premise_nodes N nd s e p" and m': "m' |\<in>| finite_premise_nodes N nd s e' p'"
    by (auto simp: finite_node_links_member)
  have "(e,p) = (e',p')" using finite_relation_functional_at[OF prem sp] .
  then have "m' |\<in>| finite_premise_nodes N nd s e p" using m' by simp
  from finite_premise_nodes_unique[OF distinct m this] show "m=m'" .
qed

section \<open>The premises a table closes\<close>

text \<open>
  At a table (@{const resolution_table_lookup}) a premise that no node of the state reads, none at its socket and none
  reused left of it, is closed by the table's entry at its instance, and the certificate reads that entry there
  (@{const finite_socket_proofs}). In a derivation graph the entry stands as an assertion node: at the premise's position,
  at the premise's site, its call the entry's ground call; its clause and schema are its reader's, which no reading of an
  assertion reads. A premise the table closes is a table link of its node (@{text finite_table_links}); a node's links at
  a table are its state links and its table links (@{text finite_node_links_in}), and at the empty table there are none
  of the second kind.
\<close>

definition finite_table_node ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_node" where
  "finite_table_node nd s e u = Resolution_Node (resolution_node_position nd@[s]) e (resolution_node_clause nd)
    (resolution_node_schema nd) (finite_exact_term_pattern u) {||}"

lemma finite_table_node_fields [simp]:
  "resolution_node_position (finite_table_node nd s e u) = resolution_node_position nd@[s]"
  "resolution_node_site (finite_table_node nd s e u) = e"
  "finite_residual_term (resolution_node_call (finite_table_node nd s e u)) = u"
  by (simp_all add: finite_table_node_def)

definition finite_table_proof ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'c) finite_schema_proof" where
  "finite_table_proof \<Theta> m = the (resolution_table_lookup \<Theta> (resolution_node_site m,finite_residual_term (resolution_node_call m)))"

definition finite_table_links ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_table_links \<Theta> N nd = ffUnion (fimage (\<lambda>(s,e,p). if finite_premise_nodes N nd s e p={||}
      then fimage (\<lambda>u. (s,finite_table_node nd s e u)) (ffilter (\<lambda>u. resolution_table_lookup \<Theta> (e,u) \<noteq> None)
        (finite_pattern_instances (finite_node_values nd) p)) else {||})
    (finite_schema_premises (resolution_node_schema nd)))"

lemma ffUnion_fimage_iff: "x |\<in>| ffUnion (fimage F A) \<longleftrightarrow> (\<exists>y. y |\<in>| A \<and> x |\<in>| F y)"
  by (auto simp: resolution_fset_simps)

lemma finite_table_links_member:
  "(s,a) |\<in>| finite_table_links \<Theta> N nd \<longleftrightarrow> (\<exists>e p u. (s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd) \<and>
    finite_premise_nodes N nd s e p={||} \<and> u |\<in>| finite_pattern_instances (finite_node_values nd) p \<and>
    resolution_table_lookup \<Theta> (e,u) \<noteq> None \<and> a=finite_table_node nd s e u)"
proof -
  have one: "(s,a) |\<in>| (if finite_premise_nodes N nd s' e p={||}
      then fimage (\<lambda>u. (s',finite_table_node nd s' e u)) (ffilter (\<lambda>u. resolution_table_lookup \<Theta> (e,u) \<noteq> None)
        (finite_pattern_instances (finite_node_values nd) p)) else {||}) \<longleftrightarrow>
    s=s' \<and> finite_premise_nodes N nd s' e p={||} \<and> (\<exists>u. u |\<in>| finite_pattern_instances (finite_node_values nd) p \<and>
      resolution_table_lookup \<Theta> (e,u) \<noteq> None \<and> a=finite_table_node nd s' e u)" for s' e p
    by (auto simp: resolution_ffilter_member)
  show ?thesis by (simp only: finite_table_links_def ffUnion_fimage_iff split_paired_Ex prod.case one) blast
qed

lemma finite_table_links_empty [simp]: "finite_table_links resolution_empty_table N nd = {||}"
  by (rule fset_eqI) (auto simp: finite_table_links_member)

lemma finite_table_links_notin:
  assumes l: "(s,a) |\<in>| finite_table_links \<Theta> N nd"
  shows "a |\<notin>| N"
proof
  assume aN: "a |\<in>| N"
  obtain e p u where M: "finite_premise_nodes N nd s e p={||}" and u: "u |\<in>| finite_pattern_instances (finite_node_values nd) p"
    and a: "a=finite_table_node nd s e u"
    using l by (auto simp: finite_table_links_member)
  let ?C = "ffilter (\<lambda>m. resolution_node_position m=resolution_node_position nd@[s]) (ffilter (\<lambda>m. resolution_node_site m=e \<and>
    finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p) N)"
  have C: "a |\<in>| ?C" using aN u by (simp add: a resolution_ffilter_member)
  then have "?C \<noteq> {||}" by auto
  then have "finite_premise_nodes N nd s e p = ?C" by (simp add: finite_premise_nodes_def Let_def)
  then show False using M C by simp
qed

lemma finite_table_links_reach:
  assumes l: "(s,a) |\<in>| finite_table_links \<Theta> N nd" and nd: "nd |\<in>| N"
  shows "fcard (resolution_reach N a) < fcard (resolution_reach N nd)"
proof -
  obtain e u where "a=finite_table_node nd s e u" using l by (auto simp: finite_table_links_member)
  then have "resolution_node_position a=resolution_node_position nd@[s]" by simp
  then show ?thesis by (rule resolution_reach_less[OF nd disjI1])
qed

definition finite_node_links_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_node_links_in \<Theta> N nd = finite_node_links N nd |\<union>| finite_table_links \<Theta> N nd"

lemma finite_node_links_in_empty [simp]: "finite_node_links_in resolution_empty_table N nd = finite_node_links N nd"
  by (simp add: finite_node_links_in_def)

lemma finite_node_links_in_functional:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and prem: "finite_relation_functional (finite_schema_premises (resolution_node_schema nd))"
    and vals: "finite_relation_functional (finite_node_values nd)"
  shows "finite_relation_functional (finite_node_links_in \<Theta> N nd)"
proof (rule finite_relation_functional_intro)
  have links: "finite_relation_functional (finite_node_links N nd)" by (rule finite_node_links_functional[OF distinct prem])
  have mixed: False if l: "(s,m) |\<in>| finite_node_links N nd" and a: "(s,a) |\<in>| finite_table_links \<Theta> N nd" for s m a
  proof -
    obtain e p where sp: "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd)"
      and m: "m |\<in>| finite_premise_nodes N nd s e p"
      using l by (auto simp: finite_node_links_member)
    obtain e' p' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema nd)"
      and M: "finite_premise_nodes N nd s e' p'={||}"
      using a by (auto simp: finite_table_links_member)
    have "(e,p)=(e',p')" using finite_relation_functional_at[OF prem sp sp'] .
    then show False using m M by simp
  qed
  have table: "a=a'" if a: "(s,a) |\<in>| finite_table_links \<Theta> N nd" and a': "(s,a') |\<in>| finite_table_links \<Theta> N nd" for s a a'
  proof -
    obtain e p u where sp: "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema nd)"
        and u: "u |\<in>| finite_pattern_instances (finite_node_values nd) p" and au: "a=finite_table_node nd s e u"
      using a by (auto simp: finite_table_links_member)
    obtain e' p' u' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema nd)"
        and u': "u' |\<in>| finite_pattern_instances (finite_node_values nd) p'" and au': "a'=finite_table_node nd s e' u'"
      using a' by (auto simp: finite_table_links_member)
    have ep: "(e,p)=(e',p')" using finite_relation_functional_at[OF prem sp sp'] .
    then have "u=u'" using finite_pattern_instance_unique[OF vals] u u' by (simp add: finite_pattern_instances_member)
    then show ?thesis using au au' ep by simp
  qed
  fix s m m' assume first: "(s,m) |\<in>| finite_node_links_in \<Theta> N nd" and second: "(s,m') |\<in>| finite_node_links_in \<Theta> N nd"
  then consider "(s,m) |\<in>| finite_node_links N nd" "(s,m') |\<in>| finite_node_links N nd"
    | "(s,m) |\<in>| finite_table_links \<Theta> N nd" "(s,m') |\<in>| finite_table_links \<Theta> N nd"
    using mixed by (auto simp: finite_node_links_in_def)
  then show "m=m'"
  proof cases
    case 1
    then show ?thesis by (rule finite_relation_functional_at[OF links])
  next
    case 2
    then show ?thesis by (rule table)
  qed
qed

lemma finite_socket_image_member:
  "(s,c) |\<in>| fimage (\<lambda>(s,m). (s,f m)) L \<longleftrightarrow> (\<exists>m. (s,m) |\<in>| L \<and> c=f m)"
  by (force simp: resolution_fset_simps)

lemma finite_table_proofs_member:
  "c |\<in>| finite_table_proofs \<Theta> nd e p \<longleftrightarrow>
    (\<exists>u. u |\<in>| finite_pattern_instances (finite_node_values nd) p \<and> resolution_table_lookup \<Theta> (e,u)=Some c)"
  by (force simp: finite_table_proofs_def resolution_fset_simps split: option.splits)

text \<open>
  A certificate at a table is its node's clause and values with the certificates of its state links and the entries of
  its table links.
\<close>

lemma finite_node_proof_in_links:
  "finite_node_proof_in \<Theta> (Suc k) N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_proof_in \<Theta> k N m)) (finite_node_links N nd) |\<union>|
      fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N nd))"
proof -
  let ?f = "\<lambda>m. finite_node_proof_in \<Theta> k N m"
  let ?L = "ffUnion (fimage (\<lambda>(s,e,p). finite_socket_proofs \<Theta> ?f N nd s e p) (finite_schema_premises (resolution_node_schema nd)))"
  let ?R = "fimage (\<lambda>(s,m). (s,?f m)) (finite_node_links N nd) |\<union>|
    fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N nd)"
  have socket: "(s,c) |\<in>| finite_socket_proofs \<Theta> ?f N nd s' e p \<longleftrightarrow> s=s' \<and>
      (if finite_premise_nodes N nd s' e p={||} then (\<exists>u. u |\<in>| finite_pattern_instances (finite_node_values nd) p \<and>
        resolution_table_lookup \<Theta> (e,u)=Some c) else (\<exists>m. m |\<in>| finite_premise_nodes N nd s' e p \<and> c=?f m))" for s c s' e p
    by (auto simp: finite_socket_proofs_def Let_def finite_table_proofs_member image_iff)
  let ?I = "\<lambda>p. finite_pattern_instances (finite_node_values nd) p"
  let ?P = "finite_schema_premises (resolution_node_schema nd)"
  have L: "(s,c) |\<in>| ?L \<longleftrightarrow> (\<exists>e p. (s,e,p) |\<in>| ?P \<and> (if finite_premise_nodes N nd s e p={||}
      then (\<exists>u. u |\<in>| ?I p \<and> resolution_table_lookup \<Theta> (e,u)=Some c)
      else (\<exists>m. m |\<in>| finite_premise_nodes N nd s e p \<and> c=?f m)))" for s c
    by (simp only: ffUnion_fimage_iff split_paired_Ex prod.case socket) blast
  have R: "(s,c) |\<in>| ?R \<longleftrightarrow> (\<exists>e p m. (s,e,p) |\<in>| ?P \<and> m |\<in>| finite_premise_nodes N nd s e p \<and> c=?f m) \<or>
      (\<exists>e p u. (s,e,p) |\<in>| ?P \<and> finite_premise_nodes N nd s e p={||} \<and> u |\<in>| ?I p \<and>
        resolution_table_lookup \<Theta> (e,u)=Some c)" for s c
  proof -
    have links: "(\<exists>m. (s,m) |\<in>| finite_node_links N nd \<and> c=?f m) \<longleftrightarrow>
        (\<exists>e p m. (s,e,p) |\<in>| ?P \<and> m |\<in>| finite_premise_nodes N nd s e p \<and> c=?f m)"
      by (simp only: finite_node_links_member) blast
    have table: "(\<exists>a. (s,a) |\<in>| finite_table_links \<Theta> N nd \<and> c=finite_table_proof \<Theta> a) \<longleftrightarrow>
        (\<exists>e p u. (s,e,p) |\<in>| ?P \<and> finite_premise_nodes N nd s e p={||} \<and> u |\<in>| ?I p \<and>
          resolution_table_lookup \<Theta> (e,u)=Some c)"
    proof
      assume "\<exists>a. (s,a) |\<in>| finite_table_links \<Theta> N nd \<and> c=finite_table_proof \<Theta> a"
      then obtain a e p u where sp: "(s,e,p) |\<in>| ?P" and M: "finite_premise_nodes N nd s e p={||}" and u: "u |\<in>| ?I p"
          and lk: "resolution_table_lookup \<Theta> (e,u) \<noteq> None" and a: "a = finite_table_node nd s e u"
          and c: "c = finite_table_proof \<Theta> a"
        by (auto simp: finite_table_links_member)
      have "resolution_table_lookup \<Theta> (e,u) = Some c"
        using lk c a by (cases "resolution_table_lookup \<Theta> (e,u)") (simp_all add: finite_table_proof_def)
      then show "\<exists>e p u. (s,e,p) |\<in>| ?P \<and> finite_premise_nodes N nd s e p={||} \<and> u |\<in>| ?I p \<and>
          resolution_table_lookup \<Theta> (e,u)=Some c" using sp M u by blast
    next
      assume "\<exists>e p u. (s,e,p) |\<in>| ?P \<and> finite_premise_nodes N nd s e p={||} \<and> u |\<in>| ?I p \<and>
          resolution_table_lookup \<Theta> (e,u)=Some c"
      then obtain e p u where sp: "(s,e,p) |\<in>| ?P" and M: "finite_premise_nodes N nd s e p={||}" and u: "u |\<in>| ?I p"
          and lk: "resolution_table_lookup \<Theta> (e,u)=Some c" by blast
      have "(s,finite_table_node nd s e u) |\<in>| finite_table_links \<Theta> N nd"
        using sp M u lk by (auto simp: finite_table_links_member)
      moreover have "c = finite_table_proof \<Theta> (finite_table_node nd s e u)" using lk by (simp add: finite_table_proof_def)
      ultimately show "\<exists>a. (s,a) |\<in>| finite_table_links \<Theta> N nd \<and> c=finite_table_proof \<Theta> a" by blast
    qed
    have "(s,c) |\<in>| ?R \<longleftrightarrow> (\<exists>m. (s,m) |\<in>| finite_node_links N nd \<and> c=?f m) \<or>
        (\<exists>a. (s,a) |\<in>| finite_table_links \<Theta> N nd \<and> c=finite_table_proof \<Theta> a)"
      by (simp only: funion_iff finite_socket_image_member)
    then show ?thesis unfolding links table .
  qed
  have ne: "\<And>m A. m |\<in>| A \<Longrightarrow> A \<noteq> {||}" by auto
  have pt: "(s,c) |\<in>| ?L \<longleftrightarrow> (s,c) |\<in>| ?R" for s c
    unfolding L R if_bool_eq_disj using ne by blast
  have "?L = ?R" by (intro fset_eqI) (simp only: split_paired_all pt)
  then show ?thesis by simp
qed

lemma finite_node_proof_links:
  "finite_node_proof (Suc k) N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_proof k N m)) (finite_node_links N nd))"
  using finite_node_proof_in_links[of resolution_empty_table k N nd] by simp

section \<open>A certificate is built once per node\<close>

text \<open>
  The fuel of @{const finite_node_proof} truncates only a chain of reads longer than it; every chain decreases in the
  reach, so fuel at least a node's reach gives the same certificate, on every state. The node's certificate is that one.
\<close>

lemma finite_node_proof_in_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> fcard (resolution_reach N nd) \<le> k' \<Longrightarrow>
    finite_node_proof_in \<Theta> k N nd = finite_node_proof_in \<Theta> k' N nd"
proof (induction k arbitrary: nd k')
  case 0
  then show ?case using finite_reach_positive[OF 0(1)] 0(2) by linarith
next
  case (Suc k)
  have "k' \<noteq> 0" using Suc.prems(3) finite_reach_positive[OF Suc.prems(1)] by linarith
  then obtain k'' where k': "k' = Suc k''" by (cases k') auto
  have "(\<lambda>(s,m). (s,finite_node_proof_in \<Theta> k N m)) x = (\<lambda>(s,m). (s,finite_node_proof_in \<Theta> k'' N m)) x"
    if x: "x |\<in>| finite_node_links N nd" for x
  proof -
    obtain s m where xs: "x = (s,m)" by (cases x) auto
    have mN: "m |\<in>| N" and less: "fcard (resolution_reach N m) < fcard (resolution_reach N nd)"
      using finite_node_links_reach[OF x[unfolded xs]] Suc.prems(1) by auto
    have "fcard (resolution_reach N m) \<le> k" using less Suc.prems(2) by linarith
    moreover have "fcard (resolution_reach N m) \<le> k''" using less Suc.prems(3) unfolding k' by linarith
    ultimately have "finite_node_proof_in \<Theta> k N m = finite_node_proof_in \<Theta> k'' N m" by (rule Suc.IH[OF mN])
    then show ?thesis using xs by simp
  qed
  from fimage_cong[where N="finite_node_links N nd", OF refl this] show ?case
    unfolding k' finite_node_proof_in_links by simp
qed

lemma finite_node_proof_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> fcard (resolution_reach N nd) \<le> k' \<Longrightarrow>
    finite_node_proof k N nd = finite_node_proof k' N nd"
  by (rule finite_node_proof_in_fuel)

definition finite_node_certificate_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('a,'s,'c) finite_schema_proof" where
  "finite_node_certificate_in \<Theta> N nd = finite_node_proof_in \<Theta> (fcard (resolution_reach N nd)) N nd"

abbreviation finite_node_certificate ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'c) finite_schema_proof" where
  "finite_node_certificate \<equiv> finite_node_certificate_in resolution_empty_table"

lemma finite_node_certificate_in_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> finite_node_proof_in \<Theta> k N nd = finite_node_certificate_in \<Theta> N nd"
  unfolding finite_node_certificate_in_def by (rule finite_node_proof_in_fuel) simp_all

lemma finite_node_certificate_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> finite_node_proof k N nd = finite_node_certificate N nd"
  by (rule finite_node_certificate_in_fuel)

lemma finite_node_certificate_in_links:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_certificate_in \<Theta> N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_certificate_in \<Theta> N m)) (finite_node_links N nd) |\<union>|
      fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N nd))"
proof -
  obtain j where j: "fcard (resolution_reach N nd) = Suc j"
    using finite_reach_positive[OF nd] by (cases "fcard (resolution_reach N nd)") auto
  have "(\<lambda>(s,m). (s,finite_node_proof_in \<Theta> j N m)) x = (\<lambda>(s,m). (s,finite_node_certificate_in \<Theta> N m)) x"
    if x: "x |\<in>| finite_node_links N nd" for x
  proof -
    obtain s m where xs: "x = (s,m)" by (cases x) auto
    have mN: "m |\<in>| N" and "fcard (resolution_reach N m) < fcard (resolution_reach N nd)"
      using finite_node_links_reach[OF x[unfolded xs]] nd by auto
    then have "fcard (resolution_reach N m) \<le> j" using j by simp
    then show ?thesis using finite_node_certificate_in_fuel[OF mN] xs by simp
  qed
  from fimage_cong[where N="finite_node_links N nd", OF refl this] show ?thesis
    unfolding finite_node_certificate_in_def[of \<Theta> N nd] j finite_node_proof_in_links by simp
qed

lemma finite_node_certificate_links:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_certificate N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_certificate N m)) (finite_node_links N nd))"
  using finite_node_certificate_in_links[OF nd, of resolution_empty_table] by simp

lemma finite_state_node_certificate_in:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_proof_in \<Theta> (fcard N) N nd = finite_node_certificate_in \<Theta> N nd"
proof (rule finite_node_certificate_in_fuel[OF nd])
  show "fcard (resolution_reach N nd) \<le> fcard N" by (rule fcard_mono) auto
qed

lemma finite_state_node_certificate:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_proof (fcard N) N nd = finite_node_certificate N nd"
  by (rule finite_state_node_certificate_in[OF nd])

text \<open>
  The nodes of a state, each with its rank and its links, computed once: the certificates are made in increasing rank,
  each from the certificates its links already hold (@{text finite_certificate_table}), and a node's certificate is
  looked up there, so every certificate is one value shared by every certificate that reads it.
\<close>

definition finite_node_ranked ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset" where
  "finite_node_ranked N = fimage (\<lambda>m. (m,fcard (resolution_reach N m),finite_node_links N m)) N"

lemma finite_relation_option_keyed:
  assumes m: "m |\<in>| A"
  shows "the (finite_relation_option (fimage (\<lambda>x. (x,f x)) A) m) = f m"
proof -
  have F: "finite_relation_functional (fimage (\<lambda>x. (x,f x)) A)"
    by (rule finite_relation_functional_intro) (auto simp: resolution_fset_simps)
  have "(m,f m) |\<in>| fimage (\<lambda>x. (x,f x)) A" using m by simp
  then have "finite_relation_option (fimage (\<lambda>x. (x,f x)) A) m = Some (f m)"
    using finite_relation_option_correct[OF F] by blast
  then show ?thesis by simp
qed

definition finite_certificate_step ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset \<Rightarrow> nat \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset" where
  "finite_certificate_step K T r = T |\<union>| fimage (\<lambda>(m,k,L). (m,Schema_Proof (resolution_node_clause m) (finite_node_values m)
    (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) L))) (ffilter (\<lambda>(m,k,L). k=r) K)"

definition finite_certificate_table ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset" where
  "finite_certificate_table K = foldl (finite_certificate_step K) {||} (sorted_list_of_fset (fimage (\<lambda>(m,k,L). k) K))"

text \<open>
  At a table the certificates are made in the same order, each from its state links' certificates, already made, and its
  table links' entries (@{text finite_certificate_table_in}); at the empty table this is the table above.
\<close>

definition finite_certificate_step_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset \<Rightarrow> nat \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset" where
  "finite_certificate_step_in \<Theta> N K T r = T |\<union>| fimage (\<lambda>(m,k,L). (m,Schema_Proof (resolution_node_clause m) (finite_node_values m)
    (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) L |\<union>|
      fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N m)))) (ffilter (\<lambda>(m,k,L). k=r) K)"

definition finite_certificate_table_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'c) finite_schema_proof) fset" where
  "finite_certificate_table_in \<Theta> N K = foldl (finite_certificate_step_in \<Theta> N K) {||}
    (sorted_list_of_fset (fimage (\<lambda>(m,k,L). k) K))"

lemma finite_certificate_step_empty: "finite_certificate_step_in resolution_empty_table N K = finite_certificate_step K"
  by (intro ext) (simp add: finite_certificate_step_in_def finite_certificate_step_def)

lemma finite_certificate_table_empty: "finite_certificate_table_in resolution_empty_table N K = finite_certificate_table K"
  by (simp add: finite_certificate_table_in_def finite_certificate_table_def finite_certificate_step_empty)

lemma finite_certificate_step_in_member:
  "x |\<in>| finite_certificate_step_in \<Theta> N (finite_node_ranked N) T r \<longleftrightarrow> x |\<in>| T \<or> (\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and>
    x = (m,Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>|
        fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N m))))"
  by (force simp: finite_certificate_step_in_def finite_node_ranked_def resolution_fset_simps)

lemma finite_certificate_step_member:
  "x |\<in>| finite_certificate_step (finite_node_ranked N) T r \<longleftrightarrow> x |\<in>| T \<or> (\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and>
    x = (m,Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m))))"
  using finite_certificate_step_in_member[of x resolution_empty_table N T r] by (simp add: finite_certificate_step_empty)

lemma finite_certificate_table_fold_in:
  assumes "sorted_wrt (<) rs"
    and "T = fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
    and "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. fcard (resolution_reach N m) < j)"
  shows "foldl (finite_certificate_step_in \<Theta> N (finite_node_ranked N)) T rs = fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m)) N"
  using assms
proof (induction rs arbitrary: T)
  case Nil
  have "ffilter (\<lambda>m. True) N = N" by (simp add: fset_eq_iff)
  then show ?case using Nil by simp
next
  case (Cons r rs)
  let ?tb = "\<lambda>m. fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N m)"
  have sorted: "sorted_wrt (<) rs" and above: "\<forall>j\<in>set rs. r < j" using Cons.prems(1) by simp_all
  have child: "the (finite_relation_option T m') = finite_node_certificate_in \<Theta> N m'"
    if m: "m |\<in>| N" "fcard (resolution_reach N m) = r" and link: "(s,m') |\<in>| finite_node_links N m" for m s m'
  proof -
    have m'N: "m' |\<in>| N" and less: "fcard (resolution_reach N m') < r"
      using finite_node_links_reach(1)[OF link] finite_node_links_reach(2)[OF link m(1)] m(2) by auto
    have "fcard (resolution_reach N m') \<notin> set (r#rs)" using less above by auto
    then have "m' |\<in>| ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set (r#rs)) N" using m'N by simp
    then show ?thesis unfolding Cons.prems(2) by (rule finite_relation_option_keyed)
  qed
  have made: "Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>| ?tb m) =
    finite_node_certificate_in \<Theta> N m"
    if m: "m |\<in>| N" "fcard (resolution_reach N m) = r" for m
  proof -
    have "fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) =
        fimage (\<lambda>(s,m'). (s,finite_node_certificate_in \<Theta> N m')) (finite_node_links N m)"
      by (rule fimage_cong[OF refl]) (auto simp: child[OF m])
    then show ?thesis using finite_node_certificate_in_links[OF m(1)] by simp
  qed
  have rr: "r \<notin> set rs" using above by auto
  have step: "finite_certificate_step_in \<Theta> N (finite_node_ranked N) T r =
      fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| finite_certificate_step_in \<Theta> N (finite_node_ranked N) T r \<longleftrightarrow>
      x |\<in>| fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
    proof -
      have "(\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>| ?tb m))) \<longleftrightarrow>
          (\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate_in \<Theta> N m))"
      proof
        assume "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>| ?tb m))"
        then obtain m where "m |\<in>| N" "fcard (resolution_reach N m) = r" "x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>| ?tb m))"
          by blast
        then show "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate_in \<Theta> N m)" using made by auto
      next
        assume "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate_in \<Theta> N m)"
        then obtain m where "m |\<in>| N" "fcard (resolution_reach N m) = r" "x = (m,finite_node_certificate_in \<Theta> N m)" by blast
        then show "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) |\<union>| ?tb m))"
          using made by auto
      qed
      then show ?thesis unfolding finite_certificate_step_in_member Cons.prems(2) using rr
        by (force simp: resolution_fset_simps)
    qed
  qed
  have processed: "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. fcard (resolution_reach N m) < j)"
    using Cons.prems(3) above by fastforce
  show ?case using Cons.IH[OF sorted step processed] by simp
qed

lemma finite_certificate_table_fold:
  assumes "sorted_wrt (<) rs"
    and "T = fimage (\<lambda>m. (m,finite_node_certificate N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
    and "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. fcard (resolution_reach N m) < j)"
  shows "foldl (finite_certificate_step (finite_node_ranked N)) T rs = fimage (\<lambda>m. (m,finite_node_certificate N m)) N"
  using finite_certificate_table_fold_in[where \<Theta>=resolution_empty_table, OF assms] by (simp only: finite_certificate_step_empty)

lemma finite_certificate_table_in_exact:
  "finite_certificate_table_in \<Theta> N (finite_node_ranked N) = fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m)) N"
proof -
  have ranks: "fimage (\<lambda>(m,k,L). k) (finite_node_ranked N) = fimage ((\<lambda>m. fcard (resolution_reach N m))) N"
    by (force simp: fset_eq_iff finite_node_ranked_def resolution_fset_simps)
  have "{||} = fimage (\<lambda>m. (m,finite_node_certificate_in \<Theta> N m))
      (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set (sorted_list_of_fset (fimage ((\<lambda>m. fcard (resolution_reach N m))) N))) N)"
    by (force simp: fset_eq_iff resolution_fset_simps)
  then show ?thesis unfolding finite_certificate_table_in_def ranks
    by (rule finite_certificate_table_fold_in[rotated]) (auto simp: sorted_list_of_fset.rep_eq)
qed

lemma finite_certificate_table_exact:
  "finite_certificate_table (finite_node_ranked N) = fimage (\<lambda>m. (m,finite_node_certificate N m)) N"
  using finite_certificate_table_in_exact[of resolution_empty_table N] by (simp only: finite_certificate_table_empty)

lemma finite_certificate_table_in_proof:
  "m |\<in>| N \<Longrightarrow> the (finite_relation_option (finite_certificate_table_in \<Theta> N (finite_node_ranked N)) m) =
    finite_node_proof_in \<Theta> (fcard N) N m"
  by (simp add: finite_certificate_table_in_exact finite_relation_option_keyed finite_state_node_certificate_in)

lemma finite_certificate_table_proof:
  "m |\<in>| N \<Longrightarrow> the (finite_relation_option (finite_certificate_table (finite_node_ranked N)) m) = finite_node_proof (fcard N) N m"
  using finite_certificate_table_in_proof[of m N resolution_empty_table] by (simp only: finite_certificate_table_empty)

section \<open>The reach of a root\<close>

text \<open>
  The nodes a certificate reads from its root, transitively: from the root, in decreasing rank, each reached node adds
  the nodes it links to, which stand at lesser ranks; one pass over the ranks reaches them all
  (@{text finite_link_reach}).
\<close>

definition finite_link_edges ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> (('a,'s,'d,'c) resolution_node \<times> ('a,'s,'d,'c) resolution_node) set" where
  "finite_link_edges N = {(n,m). \<exists>s. (s,m) |\<in>| finite_node_links N n}"

definition finite_reach_step ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_node fset \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_reach_step K T r = T |\<union>| ffUnion (fimage (\<lambda>(m,k,L). if k=r \<and> m |\<in>| T then fimage snd L else {||}) K)"

definition finite_ranked_reach ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_ranked_reach K nd = foldl (finite_reach_step K) {|nd|} (rev (sorted_list_of_fset (fimage (\<lambda>(m,k,L). k) K)))"

definition finite_link_reach ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_link_reach N nd = finite_ranked_reach (finite_node_ranked N) nd"

lemma finite_reach_step_member:
  "x |\<in>| finite_reach_step (finite_node_ranked N) T r \<longleftrightarrow> x |\<in>| T \<or>
    (\<exists>m s. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> m |\<in>| T \<and> (s,x) |\<in>| finite_node_links N m)"
  by (force simp: finite_reach_step_def finite_node_ranked_def resolution_fset_simps split: if_splits)

lemma finite_reach_fold:
  assumes "sorted_wrt (>) rs" and "nd |\<in>| T" and "T |\<subseteq>| N"
    and "\<forall>m. m |\<in>| T \<longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    and "\<forall>m. m |\<in>| T \<longrightarrow> fcard (resolution_reach N m) \<in> set rs \<or> (\<forall>s m'. (s,m') |\<in>| finite_node_links N m \<longrightarrow> m' |\<in>| T)"
    and "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. j < fcard (resolution_reach N m))"
  shows "nd |\<in>| foldl (finite_reach_step (finite_node_ranked N)) T rs \<and>
    foldl (finite_reach_step (finite_node_ranked N)) T rs |\<subseteq>| N \<and>
    (\<forall>m. m |\<in>| foldl (finite_reach_step (finite_node_ranked N)) T rs \<longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*) \<and>
    (\<forall>m s m'. m |\<in>| foldl (finite_reach_step (finite_node_ranked N)) T rs \<longrightarrow> (s,m') |\<in>| finite_node_links N m \<longrightarrow>
      m' |\<in>| foldl (finite_reach_step (finite_node_ranked N)) T rs)"
  using assms
proof (induction rs arbitrary: T)
  case Nil
  then show ?case by auto
next
  case (Cons r rs)
  let ?T = "finite_reach_step (finite_node_ranked N) T r"
  have sorted: "sorted_wrt (>) rs" and below: "\<forall>j\<in>set rs. j < r" using Cons.prems(1) by simp_all
  have new: "m |\<in>| N \<and> fcard (resolution_reach N m) < r \<and> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    if "m0 |\<in>| N" "fcard (resolution_reach N m0) = r" "m0 |\<in>| T" "(s,m) |\<in>| finite_node_links N m0" for m0 s m
  proof -
    have "m |\<in>| N" "fcard (resolution_reach N m) < fcard (resolution_reach N m0)"
      using finite_node_links_reach(1)[OF that(4)] finite_node_links_reach(2)[OF that(4) that(1)] by auto
    moreover have "(nd,m) \<in> (finite_link_edges N)\<^sup>*"
      using Cons.prems(4) that(3,4) by (auto simp: finite_link_edges_def intro: rtrancl_into_rtrancl)
    ultimately show ?thesis using that(2) by simp
  qed
  have root: "nd |\<in>| ?T" using Cons.prems(2) by (simp add: finite_reach_step_member)
  have inside: "?T |\<subseteq>| N" using Cons.prems(3) new by (auto simp: finite_reach_step_member)
  have reach: "\<forall>m. m |\<in>| ?T \<longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    using Cons.prems(4) new by (auto simp: finite_reach_step_member)
  have pending: "\<forall>m. m |\<in>| ?T \<longrightarrow> fcard (resolution_reach N m) \<in> set rs \<or> (\<forall>s m'. (s,m') |\<in>| finite_node_links N m \<longrightarrow> m' |\<in>| ?T)"
  proof (intro allI impI)
    fix m assume m: "m |\<in>| ?T"
    show "fcard (resolution_reach N m) \<in> set rs \<or> (\<forall>s m'. (s,m') |\<in>| finite_node_links N m \<longrightarrow> m' |\<in>| ?T)"
    proof (cases "m |\<in>| T")
      case True
      then have mN: "m |\<in>| N" using Cons.prems(3) by auto
      from Cons.prems(5) True consider "fcard (resolution_reach N m) = r" | "fcard (resolution_reach N m) \<in> set rs"
        | "\<forall>s m'. (s,m') |\<in>| finite_node_links N m \<longrightarrow> m' |\<in>| T" by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using mN True by (auto simp: finite_reach_step_member)
      next
        case 2
        then show ?thesis by blast
      next
        case 3
        then show ?thesis by (auto simp: finite_reach_step_member)
      qed
    next
      case False
      then obtain m0 s where "m0 |\<in>| N" "fcard (resolution_reach N m0) = r" "m0 |\<in>| T" "(s,m) |\<in>| finite_node_links N m0"
        using m by (auto simp: finite_reach_step_member)
      from new[OF this] have mN: "m |\<in>| N" and less: "fcard (resolution_reach N m) < r" by auto
      have "fcard (resolution_reach N m) \<in> set rs"
      proof (rule ccontr)
        assume "fcard (resolution_reach N m) \<notin> set rs"
        then have "fcard (resolution_reach N m) \<notin> set (r#rs)" using less by auto
        then have "r < fcard (resolution_reach N m)" using Cons.prems(6) mN by auto
        then show False using less by simp
      qed
      then show ?thesis by blast
    qed
  qed
  have processed: "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. j < fcard (resolution_reach N m))"
    using Cons.prems(6) below by fastforce
  show ?case using Cons.IH[OF sorted root inside reach pending processed] by simp
qed

lemma finite_link_reach:
  assumes nd: "nd |\<in>| N"
  shows "nd |\<in>| finite_link_reach N nd" "finite_link_reach N nd |\<subseteq>| N"
    "\<And>m. m |\<in>| finite_link_reach N nd \<Longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    "\<And>m s m'. m |\<in>| finite_link_reach N nd \<Longrightarrow> (s,m') |\<in>| finite_node_links N m \<Longrightarrow> m' |\<in>| finite_link_reach N nd"
proof -
  have ranks: "fimage (\<lambda>(m,k,L). k) (finite_node_ranked N) = fimage ((\<lambda>m. fcard (resolution_reach N m))) N"
    by (force simp: fset_eq_iff finite_node_ranked_def resolution_fset_simps)
  let ?rs = "rev (sorted_list_of_fset (fimage ((\<lambda>m. fcard (resolution_reach N m))) N))"
  have sorted: "sorted_wrt (>) ?rs" by (simp add: sorted_wrt_rev sorted_list_of_fset.rep_eq)
  have all: "fcard (resolution_reach N m) \<in> set ?rs" if "m |\<in>| N" for m using that by simp
  have "nd |\<in>| foldl (finite_reach_step (finite_node_ranked N)) {|nd|} ?rs \<and>
    foldl (finite_reach_step (finite_node_ranked N)) {|nd|} ?rs |\<subseteq>| N \<and>
    (\<forall>m. m |\<in>| foldl (finite_reach_step (finite_node_ranked N)) {|nd|} ?rs \<longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*) \<and>
    (\<forall>m s m'. m |\<in>| foldl (finite_reach_step (finite_node_ranked N)) {|nd|} ?rs \<longrightarrow> (s,m') |\<in>| finite_node_links N m \<longrightarrow>
      m' |\<in>| foldl (finite_reach_step (finite_node_ranked N)) {|nd|} ?rs)"
    by (rule finite_reach_fold[OF sorted]) (use nd all in auto)
  then show "nd |\<in>| finite_link_reach N nd" "finite_link_reach N nd |\<subseteq>| N"
    "\<And>m. m |\<in>| finite_link_reach N nd \<Longrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    "\<And>m s m'. m |\<in>| finite_link_reach N nd \<Longrightarrow> (s,m') |\<in>| finite_node_links N m \<Longrightarrow> m' |\<in>| finite_link_reach N nd"
    unfolding finite_link_reach_def finite_ranked_reach_def ranks by blast+
qed

section \<open>The derivation graph of a found state\<close>

text \<open>
  The graph of a state at a root: an inference of the library's graphs (@{text Factor_Executable_Graphs}), its nodes the
  root's reach, each node's inference its clause and values, and a premise discharged to the node its certificate reads
  there. A node's claim is its site and the residual term of its call.
\<close>

definition finite_state_graph ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('a,'s,'c,('a,'s,'d,'c) resolution_node) finite_derivation_graph" where
  "finite_state_graph N nd = \<lparr>finite_graph_inferences = fimage (\<lambda>m. (m,Finite_Inference (resolution_node_clause m)
      (finite_node_values m))) (finite_link_reach N nd),
    finite_graph_discharges = ffUnion (fimage (\<lambda>n. fimage (\<lambda>(s,m). ((n,s),m)) (finite_node_links N n))
      (finite_link_reach N nd))\<rparr>"

definition finite_state_claims ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_state_claims N nd = fimage (\<lambda>m. (m,resolution_node_site m,finite_residual_term (resolution_node_call m)))
    (finite_link_reach N nd)"

definition finite_node_link_claims ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_node_link_claims N n = fimage (\<lambda>(s,m). (s,resolution_node_site m,finite_residual_term (resolution_node_call m)))
    (finite_node_links N n)"

definition finite_state_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_state_graph_check P d t N nd = finite_graph_reading P (finite_state_graph N nd) nd d t (finite_state_claims N nd)"

lemma finite_state_graph_inference_member:
  "(n,A) |\<in>| finite_graph_inferences (finite_state_graph N nd) \<longleftrightarrow>
    n |\<in>| finite_link_reach N nd \<and> A = Finite_Inference (resolution_node_clause n) (finite_node_values n)"
  by (force simp: finite_state_graph_def resolution_fset_simps)

lemma finite_state_graph_discharge_member:
  "((n,s),m) |\<in>| finite_graph_discharges (finite_state_graph N nd) \<longleftrightarrow>
    n |\<in>| finite_link_reach N nd \<and> (s,m) |\<in>| finite_node_links N n"
  by (force simp: finite_state_graph_def resolution_fset_simps)

lemma finite_state_graph_nodes: "finite_graph_nodes (finite_state_graph N nd) = finite_link_reach N nd"
  by (rule fset_eqI) (force simp: finite_graph_nodes_def finite_state_graph_def resolution_fset_simps)

lemma finite_state_graph_edge_member:
  "(m,n) |\<in>| finite_graph_edges (finite_state_graph N nd) \<longleftrightarrow>
    n |\<in>| finite_link_reach N nd \<and> (\<exists>s. (s,m) |\<in>| finite_node_links N n)"
  by (force simp: finite_graph_edges_def finite_state_graph_def resolution_fset_simps)

lemma finite_state_graph_premises:
  assumes "n |\<in>| finite_link_reach N nd"
  shows "finite_graph_premises (finite_state_graph N nd) n = finite_node_links N n"
  using assms by (force simp: fset_eq_iff finite_graph_premises_def finite_state_graph_def resolution_fset_simps)

lemma finite_state_claims_member:
  "(m,e,x) |\<in>| finite_state_claims N nd \<longleftrightarrow>
    m |\<in>| finite_link_reach N nd \<and> e=resolution_node_site m \<and> x=finite_residual_term (resolution_node_call m)"
  by (force simp: finite_state_claims_def resolution_fset_simps)

lemma finite_state_graph_link_claims:
  assumes nd: "nd |\<in>| N" and n: "n |\<in>| finite_link_reach N nd"
  shows "finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n = finite_node_link_claims N n"
proof -
  have pt: "(s,e,x) |\<in>| finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n \<longleftrightarrow>
    (s,e,x) |\<in>| finite_node_link_claims N n" for s e x
  proof -
    have "(s,e,x) |\<in>| finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n \<longleftrightarrow>
        (\<exists>m. (s,m) |\<in>| finite_node_links N n \<and> (m,e,x) |\<in>| finite_state_claims N nd)"
      unfolding finite_link_claims_def finite_edge_compose_member finite_state_graph_premises[OF n] by blast
    also have "\<dots> \<longleftrightarrow> (s,e,x) |\<in>| finite_node_link_claims N n"
      using finite_link_reach(4)[OF nd n]
      by (force simp: finite_state_claims_member finite_node_link_claims_def resolution_fset_simps)
    finally show ?thesis .
  qed
  show ?thesis by (intro fset_eqI) (auto simp: split_paired_all pt)
qed

lemma finite_state_graph_formed:
  assumes nd: "nd |\<in>| N"
  shows "finite_graph_formed (finite_state_graph N nd) nd \<longleftrightarrow>
    fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n))"
proof -
  let ?G = "finite_state_graph N nd" and ?R = "finite_link_reach N nd"
  have inf: "finite_relation_functional (finite_graph_inferences ?G)"
    by (rule finite_relation_functional_intro) (simp add: finite_state_graph_inference_member)
  have dis: "finite_relation_functional (finite_graph_discharges ?G) \<longleftrightarrow>
      fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links N n))"
  proof
    assume D: "finite_relation_functional (finite_graph_discharges ?G)"
    show "fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links N n))"
    proof (intro ballI finite_relation_functional_intro)
      fix n s m m' assume n: "n |\<in>| ?R" and l: "(s,m) |\<in>| finite_node_links N n" "(s,m') |\<in>| finite_node_links N n"
      have "((n,s),m) |\<in>| finite_graph_discharges ?G" "((n,s),m') |\<in>| finite_graph_discharges ?G"
        using n l by (simp_all add: finite_state_graph_discharge_member)
      then show "m = m'" by (rule finite_relation_functional_at[OF D])
    qed
  next
    assume L: "fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links N n))"
    show "finite_relation_functional (finite_graph_discharges ?G)"
    proof (rule finite_relation_functional_intro)
      fix x y z assume y: "(x,y) |\<in>| finite_graph_discharges ?G" and z: "(x,z) |\<in>| finite_graph_discharges ?G"
      obtain n s where x: "x = (n,s)" by (cases x) auto
      have n: "n |\<in>| ?R" and l: "(s,y) |\<in>| finite_node_links N n" "(s,z) |\<in>| finite_node_links N n"
        using y z x by (simp_all add: finite_state_graph_discharge_member)
      from L n have "finite_relation_functional (finite_node_links N n)" by blast
      then show "y = z" using l by (rule finite_relation_functional_at)
    qed
  qed
  have "finite_assertion_uses ?G = {||}"
    by (force simp: fset_eq_iff finite_assertion_uses_def finite_state_graph_inference_member resolution_fset_simps)
  then have ass: "finite_relation_functional (finite_assertion_uses ?G)"
    by (simp add: finite_relation_functional_def)
  have inside: "fBall (finite_graph_edges ?G) (\<lambda>(m,n). m |\<in>| finite_graph_nodes ?G \<and> n |\<in>| finite_graph_nodes ?G)"
    using finite_link_reach(4)[OF nd] by (auto simp: finite_state_graph_nodes finite_state_graph_edge_member)
  have chain: "m |\<in>| ?R \<and> (m,nd) \<in> (fset (finite_graph_edges ?G))\<^sup>*" if "(nd,m) \<in> (finite_link_edges N)\<^sup>*" for m
    using that
  proof (induction rule: rtrancl_induct)
    case base
    then show ?case using finite_link_reach(1)[OF nd] by simp
  next
    case (step y z)
    then obtain s where link: "(s,z) |\<in>| finite_node_links N y" by (auto simp: finite_link_edges_def)
    have "z |\<in>| ?R" using finite_link_reach(4)[OF nd] step.IH link by blast
    moreover have "(z,y) \<in> fset (finite_graph_edges ?G)" using step.IH link by (auto simp: finite_state_graph_edge_member)
    ultimately show ?case using step.IH by (auto intro: converse_rtrancl_into_rtrancl)
  qed
  have reaches: "fBall (finite_graph_nodes ?G) (\<lambda>n. finite_edge_reaches (finite_graph_edges ?G) n nd)"
    using chain finite_link_reach(3)[OF nd] by (auto simp: finite_state_graph_nodes finite_edge_reaches_correct)
  have "fset (finite_graph_edges ?G) \<subseteq> measure ((\<lambda>m. fcard (resolution_reach N m)))"
  proof
    fix z assume z: "z \<in> fset (finite_graph_edges ?G)"
    obtain m n where mn: "z=(m,n)" by (cases z) auto
    then obtain s where link: "(s,m) |\<in>| finite_node_links N n" and nR: "n |\<in>| ?R"
      using z by (auto simp: finite_state_graph_edge_member)
    have "n |\<in>| N" using nR finite_link_reach(2)[OF nd] by auto
    then show "z \<in> measure ((\<lambda>m. fcard (resolution_reach N m)))"
      using finite_node_links_reach(2)[OF link] mn by auto
  qed
  then have wf: "finite_edge_wellfounded (finite_graph_edges ?G)"
    unfolding finite_edge_wellfounded_correct by (rule wf_subset[OF wf_measure])
  show ?thesis
    unfolding finite_graph_formed_def using inf ass inside reaches wf finite_link_reach(1)[OF nd] dis
    by (simp add: finite_state_graph_nodes)
qed

lemma finite_state_claims_at:
  "n |\<in>| finite_link_reach N nd \<Longrightarrow> fBex (finite_state_claims N nd) (\<lambda>(m,e,x). m=n \<and> Q e x) \<longleftrightarrow>
    Q (resolution_node_site n) (finite_residual_term (resolution_node_call n))"
  by (force simp: finite_state_claims_def resolution_fset_simps)

lemma finite_state_graph_node_check:
  assumes nd: "nd |\<in>| N" and n: "n |\<in>| finite_link_reach N nd"
  shows "finite_checks_graph_node P (finite_state_graph N nd) (finite_state_claims N nd) n (Finite_Inference c V) \<longleftrightarrow>
    finite_admitted_schema_instance P (resolution_node_site n) c V (finite_residual_term (resolution_node_call n))
      (finite_node_link_claims N n)"
proof -
  have "finite_checks_graph_node P (finite_state_graph N nd) (finite_state_claims N nd) n (Finite_Inference c V) \<longleftrightarrow>
      fBex (finite_state_claims N nd) (\<lambda>(m,e,x). m=n \<and> finite_admitted_schema_instance P e c V x
        (finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n))"
    by simp
  also have "\<dots> \<longleftrightarrow> finite_admitted_schema_instance P (resolution_node_site n) c V (finite_residual_term (resolution_node_call n))
      (finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n)"
    by (rule finite_state_claims_at[OF n, where Q="\<lambda>e x. finite_admitted_schema_instance P e c V x
      (finite_link_claims (finite_state_graph N nd) (finite_state_claims N nd) n)"])
  finally show ?thesis by (simp only: finite_state_graph_link_claims[OF nd n])
qed

theorem finite_state_graph_check_iff:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_check P d t N nd \<longleftrightarrow>
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and>
    fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n))"
proof -
  let ?R = "finite_link_reach N nd"
  have Jf: "finite_relation_functional (finite_state_claims N nd)"
    by (rule finite_relation_functional_intro) (auto simp: finite_state_claims_def resolution_fset_simps)
  have Jd: "fimage fst (finite_state_claims N nd) = finite_graph_nodes (finite_state_graph N nd)"
    by (rule fset_eqI) (force simp: finite_state_graph_nodes finite_state_claims_def resolution_fset_simps)
  have Jr: "(nd,d,t) |\<in>| finite_state_claims N nd \<longleftrightarrow>
      resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t"
    using finite_link_reach(1)[OF nd] by (auto simp: finite_state_claims_member)
  have checks: "fBall (finite_graph_inferences (finite_state_graph N nd))
      (\<lambda>(n,A). finite_checks_graph_node P (finite_state_graph N nd) (finite_state_claims N nd) n A) \<longleftrightarrow>
    fBall ?R (\<lambda>n. finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n)
      (finite_node_values n) (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n))"
  proof -
    have "fBall (finite_graph_inferences (finite_state_graph N nd))
        (\<lambda>(n,A). finite_checks_graph_node P (finite_state_graph N nd) (finite_state_claims N nd) n A) \<longleftrightarrow>
      fBall ?R (\<lambda>n. finite_checks_graph_node P (finite_state_graph N nd) (finite_state_claims N nd) n
        (Finite_Inference (resolution_node_clause n) (finite_node_values n)))"
      by (simp add: finite_state_graph_def fimage.rep_eq)
    also have "\<dots> \<longleftrightarrow> fBall ?R (\<lambda>n. finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n)
      (finite_node_values n) (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n))"
      by (auto simp del: finite_checks_graph_node.simps simp add: finite_state_graph_node_check[OF nd])
    finally show ?thesis .
  qed
  show ?thesis
    unfolding finite_state_graph_check_def finite_graph_reading_def
    using finite_state_graph_formed[OF nd] Jf Jd Jr checks by auto
qed

section \<open>The derivation graph at a table\<close>

text \<open>
  At a table the graph of a found state holds, beside the nodes a certificate reads from its root, an assertion node at
  every table link of a reached node: no inference supplies it, its claim is the entry's call, and the premise the table
  closed is discharged to it. The claims of the assertion nodes are the graph's assumption boundary, all among the
  table's calls (@{text finite_state_graph_in_assumptions}), so the graph reading accepts the derivation conditional on
  the table's entries (@{thm [source] finite_graph_reading_conditional_sound}). At the empty table there is no assertion
  node, and the graph, its claims and its check are the state's.
\<close>

definition finite_table_discharges ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ((('a,'s,'d,'c) resolution_node \<times> 's) \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_table_discharges \<Theta> N nd = ffUnion (fimage (\<lambda>n. fimage (\<lambda>(s,a). ((n,s),a)) (finite_table_links \<Theta> N n))
    (finite_link_reach N nd))"

definition finite_state_graph_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('a,'s,'c,('a,'s,'d,'c) resolution_node) finite_derivation_graph" where
  "finite_state_graph_in \<Theta> N nd = \<lparr>finite_graph_inferences = finite_graph_inferences (finite_state_graph N nd) |\<union>|
      fimage (\<lambda>((n,s),a). (a,Finite_Assertion)) (finite_table_discharges \<Theta> N nd),
    finite_graph_discharges = finite_graph_discharges (finite_state_graph N nd) |\<union>| finite_table_discharges \<Theta> N nd\<rparr>"

definition finite_state_claims_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_state_claims_in \<Theta> N nd = finite_state_claims N nd |\<union>|
    fimage (\<lambda>((n,s),a). (a,resolution_node_site a,finite_residual_term (resolution_node_call a))) (finite_table_discharges \<Theta> N nd)"

definition finite_table_link_claims ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s \<times> ('d \<times> finite_factor_term)) fset" where
  "finite_table_link_claims \<Theta> N n = fimage (\<lambda>(s,a). (s,resolution_node_site a,finite_residual_term (resolution_node_call a)))
    (finite_table_links \<Theta> N n)"

definition finite_state_graph_check_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_state_graph_check_in \<Theta> P d t N nd =
    finite_graph_reading P (finite_state_graph_in \<Theta> N nd) nd d t (finite_state_claims_in \<Theta> N nd)"

lemma finite_table_discharges_member:
  "((n,s),a) |\<in>| finite_table_discharges \<Theta> N nd \<longleftrightarrow> n |\<in>| finite_link_reach N nd \<and> (s,a) |\<in>| finite_table_links \<Theta> N n"
  by (force simp: finite_table_discharges_def resolution_fset_simps)

lemma finite_table_discharges_empty [simp]: "finite_table_discharges resolution_empty_table N nd = {||}"
  by (rule fset_eqI) (auto simp: finite_table_discharges_def resolution_fset_simps)

lemma finite_state_graph_in_empty [simp]: "finite_state_graph_in resolution_empty_table N nd = finite_state_graph N nd"
  by (simp add: finite_state_graph_in_def finite_state_graph_def)

lemma finite_state_claims_in_empty [simp]: "finite_state_claims_in resolution_empty_table N nd = finite_state_claims N nd"
  by (simp add: finite_state_claims_in_def)

lemma finite_state_graph_check_in_empty:
  "finite_state_graph_check_in resolution_empty_table P d t N nd = finite_state_graph_check P d t N nd"
  by (simp add: finite_state_graph_check_in_def finite_state_graph_check_def)

lemma finite_table_discharges_out:
  assumes nd: "nd |\<in>| N" and D: "((n,s),a) |\<in>| finite_table_discharges \<Theta> N nd"
  shows "a |\<notin>| finite_link_reach N nd" "n |\<in>| finite_link_reach N nd" "(s,a) |\<in>| finite_table_links \<Theta> N n"
proof -
  have n: "n |\<in>| finite_link_reach N nd" and l: "(s,a) |\<in>| finite_table_links \<Theta> N n"
    using D by (simp_all add: finite_table_discharges_member)
  show "a |\<notin>| finite_link_reach N nd" using finite_table_links_notin[OF l] finite_link_reach(2)[OF nd] by auto
  show "n |\<in>| finite_link_reach N nd" by (rule n)
  show "(s,a) |\<in>| finite_table_links \<Theta> N n" by (rule l)
qed

lemma finite_state_graph_in_inference_member:
  "(n,A) |\<in>| finite_graph_inferences (finite_state_graph_in \<Theta> N nd) \<longleftrightarrow>
    (n |\<in>| finite_link_reach N nd \<and> A = Finite_Inference (resolution_node_clause n) (finite_node_values n)) \<or>
    (A = Finite_Assertion \<and> (\<exists>m s. ((m,s),n) |\<in>| finite_table_discharges \<Theta> N nd))"
  by (force simp: finite_state_graph_in_def finite_state_graph_inference_member resolution_fset_simps)

lemma finite_state_graph_in_discharge_member:
  "((n,s),m) |\<in>| finite_graph_discharges (finite_state_graph_in \<Theta> N nd) \<longleftrightarrow>
    n |\<in>| finite_link_reach N nd \<and> (s,m) |\<in>| finite_node_links_in \<Theta> N n"
  by (auto simp: finite_state_graph_in_def finite_state_graph_discharge_member finite_table_discharges_member
    finite_node_links_in_def)

lemma finite_state_graph_in_nodes:
  "finite_graph_nodes (finite_state_graph_in \<Theta> N nd) = finite_link_reach N nd |\<union>| fimage snd (finite_table_discharges \<Theta> N nd)"
  by (rule fset_eqI) (force simp: finite_graph_nodes_def finite_state_graph_in_def finite_state_graph_def resolution_fset_simps)

lemma finite_graph_edges_member:
  "(m,n) |\<in>| finite_graph_edges G \<longleftrightarrow> (\<exists>s. ((n,s),m) |\<in>| finite_graph_discharges G)"
  by (force simp: finite_graph_edges_def resolution_fset_simps)

lemma finite_state_graph_in_edge_member:
  "(m,n) |\<in>| finite_graph_edges (finite_state_graph_in \<Theta> N nd) \<longleftrightarrow>
    n |\<in>| finite_link_reach N nd \<and> (\<exists>s. (s,m) |\<in>| finite_node_links_in \<Theta> N n)"
  by (auto simp: finite_graph_edges_member finite_state_graph_in_discharge_member)

lemma finite_state_graph_in_premises:
  "n |\<in>| finite_link_reach N nd \<Longrightarrow> finite_graph_premises (finite_state_graph_in \<Theta> N nd) n = finite_node_links_in \<Theta> N n"
  "n |\<notin>| finite_link_reach N nd \<Longrightarrow> finite_graph_premises (finite_state_graph_in \<Theta> N nd) n = {||}"
  by (force simp: fset_eq_iff finite_graph_premises_def finite_state_graph_in_discharge_member resolution_fset_simps)+

lemma finite_state_claims_in_member:
  "(m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd \<longleftrightarrow>
    (m |\<in>| finite_link_reach N nd \<or> (\<exists>n s. ((n,s),m) |\<in>| finite_table_discharges \<Theta> N nd)) \<and>
    e=resolution_node_site m \<and> x=finite_residual_term (resolution_node_call m)"
  by (force simp: finite_state_claims_in_def finite_state_claims_member resolution_fset_simps)

lemma finite_state_claims_in_at:
  assumes "n |\<in>| finite_link_reach N nd \<or> (\<exists>m s. ((m,s),n) |\<in>| finite_table_discharges \<Theta> N nd)"
  shows "fBex (finite_state_claims_in \<Theta> N nd) (\<lambda>(m,e,x). m=n \<and> Q e x) \<longleftrightarrow>
    Q (resolution_node_site n) (finite_residual_term (resolution_node_call n))"
proof
  assume "fBex (finite_state_claims_in \<Theta> N nd) (\<lambda>(m,e,x). m=n \<and> Q e x)"
  then obtain m e x where "(m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd" "m=n" "Q e x" by auto
  then show "Q (resolution_node_site n) (finite_residual_term (resolution_node_call n))"
    by (simp add: finite_state_claims_in_member)
next
  assume "Q (resolution_node_site n) (finite_residual_term (resolution_node_call n))"
  moreover have "(n,resolution_node_site n,finite_residual_term (resolution_node_call n)) |\<in>| finite_state_claims_in \<Theta> N nd"
    using assms by (simp add: finite_state_claims_in_member)
  ultimately show "fBex (finite_state_claims_in \<Theta> N nd) (\<lambda>(m,e,x). m=n \<and> Q e x)" by force
qed

lemma finite_state_graph_in_link_claims:
  assumes nd: "nd |\<in>| N" and n: "n |\<in>| finite_link_reach N nd"
  shows "finite_link_claims (finite_state_graph_in \<Theta> N nd) (finite_state_claims_in \<Theta> N nd) n =
    finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n"
proof -
  have pt: "(s,e,x) |\<in>| finite_link_claims (finite_state_graph_in \<Theta> N nd) (finite_state_claims_in \<Theta> N nd) n \<longleftrightarrow>
    (s,e,x) |\<in>| finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n" for s e x
  proof -
    have "(s,e,x) |\<in>| finite_link_claims (finite_state_graph_in \<Theta> N nd) (finite_state_claims_in \<Theta> N nd) n \<longleftrightarrow>
        (\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> (m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd)"
      unfolding finite_link_claims_def finite_edge_compose_member finite_state_graph_in_premises(1)[OF n] by blast
    also have "\<dots> \<longleftrightarrow> (\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> e=resolution_node_site m \<and>
        x=finite_residual_term (resolution_node_call m))"
    proof -
      have inside: "m |\<in>| finite_link_reach N nd \<or> (\<exists>n' s'. ((n',s'),m) |\<in>| finite_table_discharges \<Theta> N nd)"
        if "(s,m) |\<in>| finite_node_links_in \<Theta> N n" for m
        using that finite_link_reach(4)[OF nd n] n by (auto simp: finite_node_links_in_def finite_table_discharges_member)
      show ?thesis
      proof
        assume "\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> (m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd"
        then show "\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> e=resolution_node_site m \<and>
            x=finite_residual_term (resolution_node_call m)"
          by (auto simp: finite_state_claims_in_member)
      next
        assume "\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> e=resolution_node_site m \<and>
            x=finite_residual_term (resolution_node_call m)"
        then obtain m where m: "(s,m) |\<in>| finite_node_links_in \<Theta> N n" "e=resolution_node_site m"
            "x=finite_residual_term (resolution_node_call m)" by blast
        then have "(m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd" using inside[OF m(1)] by (simp add: finite_state_claims_in_member)
        then show "\<exists>m. (s,m) |\<in>| finite_node_links_in \<Theta> N n \<and> (m,e,x) |\<in>| finite_state_claims_in \<Theta> N nd"
          using m(1) by blast
      qed
    qed
    also have "\<dots> \<longleftrightarrow> (s,e,x) |\<in>| finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n"
      by (force simp: finite_node_links_in_def finite_node_link_claims_def finite_table_link_claims_def resolution_fset_simps)
    finally show ?thesis .
  qed
  show ?thesis by (intro fset_eqI) (auto simp: split_paired_all pt)
qed

lemma finite_state_graph_in_formed:
  assumes nd: "nd |\<in>| N"
  shows "finite_graph_formed (finite_state_graph_in \<Theta> N nd) nd \<longleftrightarrow>
    fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links_in \<Theta> N n)) \<and>
    finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd))"
proof -
  let ?G = "finite_state_graph_in \<Theta> N nd" and ?R = "finite_link_reach N nd" and ?D = "finite_table_discharges \<Theta> N nd"
  have inf: "finite_relation_functional (finite_graph_inferences ?G)"
  proof (rule finite_relation_functional_intro)
    fix x A B assume A: "(x,A) |\<in>| finite_graph_inferences ?G" and B: "(x,B) |\<in>| finite_graph_inferences ?G"
    have out: "x |\<notin>| ?R" if "((m,s),x) |\<in>| ?D" for m s using finite_table_discharges_out(1)[OF nd that] .
    show "A = B" using A B out unfolding finite_state_graph_in_inference_member by blast
  qed
  have dis: "finite_relation_functional (finite_graph_discharges ?G) \<longleftrightarrow>
      fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links_in \<Theta> N n))"
  proof
    assume D: "finite_relation_functional (finite_graph_discharges ?G)"
    show "fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links_in \<Theta> N n))"
    proof (intro ballI finite_relation_functional_intro)
      fix n s m m' assume n: "n |\<in>| ?R" and l: "(s,m) |\<in>| finite_node_links_in \<Theta> N n" "(s,m') |\<in>| finite_node_links_in \<Theta> N n"
      have "((n,s),m) |\<in>| finite_graph_discharges ?G" "((n,s),m') |\<in>| finite_graph_discharges ?G"
        using n l by (simp_all add: finite_state_graph_in_discharge_member)
      then show "m = m'" by (rule finite_relation_functional_at[OF D])
    qed
  next
    assume L: "fBall ?R (\<lambda>n. finite_relation_functional (finite_node_links_in \<Theta> N n))"
    show "finite_relation_functional (finite_graph_discharges ?G)"
    proof (rule finite_relation_functional_intro)
      fix x y z assume y: "(x,y) |\<in>| finite_graph_discharges ?G" and z: "(x,z) |\<in>| finite_graph_discharges ?G"
      obtain n s where x: "x = (n,s)" by (cases x) auto
      have n: "n |\<in>| ?R" and l: "(s,y) |\<in>| finite_node_links_in \<Theta> N n" "(s,z) |\<in>| finite_node_links_in \<Theta> N n"
        using y z x by (simp_all add: finite_state_graph_in_discharge_member)
      from L n have "finite_relation_functional (finite_node_links_in \<Theta> N n)" by blast
      then show "y = z" using l by (rule finite_relation_functional_at)
    qed
  qed
  have target: "m |\<in>| finite_graph_nodes ?G" if n: "n |\<in>| ?R" and l: "(s,m) |\<in>| finite_node_links_in \<Theta> N n" for n s m
  proof -
    from l consider "(s,m) |\<in>| finite_node_links N n" | "(s,m) |\<in>| finite_table_links \<Theta> N n"
      by (auto simp: finite_node_links_in_def)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using finite_link_reach(4)[OF nd n 1] by (simp add: finite_state_graph_in_nodes)
    next
      case 2
      then have "((n,s),m) |\<in>| ?D" using n by (simp add: finite_table_discharges_member)
      then show ?thesis by (force simp: finite_state_graph_in_nodes resolution_fset_simps)
    qed
  qed
  have inside: "fBall (finite_graph_edges ?G) (\<lambda>(m,n). m |\<in>| finite_graph_nodes ?G \<and> n |\<in>| finite_graph_nodes ?G)"
  proof (rule ballI, clarify)
    fix m n assume "(m,n) \<in> fset (finite_graph_edges ?G)"
    then obtain s where n: "n |\<in>| ?R" and l: "(s,m) |\<in>| finite_node_links_in \<Theta> N n"
      by (auto simp: finite_state_graph_in_edge_member)
    have "n |\<in>| finite_graph_nodes ?G" using n by (simp add: finite_state_graph_in_nodes)
    then show "m |\<in>| finite_graph_nodes ?G \<and> n |\<in>| finite_graph_nodes ?G" using target[OF n l] by simp
  qed
  have chain: "m |\<in>| ?R \<and> (m,nd) \<in> (fset (finite_graph_edges ?G))\<^sup>*" if "(nd,m) \<in> (finite_link_edges N)\<^sup>*" for m
    using that
  proof (induction rule: rtrancl_induct)
    case base
    then show ?case using finite_link_reach(1)[OF nd] by simp
  next
    case (step y z)
    then obtain s where link: "(s,z) |\<in>| finite_node_links N y" by (auto simp: finite_link_edges_def)
    have "z |\<in>| ?R" using finite_link_reach(4)[OF nd] step.IH link by blast
    moreover have "(z,y) \<in> fset (finite_graph_edges ?G)"
      using step.IH link by (auto simp: finite_state_graph_in_edge_member finite_node_links_in_def)
    ultimately show ?case using step.IH by (auto intro: converse_rtrancl_into_rtrancl)
  qed
  have reached: "(n,nd) \<in> (fset (finite_graph_edges ?G))\<^sup>*" if "n |\<in>| ?R" for n
    using chain finite_link_reach(3)[OF nd that] by blast
  have reaches: "fBall (finite_graph_nodes ?G) (\<lambda>n. finite_edge_reaches (finite_graph_edges ?G) n nd)"
  proof
    fix x assume "x \<in> fset (finite_graph_nodes ?G)"
    then consider "x |\<in>| ?R" | n s where "((n,s),x) |\<in>| ?D"
      by (force simp: finite_state_graph_in_nodes resolution_fset_simps)
    then show "finite_edge_reaches (finite_graph_edges ?G) x nd"
    proof cases
      case 1
      then show ?thesis using reached[OF 1] by (simp add: finite_edge_reaches_correct)
    next
      case (2 n s)
      then have n: "n |\<in>| ?R" and l: "(s,x) |\<in>| finite_table_links \<Theta> N n" by (simp_all add: finite_table_discharges_member)
      have "(x,n) \<in> fset (finite_graph_edges ?G)" using n l by (auto simp: finite_state_graph_in_edge_member finite_node_links_in_def)
      then show ?thesis using reached[OF n] by (auto simp: finite_edge_reaches_correct intro: converse_rtrancl_into_rtrancl)
    qed
  qed
  have "fset (finite_graph_edges ?G) \<subseteq> measure ((\<lambda>m. fcard (resolution_reach N m)))"
  proof
    fix z assume z: "z \<in> fset (finite_graph_edges ?G)"
    obtain m n where mn: "z=(m,n)" by (cases z) auto
    then obtain s where l: "(s,m) |\<in>| finite_node_links_in \<Theta> N n" and nR: "n |\<in>| ?R"
      using z by (auto simp: finite_state_graph_in_edge_member)
    have nN: "n |\<in>| N" using nR finite_link_reach(2)[OF nd] by auto
    from l consider "(s,m) |\<in>| finite_node_links N n" | "(s,m) |\<in>| finite_table_links \<Theta> N n"
      by (auto simp: finite_node_links_in_def)
    then have "fcard (resolution_reach N m) < fcard (resolution_reach N n)"
    proof cases
      case 1
      then show ?thesis by (rule finite_node_links_reach(2)[OF _ nN])
    next
      case 2
      then show ?thesis by (rule finite_table_links_reach[OF _ nN])
    qed
    then show "z \<in> measure ((\<lambda>m. fcard (resolution_reach N m)))" using mn by simp
  qed
  then have wf: "finite_edge_wellfounded (finite_graph_edges ?G)"
    unfolding finite_edge_wellfounded_correct by (rule wf_subset[OF wf_measure])
  have root: "nd |\<in>| finite_graph_nodes ?G" using finite_link_reach(1)[OF nd] by (simp add: finite_state_graph_in_nodes)
  show ?thesis unfolding finite_graph_formed_def using inf inside reaches wf root dis by auto
qed

lemma finite_state_graph_in_assertion_use:
  assumes nd: "nd |\<in>| N" and u: "(a,n,s) |\<in>| finite_assertion_uses (finite_state_graph_in \<Theta> N nd)"
  shows "n |\<in>| finite_link_reach N nd \<and> (s,a) |\<in>| finite_table_links \<Theta> N n"
proof -
  have dis: "((n,s),a) |\<in>| finite_graph_discharges (finite_state_graph_in \<Theta> N nd)"
    and as: "(a,Finite_Assertion) |\<in>| finite_graph_inferences (finite_state_graph_in \<Theta> N nd)"
    using u by (force simp: finite_assertion_uses_def resolution_fset_simps)+
  have nR: "n |\<in>| finite_link_reach N nd" and l: "(s,a) |\<in>| finite_node_links_in \<Theta> N n"
    using dis by (simp_all add: finite_state_graph_in_discharge_member)
  obtain m s' where D: "((m,s'),a) |\<in>| finite_table_discharges \<Theta> N nd"
    using as by (auto simp: finite_state_graph_in_inference_member)
  have "a |\<notin>| finite_link_reach N nd" by (rule finite_table_discharges_out(1)[OF nd D])
  then have "(s,a) |\<notin>| finite_node_links N n" using finite_link_reach(4)[OF nd nR] by blast
  then show ?thesis using nR l by (auto simp: finite_node_links_in_def)
qed

text \<open>
  Where the state's nodes stand at distinct positions, an assertion node's position names the node and the socket that
  discharge to it, so no assertion node is used twice.
\<close>

lemma finite_state_graph_in_uses:
  assumes nd: "nd |\<in>| N"
    and dist: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
  shows "finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd))"
proof (rule finite_relation_functional_intro)
  fix a x y assume ax: "(a,x) |\<in>| finite_assertion_uses (finite_state_graph_in \<Theta> N nd)"
    and ay: "(a,y) |\<in>| finite_assertion_uses (finite_state_graph_in \<Theta> N nd)"
  obtain n s where x: "x = (n,s)" by (cases x) auto
  obtain n' s' where y: "y = (n',s')" by (cases y) auto
  have n: "n |\<in>| finite_link_reach N nd" "(s,a) |\<in>| finite_table_links \<Theta> N n"
    using finite_state_graph_in_assertion_use[OF nd ax[unfolded x]] by blast+
  have n': "n' |\<in>| finite_link_reach N nd" "(s',a) |\<in>| finite_table_links \<Theta> N n'"
    using finite_state_graph_in_assertion_use[OF nd ay[unfolded y]] by blast+
  have "resolution_node_position a = resolution_node_position n@[s]" using n(2) by (auto simp: finite_table_links_member)
  moreover have "resolution_node_position a = resolution_node_position n'@[s']"
    using n'(2) by (auto simp: finite_table_links_member)
  ultimately have "resolution_node_position n@[s] = resolution_node_position n'@[s']" by simp
  then have "s = s'" "resolution_node_position n = resolution_node_position n'" by simp_all
  moreover have "n |\<in>| N" "n' |\<in>| N" using n(1) n'(1) finite_link_reach(2)[OF nd] by auto
  ultimately show "x = y" using dist x y by auto
qed

text \<open>
  Every assumption of the graph at a table is an entry's call.
\<close>

lemma finite_state_graph_in_assumptions:
  assumes a: "(n,e,u) |\<in>| finite_graph_assumptions (finite_state_graph_in \<Theta> N nd) (finite_state_claims_in \<Theta> N nd)"
  shows "\<exists>c. resolution_table_lookup \<Theta> (e,u) = Some c"
proof -
  have J: "(n,e,u) |\<in>| finite_state_claims_in \<Theta> N nd"
    and as: "(n,Finite_Assertion) |\<in>| finite_graph_inferences (finite_state_graph_in \<Theta> N nd)"
    using a by (auto simp: finite_graph_assumptions_def resolution_fset_simps)
  obtain m s where "((m,s),n) |\<in>| finite_table_discharges \<Theta> N nd"
    using as by (auto simp: finite_state_graph_in_inference_member)
  then have "(s,n) |\<in>| finite_table_links \<Theta> N m" by (simp add: finite_table_discharges_member)
  then obtain e' u' where l: "resolution_table_lookup \<Theta> (e',u') \<noteq> None" and n: "n = finite_table_node m s e' u'"
    by (auto simp: finite_table_links_member)
  have "e = e'" "u = u'" using J by (simp_all add: finite_state_claims_in_member n)
  then show ?thesis using l by auto
qed

theorem finite_state_graph_check_in_iff:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_check_in \<Theta> P d t N nd \<longleftrightarrow>
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and>
    finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd)) \<and>
    fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links_in \<Theta> N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n) \<and>
      fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
        (finite_residual_term (resolution_node_call a))))"
proof -
  let ?G = "finite_state_graph_in \<Theta> N nd" and ?J = "finite_state_claims_in \<Theta> N nd"
  let ?R = "finite_link_reach N nd" and ?D = "finite_table_discharges \<Theta> N nd"
  have Jf: "finite_relation_functional ?J"
    by (rule finite_relation_functional_intro) (force simp: finite_state_claims_in_def finite_state_claims_def resolution_fset_simps)
  have Jd: "fimage fst ?J = finite_graph_nodes ?G"
    by (rule fset_eqI) (force simp: finite_state_graph_in_nodes finite_state_claims_in_def finite_state_claims_def resolution_fset_simps)
  have Jr: "(nd,d,t) |\<in>| ?J \<longleftrightarrow> resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t"
    using finite_link_reach(1)[OF nd] by (auto simp: finite_state_claims_in_member)
  have node: "finite_checks_graph_node P ?G ?J n (Finite_Inference c V) \<longleftrightarrow>
      finite_admitted_schema_instance P (resolution_node_site n) c V (finite_residual_term (resolution_node_call n))
        (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n)" if n: "n |\<in>| ?R" for n c V
  proof -
    have "finite_checks_graph_node P ?G ?J n (Finite_Inference c V) \<longleftrightarrow>
        fBex ?J (\<lambda>(m,e,x). m=n \<and> finite_admitted_schema_instance P e c V x (finite_link_claims ?G ?J n))" by simp
    also have "\<dots> \<longleftrightarrow> finite_admitted_schema_instance P (resolution_node_site n) c V (finite_residual_term (resolution_node_call n))
        (finite_link_claims ?G ?J n)"
      by (rule finite_state_claims_in_at) (use n in blast)
    finally show ?thesis by (simp only: finite_state_graph_in_link_claims[OF nd n])
  qed
  have assertion: "finite_checks_graph_node P ?G ?J a Finite_Assertion \<longleftrightarrow>
      finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))"
    if D: "((n,s),a) |\<in>| ?D" for n s a
  proof -
    have "finite_graph_premises ?G a = {||}"
      by (rule finite_state_graph_in_premises(2)) (rule finite_table_discharges_out(1)[OF nd D])
    moreover have "fBex ?J (\<lambda>(m,e,x). m=a \<and> finite_schema_call_formed P e x) \<longleftrightarrow>
        finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))"
      by (rule finite_state_claims_in_at) (use D in blast)
    ultimately show ?thesis by simp
  qed
  have inf: "finite_graph_inferences ?G = fimage (\<lambda>m. (m,Finite_Inference (resolution_node_clause m) (finite_node_values m))) ?R |\<union>|
      fimage (\<lambda>((n,s),a). (a,Finite_Assertion)) ?D"
    by (simp add: finite_state_graph_in_def finite_state_graph_def)
  have one: "fBall (fimage (\<lambda>m. (m,Finite_Inference (resolution_node_clause m) (finite_node_values m))) ?R)
      (\<lambda>(n,A). finite_checks_graph_node P ?G ?J n A) \<longleftrightarrow>
    fBall ?R (\<lambda>n. finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
      (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n))"
    by (auto simp: fimage.rep_eq simp del: finite_checks_graph_node.simps simp add: node)
  have two: "fBall (fimage (\<lambda>((n,s),a). (a,Finite_Assertion)) ?D) (\<lambda>(n,A). finite_checks_graph_node P ?G ?J n A) \<longleftrightarrow>
    fBall ?D (\<lambda>((n,s),a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a)))"
    by (auto simp: fimage.rep_eq simp del: finite_checks_graph_node.simps simp add: assertion)
  have three: "fBall ?D (\<lambda>((n,s),a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))) \<longleftrightarrow>
    fBall ?R (\<lambda>n. fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
      (finite_residual_term (resolution_node_call a))))"
    by (auto simp: finite_table_discharges_def resolution_fset_simps)
  have checks: "fBall (finite_graph_inferences ?G) (\<lambda>(n,A). finite_checks_graph_node P ?G ?J n A) \<longleftrightarrow>
      fBall ?R (\<lambda>n. finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n)) \<and>
      fBall ?R (\<lambda>n. fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
        (finite_residual_term (resolution_node_call a))))"
    unfolding inf using one two three by (simp add: sup_fset.rep_eq ball_Un)
  show ?thesis
    unfolding finite_state_graph_check_in_def finite_graph_reading_def
    using finite_state_graph_in_formed[OF nd] Jf Jd Jr checks by auto
qed

section \<open>The graph reading gives the tree check\<close>

text \<open>
  The graph reading at a table gives the tree check of the certificate at that table wherever the entries its assumptions
  read are accepted at their calls, on every input; at a valid table they all are
  (@{text finite_state_graph_check_accepts_valid}), and the call then holds through the graph reading's conditional
  soundness (@{text finite_state_graph_check_true_in}). Today's check is the instance at the empty table, where the graph
  holds no assumption.
\<close>

theorem finite_state_graph_check_accepts_in:
  assumes nd: "nd |\<in>| N" and check: "finite_state_graph_check_in \<Theta> P d t N nd"
    and entries: "\<And>n s a. n |\<in>| finite_link_reach N nd \<Longrightarrow> (s,a) |\<in>| finite_table_links \<Theta> N n \<Longrightarrow>
      finite_checks_schema_proof P (finite_table_proof \<Theta> a) (resolution_node_site a) (finite_residual_term (resolution_node_call a))"
  shows "finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard N) N nd) d t"
proof -
  note char = check[unfolded finite_state_graph_check_in_iff[OF nd]]
  have node: "finite_checks_schema_proof P (finite_node_certificate_in \<Theta> N n) (resolution_node_site n)
      (finite_residual_term (resolution_node_call n))" if "n |\<in>| finite_link_reach N nd" for n
    using that
  proof (induction "fcard (resolution_reach N n)" arbitrary: n rule: less_induct)
    case less
    have lf: "finite_relation_functional (finite_node_links_in \<Theta> N n)"
      and adm: "finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n)"
      using char less.prems by auto
    have nN: "n |\<in>| N" using less.prems finite_link_reach(2)[OF nd] by auto
    let ?C = "fimage (\<lambda>(s,m). (s,finite_node_certificate_in \<Theta> N m)) (finite_node_links N n)"
    let ?E = "fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N n)"
    let ?f = "\<lambda>m. if m |\<in>| N then finite_node_certificate_in \<Theta> N m else finite_table_proof \<Theta> m"
    have C: "?C = fimage (\<lambda>(s,m). (s,?f m)) (finite_node_links N n)"
      by (rule fimage_cong[OF refl]) (auto dest: finite_node_links_reach(1))
    have E: "?E = fimage (\<lambda>(s,m). (s,?f m)) (finite_table_links \<Theta> N n)"
      by (rule fimage_cong[OF refl]) (auto dest: finite_table_links_notin)
    have B: "?C |\<union>| ?E = fimage (\<lambda>(s,m). (s,?f m)) (finite_node_links_in \<Theta> N n)"
      unfolding C E finite_node_links_in_def by (auto simp: fset_eq_iff resolution_fset_simps)
    have Bf: "finite_relation_functional (?C |\<union>| ?E)"
    proof (rule finite_relation_functional_intro)
      fix s p p' assume "(s,p) |\<in>| ?C |\<union>| ?E" "(s,p') |\<in>| ?C |\<union>| ?E"
      then obtain m m' where "(s,m) |\<in>| finite_node_links_in \<Theta> N n" "p = ?f m"
          "(s,m') |\<in>| finite_node_links_in \<Theta> N n" "p' = ?f m'"
        unfolding B by (force simp: resolution_fset_simps)
      then show "p = p'" using finite_relation_functional_at[OF lf] by metis
    qed
    have read: "finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n |\<in>| finite_admitted_premise_readings P
        (resolution_node_site n) (resolution_node_clause n) (finite_node_values n) (finite_residual_term (resolution_node_call n))"
      using adm by (simp add: finite_admitted_premise_reading_exact)
    have dom: "fimage fst (?C |\<union>| ?E) = fimage fst (finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n)"
      by (rule fset_eqI) (force simp: finite_node_link_claims_def finite_table_link_claims_def resolution_fset_simps)
    have children: "\<forall>s p. (s,p) |\<in>| ?C |\<union>| ?E \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n \<and>
        finite_checks_schema_proof P p e x)"
    proof (intro allI impI)
      fix s p assume "(s,p) |\<in>| ?C |\<union>| ?E"
      then consider m where "(s,m) |\<in>| finite_node_links N n" "p = finite_node_certificate_in \<Theta> N m"
        | a where "(s,a) |\<in>| finite_table_links \<Theta> N n" "p = finite_table_proof \<Theta> a"
        by (force simp: resolution_fset_simps)
      then show "\<exists>e x. (s,e,x) |\<in>| finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n \<and> finite_checks_schema_proof P p e x"
      proof cases
        case (1 m)
        have mR: "m |\<in>| finite_link_reach N nd" using finite_link_reach(4)[OF nd less.prems 1(1)] .
        have "fcard (resolution_reach N m) < fcard (resolution_reach N n)" using finite_node_links_reach(2)[OF 1(1) nN] .
        then have "finite_checks_schema_proof P p (resolution_node_site m) (finite_residual_term (resolution_node_call m))"
          using less.hyps[OF _ mR] 1(2) by blast
        moreover have "(s,resolution_node_site m,finite_residual_term (resolution_node_call m)) |\<in>| finite_node_link_claims N n"
          using 1(1) by (force simp: finite_node_link_claims_def resolution_fset_simps)
        ultimately show ?thesis by auto
      next
        case (2 a)
        have "finite_checks_schema_proof P p (resolution_node_site a) (finite_residual_term (resolution_node_call a))"
          using entries[OF less.prems 2(1)] 2(2) by simp
        moreover have "(s,resolution_node_site a,finite_residual_term (resolution_node_call a)) |\<in>| finite_table_link_claims \<Theta> N n"
          using 2(1) by (force simp: finite_table_link_claims_def resolution_fset_simps)
        ultimately show ?thesis by auto
      qed
    qed
    show ?case
      unfolding finite_node_certificate_in_links[OF nN] finite_checks_schema_proof_node
      using Bf read dom children by blast
  qed
  have "finite_checks_schema_proof P (finite_node_certificate_in \<Theta> N nd) d t"
    using node[OF finite_link_reach(1)[OF nd]] char by simp
  then show ?thesis by (simp add: finite_state_node_certificate_in[OF nd])
qed

text \<open>
  The entries a graph at a table reads, each accepted at its call: at a valid table all are, and at the empty table there
  are none.
\<close>

definition finite_table_entries_accepted ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_table_entries_accepted P \<Theta> N nd = fBall (finite_table_discharges \<Theta> N nd) (\<lambda>((n,s),a).
    finite_checks_schema_proof P (finite_table_proof \<Theta> a) (resolution_node_site a) (finite_residual_term (resolution_node_call a)))"

lemma finite_table_entries_accepted_empty [simp]: "finite_table_entries_accepted P resolution_empty_table N nd"
  by (simp add: finite_table_entries_accepted_def)

lemma finite_table_entries_accepted_valid:
  assumes valid: "finite_table_valid P \<Theta>"
  shows "finite_table_entries_accepted P \<Theta> N nd"
  unfolding finite_table_entries_accepted_def
proof (rule ballI, clarify)
  fix n s a assume "((n,s),a) \<in> fset (finite_table_discharges \<Theta> N nd)"
  then have "(s,a) |\<in>| finite_table_links \<Theta> N n" by (simp add: finite_table_discharges_member)
  then obtain c where "resolution_table_lookup \<Theta> (resolution_node_site a,finite_residual_term (resolution_node_call a)) = Some c"
    by (auto simp: finite_table_links_member)
  then show "finite_checks_schema_proof P (finite_table_proof \<Theta> a) (resolution_node_site a)
      (finite_residual_term (resolution_node_call a))"
    by (simp add: finite_table_proof_def finite_table_valid_entry[OF valid])
qed

corollary finite_state_graph_check_accepts_entries:
  assumes nd: "nd |\<in>| N" and check: "finite_state_graph_check_in \<Theta> P d t N nd"
    and entries: "finite_table_entries_accepted P \<Theta> N nd"
  shows "finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard N) N nd) d t"
proof (rule finite_state_graph_check_accepts_in[OF nd check])
  fix n s a assume "n |\<in>| finite_link_reach N nd" and "(s,a) |\<in>| finite_table_links \<Theta> N n"
  then have "((n,s),a) |\<in>| finite_table_discharges \<Theta> N nd" by (simp add: finite_table_discharges_member)
  then show "finite_checks_schema_proof P (finite_table_proof \<Theta> a) (resolution_node_site a)
      (finite_residual_term (resolution_node_call a))"
    using entries by (auto simp: finite_table_entries_accepted_def)
qed

corollary finite_state_graph_check_accepts_valid:
  assumes valid: "finite_table_valid P \<Theta>" and nd: "nd |\<in>| N" and check: "finite_state_graph_check_in \<Theta> P d t N nd"
  shows "finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard N) N nd) d t"
  by (rule finite_state_graph_check_accepts_entries[OF nd check finite_table_entries_accepted_valid[OF valid]])

text \<open>
  The graph reading's assumptions are table calls, so a call it reads is true wherever the table's calls are: no entry's
  certificate is read. Validity is one way the table's calls are true.
\<close>

text \<open>
  Every entry's call true (@{const finite_table_true}), validity's consequence (@{thm [source] finite_table_valid_true}),
  and every true call's accepted certificate (@{thm [source] finite_checks_schema_proof_complete}) stand beside the
  table's validity in @{text Factor_Resolution_Acceptance} (GT2a), where the committed forms read them too.
\<close>

theorem finite_state_graph_check_true_at:
  assumes true: "finite_table_true P \<Theta>" and check: "finite_state_graph_check_in \<Theta> P d t N nd"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof (rule finite_graph_reading_conditional_sound[OF check[unfolded finite_state_graph_check_in_def]])
  fix n e u assume a: "(n,e,u) |\<in>| finite_graph_assumptions (finite_state_graph_in \<Theta> N nd) (finite_state_claims_in \<Theta> N nd)"
  obtain c where "resolution_table_lookup \<Theta> (e,u) = Some c" using finite_state_graph_in_assumptions[OF a] by blast
  then show "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
    using true unfolding finite_table_true_def by blast
qed

corollary finite_state_graph_check_true_in:
  assumes valid: "finite_table_valid P \<Theta>" and check: "finite_state_graph_check_in \<Theta> P d t N nd"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_state_graph_check_true_at[OF finite_table_valid_true[OF valid] check])

theorem finite_state_graph_check_accepts:
  assumes nd: "nd |\<in>| N" and check: "finite_state_graph_check P d t N nd"
  shows "finite_checks_schema_proof P (finite_node_proof (fcard N) N nd) d t"
  by (rule finite_state_graph_check_accepts_in[OF nd check[folded finite_state_graph_check_in_empty]]) simp

section \<open>At every found state the graph reading holds\<close>

lemma fimage_fst_certificates:
  "fimage fst (fimage (\<lambda>(s,m). (s,f m)) L) = fimage fst L"
  by (rule fset_eqI) (force simp: resolution_fset_simps)

theorem finite_state_graph_check_found_in:
  assumes valid: "finite_table_valid P \<Theta>" and I: "resolution_invariant_in \<Theta> P d t st"
    and closed: "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and root: "resolution_node_position nd=[]"
  shows "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd"
proof -
  let ?N = "resolution_nodes st"
  have Pf: "finite_system_formed P" and placed: "resolution_nodes_placed_in \<Theta> P d t st"
    and distinct: "resolution_positions_distinct st"
    using I by (simp_all add: resolution_invariant_in_def)
  have dist: "\<And>m m'. m |\<in>| ?N \<Longrightarrow> m' |\<in>| ?N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    using distinct by (simp add: resolution_positions_distinct_def)
  have rootsite: "resolution_node_site nd=d" and rootcall: "resolution_node_call nd=finite_exact_term_pattern t"
    using placed nd root by (simp_all add: resolution_nodes_placed_in_def)
  have clauses: "finite_relation_functional (finite_system_clauses P)" using Pf by (simp add: finite_system_formed_def)
  have entry: "finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))"
    if l: "(s,a) |\<in>| finite_table_links \<Theta> ?N n" for n s a
  proof -
    obtain e u where lk: "resolution_table_lookup \<Theta> (e,u) \<noteq> None" and a: "a = finite_table_node n s e u"
      using l by (auto simp: finite_table_links_member)
    then obtain c where "resolution_table_lookup \<Theta> (e,u) = Some c" by blast
    then have "finite_checks_schema_proof P c e u" by (rule finite_table_valid_entry[OF valid])
    from finite_checks_call_formed[OF this] show ?thesis by (simp add: a)
  qed
  have each: "finite_relation_functional (finite_node_links_in \<Theta> ?N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims ?N n |\<union>| finite_table_link_claims \<Theta> ?N n)"
    if n: "n |\<in>| ?N" for n
  proof -
    have linked: "resolution_node_linked_in \<Theta> P st n" using placed n by (simp add: resolution_nodes_placed_in_def)
    have clause: "((resolution_node_site n,resolution_node_clause n),resolution_node_schema n) |\<in>| finite_system_clauses P"
      using linked by (simp add: resolution_node_linked_in_def)
    have prem: "finite_relation_functional (finite_schema_premises (resolution_node_schema n))"
      using finite_system_clause_formed[OF Pf clause] by (simp add: finite_schema_formed_def)
    have "fcard (resolution_reach ?N n) \<le> fcard ?N" by (rule fcard_mono) auto
    from finite_node_proof_accepted_in[OF valid I closed n this]
    have tree: "finite_checks_schema_proof P (finite_node_certificate_in \<Theta> ?N n) (resolution_node_site n)
        (finite_residual_term (resolution_node_call n))"
      by (simp add: finite_state_node_certificate_in[OF n])
    let ?B = "fimage (\<lambda>(s,m). (s,finite_node_certificate_in \<Theta> ?N m)) (finite_node_links ?N n) |\<union>|
      fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> ?N n)"
    obtain H where read: "H |\<in>| finite_admitted_premise_readings P (resolution_node_site n) (resolution_node_clause n)
        (finite_node_values n) (finite_residual_term (resolution_node_call n))"
      and dom: "fimage fst ?B = fimage fst H"
      using tree unfolding finite_node_certificate_in_links[OF n] finite_checks_schema_proof_node by blast
    have adm: "finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) H"
      using read by (simp add: finite_admitted_premise_reading_exact)
    obtain S where Sin: "((resolution_node_site n,resolution_node_clause n),S) |\<in>| finite_system_clauses P"
      and HS: "H = finite_instantiated_premises S (finite_node_values n)"
      using read by (auto simp: finite_admitted_premise_readings_def)
    have S: "S = resolution_node_schema n" using finite_relation_functional_at[OF clauses Sin clause] .
    have Vf: "finite_relation_functional (finite_node_values n)"
      using adm by (auto simp: finite_admitted_schema_instance_def finite_schema_instance_def finite_term_bindings_formed_def)
    have links: "finite_relation_functional (finite_node_links_in \<Theta> ?N n)" by (rule finite_node_links_in_functional[OF dist prem Vf])
    have domL: "fimage fst (finite_node_links_in \<Theta> ?N n) = fimage fst H"
    proof -
      have "fimage fst ?B = fimage fst (finite_node_links_in \<Theta> ?N n)"
        by (rule fset_eqI) (force simp: finite_node_links_in_def resolution_fset_simps)
      then show ?thesis using dom by simp
    qed
    have pt: "(s,e,x) |\<in>| H \<longleftrightarrow> (s,e,x) |\<in>| finite_node_link_claims ?N n |\<union>| finite_table_link_claims \<Theta> ?N n" for s e x
    proof
      assume zH: "(s,e,x) |\<in>| H"
      then obtain p where sp: "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema n)"
        and xp: "x |\<in>| finite_pattern_instances (finite_node_values n) p"
        unfolding HS S finite_instantiated_premises_member by blast
      have "s |\<in>| fimage fst H" using zH by (force simp: resolution_fset_simps)
      then obtain m where sm: "(s,m) |\<in>| finite_node_links_in \<Theta> ?N n"
        using domL by (force simp: fset_eq_iff resolution_fset_simps)
      then consider "(s,m) |\<in>| finite_node_links ?N n" | "(s,m) |\<in>| finite_table_links \<Theta> ?N n"
        by (auto simp: finite_node_links_in_def)
      then show "(s,e,x) |\<in>| finite_node_link_claims ?N n |\<union>| finite_table_link_claims \<Theta> ?N n"
      proof cases
        case 1
        then obtain e' p' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and m: "m |\<in>| finite_premise_nodes ?N n s e' p'" by (auto simp: finite_node_links_member)
        have "(e',p') = (e,p)" using finite_relation_functional_at[OF prem sp' sp] .
        then have same: "e'=e \<and> p'=p" by simp
        have site: "resolution_node_site m = e" and inst: "finite_residual_term (resolution_node_call m) |\<in>|
            finite_pattern_instances (finite_node_values n) p"
          using finite_premise_nodes_member(2,3)[OF m] same by auto
        have "x = finite_residual_term (resolution_node_call m)"
          using finite_pattern_instance_unique[OF Vf] xp inst by (simp add: finite_pattern_instances_member)
        then show ?thesis using 1 site by (force simp: finite_node_link_claims_def resolution_fset_simps)
      next
        case 2
        then obtain e' p' u where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and u: "u |\<in>| finite_pattern_instances (finite_node_values n) p'" and m: "m = finite_table_node n s e' u"
          by (auto simp: finite_table_links_member)
        have "(e',p') = (e,p)" using finite_relation_functional_at[OF prem sp' sp] .
        then have same: "e'=e \<and> p'=p" by simp
        have "x = u" using finite_pattern_instance_unique[OF Vf] xp u same by (simp add: finite_pattern_instances_member)
        then show ?thesis using 2 same m by (force simp: finite_table_link_claims_def resolution_fset_simps)
      qed
    next
      assume "(s,e,x) |\<in>| finite_node_link_claims ?N n |\<union>| finite_table_link_claims \<Theta> ?N n"
      then consider "(s,e,x) |\<in>| finite_node_link_claims ?N n" | "(s,e,x) |\<in>| finite_table_link_claims \<Theta> ?N n" by auto
      then show "(s,e,x) |\<in>| H"
      proof cases
        case 1
        then obtain m where sm: "(s,m) |\<in>| finite_node_links ?N n" and ex: "e=resolution_node_site m"
            "x=finite_residual_term (resolution_node_call m)"
          by (force simp: finite_node_link_claims_def resolution_fset_simps)
        then obtain e' p' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and m: "m |\<in>| finite_premise_nodes ?N n s e' p'" by (auto simp: finite_node_links_member)
        show ?thesis
          using finite_premise_nodes_member(2,3)[OF m] sp' ex
          unfolding HS S finite_instantiated_premises_member by blast
      next
        case 2
        then obtain a where sa: "(s,a) |\<in>| finite_table_links \<Theta> ?N n" and ex: "e=resolution_node_site a"
            "x=finite_residual_term (resolution_node_call a)"
          by (force simp: finite_table_link_claims_def resolution_fset_simps)
        then obtain e' p' u where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and u: "u |\<in>| finite_pattern_instances (finite_node_values n) p'" and a: "a = finite_table_node n s e' u"
          by (auto simp: finite_table_links_member)
        show ?thesis using sp' u ex a unfolding HS S finite_instantiated_premises_member by auto
      qed
    qed
    have "H = finite_node_link_claims ?N n |\<union>| finite_table_link_claims \<Theta> ?N n"
      by (intro fset_eqI) (auto simp: split_paired_all pt)
    then show ?thesis using links adm by simp
  qed
  have uses: "finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> ?N nd))"
    by (rule finite_state_graph_in_uses[OF nd dist])
  show ?thesis unfolding finite_state_graph_check_in_iff[OF nd]
    using rootsite rootcall uses each entry finite_link_reach(2)[OF nd] by auto
qed

text \<open>
  At a table whose calls are true the graph reading holds at every found state too: the same calls certified by the
  checker form a valid table, and the invariant and the graph read only which calls the table holds.
\<close>

theorem finite_state_graph_check_found_true:
  assumes true: "finite_table_true P \<Theta>" and I: "resolution_invariant_in \<Theta> P d t st"
    and closed: "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and root: "resolution_node_position nd=[]"
  shows "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd"
proof -
  define C where "C = Resolution_Table (\<lambda>q. case resolution_table_lookup \<Theta> q of None \<Rightarrow> None
    | Some c \<Rightarrow> Some (SOME c'. finite_checks_schema_proof P c' (fst q) (snd q)))"
  have dom: "resolution_table_lookup C q = None \<longleftrightarrow> resolution_table_lookup \<Theta> q = None" for q
    unfolding C_def by (simp split: option.split)
  have valid: "finite_table_valid P C"
    unfolding finite_table_valid_def
  proof (intro allI impI)
    fix e u c assume "resolution_table_lookup C (e,u) = Some c"
    then obtain c0 where c0: "resolution_table_lookup \<Theta> (e,u) = Some c0"
      and c: "c = (SOME c'. finite_checks_schema_proof P c' e u)"
      unfolding C_def by (auto split: option.splits)
    have "(e,decode_finite_term u) \<in> positive_meaning (decode_finite_system P)"
      using true c0 unfolding finite_table_true_def by blast
    then have "\<exists>c'. finite_checks_schema_proof P c' e u" by (rule finite_checks_schema_proof_complete)
    then show "finite_checks_schema_proof P c e u" unfolding c by (rule someI_ex)
  qed
  have closed_eq: "resolution_premise_closed_in C st q e x \<longleftrightarrow> resolution_premise_closed_in \<Theta> st q e x" for q e x
    by (simp add: resolution_premise_closed_in_def dom)
  have I': "resolution_invariant_in C P d t st"
    using I unfolding resolution_invariant_in_def resolution_nodes_placed_in_def resolution_node_linked_in_def closed_eq .
  have links: "finite_table_links C N' n = finite_table_links \<Theta> N' n" for N' n
    by (simp add: finite_table_links_def dom cong: if_cong)
  have "finite_state_graph_check_in C P d t (resolution_nodes st) nd"
    by (rule finite_state_graph_check_found_in[OF valid I' closed nd root])
  then show ?thesis
    unfolding finite_state_graph_check_in_def finite_state_graph_in_def finite_state_claims_in_def
      finite_table_discharges_def links .
qed

theorem finite_state_graph_check_found:
  assumes I: "resolution_invariant P d t st" and closed: "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and root: "resolution_node_position nd=[]"
  shows "finite_state_graph_check P d t (resolution_nodes st) nd"
  using finite_state_graph_check_found_in[OF finite_table_valid_empty I closed nd root]
  by (simp only: finite_state_graph_check_in_empty)


corollary finite_state_graph_check_found_exact:
  assumes "resolution_invariant P d t st" and "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and "resolution_node_position nd=[]"
  shows "finite_state_graph_check P d t (resolution_nodes st) nd \<longleftrightarrow>
    finite_checks_schema_proof P (finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st) nd) d t"
  using finite_state_graph_check_found[OF assms] finite_state_graph_check_accepts[OF nd] by blast

section \<open>A table produced in order and checked over graphs\<close>

text \<open>
  A table is produced entry by entry: each entry is a found state's root certificate at its call, found at the table of
  the entries before it (@{text finite_table_produced}). Its check reads each entry's graph at that table, with its
  assumptions among the calls of the entries before it (@{text finite_table_graph_checks}), in production order; no
  certificate is checked as a tree. A table so checked is valid (@{text finite_table_graph_checks_valid}): each checked
  graph gives its certificate's acceptance at the valid table before it, and an accepted entry keeps the table valid.
\<close>

definition resolution_table_extend ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'c) finite_schema_proof \<Rightarrow>
      ('a,'s,'d,'c) resolution_table" where
  "resolution_table_extend \<Theta> e u c = Resolution_Table ((resolution_table_lookup \<Theta>)((e,u) := Some c))"

lemma finite_table_valid_extend:
  assumes valid: "finite_table_valid P \<Theta>" and c: "finite_checks_schema_proof P c e u"
  shows "finite_table_valid P (resolution_table_extend \<Theta> e u c)"
  using valid c by (auto simp: finite_table_valid_def resolution_table_extend_def)

type_synonym ('a,'s,'d,'c) resolution_table_row =
  "'d \<times> finite_factor_term \<times> ('a,'s,'d,'c) resolution_node fset \<times> ('a,'s,'d,'c) resolution_node"

fun finite_table_produced ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_table_row list \<Rightarrow> ('a,'s,'d,'c) resolution_table" where
  "finite_table_produced \<Theta> [] = \<Theta>"
| "finite_table_produced \<Theta> ((e,u,N,nd)#rows) =
    finite_table_produced (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows"

fun finite_table_graph_checks ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a,'s,'d,'c) resolution_table_row list \<Rightarrow> bool" where
  "finite_table_graph_checks P \<Theta> [] = True"
| "finite_table_graph_checks P \<Theta> ((e,u,N,nd)#rows) = (nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd \<and>
    finite_table_graph_checks P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows)"

theorem finite_table_graph_checks_valid:
  "finite_table_valid P \<Theta> \<Longrightarrow> finite_table_graph_checks P \<Theta> rows \<Longrightarrow> finite_table_valid P (finite_table_produced \<Theta> rows)"
proof (induction rows arbitrary: \<Theta>)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  obtain e u N nd where row: "row = (e,u,N,nd)" by (cases row) auto
  have nd: "nd |\<in>| N" and check: "finite_state_graph_check_in \<Theta> P e u N nd"
    and rest: "finite_table_graph_checks P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows"
    using Cons.prems(2) by (simp_all add: row)
  have "finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard N) N nd) e u"
    by (rule finite_state_graph_check_accepts_valid[OF Cons.prems(1) nd check])
  then have "finite_table_valid P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd))"
    by (rule finite_table_valid_extend[OF Cons.prems(1)])
  from Cons.IH[OF this rest] show ?case by (simp add: row)
qed

corollary finite_table_graph_checks_produced:
  "finite_table_graph_checks P resolution_empty_table rows \<Longrightarrow>
    finite_table_valid P (finite_table_produced resolution_empty_table rows)"
  by (rule finite_table_graph_checks_valid[OF finite_table_valid_empty])

text \<open>The check and the table it produces in one fold: the produced table only where the check passes.\<close>

fun finite_table_checked ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a,'s,'d,'c) resolution_table_row list \<Rightarrow> ('a,'s,'d,'c) resolution_table option" where
  "finite_table_checked P \<Theta> [] = Some \<Theta>"
| "finite_table_checked P \<Theta> ((e,u,N,nd)#rows) = (if nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd
    then finite_table_checked P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows else None)"

lemma finite_table_checked_exact:
  "finite_table_checked P \<Theta> rows =
    (if finite_table_graph_checks P \<Theta> rows then Some (finite_table_produced \<Theta> rows) else None)"
  by (induction P \<Theta> rows rule: finite_table_checked.induct) auto

corollary finite_table_checked_valid:
  "finite_table_valid P \<Theta> \<Longrightarrow> finite_table_checked P \<Theta> rows = Some \<Theta>' \<Longrightarrow> finite_table_valid P \<Theta>'"
  by (auto simp: finite_table_checked_exact split: if_splits intro: finite_table_graph_checks_valid)

section \<open>The code equations: the check over the graph, the certificates once per node\<close>

text \<open>
  A found state's verdicts: each root certificate with its acceptance, the graph reading first and the tree check only
  where it does not hold; since the graph reading gives the tree check, the verdict is the tree check's on every input.
\<close>

definition finite_state_verdicts ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_state_verdicts P d t st = (let N = resolution_nodes st in fimage (\<lambda>nd. let c = finite_node_proof (fcard N) N nd in
    (c,finite_state_graph_check P d t N nd \<or> finite_checks_schema_proof P c d t))
    (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"

text \<open>
  At a table a verdict is the graph reading with the entries it reads accepted, and the tree check only where they do not
  hold: equal to the tree check's on every input (@{text finite_state_verdicts_in_accepted}), today's verdicts its
  instance at the empty table.
\<close>

definition finite_state_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_state_verdicts_in \<Theta> P d t st = (let N = resolution_nodes st in
    fimage (\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard N) N nd in
      (c,(finite_state_graph_check_in \<Theta> P d t N nd \<and> finite_table_entries_accepted P \<Theta> N nd) \<or>
        finite_checks_schema_proof P c d t))
    (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"

lemma finite_state_verdicts_empty: "finite_state_verdicts_in resolution_empty_table P d t = finite_state_verdicts P d t"
  by (intro ext) (simp add: finite_state_verdicts_in_def finite_state_verdicts_def finite_state_graph_check_in_empty)

lemma finite_state_verdicts_in_accepted:
  "finite_state_verdicts_in \<Theta> P d t st = fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) (finite_state_proofs_in \<Theta> st)"
proof -
  let ?N = "resolution_nodes st"
  have "(\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard ?N) ?N nd in
      (c,(finite_state_graph_check_in \<Theta> P d t ?N nd \<and> finite_table_entries_accepted P \<Theta> ?N nd) \<or>
        finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. (finite_node_proof_in \<Theta> (fcard ?N) ?N nd,
      finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard ?N) ?N nd) d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that finite_state_graph_check_accepts_entries[of x ?N \<Theta> P d t] by (auto simp: Let_def)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this]
  have "finite_state_verdicts_in \<Theta> P d t st = fimage (\<lambda>nd. (finite_node_proof_in \<Theta> (fcard ?N) ?N nd,
      finite_checks_schema_proof P (finite_node_proof_in \<Theta> (fcard ?N) ?N nd) d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N)"
    by (simp add: finite_state_verdicts_in_def Let_def)
  then show ?thesis by (simp add: finite_state_proofs_in_def fset.map_comp comp_def)
qed

lemma finite_state_verdicts_accepted:
  "finite_state_verdicts P d t st = fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) (finite_state_proofs st)"
  using finite_state_verdicts_in_accepted[of resolution_empty_table P d t st]
  by (simp add: finite_state_verdicts_empty finite_state_proofs_def)

lemma finite_outcome_result_in_verdicts [code]:
  "finite_outcome_result_in \<Theta> P d t R = (let V = ffUnion (fimage (finite_state_verdicts_in \<Theta> P d t) (resolution_found R));
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R |\<union>| fimage Resolution_Refused C))"
proof -
  let ?C = "ffUnion (fimage (finite_state_proofs_in \<Theta>) (resolution_found R))"
  have V: "ffUnion (fimage (finite_state_verdicts_in \<Theta> P d t) (resolution_found R)) =
      fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C"
    by (rule fset_eqI) (force simp: finite_state_verdicts_in_accepted resolution_fset_simps)
  have C: "fimage fst (fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C) = ?C"
    by (rule fset_eqI) (force simp: resolution_fset_simps)
  have A: "fimage fst (ffilter snd (fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C)) =
      ffilter (\<lambda>p. finite_checks_schema_proof P p d t) ?C"
    by (rule fset_eqI) (force simp: resolution_fset_simps)
  show ?thesis unfolding finite_outcome_result_in_def Let_def V C A ..
qed

lemma finite_outcome_result_verdicts [code]:
  "finite_outcome_result P d t R = (let V = ffUnion (fimage (finite_state_verdicts P d t) (resolution_found R));
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R |\<union>| fimage Resolution_Refused C))"
  unfolding finite_outcome_result_def finite_outcome_result_in_verdicts finite_state_verdicts_empty ..

declare finite_program_resolution_outcome [code]

text \<open>
  The executable forms: the nodes of a state ranked and linked once, the certificates made once per node from them, and
  the graph reading of @{text finite_state_graph_check_iff} over the same table, its formation reduced to the links'
  functionality (the order and the reach hold by construction) and the program's formation read once rather than at
  every node's admitted instance. A node's premise instances are computed once per premise.
\<close>

lemma finite_premise_nodes_instances [code]:
  "finite_premise_nodes N nd s e p = (let q = resolution_node_position nd@[s];
      I = finite_pattern_instances (finite_node_values nd) p;
      F = ffilter (\<lambda>m. resolution_node_site m=e \<and> finite_residual_term (resolution_node_call m) |\<in>| I) N;
      C = ffilter (\<lambda>m. resolution_node_position m=q) F in
    if C \<noteq> {||} then C else finite_first_nodes (ffilter (\<lambda>m. finite_position_left (resolution_node_position m) q) F))"
  by (simp add: finite_premise_nodes_def Let_def)

definition finite_admitted_instance_at ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_admitted_instance_at P d c V t Q \<longleftrightarrow>
    fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_pattern_accepts p t) \<and>
    fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and>
      finite_schema_instance S V t Q \<and> finite_schema_material_satisfied S V) \<and>
    fBall Q (\<lambda>(s,e,x). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_pattern_accepts p x))"

lemma finite_admitted_instance_formed:
  "finite_admitted_schema_instance P d c V t Q \<longleftrightarrow> finite_system_formed P \<and> finite_admitted_instance_at P d c V t Q"
  by (auto simp: finite_admitted_schema_instance_def finite_admitted_instance_at_def finite_schema_call_formed_def)

definition finite_state_graph_code ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_state_graph_code P d t K nd = (let R = finite_ranked_reach K nd in
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    fBall K (\<lambda>(m,k,L). m |\<in>| R \<longrightarrow> finite_relation_functional L \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L)))"

definition finite_state_graph_code_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_node fset \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> nat \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_state_graph_code_in \<Theta> P d t N K nd = (let R = finite_ranked_reach K nd in
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd)) \<and>
    fBall K (\<lambda>(m,k,L). m |\<in>| R \<longrightarrow> finite_relation_functional (L |\<union>| finite_table_links \<Theta> N m) \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
          (L |\<union>| finite_table_links \<Theta> N m)) \<and>
      fBall (finite_table_links \<Theta> N m) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
        (finite_residual_term (resolution_node_call a)))))"

lemma finite_admitted_ball_formed:
  assumes "nd |\<in>| R"
  shows "fBall R (\<lambda>n. A n \<and> finite_admitted_schema_instance P (e n) (c n) (V n) (x n) (Q n) \<and> F n) \<longleftrightarrow>
    finite_system_formed P \<and> fBall R (\<lambda>n. A n \<and> finite_admitted_instance_at P (e n) (c n) (V n) (x n) (Q n) \<and> F n)"
  using assms by (auto simp: finite_admitted_instance_formed)

lemma finite_state_graph_uses_empty: "finite_assertion_uses (finite_state_graph N nd) = {||}"
  by (force simp: fset_eq_iff finite_assertion_uses_def finite_state_graph_inference_member resolution_fset_simps)

lemma finite_state_graph_code_empty:
  "finite_state_graph_code_in resolution_empty_table P d t N K nd = finite_state_graph_code P d t K nd"
  by (simp add: finite_state_graph_code_in_def finite_state_graph_code_def finite_state_graph_uses_empty
    finite_relation_functional_def)

text \<open>
  The graph reading at a table with the program's formation read once: the form both executable checks read.
\<close>

lemma finite_state_graph_check_in_at:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_check_in \<Theta> P d t N nd \<longleftrightarrow>
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd)) \<and>
    fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n |\<union>| finite_table_links \<Theta> N n) \<and>
      finite_admitted_instance_at P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
          (finite_node_links N n |\<union>| finite_table_links \<Theta> N n)) \<and>
      fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
        (finite_residual_term (resolution_node_call a))))"
proof -
  let ?F = "\<lambda>n. fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
    (finite_residual_term (resolution_node_call a)))"
  let ?Q = "\<lambda>n. fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
    (finite_node_links N n |\<union>| finite_table_links \<Theta> N n)"
  have claims: "finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n = ?Q n" for n
    by (rule fset_eqI) (force simp: finite_node_link_claims_def finite_table_link_claims_def resolution_fset_simps)
  have formed: "fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n |\<union>| finite_table_links \<Theta> N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (?Q n) \<and> ?F n) \<longleftrightarrow>
    finite_system_formed P \<and> fBall (finite_link_reach N nd) (\<lambda>n.
      finite_relation_functional (finite_node_links N n |\<union>| finite_table_links \<Theta> N n) \<and>
      finite_admitted_instance_at P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (?Q n) \<and> ?F n)"
    by (rule finite_admitted_ball_formed[OF finite_link_reach(1)[OF nd]])
  have check: "finite_state_graph_check_in \<Theta> P d t N nd \<longleftrightarrow>
      resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and>
      finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd)) \<and>
      fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n |\<union>| finite_table_links \<Theta> N n) \<and>
        finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
          (finite_residual_term (resolution_node_call n)) (?Q n) \<and> ?F n)"
    unfolding finite_state_graph_check_in_iff[OF nd] claims finite_node_links_in_def ..
  show ?thesis unfolding check using formed by blast
qed

lemma finite_state_graph_code_in_check:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_code_in \<Theta> P d t N (finite_node_ranked N) nd = finite_state_graph_check_in \<Theta> P d t N nd"
proof -
  let ?F = "\<lambda>n. fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
    (finite_residual_term (resolution_node_call a)))"
  have ball: "fBall (finite_node_ranked N) (\<lambda>(m,k,L). m |\<in>| finite_link_reach N nd \<longrightarrow> \<Phi> m L) \<longleftrightarrow>
      fBall (finite_link_reach N nd) (\<lambda>m. \<Phi> m (finite_node_links N m))" for \<Phi>
    using finite_link_reach(2)[OF nd] by (force simp: finite_node_ranked_def resolution_fset_simps)
  let ?\<Psi> = "\<lambda>m L. finite_relation_functional (L |\<union>| finite_table_links \<Theta> N m) \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
          (L |\<union>| finite_table_links \<Theta> N m)) \<and> ?F m"
  have code: "finite_state_graph_code_in \<Theta> P d t N (finite_node_ranked N) nd \<longleftrightarrow>
      resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
      finite_relation_functional (finite_assertion_uses (finite_state_graph_in \<Theta> N nd)) \<and>
      fBall (finite_link_reach N nd) (\<lambda>m. ?\<Psi> m (finite_node_links N m))"
    unfolding finite_state_graph_code_in_def Let_def finite_link_reach_def[symmetric] ball ..
  show ?thesis by (simp only: code finite_state_graph_check_in_at[OF nd])
qed

lemma finite_state_graph_code_check:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_code P d t (finite_node_ranked N) nd = finite_state_graph_check P d t N nd"
  using finite_state_graph_code_in_check[OF nd, of resolution_empty_table P d t]
  by (simp only: finite_state_graph_code_empty finite_state_graph_check_in_empty)


lemma finite_state_verdicts_in_code [code]:
  "finite_state_verdicts_in \<Theta> P d t st = (let N = resolution_nodes st; K = finite_node_ranked N;
      T = finite_certificate_table_in \<Theta> N K in
    fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
      (c,(finite_state_graph_code_in \<Theta> P d t N K nd \<and> finite_table_entries_accepted P \<Theta> N nd) \<or>
        finite_checks_schema_proof P c d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
proof -
  let ?N = "resolution_nodes st"
  have "(\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard ?N) ?N nd in
      (c,(finite_state_graph_check_in \<Theta> P d t ?N nd \<and> finite_table_entries_accepted P \<Theta> ?N nd) \<or>
        finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (finite_relation_option (finite_certificate_table_in \<Theta> ?N (finite_node_ranked ?N)) nd) in
      (c,(finite_state_graph_code_in \<Theta> P d t ?N (finite_node_ranked ?N) nd \<and> finite_table_entries_accepted P \<Theta> ?N nd) \<or>
        finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that by (simp add: finite_certificate_table_in_proof finite_state_graph_code_in_check)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    by (simp add: finite_state_verdicts_in_def Let_def)
qed

lemma finite_state_verdicts_code [code]:
  "finite_state_verdicts P d t st = (let N = resolution_nodes st; K = finite_node_ranked N;
      T = finite_certificate_table K in
    fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
      (c,finite_state_graph_code P d t K nd \<or> finite_checks_schema_proof P c d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
  using finite_state_verdicts_in_code[of resolution_empty_table P d t st]
  by (simp add: finite_state_verdicts_empty finite_certificate_table_empty finite_state_graph_code_empty Let_def)

lemma finite_state_proofs_in_table [code]:
  "finite_state_proofs_in \<Theta> st = (let N = resolution_nodes st; T = finite_certificate_table_in \<Theta> N (finite_node_ranked N) in
    fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
proof -
  let ?N = "resolution_nodes st"
  have "finite_node_proof_in \<Theta> (fcard ?N) ?N x =
      the (finite_relation_option (finite_certificate_table_in \<Theta> ?N (finite_node_ranked ?N)) x)"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that by (simp add: finite_certificate_table_in_proof)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    by (simp add: finite_state_proofs_in_def Let_def)
qed

lemma finite_state_proofs_table [code]:
  "finite_state_proofs st = (let N = resolution_nodes st; T = finite_certificate_table (finite_node_ranked N) in
    fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
  using finite_state_proofs_in_table[of resolution_empty_table st]
  by (simp add: finite_state_proofs_def finite_certificate_table_empty Let_def)

section \<open>The check linear in the nodes: the found state indexed\<close>

text \<open>
  The code equations above read a state's nodes through sets: a premise's nodes filter every node, a node's rank counts
  its reach, and the table, the reach and the graph's membership test are sets searched member by member. Here, where
  the nodes stand at distinct positions, they are listed once in the post-order of their positions
  (@{text finite_post_key}: a node after every node under it and every node left of it), which every link decreases
  (@{text finite_node_links_post}); the nodes are indexed by position, and by the reference of their ground call in a
  table of shared terms built once from the state (@{text Shared_Term_Tables}), so that two equal calls are compared as
  two numbers (@{text finite_term_keyed}); the certificates and the reach are tree maps filled in one pass each over
  the listing. Each index is the red-black tree's (@{text Tree_Map_Indexes}: @{text tree_map_index} for the position
  index, its update @{text tree_map_updates} for the others). Where the positions are not distinct the listing is
  refused and the code equations above run.
\<close>

subsection \<open>The post-order of positions\<close>

definition finite_post_key :: "'s::linorder list \<Rightarrow> (nat \<times> 's option) list" where
  "finite_post_key p = map (\<lambda>s. (0, Some s)) p @ [(1, None)]"

lemma finite_post_key_Nil [simp]: "finite_post_key [] = [(1, None)]"
  by (simp add: finite_post_key_def)

lemma finite_post_key_Cons [simp]: "finite_post_key (x#xs) = (0, Some x) # finite_post_key xs"
  by (simp add: finite_post_key_def)

lemma finite_post_key_left: "finite_position_left p q \<Longrightarrow> finite_post_key p < finite_post_key q"
proof (induction p arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases q) auto
qed

lemma finite_post_key_under: "r \<noteq> [] \<Longrightarrow> finite_post_key (q @ r) < finite_post_key q"
proof (induction q)
  case Nil
  then show ?case by (cases r) auto
next
  case (Cons x xs)
  then show ?case by simp
qed

abbreviation finite_node_key :: "('a,'s::linorder,'d,'c) resolution_node \<Rightarrow> (nat \<times> 's option) list" where
  "finite_node_key m \<equiv> finite_post_key (resolution_node_position m)"

lemma finite_node_links_post:
  assumes l: "(s,m) |\<in>| finite_node_links N nd"
  shows "finite_node_key m < finite_node_key nd"
proof -
  obtain e p where m: "m |\<in>| finite_premise_nodes N nd s e p" using l by (auto simp: finite_node_links_member)
  let ?q = "resolution_node_position nd" and ?p = "resolution_node_position m"
  have "?p = ?q@[s] \<or> finite_position_left ?p (?q@[s])" by (rule finite_premise_nodes_member(4)[OF m])
  then have either: "finite_position_left ?p ?q \<or> (\<exists>r. r \<noteq> [] \<and> ?p = ?q @ r)"
  proof
    assume "?p = ?q@[s]"
    then show ?thesis by blast
  next
    assume left: "finite_position_left ?p (?q@[s])"
    from finite_position_left_socket[OF left] show ?thesis
    proof
      assume "finite_position_left ?p ?q"
      then show ?thesis ..
    next
      assume t: "take (length ?q) ?p = ?q"
      have ne: "?p \<noteq> ?q" using left by (auto simp: finite_position_left_def)
      have split: "?p = ?q @ drop (length ?q) ?p" using t by (metis append_take_drop_id)
      then have "drop (length ?q) ?p \<noteq> []" using ne by (metis append_Nil2)
      then show ?thesis using split by blast
    qed
  qed
  then show ?thesis
  proof
    assume "finite_position_left ?p ?q"
    then show ?thesis by (rule finite_post_key_left)
  next
    assume "\<exists>r. r \<noteq> [] \<and> ?p = ?q @ r"
    then obtain r where "r \<noteq> []" "?p = ?q @ r" by blast
    then show ?thesis using finite_post_key_under[of r ?q] by simp
  qed
qed

subsection \<open>The nodes listed in the post-order\<close>

definition finite_post_listed ::
    "('a,'s::linorder,'d,'c) resolution_node set \<Rightarrow> ('a,'s,'d,'c) resolution_node list \<Rightarrow> bool" where
  "finite_post_listed S ns \<longleftrightarrow> set ns = S \<and> sorted_wrt (\<lambda>m m'. finite_node_key m < finite_node_key m') ns"

lemma finite_post_listed_positions:
  assumes listed: "finite_post_listed S ns"
  shows "distinct (map resolution_node_position ns)" "set ns = S"
    "\<And>m m'. m \<in> S \<Longrightarrow> m' \<in> S \<Longrightarrow> resolution_node_position m = resolution_node_position m' \<Longrightarrow> m = m'"
proof -
  have "sorted_wrt (<) (map finite_node_key ns)" using listed by (simp add: finite_post_listed_def sorted_wrt_map)
  then have "distinct (map finite_post_key (map resolution_node_position ns))" by (simp add: strict_sorted_iff o_def)
  then show d: "distinct (map resolution_node_position ns)" by (auto simp: distinct_map intro: inj_on_imageI2)
  show s: "set ns = S" using listed by (simp add: finite_post_listed_def)
  show "\<And>m m'. m \<in> S \<Longrightarrow> m' \<in> S \<Longrightarrow> resolution_node_position m = resolution_node_position m' \<Longrightarrow> m = m'"
    using d s by (auto simp: distinct_map inj_on_def)
qed

lemma finite_post_listed_unique:
  assumes first: "finite_post_listed S ns" and second: "finite_post_listed S ns'"
  shows "ns = ns'"
proof -
  have "sorted_wrt (<) (map finite_node_key ns)" "sorted_wrt (<) (map finite_node_key ns')"
    using first second by (simp_all add: finite_post_listed_def sorted_wrt_map)
  then have k: "sorted (map finite_node_key ns) \<and> distinct (map finite_node_key ns)"
      "sorted (map finite_node_key ns') \<and> distinct (map finite_node_key ns')"
    by (simp_all only: strict_sorted_iff)
  have s: "set ns = S" "set ns' = S" using first second by (simp_all add: finite_post_listed_def)
  have "map finite_node_key ns = map finite_node_key ns'"
    using k s by (intro sorted_distinct_set_unique) auto
  moreover have "inj_on finite_node_key (set ns \<union> set ns')" using k s by (simp add: distinct_map)
  ultimately show ?thesis by (rule map_inj_on)
qed

definition finite_post_listing ::
    "('a,'s::linorder,'d,'c) resolution_node set \<Rightarrow> ('a,'s,'d,'c) resolution_node list option" where
  "finite_post_listing S = (if \<exists>ns. finite_post_listed S ns then Some (THE ns. finite_post_listed S ns) else None)"

lemma finite_post_listing_some:
  assumes "finite_post_listing S = Some ns"
  shows "finite_post_listed S ns"
proof -
  obtain ns0 where ns0: "finite_post_listed S ns0" and ns: "ns = (THE ns. finite_post_listed S ns)"
    using assms by (auto simp: finite_post_listing_def split: if_splits)
  have "\<exists>!ns. finite_post_listed S ns" using ns0 finite_post_listed_unique by blast
  from theI'[OF this] show ?thesis by (simp only: ns)
qed

lemma finite_remdups_adj_map_on:
  assumes "inj_on f (set xs)"
  shows "remdups_adj (map f xs) = map f (remdups_adj xs)"
  using assms
proof (induction xs rule: remdups_adj.induct)
  case (3 x y xs)
  have inj: "inj_on f (set (x#xs))" "inj_on f (set (y#xs))" using "3.prems" by (auto intro: inj_on_subset)
  have eq: "f x = f y \<longleftrightarrow> x = y" using "3.prems" by (auto dest: inj_onD)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis using "3.IH"(1)[OF True inj(1)] by simp
  next
    case False
    then have "f x \<noteq> f y" using eq by simp
    then show ?thesis using "3.IH"(2)[OF False inj(2)] False by simp
  qed
qed simp_all

text \<open>
  The listing is computed by one sort of the nodes on the key of their positions: repeated rows of one node become
  adjacent and are removed, and the listing is refused when two nodes share a position. A node is compared with another
  only where their positions are equal.
\<close>

lemma finite_post_listing_code [code]:
  fixes xs :: "('a,'s::linorder,'d,'c) resolution_node list"
  shows "finite_post_listing (set xs) = (let ys = remdups_adj (Sorting_Algorithms.mergesort (Comparator.key finite_node_key default) xs) in
    if ascending_listing (map finite_node_key ys) then Some ys else None)"
proof -
  let ?k = "finite_node_key :: ('a,'s,'d,'c) resolution_node \<Rightarrow> _"
  let ?ys = "remdups_adj (sort_key ?k xs)"
  have ys: "remdups_adj (Sorting_Algorithms.mergesort (Comparator.key finite_node_key default) xs) = ?ys"
    by (simp only: sort_key_by_mergesort)
  show ?thesis
  proof (cases "ascending_listing (map ?k ?ys)")
    case True
    then have "sorted (map ?k ?ys) \<and> distinct (map ?k ?ys)" by (simp only: ascending_listing_exact)
    then have "sorted_wrt (<) (map ?k ?ys)" by (simp only: strict_sorted_iff)
    then have "sorted_wrt (\<lambda>m m'. ?k m < ?k m') ?ys" by (simp only: sorted_wrt_map)
    then have listed: "finite_post_listed (set xs) ?ys" by (simp add: finite_post_listed_def)
    have "(THE ns. finite_post_listed (set xs) ns) = ?ys"
      by (rule the_equality[where P="finite_post_listed (set xs)", OF listed]) (rule finite_post_listed_unique[OF _ listed])
    then have "finite_post_listing (set xs) = Some ?ys" using listed by (auto simp: finite_post_listing_def)
    then show ?thesis using True by (simp only: ys Let_def if_True)
  next
    case False
    have "\<not> (\<exists>ns. finite_post_listed (set xs) ns)"
    proof
      assume "\<exists>ns. finite_post_listed (set xs) ns"
      then obtain ns where ns: "finite_post_listed (set xs) ns" by blast
      have inj: "inj_on ?k (set (sort_key ?k xs))"
        using finite_post_listed_positions[OF ns] by (auto simp: inj_on_def finite_post_key_def)
      have eqk: "map ?k ?ys = remdups_adj (map ?k (sort_key ?k xs))" by (rule finite_remdups_adj_map_on[OF inj, symmetric])
      have sl: "sorted (map ?k (sort_key ?k xs))" by (rule sorted_sort_key)
      have "sorted (map ?k ?ys) \<and> distinct (map ?k ?ys)"
        by (simp only: eqk) (use sorted_remdups_adj[OF sl] sorted_remdups_adj_distinct[OF sl] in blast)
      then show False using False by (simp add: ascending_listing_exact)
    qed
    then show ?thesis using False by (simp only: ys Let_def) (simp add: finite_post_listing_def)
  qed
qed

subsection \<open>Ground calls keyed by their reference in a shared table\<close>

text \<open>
  A reference keys a term when the reference the keyed step gives any term at that state is it exactly for that term:
  equal calls then have equal references, and a comparison of two references reads two numbers.
\<close>

definition finite_term_keyed :: "share_state \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_term_keyed q r y \<longleftrightarrow> (\<forall>x. fst (keyed_share_term x q) = r \<longleftrightarrow> x = y)"

lemma finite_term_keyed_intro:
  assumes rep: "keyed_state_represents q T" and f: "table_formed T" and y: "reference_term T r = Some y"
  shows "finite_term_keyed q r y"
  unfolding finite_term_keyed_def
proof
  fix x
  let ?T = "snd (share_term x T)" and ?i = "fst (share_term x T)"
  have i: "fst (keyed_share_term x q) = ?i" using keyed_share_term_exact[OF rep] by blast
  have ft: "table_formed ?T" and ix: "reference_term ?T ?i = Some x" using share_term_exact[OF f, of x] by simp_all
  have ry: "reference_term ?T r = Some y" by (rule share_term_preserves[OF y])
  show "fst (keyed_share_term x q) = r \<longleftrightarrow> x = y"
  proof
    assume "fst (keyed_share_term x q) = r"
    then show "x = y" using i ix ry by simp
  next
    assume xy: "x = y"
    have "?i = r" by (rule reference_term_injective[OF ft ix]) (use ry xy in simp)
    then show "fst (keyed_share_term x q) = r" using i by simp
  qed
qed

fun finite_share_rows :: "('a,'s,'d,'c) resolution_node list \<Rightarrow> share_state \<Rightarrow>
    (('a,'s,'d,'c) resolution_node \<times> finite_factor_term \<times> nat) list \<times> share_state" where
  "finite_share_rows [] q = ([],q)"
| "finite_share_rows (m#ms) q = (let x = finite_residual_term (resolution_node_call m) in
    case keyed_share_term x q of (r,q1) \<Rightarrow> (case finite_share_rows ms q1 of (rows,q2) \<Rightarrow> ((m,x,r)#rows,q2)))"

text \<open>
  The rows of a found state read from a representation of it (C2, task 993): a node whose call the representation holds
  at a reference of a sharing state takes that reference, and any other node shares its call there, as
  @{const finite_share_rows} shares every node's. Re-sharing is the instance that reads no reference
  (@{text finite_share_rows_read}); a reference read is exact where the state's table holds the node's call at it
  (@{text finite_read_rows_exact}).
\<close>

fun finite_read_rows :: "('s list \<Rightarrow> nat option) \<Rightarrow> ('a,'s,'d,'c) resolution_node list \<Rightarrow> share_state \<Rightarrow>
    (('a,'s,'d,'c) resolution_node \<times> finite_factor_term \<times> nat) list \<times> share_state" where
  "finite_read_rows L [] q = ([],q)"
| "finite_read_rows L (m#ms) q = (let x = finite_residual_term (resolution_node_call m) in
    case (case L (resolution_node_position m) of Some i \<Rightarrow> (i,q) | None \<Rightarrow> keyed_share_term x q) of (r,q1) \<Rightarrow>
      (case finite_read_rows L ms q1 of (rows,q2) \<Rightarrow> ((m,x,r)#rows,q2)))"

lemma finite_share_rows_read: "finite_share_rows ms q = finite_read_rows (\<lambda>_. None) ms q"
  by (induction ms arbitrary: q) (simp_all add: Let_def split: prod.split)

lemma finite_read_rows_exact:
  assumes "keyed_state_represents q T" "table_formed T"
    "\<forall>m\<in>set ms. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
  shows "\<exists>T'. keyed_state_represents (snd (finite_read_rows L ms q)) T' \<and> table_formed T' \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u) \<and>
    map fst (fst (finite_read_rows L ms q)) = ms \<and>
    (\<forall>row\<in>set (fst (finite_read_rows L ms q)). fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
      reference_term T' (snd (snd row)) = Some (fst (snd row)))"
  using assms
proof (induction ms arbitrary: q T)
  case Nil
  then show ?case by auto
next
  case (Cons m ms)
  let ?x = "finite_residual_term (resolution_node_call m)"
  let ?c = "case L (resolution_node_position m) of Some i \<Rightarrow> (i,q) | None \<Rightarrow> keyed_share_term ?x q"
  obtain r q1 T1 where k: "?c = (r,q1)" and rep1: "keyed_state_represents q1 T1" and f1: "table_formed T1"
    and r1: "reference_term T1 r = Some ?x" and pres1: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T1 i = Some u"
  proof (cases "L (resolution_node_position m)")
    case None
    obtain r q1 where k: "keyed_share_term ?x q = (r,q1)" by (cases "keyed_share_term ?x q")
    let ?T1 = "snd (share_term ?x T)"
    have e: "r = fst (share_term ?x T)" and rep1: "keyed_state_represents q1 ?T1"
      using keyed_share_term_exact[OF Cons.prems(1), of ?x] k by simp_all
    have f1: "table_formed ?T1" and r1: "reference_term ?T1 r = Some ?x"
      using share_term_exact[OF Cons.prems(2), of ?x] e by simp_all
    have pres: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term ?T1 i = Some u"
      using share_term_preserves[of T _ _ ?x] by blast
    show ?thesis by (rule that[of r q1 ?T1]) (use None k rep1 f1 r1 pres in simp_all)
  next
    case (Some i)
    have "reference_term T i = Some ?x" using Cons.prems(3) Some by simp
    then show ?thesis using that[of i q T] Some Cons.prems(1,2) by simp
  qed
  obtain rows q2 where s: "finite_read_rows L ms q1 = (rows,q2)" by (cases "finite_read_rows L ms q1")
  have L1: "\<forall>m'\<in>set ms. \<forall>i. L (resolution_node_position m') = Some i \<longrightarrow>
      reference_term T1 i = Some (finite_residual_term (resolution_node_call m'))"
    using Cons.prems(3) pres1 by simp
  from Cons.IH[OF rep1 f1 L1] s obtain T' where T': "keyed_state_represents q2 T'" "table_formed T'"
      "\<forall>i u. reference_term T1 i = Some u \<longrightarrow> reference_term T' i = Some u" "map fst rows = ms"
      "\<forall>row\<in>set rows. fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
        reference_term T' (snd (snd row)) = Some (fst (snd row))"
    by auto
  have pres: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u" using T'(3) pres1 by blast
  have r': "reference_term T' r = Some ?x" using T'(3) r1 by blast
  have run: "finite_read_rows L (m#ms) q = ((m,?x,r)#rows,q2)" using k s by (simp add: Let_def)
  show ?case by (rule exI[of _ T']) (use run T' pres r' in auto)
qed

lemma finite_share_rows_exact:
  assumes "keyed_state_represents q T" "table_formed T"
  shows "\<exists>T'. keyed_state_represents (snd (finite_share_rows ms q)) T' \<and> table_formed T' \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u) \<and>
    map fst (fst (finite_share_rows ms q)) = ms \<and>
    (\<forall>row\<in>set (fst (finite_share_rows ms q)). fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
      reference_term T' (snd (snd row)) = Some (fst (snd row)))"
  unfolding finite_share_rows_read by (rule finite_read_rows_exact[OF assms]) simp

subsection \<open>The indexes of the found state\<close>

text \<open>
  An insertion into a tree map is the index notion's update at the tree map (@{text tree_map_updates}): the inserted
  value is found at its key, and every other key is kept. Every insertion below is read through this lookup alone.
\<close>

lemma finite_option_eqI: "(\<And>v. a = Some v \<longleftrightarrow> b = Some v) \<Longrightarrow> a = b"
  by (cases a; cases b) auto

lemma finite_tree_insert_lookup: "RBT.lookup (RBT.insert k u T) k' = (if k' = k then Some u else RBT.lookup T k')"
proof (cases "k' = k")
  case True
  have "RBT.lookup (RBT.insert k u T) k = Some u" by (simp only: tree_map_updates.update_at)
  then show ?thesis using True by simp
next
  case False
  have "RBT.lookup (RBT.insert k u T) k' = RBT.lookup T k'"
    by (rule finite_option_eqI) (rule tree_map_updates.update_preserves_else[OF False])
  then show ?thesis using False by simp
qed

definition finite_position_index :: "(('a,'s::linorder,'d,'c) resolution_node \<times> finite_factor_term \<times> nat) list \<Rightarrow>
    ('s list, ('a,'s,'d,'c) resolution_node \<times> nat) rbt" where
  "finite_position_index rows = RBT.bulkload (map (\<lambda>row. (resolution_node_position (fst row),(fst row,snd (snd row)))) rows)"

lemma finite_position_index_lookup:
  assumes d: "distinct (map (\<lambda>row. resolution_node_position (fst row)) rows)"
  shows "RBT.lookup (finite_position_index rows) q = Some v \<longleftrightarrow>
    (q,v) \<in> set (map (\<lambda>row. (resolution_node_position (fst row),(fst row,snd (snd row)))) rows)"
  using tree_map_index.query_search[of "map (\<lambda>row. (resolution_node_position (fst row),(fst row,snd (snd row)))) rows" q v] d
  by (simp add: finite_position_index_def o_def)

definition finite_group_lookup :: "(nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) resolution_node list" where
  "finite_group_lookup G r = (case RBT.lookup G r of None \<Rightarrow> [] | Some ms \<Rightarrow> ms)"

definition finite_group_step ::
    "(nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<times> finite_factor_term \<times> nat \<Rightarrow>
      (nat, ('a,'s,'d,'c) resolution_node list) rbt" where
  "finite_group_step G row = RBT.insert (snd (snd row)) (fst row # finite_group_lookup G (snd (snd row))) G"

definition finite_group_index ::
    "(('a,'s,'d,'c) resolution_node \<times> finite_factor_term \<times> nat) list \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt" where
  "finite_group_index rows = foldl finite_group_step RBT.empty rows"

lemma finite_group_index_lookup:
  "set (finite_group_lookup (finite_group_index rows) r) = {m. \<exists>row\<in>set rows. fst row = m \<and> snd (snd row) = r}"
proof (induction rows rule: rev_induct)
  case Nil
  then show ?case by (simp add: finite_group_index_def finite_group_lookup_def)
next
  case (snoc row rows)
  have step: "finite_group_lookup (finite_group_step G row) r =
      (if r = snd (snd row) then fst row # finite_group_lookup G r else finite_group_lookup G r)" for G
    by (cases "r = snd (snd row)") (simp_all add: finite_group_step_def finite_group_lookup_def finite_tree_insert_lookup)
  show ?case using snoc by (auto simp: finite_group_index_def step)
qed

definition finite_indexed_premise_nodes ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'a finite_term_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_indexed_premise_nodes PI G q0 nd s e p = (let q = resolution_node_position nd@[s];
      IR = fimage (\<lambda>x. fst (keyed_share_term x q0)) (finite_pattern_instances (finite_node_values nd) p);
      C = (case RBT.lookup PI q of None \<Rightarrow> {||}
        | Some (m,r) \<Rightarrow> if resolution_node_site m = e \<and> r |\<in>| IR then {|m|} else {||}) in
    if C \<noteq> {||} then C else finite_first_nodes (fset_of_list (filter (\<lambda>m. resolution_node_site m = e \<and>
      finite_position_left (resolution_node_position m) q) (concat (map (finite_group_lookup G) (sorted_list_of_fset IR))))))"

text \<open>
  A premise's nodes are read through the two indexes from the references of the premise's instances
  (@{text finite_premise_reference_nodes}); any set of references that holds a node's reference exactly when the node's
  call is an instance gives the premise's nodes (@{text finite_premise_reference_nodes_exact}). The instances shared
  again are one such set (@{text finite_indexed_premise_nodes_references}), the instance's reference by substituting the
  node's bindings another (@{text finite_bound_premise_nodes}).
\<close>

definition finite_premise_reference_nodes ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      nat fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_premise_reference_nodes PI G IR nd s e = (let q = resolution_node_position nd@[s];
      C = (case RBT.lookup PI q of None \<Rightarrow> {||}
        | Some (m,r) \<Rightarrow> if resolution_node_site m = e \<and> r |\<in>| IR then {|m|} else {||}) in
    if C \<noteq> {||} then C else finite_first_nodes (fset_of_list (filter (\<lambda>m. resolution_node_site m = e \<and>
      finite_position_left (resolution_node_position m) q) (concat (map (finite_group_lookup G) (sorted_list_of_fset IR))))))"

lemma finite_indexed_premise_nodes_references:
  "finite_indexed_premise_nodes PI G q0 nd s e p = finite_premise_reference_nodes PI G
    (fimage (\<lambda>x. fst (keyed_share_term x q0)) (finite_pattern_instances (finite_node_values nd) p)) nd s e"
  by (simp only: finite_indexed_premise_nodes_def finite_premise_reference_nodes_def Let_def)

lemma finite_premise_reference_nodes_exact:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and PI: "\<And>q m r. RBT.lookup PI q = Some (m,r) \<longleftrightarrow> m |\<in>| N \<and> resolution_node_position m = q \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and G: "\<And>r m. m \<in> set (finite_group_lookup G r) \<longleftrightarrow> m |\<in>| N \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and keyed: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and IR: "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
      r |\<in>| IR \<longleftrightarrow> finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p"
  shows "finite_premise_reference_nodes PI G IR nd s e = finite_premise_nodes N nd s e p"
proof -
  let ?q = "resolution_node_position nd@[s]"
  let ?I = "finite_pattern_instances (finite_node_values nd) p"
  let ?IR = "IR"
  let ?res = "\<lambda>m. finite_residual_term (resolution_node_call m)"
  let ?F = "ffilter (\<lambda>m. resolution_node_site m=e \<and> finite_residual_term (resolution_node_call m) |\<in>| ?I) N"
  have K: "r |\<in>| ?IR \<longleftrightarrow> ?res m |\<in>| ?I" if "m |\<in>| N" "finite_term_keyed q0 r (?res m)" for m r
    using IR[OF that] by simp
  have C: "(case RBT.lookup PI ?q of None \<Rightarrow> {||}
        | Some (m,r) \<Rightarrow> if resolution_node_site m = e \<and> r |\<in>| ?IR then {|m|} else {||}) =
      ffilter (\<lambda>m. resolution_node_position m=?q) ?F"
  proof (cases "RBT.lookup PI ?q")
    case None
    have none: "\<not> (m |\<in>| N \<and> resolution_node_position m = ?q)" for m
    proof
      assume m: "m |\<in>| N \<and> resolution_node_position m = ?q"
      obtain r where r: "finite_term_keyed q0 r (?res m)" using keyed m by blast
      then have "RBT.lookup PI ?q = Some (m,r)" using PI[of ?q m r] m by simp
      then show False using None by simp
    qed
    have "ffilter (\<lambda>m. resolution_node_position m=?q) ?F = {||}"
    proof (rule fset_eqI)
      fix m
      show "m |\<in>| ffilter (\<lambda>m. resolution_node_position m=?q) ?F \<longleftrightarrow> m |\<in>| {||}"
        using none[of m] by (simp only: resolution_ffilter_member) simp
    qed
    then show ?thesis using None by simp
  next
    case (Some v)
    then obtain m1 r1 where v: "RBT.lookup PI ?q = Some (m1,r1)" by (cases v) auto
    have m1: "m1 |\<in>| N" "resolution_node_position m1 = ?q" "finite_term_keyed q0 r1 (?res m1)"
      using PI[of ?q m1 r1] v by simp_all
    have eq: "m |\<in>| N \<and> resolution_node_position m = ?q \<longleftrightarrow> m = m1" for m
    proof
      assume a: "m |\<in>| N \<and> resolution_node_position m = ?q"
      show "m = m1" by (rule distinct) (use a m1 in simp_all)
    next
      assume "m = m1"
      then show "m |\<in>| N \<and> resolution_node_position m = ?q" using m1 by simp
    qed
    have mem: "m |\<in>| ffilter (\<lambda>m. resolution_node_position m=?q) ?F \<longleftrightarrow>
        m = m1 \<and> resolution_node_site m1 = e \<and> ?res m1 |\<in>| ?I" for m
    proof -
      have "m |\<in>| ffilter (\<lambda>m. resolution_node_position m=?q) ?F \<longleftrightarrow>
          (m |\<in>| N \<and> resolution_node_position m = ?q) \<and> resolution_node_site m = e \<and> ?res m |\<in>| ?I"
        by (simp only: resolution_ffilter_member) blast
      also have "\<dots> \<longleftrightarrow> m = m1 \<and> resolution_node_site m1 = e \<and> ?res m1 |\<in>| ?I" by (simp only: eq) fastforce
      finally show ?thesis .
    qed
    have "ffilter (\<lambda>m. resolution_node_position m=?q) ?F =
        (if resolution_node_site m1 = e \<and> ?res m1 |\<in>| ?I then {|m1|} else {||})"
      by (rule fset_eqI) (simp only: mem, auto)
    then show ?thesis using v K[OF m1(1) m1(3)] by simp
  qed
  let ?L = "filter (\<lambda>m. resolution_node_site m = e \<and> finite_position_left (resolution_node_position m) ?q)
    (concat (map (finite_group_lookup G) (sorted_list_of_fset ?IR)))"
  have L: "fset_of_list ?L = ffilter (\<lambda>m. finite_position_left (resolution_node_position m) ?q) ?F"
  proof (rule fset_eqI)
    fix m
    have group: "(\<exists>r. r |\<in>| ?IR \<and> m \<in> set (finite_group_lookup G r)) \<longleftrightarrow> m |\<in>| N \<and> ?res m |\<in>| ?I"
    proof
      assume "\<exists>r. r |\<in>| ?IR \<and> m \<in> set (finite_group_lookup G r)"
      then obtain r where r: "r |\<in>| ?IR" "m \<in> set (finite_group_lookup G r)" by blast
      then have "m |\<in>| N" "finite_term_keyed q0 r (?res m)" using G[where r=r and m=m] by simp_all
      then show "m |\<in>| N \<and> ?res m |\<in>| ?I" using K r(1) by blast
    next
      assume a: "m |\<in>| N \<and> ?res m |\<in>| ?I"
      then obtain r where r: "finite_term_keyed q0 r (?res m)" using keyed by blast
      then have "r |\<in>| ?IR" using K a by blast
      then show "\<exists>r. r |\<in>| ?IR \<and> m \<in> set (finite_group_lookup G r)" using G[where r=r and m=m] a r by blast
    qed
    have memL: "m |\<in>| fset_of_list ?L \<longleftrightarrow> resolution_node_site m = e \<and>
        finite_position_left (resolution_node_position m) ?q \<and> (\<exists>r. r |\<in>| ?IR \<and> m \<in> set (finite_group_lookup G r))"
      by (auto simp: fset_of_list_elem sorted_list_of_fset.rep_eq)
    show "m |\<in>| fset_of_list ?L \<longleftrightarrow> m |\<in>| ffilter (\<lambda>m. finite_position_left (resolution_node_position m) ?q) ?F"
      using group by (simp only: memL resolution_ffilter_member) blast
  qed
  show ?thesis unfolding finite_premise_reference_nodes_def finite_premise_nodes_def Let_def C L ..
qed

lemma finite_indexed_premise_nodes_exact:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and PI: "\<And>q m r. RBT.lookup PI q = Some (m,r) \<longleftrightarrow> m |\<in>| N \<and> resolution_node_position m = q \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and G: "\<And>r m. m \<in> set (finite_group_lookup G r) \<longleftrightarrow> m |\<in>| N \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and keyed: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
  shows "finite_indexed_premise_nodes PI G q0 nd s e p = finite_premise_nodes N nd s e p"
  unfolding finite_indexed_premise_nodes_references
proof (rule finite_premise_reference_nodes_exact[OF distinct PI G keyed])
  fix m r assume "m |\<in>| N" and key: "finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
  let ?I = "finite_pattern_instances (finite_node_values nd) p"
  let ?res = "finite_residual_term (resolution_node_call m)"
  have kx: "fst (keyed_share_term x q0) = r \<longleftrightarrow> x = ?res" for x using key by (simp add: finite_term_keyed_def)
  show "r |\<in>| fimage (\<lambda>x. fst (keyed_share_term x q0)) ?I \<longleftrightarrow> ?res |\<in>| ?I"
  proof
    assume "r |\<in>| fimage (\<lambda>x. fst (keyed_share_term x q0)) ?I"
    then obtain x where x: "x |\<in>| ?I" "r = fst (keyed_share_term x q0)" by auto
    then have "x = ?res" using kx[of x] by simp
    then show "?res |\<in>| ?I" using x(1) by simp
  next
    assume "?res |\<in>| ?I"
    then show "r |\<in>| fimage (\<lambda>x. fst (keyed_share_term x q0)) ?I" using kx[of ?res] by force
  qed
qed

definition finite_indexed_links ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_indexed_links PI G q0 nd = ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,m)) (finite_indexed_premise_nodes PI G q0 nd s e p))
    (finite_schema_premises (resolution_node_schema nd)))"

definition finite_indexed_links_rows ::
    "('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow> (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_indexed_links_rows ns = (case finite_share_rows ns empty_share_state of (rows,q0) \<Rightarrow>
    map (\<lambda>m. (m,finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m)) ns)"

text \<open>
  The two indexes are invariants of the walk over the nodes: its code equation builds them once from the shared rows,
  beside the definition, which builds them within the function mapped over the nodes (task 873, from #851's
  attribution: once per node, quadratic in the nodes). Equal by definition on every input; every statement
  and proof reads the definition.
\<close>

lemma finite_indexed_links_rows_once [code]:
  "finite_indexed_links_rows ns = (case finite_share_rows ns empty_share_state of (rows,q0) \<Rightarrow>
    let PI = finite_position_index rows; G = finite_group_index rows in
    map (\<lambda>m. (m,finite_indexed_links PI G q0 m)) ns)"
  by (simp add: finite_indexed_links_rows_def Let_def split: prod.split)

text \<open>
  The index built from the shared rows reads every premise's nodes exactly: the one index of the found state, read by the
  links and, at a table, by the table links alike.
\<close>

text \<open>
  What the rows read from a representation give the indexes: the table the rows' sharing state represents, extending the
  one read, each node's position and group found by its call's reference, and each such reference decoding the call.
\<close>

lemma finite_read_index_facts:
  assumes listed: "finite_post_listed (fset N) ns" and rep0: "keyed_state_represents q T" and f0: "table_formed T"
    and L: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    and run: "finite_read_rows L ns q = (rows,q0)"
  obtains T' where "keyed_state_represents q0 T'" "table_formed T'"
    "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
    "\<And>q m r. RBT.lookup (finite_position_index rows) q = Some (m,r) \<longleftrightarrow>
      m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    "\<And>r m. m \<in> set (finite_group_lookup (finite_group_index rows) r) \<longleftrightarrow>
      m |\<in>| N \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
      reference_term T' r = Some (finite_residual_term (resolution_node_call m))"
proof -
  note P = finite_post_listed_positions[OF listed]
  let ?res = "\<lambda>m. finite_residual_term (resolution_node_call m)"
  obtain T' where rep: "keyed_state_represents q0 T'" and ft: "table_formed T'" and fsts: "map fst rows = ns"
      and pres: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
      and rw: "\<forall>row\<in>set rows. fst (snd row) = ?res (fst row) \<and> reference_term T' (snd (snd row)) = Some (fst (snd row))"
    using finite_read_rows_exact[OF rep0 f0 L] run by auto
  have keyed: "finite_term_keyed q0 (snd (snd row)) (?res (fst row))" if row: "row \<in> set rows" for row
  proof -
    have "finite_term_keyed q0 (snd (snd row)) (fst (snd row))"
      by (rule finite_term_keyed_intro[OF rep ft]) (use rw row in blast)
    then show ?thesis using rw row by simp
  qed
  have unique: "r = r'" if "finite_term_keyed q0 r y" "finite_term_keyed q0 r' y" for r r' y
    using that unfolding finite_term_keyed_def by metis
  have rowN: "fst row |\<in>| N" if "row \<in> set rows" for row
  proof -
    have "fst row \<in> set (map fst rows)" using that by simp
    then show ?thesis using fsts P(2) by simp
  qed
  have exists: "\<exists>row\<in>set rows. fst row = m" if "m |\<in>| N" for m
  proof -
    have "m \<in> set (map fst rows)" using that fsts P(2) by simp
    then show ?thesis by auto
  qed
  have rows_keyed: "(\<exists>row\<in>set rows. fst row = m \<and> snd (snd row) = r) \<longleftrightarrow>
      m |\<in>| N \<and> finite_term_keyed q0 r (?res m)" for m r
  proof
    assume "\<exists>row\<in>set rows. fst row = m \<and> snd (snd row) = r"
    then show "m |\<in>| N \<and> finite_term_keyed q0 r (?res m)" using rowN keyed by blast
  next
    assume a: "m |\<in>| N \<and> finite_term_keyed q0 r (?res m)"
    then obtain row where row: "row \<in> set rows" "fst row = m" using exists by blast
    then have "snd (snd row) = r" using unique keyed a by blast
    then show "\<exists>row\<in>set rows. fst row = m \<and> snd (snd row) = r" using row by blast
  qed
  have d: "distinct (map (\<lambda>row. resolution_node_position (fst row)) rows)"
    using P(1) unfolding fsts[symmetric] by (simp add: o_def)
  have PI: "RBT.lookup (finite_position_index rows) q = Some (m,r) \<longleftrightarrow>
      m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0 r (?res m)" for q m r
    using finite_position_index_lookup[OF d, of q "(m,r)"] rows_keyed[of m r] by auto
  have G: "m \<in> set (finite_group_lookup (finite_group_index rows) r) \<longleftrightarrow> m |\<in>| N \<and> finite_term_keyed q0 r (?res m)" for m r
    using rows_keyed[of m r] by (simp add: finite_group_index_lookup)
  have ex: "\<exists>r. finite_term_keyed q0 r (?res m)" if "m |\<in>| N" for m using exists[OF that] keyed by blast
  have dist: "m=m'" if "m |\<in>| N" "m' |\<in>| N" "resolution_node_position m=resolution_node_position m'" for m m'
    using P(3) that by blast
  have refd: "reference_term T' r = Some (?res m)" if mN: "m |\<in>| N" and k: "finite_term_keyed q0 r (?res m)" for m r
  proof -
    obtain row where row: "row \<in> set rows" "fst row = m" using exists[OF mN] by blast
    have "snd (snd row) = r" using unique[OF keyed[OF row(1)]] k row(2) by blast
    then show ?thesis using rw row by auto
  qed
  show ?thesis by (rule that[OF rep ft _ PI G ex dist refd]) (use pres in blast)
qed

lemma finite_read_index_exact:
  assumes listed: "finite_post_listed (fset N) ns" and rep0: "keyed_state_represents q T" and f0: "table_formed T"
    and L: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    and run: "finite_read_rows L ns q = (rows,q0)"
  shows "finite_indexed_premise_nodes (finite_position_index rows) (finite_group_index rows) q0 nd s e p =
    finite_premise_nodes N nd s e p"
proof (rule finite_read_index_facts[OF listed rep0 f0 L run])
  fix T'
  assume "keyed_state_represents q0 T'" "table_formed T'"
    "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
    and PI: "\<And>q m r. RBT.lookup (finite_position_index rows) q = Some (m,r) \<longleftrightarrow>
      m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and G: "\<And>r m. m \<in> set (finite_group_lookup (finite_group_index rows) r) \<longleftrightarrow>
      m |\<in>| N \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and ex: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and dist: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
      reference_term T' r = Some (finite_residual_term (resolution_node_call m))"
  show ?thesis by (rule finite_indexed_premise_nodes_exact[OF dist PI G ex])
qed

lemma finite_share_index_exact:
  assumes listed: "finite_post_listed (fset N) ns" and run: "finite_share_rows ns empty_share_state = (rows,q0)"
  shows "finite_indexed_premise_nodes (finite_position_index rows) (finite_group_index rows) q0 nd s e p =
    finite_premise_nodes N nd s e p"
  by (rule finite_read_index_exact[OF listed keyed_state_represents_empty table_formed_empty _
    run[unfolded finite_share_rows_read]]) simp

lemma finite_indexed_links_rows_exact:
  assumes listed: "finite_post_listed (fset N) ns"
  shows "finite_indexed_links_rows ns = map (\<lambda>m. (m,finite_node_links N m)) ns"
proof -
  obtain rows q0 where run: "finite_share_rows ns empty_share_state = (rows,q0)" by (cases "finite_share_rows ns empty_share_state")
  have links: "finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m = finite_node_links N m" for m
    by (simp add: finite_indexed_links_def finite_node_links_def finite_share_index_exact[OF listed run])
  show ?thesis using run links by (simp add: finite_indexed_links_rows_def)
qed

text \<open>
  At a table each row carries, beside the node's links, its table links, read through the same index; an entry is looked
  up first, so a premise with no entry reads no node.
\<close>

definition finite_indexed_table_links ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow>
      (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_indexed_table_links \<Theta> PI G q0 nd = ffUnion (fimage (\<lambda>(s,e,p).
      let U = ffilter (\<lambda>u. resolution_table_lookup \<Theta> (e,u) \<noteq> None) (finite_pattern_instances (finite_node_values nd) p) in
    if U={||} then {||} else if finite_indexed_premise_nodes PI G q0 nd s e p={||}
      then fimage (\<lambda>u. (s,finite_table_node nd s e u)) U else {||})
    (finite_schema_premises (resolution_node_schema nd)))"

definition finite_indexed_table_rows ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_indexed_table_rows \<Theta> ns = (case finite_share_rows ns empty_share_state of (rows,q0) \<Rightarrow>
    let PI = finite_position_index rows; G = finite_group_index rows in
    map (\<lambda>m. (m,finite_indexed_links PI G q0 m,finite_indexed_table_links \<Theta> PI G q0 m)) ns)"

lemma finite_guarded_image: "(if U={||} then {||} else if b then fimage f U else {||}) = (if b then fimage f U else {||})"
  by auto

lemma finite_ffilter_false [simp]: "ffilter (\<lambda>u. False) A = {||}"
  by (rule fset_eqI) simp

lemma finite_indexed_table_rows_exact:
  assumes listed: "finite_post_listed (fset N) ns"
  shows "finite_indexed_table_rows \<Theta> ns = map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns"
proof -
  obtain rows q0 where run: "finite_share_rows ns empty_share_state = (rows,q0)" by (cases "finite_share_rows ns empty_share_state")
  note index = finite_share_index_exact[OF listed run]
  have links: "finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m = finite_node_links N m" for m
    by (simp add: finite_indexed_links_def finite_node_links_def index)
  have table: "finite_indexed_table_links \<Theta> (finite_position_index rows) (finite_group_index rows) q0 m =
      finite_table_links \<Theta> N m" for m
    by (simp only: finite_indexed_table_links_def finite_table_links_def index Let_def finite_guarded_image)
  show ?thesis using run links table by (simp add: finite_indexed_table_rows_def Let_def)
qed

lemma finite_indexed_table_links_empty [simp]: "finite_indexed_table_links resolution_empty_table PI G q0 nd = {||}"
  by (simp add: finite_indexed_table_links_def fset_eq_iff ffUnion_fimage_iff split_paired_Ex)

lemma finite_indexed_table_rows_empty:
  "finite_indexed_table_rows resolution_empty_table ns = map (\<lambda>(m,L). (m,L,{||})) (finite_indexed_links_rows ns)"
  by (simp add: finite_indexed_table_rows_def finite_indexed_links_rows_def Let_def split: prod.split)

subsection \<open>The certificates, once per node, in one pass\<close>

definition finite_indexed_certificate_step ::
    "('s list, ('a,'s,'c) finite_schema_proof) rbt \<Rightarrow>
      ('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow>
      ('s list, ('a,'s,'c) finite_schema_proof) rbt" where
  "finite_indexed_certificate_step T row = RBT.insert (resolution_node_position (fst row))
    (Schema_Proof (resolution_node_clause (fst row)) (finite_node_values (fst row))
      (fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) (snd row))) T"

definition finite_indexed_certificates ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow>
      ('s list, ('a,'s,'c) finite_schema_proof) rbt" where
  "finite_indexed_certificates LS = foldl finite_indexed_certificate_step RBT.empty LS"

text \<open>
  At a table a row's certificate is made from its links' certificates, already in the tree, and its table links' entries;
  at the empty table this is the pass above.
\<close>

definition finite_indexed_certificate_step_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list, ('a,'s,'c) finite_schema_proof) rbt \<Rightarrow>
      ('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow>
      ('s list, ('a,'s,'c) finite_schema_proof) rbt" where
  "finite_indexed_certificate_step_in \<Theta> T row = (case row of (m,L,TL) \<Rightarrow> RBT.insert (resolution_node_position m)
    (Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) L |\<union>|
        fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) TL)) T)"

definition finite_indexed_certificates_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow>
      (('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow>
      ('s list, ('a,'s,'c) finite_schema_proof) rbt" where
  "finite_indexed_certificates_in \<Theta> LS = foldl (finite_indexed_certificate_step_in \<Theta>) RBT.empty LS"

lemma finite_indexed_certificate_steps_empty:
  "foldl finite_indexed_certificate_step T LS = foldl (finite_indexed_certificate_step_in \<Theta>) T (map (\<lambda>(m,L). (m,L,{||})) LS)"
  by (induction LS arbitrary: T)
    (simp_all add: finite_indexed_certificate_step_def finite_indexed_certificate_step_in_def split_def)

lemma finite_indexed_certificates_empty:
  "finite_indexed_certificates LS = finite_indexed_certificates_in \<Theta> (map (\<lambda>(m,L). (m,L,{||})) LS)"
  by (simp add: finite_indexed_certificates_def finite_indexed_certificates_in_def finite_indexed_certificate_steps_empty)

lemma finite_indexed_certificates_in_fold:
  assumes listed: "finite_post_listed (fset N) (pre @ rest)"
    and T: "\<And>p c. RBT.lookup T p = Some c \<longleftrightarrow>
      (\<exists>m\<in>set pre. resolution_node_position m = p \<and> c = finite_node_certificate_in \<Theta> N m)"
  shows "RBT.lookup (foldl (finite_indexed_certificate_step_in \<Theta>) T
      (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) rest)) p = Some c \<longleftrightarrow>
    (\<exists>m\<in>set (pre @ rest). resolution_node_position m = p \<and> c = finite_node_certificate_in \<Theta> N m)"
  using assms
proof (induction rest arbitrary: pre T)
  case Nil
  then show ?case by simp
next
  case (Cons m rest)
  have sw: "sorted_wrt (\<lambda>a b. finite_node_key a < finite_node_key b) (pre @ m # rest)"
    and setn: "set (pre @ m # rest) = fset N"
    using Cons.prems(1) by (simp_all add: finite_post_listed_def)
  have mN: "m |\<in>| N" using setn by auto
  have earlier: "m' \<in> set pre" if l: "(s,m') |\<in>| finite_node_links N m" for s m'
  proof (rule ccontr)
    assume out: "m' \<notin> set pre"
    have lt: "finite_node_key m' < finite_node_key m" by (rule finite_node_links_post[OF l])
    have "m' \<in> set (pre @ m # rest)" using finite_node_links_reach(1)[OF l] setn by auto
    then have "m' = m \<or> m' \<in> set rest" using out by auto
    then show False using lt sw by (auto simp: sorted_wrt_append)
  qed
  have looked: "the (RBT.lookup T (resolution_node_position m')) = finite_node_certificate_in \<Theta> N m'"
    if "(s,m') |\<in>| finite_node_links N m" for s m'
    using Cons.prems(2)[of "resolution_node_position m'" "finite_node_certificate_in \<Theta> N m'"] earlier[OF that] by auto
  have made: "Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) (finite_node_links N m) |\<union>|
        fimage (\<lambda>(s,a). (s,finite_table_proof \<Theta> a)) (finite_table_links \<Theta> N m)) =
    finite_node_certificate_in \<Theta> N m"
  proof -
    have "fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) (finite_node_links N m) =
        fimage (\<lambda>(s,m'). (s,finite_node_certificate_in \<Theta> N m')) (finite_node_links N m)"
      by (rule fimage_cong[OF refl]) (auto simp: looked)
    then show ?thesis using finite_node_certificate_in_links[OF mN] by simp
  qed
  have fresh: "resolution_node_position m' \<noteq> resolution_node_position m" if "m' \<in> set pre" for m'
    using sw that by (auto simp: sorted_wrt_append)
  have T': "RBT.lookup (finite_indexed_certificate_step_in \<Theta> T (m,finite_node_links N m,finite_table_links \<Theta> N m)) p = Some c \<longleftrightarrow>
      (\<exists>m'\<in>set (pre @ [m]). resolution_node_position m' = p \<and> c = finite_node_certificate_in \<Theta> N m')" for p c
    using Cons.prems(2)[of p c] made fresh
    by (auto simp: finite_indexed_certificate_step_in_def finite_tree_insert_lookup)
  have "finite_post_listed (fset N) ((pre @ [m]) @ rest)" using Cons.prems(1) by simp
  from Cons.IH[OF this T'] show ?case by simp
qed

lemma finite_indexed_certificates_in_exact:
  assumes listed: "finite_post_listed (fset N) ns" and m: "m |\<in>| N"
  shows "the (RBT.lookup (finite_indexed_certificates_in \<Theta> (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns))
      (resolution_node_position m)) = finite_node_proof_in \<Theta> (fcard N) N m"
proof -
  have "RBT.lookup (finite_indexed_certificates_in \<Theta> (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns))
      (resolution_node_position m) = Some (finite_node_certificate_in \<Theta> N m)"
    using finite_indexed_certificates_in_fold[of N "[]" ns RBT.empty \<Theta> "resolution_node_position m" "finite_node_certificate_in \<Theta> N m"]
      listed m by (auto simp: finite_indexed_certificates_in_def finite_post_listed_def)
  then show ?thesis by (simp add: finite_state_node_certificate_in[OF m])
qed

lemma finite_indexed_certificates_fold:
  assumes listed: "finite_post_listed (fset N) (pre @ rest)"
    and T: "\<And>p c. RBT.lookup T p = Some c \<longleftrightarrow> (\<exists>m\<in>set pre. resolution_node_position m = p \<and> c = finite_node_certificate N m)"
  shows "RBT.lookup (foldl finite_indexed_certificate_step T (map (\<lambda>m. (m,finite_node_links N m)) rest)) p = Some c \<longleftrightarrow>
    (\<exists>m\<in>set (pre @ rest). resolution_node_position m = p \<and> c = finite_node_certificate N m)"
  using finite_indexed_certificates_in_fold[where \<Theta>=resolution_empty_table, OF assms]
  by (simp add: finite_indexed_certificate_steps_empty[where \<Theta>=resolution_empty_table] comp_def)

lemma finite_indexed_certificates_exact:
  assumes listed: "finite_post_listed (fset N) ns" and m: "m |\<in>| N"
  shows "the (RBT.lookup (finite_indexed_certificates (map (\<lambda>m. (m,finite_node_links N m)) ns)) (resolution_node_position m)) =
    finite_node_proof (fcard N) N m"
  using finite_indexed_certificates_in_exact[OF listed m, of resolution_empty_table]
  by (simp add: finite_indexed_certificates_empty[where \<Theta>=resolution_empty_table] comp_def)

subsection \<open>The reach of a root, in one pass\<close>

lemma finite_link_reach_edges:
  assumes nd: "nd |\<in>| N"
  shows "m |\<in>| finite_link_reach N nd \<longleftrightarrow> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
proof
  assume "m |\<in>| finite_link_reach N nd"
  then show "(nd,m) \<in> (finite_link_edges N)\<^sup>*" by (rule finite_link_reach(3)[OF nd])
next
  assume "(nd,m) \<in> (finite_link_edges N)\<^sup>*"
  then show "m |\<in>| finite_link_reach N nd"
  proof (induction rule: rtrancl_induct)
    case base
    show ?case by (rule finite_link_reach(1)[OF nd])
  next
    case (step y z)
    then obtain s where "(s,z) |\<in>| finite_node_links N y" by (auto simp: finite_link_edges_def)
    then show ?case using finite_link_reach(4)[OF nd step.IH] by blast
  qed
qed

definition finite_indexed_reach_step ::
    "('s list, unit) rbt \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow>
      ('s list, unit) rbt" where
  "finite_indexed_reach_step R row = (if RBT.lookup R (resolution_node_position (fst row)) = None then R
    else foldl (\<lambda>R p. RBT.insert p () R) R (sorted_list_of_fset (fimage (\<lambda>(s,m'). resolution_node_position m') (snd row))))"

definition finite_indexed_reach ::
    "(('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s list, unit) rbt" where
  "finite_indexed_reach LS nd = foldl finite_indexed_reach_step (RBT.insert (resolution_node_position nd) () RBT.empty) (rev LS)"

lemma finite_insert_positions:
  "RBT.lookup (foldl (\<lambda>R p. RBT.insert p () R) R ps) k \<noteq> None \<longleftrightarrow> RBT.lookup R k \<noteq> None \<or> k \<in> set ps"
  by (induction ps arbitrary: R) (auto simp: finite_tree_insert_lookup)

text \<open>
  The reach's invariant: every position the tree holds is a node reached from the root, and every processed node the
  tree holds has its links in it.
\<close>

definition finite_reach_invariant ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('a,'s,'d,'c) resolution_node list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> bool" where
  "finite_reach_invariant N nd dn R \<longleftrightarrow>
    (\<forall>p. RBT.lookup R p \<noteq> None \<longrightarrow>
      (\<exists>m. m |\<in>| N \<and> resolution_node_position m = p \<and> (nd,m) \<in> (finite_link_edges N)\<^sup>*)) \<and>
    (\<forall>m s m'. m \<in> set dn \<longrightarrow> RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow>
      (s,m') |\<in>| finite_node_links N m \<longrightarrow> RBT.lookup R (resolution_node_position m') \<noteq> None)"

lemma finite_indexed_reach_fold:
  assumes dist: "inj_on resolution_node_position (fset N)"
    and sw: "sorted_wrt (\<lambda>a b. finite_node_key b < finite_node_key a) (dn @ todo)"
    and sub: "set (dn @ todo) \<subseteq> fset N"
    and inv: "finite_reach_invariant N nd dn R"
  shows "(\<forall>k. RBT.lookup R k \<noteq> None \<longrightarrow>
      RBT.lookup (foldl finite_indexed_reach_step R (map (\<lambda>m. (m,finite_node_links N m)) todo)) k \<noteq> None) \<and>
    finite_reach_invariant N nd (dn @ todo) (foldl finite_indexed_reach_step R (map (\<lambda>m. (m,finite_node_links N m)) todo))"
  using sw sub inv
proof (induction todo arbitrary: dn R)
  case Nil
  then show ?case by simp
next
  case (Cons m todo)
  have inN: "\<exists>m. m |\<in>| N \<and> resolution_node_position m = p \<and> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    if "RBT.lookup R p \<noteq> None" for p
    using Cons.prems(3) that unfolding finite_reach_invariant_def by blast
  have closed: "RBT.lookup R (resolution_node_position m') \<noteq> None"
    if "m0 \<in> set dn" "RBT.lookup R (resolution_node_position m0) \<noteq> None" "(s,m') |\<in>| finite_node_links N m0" for m0 s m'
    using Cons.prems(3) that unfolding finite_reach_invariant_def by blast
  let ?L = "finite_node_links N m"
  let ?R = "finite_indexed_reach_step R (m,?L)"
  have mN: "m |\<in>| N" using Cons.prems(2) by auto
  have ins: "RBT.lookup ?R k \<noteq> None \<longleftrightarrow> RBT.lookup R k \<noteq> None \<or>
      (RBT.lookup R (resolution_node_position m) \<noteq> None \<and> (\<exists>s m'. (s,m') |\<in>| ?L \<and> resolution_node_position m' = k))" for k
  proof -
    let ?ps = "sorted_list_of_fset (fimage (\<lambda>(s,m'). resolution_node_position m') ?L)"
    have ps: "k \<in> set ?ps \<longleftrightarrow> (\<exists>s m'. (s,m') |\<in>| ?L \<and> resolution_node_position m' = k)"
      by (force simp: sorted_list_of_fset.rep_eq)
    show ?thesis
    proof (cases "RBT.lookup R (resolution_node_position m) = None")
      case True
      then have "?R = R" by (simp add: finite_indexed_reach_step_def)
      then show ?thesis using True by simp
    next
      case False
      then have "?R = foldl (\<lambda>R p. RBT.insert p () R) R ?ps" by (simp add: finite_indexed_reach_step_def)
      then show ?thesis using False by (simp only: finite_insert_positions ps) simp
    qed
  qed
  have inN': "\<exists>m0. m0 |\<in>| N \<and> resolution_node_position m0 = p \<and> (nd,m0) \<in> (finite_link_edges N)\<^sup>*"
    if "RBT.lookup ?R p \<noteq> None" for p
  proof -
    from that ins[of p] consider "RBT.lookup R p \<noteq> None"
      | s m' where "RBT.lookup R (resolution_node_position m) \<noteq> None" "(s,m') |\<in>| ?L" "resolution_node_position m' = p"
      by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (rule inN)
    next
      case 2
      obtain m0 where m0: "m0 |\<in>| N" "resolution_node_position m0 = resolution_node_position m"
          "(nd,m0) \<in> (finite_link_edges N)\<^sup>*"
        using inN[OF 2(1)] by blast
      have "m0 = m" by (rule inj_onD[OF dist m0(2) m0(1) mN])
      then have "(nd,m') \<in> (finite_link_edges N)\<^sup>*"
        using m0(3) 2(2) by (auto simp: finite_link_edges_def intro: rtrancl_into_rtrancl)
      moreover have "m' |\<in>| N" using finite_node_links_reach(1)[OF 2(2)] .
      ultimately show ?thesis using 2(3) by blast
    qed
  qed
  have closed': "RBT.lookup ?R (resolution_node_position m') \<noteq> None"
    if m0: "m0 \<in> set (dn @ [m])" and in0: "RBT.lookup ?R (resolution_node_position m0) \<noteq> None"
      and l: "(s,m') |\<in>| finite_node_links N m0" for m0 s m'
  proof (cases "m0 = m")
    case True
    have "RBT.lookup R (resolution_node_position m) \<noteq> None"
    proof (rule ccontr)
      assume no: "\<not> RBT.lookup R (resolution_node_position m) \<noteq> None"
      have "\<not> RBT.lookup ?R (resolution_node_position m) \<noteq> None" using ins[of "resolution_node_position m"] no by blast
      then show False using in0 True by simp
    qed
    then show ?thesis using ins[of "resolution_node_position m'"] l True by blast
  next
    case False
    then have m0dn: "m0 \<in> set dn" using m0 by simp
    have m0N: "m0 |\<in>| N" using Cons.prems(2) m0dn by auto
    have key: "finite_node_key m < finite_node_key m0" using Cons.prems(1) m0dn by (auto simp: sorted_wrt_append)
    have "RBT.lookup R (resolution_node_position m0) \<noteq> None"
    proof (rule ccontr)
      assume "\<not> RBT.lookup R (resolution_node_position m0) \<noteq> None"
      then obtain s' m'' where l'': "(s',m'') |\<in>| ?L" "resolution_node_position m'' = resolution_node_position m0"
        using in0 ins[of "resolution_node_position m0"] by blast
      have "m'' = m0" by (rule inj_onD[OF dist l''(2) finite_node_links_reach(1)[OF l''(1)] m0N])
      moreover have "finite_node_key m'' < finite_node_key m" by (rule finite_node_links_post[OF l''(1)])
      ultimately show False using key less_asym by blast
    qed
    then have "RBT.lookup R (resolution_node_position m') \<noteq> None" using closed[OF m0dn _ l] by blast
    then show ?thesis using ins[of "resolution_node_position m'"] by blast
  qed
  have sw': "sorted_wrt (\<lambda>a b. finite_node_key b < finite_node_key a) ((dn @ [m]) @ todo)" using Cons.prems(1) by simp
  have sub': "set ((dn @ [m]) @ todo) \<subseteq> fset N" using Cons.prems(2) by simp
  have inv': "finite_reach_invariant N nd (dn @ [m]) ?R"
    unfolding finite_reach_invariant_def using inN' closed' by blast
  have lst: "(dn @ [m]) @ todo = dn @ m # todo" by simp
  note IH = Cons.IH[OF sw' sub' inv', unfolded lst]
  have grow: "RBT.lookup R k \<noteq> None \<Longrightarrow> RBT.lookup ?R k \<noteq> None" for k using ins[of k] by blast
  have fold: "foldl finite_indexed_reach_step R (map (\<lambda>m. (m,finite_node_links N m)) (m # todo)) =
      foldl finite_indexed_reach_step ?R (map (\<lambda>m. (m,finite_node_links N m)) todo)" by simp
  show ?case unfolding fold using IH grow by blast
qed

lemma finite_indexed_reach_exact:
  assumes listed: "finite_post_listed (fset N) ns" and nd: "nd |\<in>| N" and m: "m |\<in>| N"
  shows "RBT.lookup (finite_indexed_reach (map (\<lambda>m. (m,finite_node_links N m)) ns) nd) (resolution_node_position m) \<noteq> None
    \<longleftrightarrow> m |\<in>| finite_link_reach N nd"
proof -
  note P = finite_post_listed_positions[OF listed]
  let ?Rstart = "RBT.insert (resolution_node_position nd) () RBT.empty"
  let ?R = "finite_indexed_reach (map (\<lambda>m. (m,finite_node_links N m)) ns) nd"
  have dist: "inj_on resolution_node_position (fset N)" using P(1) P(2) by (simp add: distinct_map)
  have sw: "sorted_wrt (\<lambda>a b. finite_node_key b < finite_node_key a) ([] @ rev ns)"
    using listed by (simp add: finite_post_listed_def sorted_wrt_rev)
  have sub: "set ([] @ rev ns) \<subseteq> fset N" using P(2) by simp
  have inN: "\<exists>m. m |\<in>| N \<and> resolution_node_position m = p \<and> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    if "RBT.lookup ?Rstart p \<noteq> None" for p
  proof -
    have "p = resolution_node_position nd" using that by (simp add: finite_tree_insert_lookup split: if_splits)
    then show ?thesis using nd by blast
  qed
  have inv0: "finite_reach_invariant N nd [] ?Rstart" unfolding finite_reach_invariant_def using inN by simp
  have R: "?R = foldl finite_indexed_reach_step ?Rstart (map (\<lambda>m. (m,finite_node_links N m)) (rev ns))"
    by (simp add: finite_indexed_reach_def rev_map)
  note F = finite_indexed_reach_fold[OF dist sw sub inv0]
  note F1 = F[THEN conjunct1, rule_format]
    and F2 = F[THEN conjunct2, unfolded finite_reach_invariant_def, THEN conjunct1, rule_format]
    and F3 = F[THEN conjunct2, unfolded finite_reach_invariant_def, THEN conjunct2, rule_format]
  have root: "RBT.lookup ?R (resolution_node_position nd) \<noteq> None"
  proof -
    have start: "RBT.lookup ?Rstart (resolution_node_position nd) \<noteq> None" by (simp only: finite_tree_insert_lookup) simp
    show ?thesis unfolding R by (rule F1[OF start])
  qed
  have reached: "RBT.lookup ?R p \<noteq> None \<Longrightarrow> \<exists>m. m |\<in>| N \<and> resolution_node_position m = p \<and> (nd,m) \<in> (finite_link_edges N)\<^sup>*"
    for p unfolding R by (rule F2)
  have closure: "m0 |\<in>| N \<Longrightarrow> RBT.lookup ?R (resolution_node_position m0) \<noteq> None \<Longrightarrow> (s,m') |\<in>| finite_node_links N m0 \<Longrightarrow>
      RBT.lookup ?R (resolution_node_position m') \<noteq> None" for m0 s m'
  proof -
    assume m0: "m0 |\<in>| N" and in0: "RBT.lookup ?R (resolution_node_position m0) \<noteq> None"
      and l: "(s,m') |\<in>| finite_node_links N m0"
    have "m0 \<in> set ([] @ rev ns)" using m0 P(2) by simp
    from F3[OF this in0[unfolded R] l] show ?thesis unfolding R .
  qed
  show ?thesis
  proof
    assume "RBT.lookup ?R (resolution_node_position m) \<noteq> None"
    then obtain m0 where "m0 |\<in>| N" "resolution_node_position m0 = resolution_node_position m" "(nd,m0) \<in> (finite_link_edges N)\<^sup>*"
      using reached by blast
    then have "(nd,m) \<in> (finite_link_edges N)\<^sup>*" using inj_onD[OF dist _ _ m] by metis
    then show "m |\<in>| finite_link_reach N nd" by (simp add: finite_link_reach_edges[OF nd])
  next
    assume "m |\<in>| finite_link_reach N nd"
    then have "(nd,m) \<in> (finite_link_edges N)\<^sup>*" by (simp add: finite_link_reach_edges[OF nd])
    then have "m |\<in>| N \<and> RBT.lookup ?R (resolution_node_position m) \<noteq> None"
    proof (induction rule: rtrancl_induct)
      case base
      show ?case using nd root by blast
    next
      case (step y z)
      then obtain s where l: "(s,z) |\<in>| finite_node_links N y" by (auto simp: finite_link_edges_def)
      show ?case using finite_node_links_reach(1)[OF l] closure[OF _ _ l] step.IH by blast
    qed
    then show "RBT.lookup ?R (resolution_node_position m) \<noteq> None" by blast
  qed
qed

subsection \<open>The graph reading over the indexes\<close>

definition finite_indexed_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_indexed_graph_check P d t LS nd = (let R = finite_indexed_reach LS nd in
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    list_all (\<lambda>(m,L). RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional L \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L)) LS)"



subsection \<open>The graph reading over the indexes at a table\<close>

text \<open>
  The graph reading and the entries' acceptance at a given reach; the indexed forms read them at the root's reach.
\<close>

definition finite_indexed_reached_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_indexed_reached_graph_check P d t LS R nd = (
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    list_all (\<lambda>(m,L,TL). RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional (L |\<union>| TL) \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)) \<and>
      fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a)))) LS)"

definition finite_indexed_reached_entries ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> bool" where
  "finite_indexed_reached_entries P \<Theta> LS R = (
    list_all (\<lambda>(m,L,TL). RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow> fBall TL (\<lambda>(s,a).
      finite_checks_schema_proof P (finite_table_proof \<Theta> a) (resolution_node_site a) (finite_residual_term (resolution_node_call a))))
    LS)"

definition finite_indexed_table_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_indexed_table_graph_check P d t LS nd =
    finite_indexed_reached_graph_check P d t LS (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd"

definition finite_indexed_table_entries ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_indexed_table_entries P \<Theta> LS nd =
    finite_indexed_reached_entries P \<Theta> LS (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd)"

lemma finite_indexed_table_entries_rows [simp]:
  "finite_indexed_table_entries P \<Theta> (map (\<lambda>(m,L). (m,L,{||})) LS) nd"
  by (simp add: finite_indexed_table_entries_def finite_indexed_reached_entries_def Let_def list_all_iff split_def)

lemma finite_indexed_graph_check_rows:
  "finite_indexed_graph_check P d t LS nd = finite_indexed_table_graph_check P d t (map (\<lambda>(m,L). (m,L,{||})) LS) nd"
  by (simp add: finite_indexed_graph_check_def finite_indexed_table_graph_check_def finite_indexed_reached_graph_check_def
    Let_def list_all_iff split_def comp_def)

lemma finite_indexed_table_graph_check_exact:
  assumes listed: "finite_post_listed (fset N) ns" and nd: "nd |\<in>| N"
  shows "finite_indexed_table_graph_check P d t (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) nd =
    finite_state_graph_check_in \<Theta> P d t N nd"
proof -
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  have dist: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    using finite_post_listed_positions(3)[OF listed] by blast
  have pairs: "map (\<lambda>(m,L,TL). (m,L)) (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) =
      map (\<lambda>m. (m,finite_node_links N m)) ns" by simp
  let ?R = "finite_indexed_reach (map (\<lambda>m. (m,finite_node_links N m)) ns) nd"
  let ?Q = "\<lambda>n. fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
    (finite_node_links N n |\<union>| finite_table_links \<Theta> N n)"
  let ?F = "\<lambda>n. fBall (finite_table_links \<Theta> N n) (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a)
    (finite_residual_term (resolution_node_call a)))"
  let ?\<Phi> = "\<lambda>n. finite_relation_functional (finite_node_links N n |\<union>| finite_table_links \<Theta> N n) \<and>
    finite_admitted_instance_at P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
      (finite_residual_term (resolution_node_call n)) (?Q n) \<and> ?F n"
  have claims: "finite_node_link_claims N n |\<union>| finite_table_link_claims \<Theta> N n = ?Q n" for n
    by (rule fset_eqI) (force simp: finite_node_link_claims_def finite_table_link_claims_def resolution_fset_simps)
  have A: "list_all (\<lambda>(m,L,TL). RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional (L |\<union>| TL) \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)) \<and>
      fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))))
      (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) \<longleftrightarrow> fBall (finite_link_reach N nd) ?\<Phi>"
  proof -
    have "list_all (\<lambda>(m,L,TL). RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional (L |\<union>| TL) \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)) \<and>
      fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))))
      (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) \<longleftrightarrow>
      (\<forall>m\<in>fset N. RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> ?\<Phi> m)"
      by (simp add: list_all_iff setns)
    also have "\<dots> \<longleftrightarrow> (\<forall>m\<in>fset N. m |\<in>| finite_link_reach N nd \<longrightarrow> ?\<Phi> m)"
      by (rule ball_cong[OF refl]) (simp only: finite_indexed_reach_exact[OF listed nd])
    also have "\<dots> \<longleftrightarrow> fBall (finite_link_reach N nd) ?\<Phi>" using finite_link_reach(2)[OF nd] by auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding finite_indexed_table_graph_check_def finite_indexed_reached_graph_check_def pairs A
      finite_state_graph_check_in_at[OF nd]
    using finite_state_graph_in_uses[OF nd dist] by blast
qed

lemma finite_indexed_graph_check_exact:
  assumes listed: "finite_post_listed (fset N) ns" and nd: "nd |\<in>| N"
  shows "finite_indexed_graph_check P d t (map (\<lambda>m. (m,finite_node_links N m)) ns) nd = finite_state_graph_check P d t N nd"
  using finite_indexed_table_graph_check_exact[OF listed nd, of P d t resolution_empty_table]
  by (simp add: finite_indexed_graph_check_rows finite_state_graph_check_in_empty comp_def)

lemma finite_indexed_table_entries_exact:
  assumes listed: "finite_post_listed (fset N) ns" and nd: "nd |\<in>| N"
  shows "finite_indexed_table_entries P \<Theta> (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) nd =
    finite_table_entries_accepted P \<Theta> N nd"
proof -
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  let ?R = "finite_indexed_reach (map (\<lambda>m. (m,finite_node_links N m)) ns) nd"
  let ?E = "\<lambda>m. fBall (finite_table_links \<Theta> N m) (\<lambda>(s,a). finite_checks_schema_proof P (finite_table_proof \<Theta> a)
    (resolution_node_site a) (finite_residual_term (resolution_node_call a)))"
  have pairs: "map (\<lambda>(m,L,TL). (m,L)) (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) =
      map (\<lambda>m. (m,finite_node_links N m)) ns" by simp
  have "finite_indexed_table_entries P \<Theta> (map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns) nd \<longleftrightarrow>
      (\<forall>m\<in>fset N. RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> ?E m)"
    unfolding finite_indexed_table_entries_def finite_indexed_reached_entries_def pairs by (simp add: list_all_iff setns)
  also have "\<dots> \<longleftrightarrow> (\<forall>m\<in>fset N. m |\<in>| finite_link_reach N nd \<longrightarrow> ?E m)"
    by (rule ball_cong[OF refl]) (simp only: finite_indexed_reach_exact[OF listed nd])
  also have "\<dots> \<longleftrightarrow> fBall (finite_link_reach N nd) ?E" using finite_link_reach(2)[OF nd] by auto
  also have "\<dots> \<longleftrightarrow> finite_table_entries_accepted P \<Theta> N nd"
    by (auto simp: finite_table_entries_accepted_def finite_table_discharges_def resolution_fset_simps)
  finally show ?thesis .
qed

text \<open>
  The graph reading and the entries' acceptance over one reach: the reach of the root bound once for both passes.
\<close>

definition finite_indexed_table_accepts ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_indexed_table_accepts P \<Theta> d t LS nd = (let R = finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd in
    finite_indexed_reached_graph_check P d t LS R nd \<and> finite_indexed_reached_entries P \<Theta> LS R)"

lemma finite_indexed_table_accepts_split:
  "finite_indexed_table_accepts P \<Theta> d t LS nd =
    (finite_indexed_table_graph_check P d t LS nd \<and> finite_indexed_table_entries P \<Theta> LS nd)"
  by (simp only: finite_indexed_table_accepts_def finite_indexed_table_graph_check_def finite_indexed_table_entries_def
    Let_def)

subsection \<open>The code equations over the indexes at a table\<close>

declare finite_state_verdicts_in_code [code del] finite_state_proofs_in_table [code del]

lemma finite_state_verdicts_in_indexed [code]:
  "finite_state_verdicts_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table_in \<Theta> N K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,(finite_state_graph_code_in \<Theta> P d t N K nd \<and> finite_table_entries_accepted P \<Theta> N nd) \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns; CT = finite_indexed_certificates_in \<Theta> LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,(finite_indexed_table_graph_check P d t LS nd \<and> finite_indexed_table_entries P \<Theta> LS nd) \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_state_verdicts_in_code)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  let ?LS = "map (\<lambda>m. (m,finite_node_links ?N m,finite_table_links \<Theta> ?N m)) ns"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have "(\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard ?N) ?N nd in
      (c,(finite_state_graph_check_in \<Theta> P d t ?N nd \<and> finite_table_entries_accepted P \<Theta> ?N nd) \<or>
        finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (RBT.lookup (finite_indexed_certificates_in \<Theta> ?LS) (resolution_node_position nd)) in
      (c,(finite_indexed_table_graph_check P d t ?LS nd \<and> finite_indexed_table_entries P \<Theta> ?LS nd) \<or>
        finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
  proof -
    have xN: "x |\<in>| ?N" using that by simp
    note c = finite_indexed_certificates_in_exact[OF listed xN, of \<Theta>]
    note g = finite_indexed_table_graph_check_exact[OF listed xN, of P d t \<Theta>]
    note e = finite_indexed_table_entries_exact[OF listed xN, of P \<Theta>]
    show ?thesis by (simp only: c g e)
  qed
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using Some by (simp add: finite_state_verdicts_in_def finite_indexed_table_rows_exact[OF listed] Let_def)
qed

lemma finite_state_proofs_in_indexed [code]:
  "finite_state_proofs_in \<Theta> st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; T = finite_certificate_table_in \<Theta> N (finite_node_ranked N) in
        fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let CT = finite_indexed_certificates_in \<Theta> (finite_indexed_table_rows \<Theta> ns) in
        fimage (\<lambda>nd. the (RBT.lookup CT (resolution_node_position nd))) (ffilter (\<lambda>nd. resolution_node_position nd=[])
          (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_state_proofs_in_table)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have "finite_node_proof_in \<Theta> (fcard ?N) ?N x = the (RBT.lookup (finite_indexed_certificates_in \<Theta>
      (map (\<lambda>m. (m,finite_node_links ?N m,finite_table_links \<Theta> ?N m)) ns)) (resolution_node_position x))"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
  proof -
    have xN: "x |\<in>| ?N" using that by simp
    show ?thesis by (rule finite_indexed_certificates_in_exact[OF listed xN, symmetric])
  qed
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using Some by (simp add: finite_state_proofs_in_def finite_indexed_table_rows_exact[OF listed] Let_def)
qed

declare finite_state_verdicts_in_indexed [code del]

lemma finite_state_verdicts_in_accepts [code]:
  "finite_state_verdicts_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table_in \<Theta> N K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,(finite_state_graph_code_in \<Theta> P d t N K nd \<and> finite_table_entries_accepted P \<Theta> N nd) \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns; CT = finite_indexed_certificates_in \<Theta> LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,finite_indexed_table_accepts P \<Theta> d t LS nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
  by (simp only: finite_state_verdicts_in_indexed finite_indexed_table_accepts_split)

subsection \<open>The code equations over the indexes\<close>

declare finite_state_verdicts_code [code del] finite_state_proofs_table [code del]

lemma finite_state_verdicts_indexed [code]:
  "finite_state_verdicts P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,finite_state_graph_code P d t K nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let LS = finite_indexed_links_rows ns; CT = finite_indexed_certificates LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,finite_indexed_graph_check P d t LS nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
  using finite_state_verdicts_in_indexed[of resolution_empty_table P d t st]
  by (simp add: finite_state_verdicts_empty finite_certificate_table_empty finite_state_graph_code_empty
    finite_indexed_table_rows_empty finite_indexed_certificates_empty[where \<Theta>=resolution_empty_table, symmetric]
    finite_indexed_graph_check_rows[symmetric] Let_def split: option.split)

lemma finite_state_proofs_indexed [code]:
  "finite_state_proofs st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; T = finite_certificate_table (finite_node_ranked N) in
        fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let CT = finite_indexed_certificates (finite_indexed_links_rows ns) in
        fimage (\<lambda>nd. the (RBT.lookup CT (resolution_node_position nd))) (ffilter (\<lambda>nd. resolution_node_position nd=[])
          (resolution_nodes st))))"
  using finite_state_proofs_in_indexed[of resolution_empty_table st]
  by (simp add: finite_state_proofs_def finite_certificate_table_empty finite_indexed_table_rows_empty
    finite_indexed_certificates_empty[where \<Theta>=resolution_empty_table, symmetric] Let_def split: option.split)

subsection \<open>The found states' verdicts united without comparing certificates\<close>

text \<open>
  The verdicts of the found states are united once and then only read, so their union is the listed union
  (@{text Listed_Set_Unions}): the states' listings are concatenated and no root certificate is compared with another;
  a certificate found in two states is listed twice in the same set. The diagnoses and the refused certificates are
  united likewise.
\<close>

declare finite_outcome_result_verdicts [code del]

lemma finite_listed_union_two: "finite_listed_union [A,B] = A |\<union>| B"
  unfolding finite_listed_union_def by (rule fset_eqI) (auto simp: ffUnion.rep_eq fset_of_list.rep_eq)

lemma finite_outcome_result_listed [code]:
  "finite_outcome_result P d t R = (let V = listed_fimage_union (finite_state_verdicts P d t) (resolution_found R);
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (finite_listed_union [resolution_diagnoses R, fimage Resolution_Refused C]))"
  unfolding finite_outcome_result_verdicts listed_fimage_union_def finite_listed_union_two Let_def ..

declare finite_outcome_result_in_verdicts [code del]

lemma finite_outcome_result_in_listed [code]:
  "finite_outcome_result_in \<Theta> P d t R = (let V = listed_fimage_union (finite_state_verdicts_in \<Theta> P d t) (resolution_found R);
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (finite_listed_union [resolution_diagnoses R, fimage Resolution_Refused C]))"
  unfolding finite_outcome_result_in_verdicts listed_fimage_union_def finite_listed_union_two Let_def ..

text \<open>
  The graph check at a table and a table's check over graphs execute through the same index: where the nodes are listed,
  the graph reading at a table is the indexed check with its table links (@{text finite_indexed_table_graph_check_exact}).
\<close>

lemma finite_state_graph_check_in_indexed [code]:
  "finite_state_graph_check_in \<Theta> P d t N nd = (case finite_post_listing (fset N) of
      None \<Rightarrow> finite_graph_reading P (finite_state_graph_in \<Theta> N nd) nd d t (finite_state_claims_in \<Theta> N nd)
    | Some ns \<Rightarrow> nd |\<in>| N \<and> finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns) nd \<or>
        nd |\<notin>| N \<and> finite_graph_reading P (finite_state_graph_in \<Theta> N nd) nd d t (finite_state_claims_in \<Theta> N nd))"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by (simp add: finite_state_graph_check_in_def)
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  show ?thesis
  proof (cases "nd |\<in>| N")
    case True
    then show ?thesis using Some
      by (simp add: finite_indexed_table_rows_exact[OF listed] finite_indexed_table_graph_check_exact[OF listed True])
  next
    case False
    then show ?thesis using Some by (simp add: finite_state_graph_check_in_def)
  qed
qed

text \<open>
  A table's check and the table it produces take each entry from the certificates made once per node over the rows the
  indexed graph check reads: one listing and one index build per row, shared by the check and the certificate.
\<close>

declare finite_table_graph_checks.simps [code del] finite_table_produced.simps [code del]

lemma finite_table_graph_checks_indexed:
  "finite_table_graph_checks P \<Theta> ((e,u,N,nd)#rows) = (case finite_post_listing (fset N) of
      None \<Rightarrow> nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd \<and>
        finite_table_graph_checks P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns in nd |\<in>| N \<and> finite_indexed_table_graph_check P e u LS nd \<and>
        finite_table_graph_checks P (resolution_table_extend \<Theta> e u
          (the (RBT.lookup (finite_indexed_certificates_in \<Theta> LS) (resolution_node_position nd)))) rows))"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by simp
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  show ?thesis
  proof (cases "nd |\<in>| N")
    case True
    then show ?thesis using Some
      by (simp add: finite_indexed_table_rows_exact[OF listed] finite_indexed_table_graph_check_exact[OF listed True]
        finite_indexed_certificates_in_exact[OF listed True] Let_def)
  next
    case False
    then show ?thesis using Some by (simp add: Let_def)
  qed
qed

lemma finite_table_produced_indexed:
  "finite_table_produced \<Theta> ((e,u,N,nd)#rows) = finite_table_produced (resolution_table_extend \<Theta> e u
    (case finite_post_listing (fset N) of
      None \<Rightarrow> finite_node_proof_in \<Theta> (fcard N) N nd
    | Some ns \<Rightarrow> if nd |\<in>| N then the (RBT.lookup (finite_indexed_certificates_in \<Theta> (finite_indexed_table_rows \<Theta> ns))
        (resolution_node_position nd)) else finite_node_proof_in \<Theta> (fcard N) N nd)) rows"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by simp
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  show ?thesis
  proof (cases "nd |\<in>| N")
    case True
    then show ?thesis using Some
      by (simp add: finite_indexed_table_rows_exact[OF listed] finite_indexed_certificates_in_exact[OF listed True])
  next
    case False
    then show ?thesis using Some by simp
  qed
qed

lemmas finite_table_graph_checks_code [code] = finite_table_graph_checks.simps(1) finite_table_graph_checks_indexed
lemmas finite_table_produced_code [code] = finite_table_produced.simps(1) finite_table_produced_indexed

declare finite_table_checked.simps [code del]

lemma finite_table_checked_indexed:
  "finite_table_checked P \<Theta> ((e,u,N,nd)#rows) = (case finite_post_listing (fset N) of
      None \<Rightarrow> if nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd
        then finite_table_checked P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows else None
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns in
        if nd |\<in>| N \<and> finite_indexed_table_graph_check P e u LS nd
        then finite_table_checked P (resolution_table_extend \<Theta> e u
          (the (RBT.lookup (finite_indexed_certificates_in \<Theta> LS) (resolution_node_position nd)))) rows else None))"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by simp
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  show ?thesis
  proof (cases "nd |\<in>| N")
    case True
    then show ?thesis using Some
      by (simp add: finite_indexed_table_rows_exact[OF listed] finite_indexed_table_graph_check_exact[OF listed True]
        finite_indexed_certificates_in_exact[OF listed True] Let_def)
  next
    case False
    then show ?thesis using Some by (simp add: Let_def)
  qed
qed

lemmas finite_table_checked_code [code] = finite_table_checked.simps(1) finite_table_checked_indexed

section \<open>The verdict at a table read from its graph alone\<close>

text \<open>
  A table's part is checked once and a judgment's part at every judgment (task 495's entry, "The given's calls are decided
  once"): at a table so checked, a verdict reads each entry its graph reads as a closed premise at its call, the entry's
  certificate never checked; the certificate's tree check is made only where the graph reading does not hold. At a valid
  table it is the verdict of @{text finite_state_verdicts_in} (@{text finite_state_graph_verdicts_in_valid}), and so GT1a's
  outcome (@{text finite_outcome_result_in_graph_verdicts}); wherever the table's calls are true, a call it accepts is true
  (@{text finite_state_graph_verdicts_in_true}), as an installation's relocated table asks.
\<close>

definition finite_state_graph_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_state_graph_verdicts_in \<Theta> P d t st = (let N = resolution_nodes st in
    fimage (\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard N) N nd in
      (c,finite_state_graph_check_in \<Theta> P d t N nd \<or> finite_checks_schema_proof P c d t))
    (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"

lemma finite_state_graph_verdicts_in_valid:
  assumes valid: "finite_table_valid P \<Theta>"
  shows "finite_state_graph_verdicts_in \<Theta> P d t st = finite_state_verdicts_in \<Theta> P d t st"
  by (simp add: finite_state_graph_verdicts_in_def finite_state_verdicts_in_def finite_table_entries_accepted_valid[OF valid])

theorem finite_state_graph_verdicts_in_true:
  assumes true: "finite_table_true P \<Theta>"
    and verdict: "(c,True) |\<in>| finite_state_graph_verdicts_in \<Theta> P d t st"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  obtain nd where "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd \<or> finite_checks_schema_proof P c d t"
    using verdict by (auto simp: finite_state_graph_verdicts_in_def Let_def resolution_fset_simps)
  then show ?thesis
  proof
    assume g: "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd"
    show ?thesis by (rule finite_state_graph_check_true_at[OF true g])
  next
    assume "finite_checks_schema_proof P c d t"
    then show ?thesis unfolding finite_checks_schema_proof_exact by (rule schema_proof_sound)
  qed
qed

lemma finite_outcome_result_in_graph_verdicts:
  assumes valid: "finite_table_valid P \<Theta>"
  shows "finite_outcome_result_in \<Theta> P d t R = (let V = listed_fimage_union (finite_state_graph_verdicts_in \<Theta> P d t)
        (resolution_found R);
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (finite_listed_union [resolution_diagnoses R, fimage Resolution_Refused C]))"
proof -
  have "finite_state_graph_verdicts_in \<Theta> P d t = finite_state_verdicts_in \<Theta> P d t"
    by (rule ext) (rule finite_state_graph_verdicts_in_valid[OF valid])
  then show ?thesis unfolding finite_outcome_result_in_listed by simp
qed

lemma finite_state_graph_verdicts_in_indexed [code]:
  "finite_state_graph_verdicts_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table_in \<Theta> N K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,finite_state_graph_code_in \<Theta> P d t N K nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns; CT = finite_indexed_certificates_in \<Theta> LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,finite_indexed_table_graph_check P d t LS nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  let ?N = "resolution_nodes st"
  have "(\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard ?N) ?N nd in
      (c,finite_state_graph_check_in \<Theta> P d t ?N nd \<or> finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (finite_relation_option (finite_certificate_table_in \<Theta> ?N (finite_node_ranked ?N)) nd) in
      (c,finite_state_graph_code_in \<Theta> P d t ?N (finite_node_ranked ?N) nd \<or> finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that by (simp add: finite_certificate_table_in_proof finite_state_graph_code_in_check)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using None by (simp add: finite_state_graph_verdicts_in_def Let_def)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  let ?LS = "map (\<lambda>m. (m,finite_node_links ?N m,finite_table_links \<Theta> ?N m)) ns"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have "(\<lambda>nd. let c = finite_node_proof_in \<Theta> (fcard ?N) ?N nd in
      (c,finite_state_graph_check_in \<Theta> P d t ?N nd \<or> finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (RBT.lookup (finite_indexed_certificates_in \<Theta> ?LS) (resolution_node_position nd)) in
      (c,finite_indexed_table_graph_check P d t ?LS nd \<or> finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
  proof -
    have xN: "x |\<in>| ?N" using that by simp
    note c = finite_indexed_certificates_in_exact[OF listed xN, of \<Theta>]
    note g = finite_indexed_table_graph_check_exact[OF listed xN, of P d t \<Theta>]
    show ?thesis by (simp only: c g)
  qed
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using Some by (simp add: finite_state_graph_verdicts_in_def finite_indexed_table_rows_exact[OF listed] Let_def)
qed

export_code finite_program_resolution finite_committed_resolution finite_program_resolution_in finite_table_graph_checks
  finite_table_produced finite_table_checked finite_state_graph_verdicts_in checking SML

text \<open>
  The graph check at a table reads the table's calls alone (task 876, review 844's follow-up): its assertion nodes are
  the premises whose instance is a call of the table, never an entry's certificate, so two tables of the same calls
  give the same graph, claims and check.
\<close>

lemma finite_table_links_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
  shows "finite_table_links \<Theta> N nd = finite_table_links \<Theta>' N nd"
proof -
  have l: "(resolution_table_lookup \<Theta> q \<noteq> None) = (resolution_table_lookup \<Theta>' q \<noteq> None)" for q
    using calls by (cases q) (simp add: finite_table_calls_def set_eq_iff)
  show ?thesis unfolding finite_table_links_def l by (rule refl)
qed

lemma finite_state_graph_check_in_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
  shows "finite_state_graph_in \<Theta> N nd = finite_state_graph_in \<Theta>' N nd"
    and "finite_state_claims_in \<Theta> N nd = finite_state_claims_in \<Theta>' N nd"
    and "finite_state_graph_check_in \<Theta> P d t N nd = finite_state_graph_check_in \<Theta>' P d t N nd"
  by (simp_all add: finite_state_graph_in_def finite_state_claims_in_def finite_state_graph_check_in_def
    finite_table_discharges_def finite_table_links_calls[OF calls])

section \<open>A found state's truth at a table: the graph check alone\<close>

text \<open>
  At a table the route's consumers take a found state's truth from its graph check alone (DECISIONS.md, the entry "The
  committed side at a table", item (7); task 993): a root whose graph reading holds at the table. It is sound wherever
  the table's calls are true (@{text finite_state_graph_true_in_sound}, from @{text finite_state_graph_check_true_at}),
  it holds at every found state there (@{text finite_state_graph_true_in_found}, from
  @{text finite_state_graph_check_found_true}), and it reads the table by its calls alone
  (@{text finite_state_graph_true_in_calls}), so two tables of the same calls give the same truth; no entry's
  certificate is checked again and no certificate is built. The tree disjunct of @{const finite_state_graph_verdicts_in}
  stays where that form is read; a graph truth is a true verdict there (@{text finite_state_graph_true_in_verdicts}).
\<close>

definition finite_state_graph_true_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_state_graph_true_in \<Theta> P d t st = fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
    (finite_state_graph_check_in \<Theta> P d t (resolution_nodes st))"

theorem finite_state_graph_true_in_sound:
  assumes true: "finite_table_true P \<Theta>" and holds: "finite_state_graph_true_in \<Theta> P d t st"
  shows "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  obtain nd where "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd"
    using holds by (auto simp: finite_state_graph_true_in_def resolution_fset_simps)
  then show ?thesis by (rule finite_state_graph_check_true_at[OF true])
qed

theorem finite_state_graph_true_in_found:
  assumes true: "finite_table_true P \<Theta>" and I: "resolution_invariant_in \<Theta> P d t st"
    and closed: "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and root: "resolution_node_position nd=[]"
  shows "finite_state_graph_true_in \<Theta> P d t st"
  using finite_state_graph_check_found_true[OF true I closed nd root] nd root
  by (auto simp: finite_state_graph_true_in_def resolution_fset_simps)

lemma finite_state_graph_true_in_calls:
  assumes calls: "finite_table_calls \<Theta> = finite_table_calls \<Theta>'"
  shows "finite_state_graph_true_in \<Theta> P d t st = finite_state_graph_true_in \<Theta>' P d t st"
proof -
  have "finite_state_graph_check_in \<Theta> P d t N = finite_state_graph_check_in \<Theta>' P d t N" for N
    by (intro ext) (rule finite_state_graph_check_in_calls(3)[OF calls])
  then show ?thesis by (simp only: finite_state_graph_true_in_def)
qed

lemma finite_state_graph_true_in_verdicts:
  assumes holds: "finite_state_graph_true_in \<Theta> P d t st"
  shows "fBex (finite_state_graph_verdicts_in \<Theta> P d t st) snd"
proof -
  obtain nd where nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd=[]"
    and g: "finite_state_graph_check_in \<Theta> P d t (resolution_nodes st) nd"
    using holds by (auto simp: finite_state_graph_true_in_def resolution_fset_simps)
  let ?c = "finite_node_proof_in \<Theta> (fcard (resolution_nodes st)) (resolution_nodes st) nd"
  have "(?c,True) |\<in>| finite_state_graph_verdicts_in \<Theta> P d t st"
    using nd g by (auto simp: finite_state_graph_verdicts_in_def Let_def resolution_fset_simps intro!: fimageI[of nd])
  then show ?thesis by (metis fBexI snd_conv)
qed

text \<open>
  Its code equation reads the listed nodes' rows once for every root, as the verdicts' does, and builds no certificate.
\<close>

lemma finite_state_graph_true_in_indexed [code]:
  "finite_state_graph_true_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
        (finite_state_graph_check_in \<Theta> P d t (resolution_nodes st))
    | Some ns \<Rightarrow> (let LS = finite_indexed_table_rows \<Theta> ns in
        fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
          (finite_indexed_table_graph_check P d t LS)))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_state_graph_true_in_def)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have eq: "finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns) nd =
      finite_state_graph_check_in \<Theta> P d t ?N nd" if "nd |\<in>| ?N" for nd
    by (simp only: finite_indexed_table_rows_exact[OF listed] finite_indexed_table_graph_check_exact[OF listed that])
  have "fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N) (finite_indexed_table_graph_check P d t
      (finite_indexed_table_rows \<Theta> ns)) = fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N)
      (finite_state_graph_check_in \<Theta> P d t ?N)"
    using eq by (auto simp: resolution_fset_simps)
  then show ?thesis using Some by (simp add: finite_state_graph_true_in_def Let_def)
qed

section \<open>Formation read once per table (C3)\<close>

text \<open>
  A node's admitted instance (@{const finite_admitted_instance_at}) forms its call, its premise calls and its values,
  each term walking every target it holds: at 11 every anchor holds the whole artifact, so a node forms it once an
  anchor (task 972, Finding 4). Formation splits off exactly (@{text finite_admitted_instance_at_formed}): the call and
  the premise calls formed, and the rest, which forms only the values no call holds
  (@{text finite_admitted_instance_formed_at}); a value of a variable of the conclusion or of a premise is a subterm of
  a formed call (@{text finite_pattern_instance_values_formed}). A call a sharing state holds is formed when every leaf
  of the state's table is (@{text finite_reference_formed}), which is checked once a table, each distinct leaf once
  (@{text finite_share_leaves_formed}); where it holds the check reads no call's formation again
  (@{text finite_formed_reached_graph_check_exact}), and where it does not the check is C's as it stands.
\<close>

definition finite_pattern_matched :: "'a finite_term_pattern \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_pattern_matched p t \<longleftrightarrow> finite_relation_functional (finite_matching_bindings p t) \<and>
    fimage fst (finite_matching_bindings p t) = finite_pattern_variables p \<and>
    finite_pattern_instance (finite_matching_bindings p t) p t"

lemma finite_matching_values_formed:
  "(a,x) |\<in>| finite_matching_bindings p t \<Longrightarrow> finite_term_formed t \<Longrightarrow> finite_term_formed x"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_pattern_accepts_matches:
  "finite_pattern_accepts p t \<longleftrightarrow> finite_term_formed t \<and> finite_pattern_matched p t"
  using finite_matching_values_formed[of _ _ p t]
  by (auto simp: finite_pattern_accepts_def finite_pattern_matched_def finite_term_bindings_formed_def)

lemma finite_pattern_instance_values_formed:
  assumes "finite_pattern_instance V p t" "finite_term_formed t" "finite_relation_functional V"
    "a |\<in>| finite_pattern_variables p" "(a,x) |\<in>| V"
  shows "finite_term_formed x"
  using assms
proof (induction p arbitrary: t)
  case (Finite_Variable b)
  then have "(a,t) |\<in>| V" by simp
  then have "x = t" by (rule finite_relation_functional_at[OF Finite_Variable.prems(3) Finite_Variable.prems(5)])
  then show ?case using Finite_Variable.prems(2) by simp
next
  case (Finite_Pattern_Pair p q)
  obtain y z where t: "t = Finite_Pair y z" using Finite_Pattern_Pair.prems(1) by (cases t) simp_all
  have i: "finite_pattern_instance V p y" "finite_pattern_instance V q z" using Finite_Pattern_Pair.prems(1) t by simp_all
  have f: "finite_term_formed y" "finite_term_formed z" using Finite_Pattern_Pair.prems(2) t by simp_all
  show ?case using Finite_Pattern_Pair.prems(4) Finite_Pattern_Pair.IH(1)[OF i(1) f(1) Finite_Pattern_Pair.prems(3) _ Finite_Pattern_Pair.prems(5)]
    Finite_Pattern_Pair.IH(2)[OF i(2) f(2) Finite_Pattern_Pair.prems(3) _ Finite_Pattern_Pair.prems(5)] by auto
qed simp_all

definition finite_schema_call_variables :: "('a,'s,'d) finite_factor_schema \<Rightarrow> 'a fset" where
  "finite_schema_call_variables S = finite_pattern_variables (finite_schema_conclusion S) |\<union>|
    ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_variables p) (finite_schema_premises S))"

lemma finite_call_values_formed:
  assumes t: "finite_term_formed t" and Q: "fBall Q (\<lambda>(s,e,x). finite_term_formed x)"
    and F: "finite_relation_functional V" and c: "finite_pattern_instance V (finite_schema_conclusion S) t"
    and p: "finite_schema_premise_instance S V Q"
    and a: "a |\<in>| finite_schema_call_variables S" and x: "(a,x) |\<in>| V"
  shows "finite_term_formed x"
proof -
  consider "a |\<in>| finite_pattern_variables (finite_schema_conclusion S)"
    | s e r where "(s,e,r) |\<in>| finite_schema_premises S" "a |\<in>| finite_pattern_variables r"
    using a by (auto simp: finite_schema_call_variables_def ffUnion_fimage_iff)
  then show ?thesis
  proof cases
    case 1
    show ?thesis by (rule finite_pattern_instance_values_formed[OF c t F 1 x])
  next
    case (2 s e r)
    obtain u where u: "(s,e,u) |\<in>| Q" "finite_pattern_instance V r u"
      using p 2(1) by (auto simp: finite_schema_premise_instance_def)
    have "finite_term_formed u" using Q u(1) by auto
    then show ?thesis by (rule finite_pattern_instance_values_formed[OF u(2) _ F 2(2) x])
  qed
qed

definition finite_admitted_instance_formed_at ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_admitted_instance_formed_at P d c V t Q \<longleftrightarrow>
    fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_pattern_matched p t) \<and>
    fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
      finite_relation_functional V \<and> fimage fst V = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q \<and>
      finite_schema_material_satisfied S V) \<and>
    fBall Q (\<lambda>(s,e,x). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_pattern_matched p x))"

lemma finite_admitted_instance_at_formed:
  "finite_admitted_instance_at P d c V t Q \<longleftrightarrow> finite_term_formed t \<and> fBall Q (\<lambda>(s,e,x). finite_term_formed x) \<and>
    finite_admitted_instance_formed_at P d c V t Q"
proof -
  have I: "finite_schema_instance S V t Q \<longleftrightarrow> finite_schema_formed S \<and> finite_relation_functional V \<and>
      fimage fst V = finite_schema_variables S \<and> fBall V (\<lambda>(a,x). finite_term_formed x) \<and>
      finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q" for S
    by (auto simp: finite_schema_instance_def finite_term_bindings_formed_def)
  have V: "fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<longleftrightarrow>
      fBall V (\<lambda>(a,x). finite_term_formed x)"
    if "finite_term_formed t" "fBall Q (\<lambda>(s,e,x). finite_term_formed x)" "finite_relation_functional V"
      "finite_pattern_instance V (finite_schema_conclusion S) t" "finite_schema_premise_instance S V Q" for S
    using finite_call_values_formed[OF that] by blast
  have Qf: "fBall Q (\<lambda>(s,e,x). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_pattern_accepts p x)) \<longleftrightarrow>
      fBall Q (\<lambda>(s,e,x). finite_term_formed x) \<and>
      fBall Q (\<lambda>(s,e,x). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_pattern_matched p x))"
    by (fastforce simp: finite_pattern_accepts_matches)
  have Tf: "fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_pattern_accepts p t) \<longleftrightarrow>
      finite_term_formed t \<and> fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_pattern_matched p t)"
    by (fastforce simp: finite_pattern_accepts_matches)
  have A2: "fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_instance S V t Q \<and>
        finite_schema_material_satisfied S V) \<longleftrightarrow>
      fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
        finite_relation_functional V \<and> fimage fst V = finite_schema_variables S \<and>
        fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
        finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q \<and>
        finite_schema_material_satisfied S V)"
    if t: "finite_term_formed t" and q: "fBall Q (\<lambda>(s,e,x). finite_term_formed x)"
  proof (rule fBex_cong[OF refl], goal_cases)
    case (1 x)
    obtain e k S where x: "x = ((e,k),S)" by (cases x) auto
    show ?case
    proof (cases "finite_relation_functional V \<and> finite_pattern_instance V (finite_schema_conclusion S) t \<and>
        finite_schema_premise_instance S V Q")
      case True
      then have f: "finite_relation_functional V" and i: "finite_pattern_instance V (finite_schema_conclusion S) t"
        and p: "finite_schema_premise_instance S V Q" by simp_all
      have eq: "fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<longleftrightarrow>
          fBall V (\<lambda>(a,x). finite_term_formed x)" by (rule V[OF t q f i p])
      show ?thesis unfolding x prod.case I eq by (rule iffI) (elim conjE, intro conjI, assumption+)+
    next
      case False
      then show ?thesis unfolding x prod.case I by auto
    qed
  qed
  show ?thesis
  proof (cases "finite_term_formed t \<and> fBall Q (\<lambda>(s,e,x). finite_term_formed x)")
    case True
    then have a2: "fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_instance S V t Q \<and>
        finite_schema_material_satisfied S V) \<longleftrightarrow>
      fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
        finite_relation_functional V \<and> fimage fst V = finite_schema_variables S \<and>
        fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
        finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q \<and>
        finite_schema_material_satisfied S V)" by (intro A2) simp_all
    show ?thesis unfolding finite_admitted_instance_at_def finite_admitted_instance_formed_at_def Tf Qf a2
      using True by blast
  next
    case False
    then show ?thesis unfolding finite_admitted_instance_at_def finite_admitted_instance_formed_at_def Tf Qf by auto
  qed
qed

text \<open>
  A reached check reads, at each reached row, the functionality of its links and a test of the row, stated once
  (@{text finite_rows_reached_check}); two tests that agree on the rows give the same check
  (@{text finite_rows_reached_cong}). C's check is its instance at the admitted instance's test
  (@{text finite_indexed_reached_by}), C3's at the formed test, which forms each table link's call once, in its call's
  formation (@{text finite_formed_row_check}), and the check over references at a test that reads references
  (@{text finite_reference_reached_graph_check}).
\<close>

definition finite_rows_reached_check ::
    "(('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_rows_reached_check \<chi> P d t LS R nd = (
    resolution_node_site nd=d \<and> finite_residual_term (resolution_node_call nd)=t \<and> finite_system_formed P \<and>
    list_all (\<lambda>(m,L,TL). RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional (L |\<union>| TL) \<and>
      \<chi> (m,L,TL)) LS)"

lemma finite_rows_reached_cong:
  assumes same: "\<And>row. row \<in> set LS \<Longrightarrow> \<chi> row = \<chi>' row"
  shows "finite_rows_reached_check \<chi> P d t LS R nd = finite_rows_reached_check \<chi>' P d t LS R nd"
proof -
  have "list_all (\<lambda>row. case row of (m,L,TL) \<Rightarrow> RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow>
      finite_relation_functional (L |\<union>| TL) \<and> \<chi> (m,L,TL)) LS =
    list_all (\<lambda>row. case row of (m,L,TL) \<Rightarrow> RBT.lookup R (resolution_node_position m) \<noteq> None \<longrightarrow>
      finite_relation_functional (L |\<union>| TL) \<and> \<chi>' (m,L,TL)) LS"
  proof (rule list.pred_cong[OF refl], goal_cases)
    case (1 row)
    obtain m L TL where rr: "row = (m,L,TL)" by (cases row) auto
    show ?case using same[OF 1] rr by simp
  qed
  then show ?thesis by (simp only: finite_rows_reached_check_def)
qed

definition finite_indexed_row_check ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow> bool" where
  "finite_indexed_row_check P row = (case row of (m,L,TL) \<Rightarrow>
    finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
      (finite_residual_term (resolution_node_call m))
      (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)) \<and>
    fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))))"

definition finite_formed_row_check ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow> bool" where
  "finite_formed_row_check P row = (case row of (m,L,TL) \<Rightarrow>
    finite_admitted_instance_formed_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
      (finite_residual_term (resolution_node_call m))
      (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)) \<and>
    fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a))))"

lemma finite_indexed_reached_by:
  "finite_indexed_reached_graph_check P d t LS R nd = finite_rows_reached_check (finite_indexed_row_check P) P d t LS R nd"
  by (simp add: finite_indexed_reached_graph_check_def finite_rows_reached_check_def finite_indexed_row_check_def)

definition finite_formed_reached_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_formed_reached_graph_check P d t LS R nd = finite_rows_reached_check (finite_formed_row_check P) P d t LS R nd"

lemma finite_schema_call_formed_term: "finite_schema_call_formed P d x \<Longrightarrow> finite_term_formed x"
  by (auto simp: finite_schema_call_formed_def finite_pattern_accepts_matches)

lemma finite_formed_reached_graph_check_exact:
  assumes rows: "\<And>m L TL. (m,L,TL) \<in> set LS \<Longrightarrow> finite_term_formed (finite_residual_term (resolution_node_call m)) \<and>
      fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
  shows "finite_formed_reached_graph_check P d t LS R nd = finite_indexed_reached_graph_check P d t LS R nd"
  unfolding finite_formed_reached_graph_check_def finite_indexed_reached_by
proof (rule finite_rows_reached_cong)
  fix row assume r: "row \<in> set LS"
  obtain m L TL where rr: "row = (m,L,TL)" by (cases row) auto
  have fm: "finite_term_formed (finite_residual_term (resolution_node_call m))"
    and fl: "fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
    using rows r rr by blast+
  let ?Q = "fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) (L |\<union>| TL)"
  let ?C = "fBall TL (\<lambda>(s,a). finite_schema_call_formed P (resolution_node_site a) (finite_residual_term (resolution_node_call a)))"
  have qf: "fBall ?Q (\<lambda>(s,e,x). finite_term_formed x)" if c: ?C
  proof (rule fBallI)
    fix z assume z: "z |\<in>| ?Q"
    then obtain s m' where sm: "(s,m') |\<in>| L |\<union>| TL"
      and zz: "z = (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))" by force
    have "finite_term_formed (finite_residual_term (resolution_node_call m'))"
    proof (cases "(s,m') |\<in>| L")
      case True
      then show ?thesis using fbspec[OF fl True] by simp
    next
      case False
      then have "(s,m') |\<in>| TL" using sm by simp
      then have "finite_schema_call_formed P (resolution_node_site m') (finite_residual_term (resolution_node_call m'))"
        using fbspec[OF c] by force
      then show ?thesis by (rule finite_schema_call_formed_term)
    qed
    then show "case z of (s,e,x) \<Rightarrow> finite_term_formed x" using zz by simp
  qed
  show "finite_formed_row_check P row = finite_indexed_row_check P row"
    unfolding rr finite_formed_row_check_def finite_indexed_row_check_def prod.case finite_admitted_instance_at_formed
    using fm qf by blast
qed

definition finite_share_leaves_formed :: "share_state \<Rightarrow> bool" where
  "finite_share_leaves_formed q = (case q of (M,n,T) \<Rightarrow> list_all (\<lambda>i. case RBT.lookup T i of
      Some (Leaf_Shape l) \<Rightarrow> finite_term_formed (leaf_term l) | _ \<Rightarrow> True) [0..<n])"

lemma finite_reference_formed:
  assumes leaves: "\<And>i l. value_reference_read T i = Some (Leaf_Shape l) \<Longrightarrow> finite_term_formed (leaf_term l)"
    and r: "reference_term T i = Some u"
  shows "finite_term_formed u"
  using r
proof (induction i arbitrary: u rule: less_induct)
  case (less i)
  from less.prems show ?case
  proof (cases rule: reference_term_cases)
    case (leaf l)
    then show ?thesis using leaves by simp
  next
    case (pair j k x y)
    then show ?thesis using less.IH by simp
  qed
qed

lemma finite_share_leaves_formed_reference:
  assumes rep: "keyed_state_represents q T" and leaves: "finite_share_leaves_formed q" and r: "reference_term T i = Some u"
  shows "finite_term_formed u"
proof (rule finite_reference_formed[OF _ r])
  fix j l assume read: "value_reference_read T j = Some (Leaf_Shape l)"
  obtain M n P where q: "q = (M,n,P)" by (cases q)
  have n: "n = length T" and P: "RBT.lookup P j = value_reference_read T j" using rep q by (simp_all add: keyed_state_represents_def keyed_table_state_def)
  have j: "j \<in> set [0..<n]" using read n by (simp add: read_some)
  have all: "\<forall>i\<in>set [0..<n]. (case RBT.lookup P i of Some (Leaf_Shape l) \<Rightarrow> finite_term_formed (leaf_term l) | _ \<Rightarrow> True)"
    using leaves q by (simp only: finite_share_leaves_formed_def list_all_iff prod.case)
  have c: "case RBT.lookup P j of Some (Leaf_Shape l) \<Rightarrow> finite_term_formed (leaf_term l) | _ \<Rightarrow> True"
    by (rule bspec[OF all j])
  have "RBT.lookup P j = Some (Leaf_Shape l)" by (simp only: P read)
  then show "finite_term_formed (leaf_term l)" using c by (simp only: option.case shape.case)
qed

section \<open>The check over a represented found state (C2)\<close>

text \<open>
  A representation of a found state gives the check its rows: a reference of a sharing state for each node whose call the
  representation holds there (@{const finite_read_rows}), so the rows are read, not re-shared. A representation reads the
  calls exactly when the sharing state represents a formed table that holds each node's call at the reference read for
  it (@{text finite_reads_calls}); a representation whose projection is the found state, the shared and the deferred
  search's, is to establish this of its found states, and the equality lemmas below are then its, with nothing proved
  again: the rows equal the re-shared rows (@{text finite_read_table_rows_indexed}), and the verdicts, the graph
  verdicts and the graph truth read over them equal C's at the projected state (@{text finite_read_verdicts_in_exact},
  @{text finite_read_graph_verdicts_in_exact}, @{text finite_read_graph_true_in_exact}).
\<close>

definition finite_reads_calls ::
    "('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node fset \<Rightarrow> bool" where
  "finite_reads_calls L q N \<longleftrightarrow> (\<exists>T. keyed_state_represents q T \<and> table_formed T \<and>
    (\<forall>m i. m |\<in>| N \<longrightarrow> L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))))"

lemma finite_reads_calls_none: "finite_reads_calls (\<lambda>_. None) empty_share_state N"
  unfolding finite_reads_calls_def using keyed_state_represents_empty table_formed_empty by blast

definition finite_read_table_rows ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_read_table_rows \<Theta> L q ns = (case finite_read_rows L ns q of (rows,q0) \<Rightarrow>
    let PI = finite_position_index rows; G = finite_group_index rows in
    map (\<lambda>m. (m,finite_indexed_links PI G q0 m,finite_indexed_table_links \<Theta> PI G q0 m)) ns)"

lemma finite_indexed_table_rows_read:
  "finite_indexed_table_rows \<Theta> ns = finite_read_table_rows \<Theta> (\<lambda>_. None) empty_share_state ns"
  by (simp only: finite_indexed_table_rows_def finite_read_table_rows_def finite_share_rows_read)

lemma finite_read_table_rows_exact:
  assumes listed: "finite_post_listed (fset N) ns" and reads: "finite_reads_calls L q N"
  shows "finite_read_table_rows \<Theta> L q ns = map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns"
proof -
  obtain T where rep: "keyed_state_represents q T" and f: "table_formed T"
    and held: "\<And>m i. m |\<in>| N \<Longrightarrow> L (resolution_node_position m) = Some i \<Longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using reads unfolding finite_reads_calls_def by blast
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  have L: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using held setns by auto
  obtain rows q0 where run: "finite_read_rows L ns q = (rows,q0)" by (cases "finite_read_rows L ns q")
  note index = finite_read_index_exact[OF listed rep f L run]
  have links: "finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m = finite_node_links N m" for m
    by (simp add: finite_indexed_links_def finite_node_links_def index)
  have table: "finite_indexed_table_links \<Theta> (finite_position_index rows) (finite_group_index rows) q0 m =
      finite_table_links \<Theta> N m" for m
    by (simp only: finite_indexed_table_links_def finite_table_links_def index Let_def finite_guarded_image)
  show ?thesis using run links table by (simp add: finite_read_table_rows_def Let_def)
qed

lemma finite_read_table_rows_indexed:
  assumes listed: "finite_post_listed (fset N) ns" and reads: "finite_reads_calls L q N"
  shows "finite_read_table_rows \<Theta> L q ns = finite_indexed_table_rows \<Theta> ns"
  by (simp only: finite_read_table_rows_exact[OF listed reads] finite_indexed_table_rows_exact[OF listed])

text \<open>
  The rows read with the formation of the table they were read in (C3): its leaves formed, every listed node's call is
  formed (@{text finite_read_check_rows_formed}), and the check over the rows reads no call's formation
  (@{text finite_formed_table_exact}).
\<close>

definition finite_read_check_rows ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow>
      bool \<times> (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_read_check_rows \<Theta> L q ns = (case finite_read_rows L ns q of (rows,q0) \<Rightarrow>
    (finite_share_leaves_formed q0, let PI = finite_position_index rows; G = finite_group_index rows in
      map (\<lambda>m. (m,finite_indexed_links PI G q0 m,finite_indexed_table_links \<Theta> PI G q0 m)) ns))"

lemma finite_read_check_rows_rows: "snd (finite_read_check_rows \<Theta> L q ns) = finite_read_table_rows \<Theta> L q ns"
  by (simp add: finite_read_check_rows_def finite_read_table_rows_def split: prod.split)

lemma finite_read_check_rows_formed:
  assumes listed: "finite_post_listed (fset N) ns" and reads: "finite_reads_calls L q N"
    and fl: "fst (finite_read_check_rows \<Theta> L q ns)" and m: "m |\<in>| N"
  shows "finite_term_formed (finite_residual_term (resolution_node_call m))"
proof -
  obtain T where rep: "keyed_state_represents q T" and f: "table_formed T"
    and held: "\<And>m i. m |\<in>| N \<Longrightarrow> L (resolution_node_position m) = Some i \<Longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using reads unfolding finite_reads_calls_def by blast
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  have L: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using held setns by auto
  obtain rows q0 where run: "finite_read_rows L ns q = (rows,q0)" by (cases "finite_read_rows L ns q")
  obtain T' where rep': "keyed_state_represents q0 T'" and fsts: "map fst rows = ns"
      and rw: "\<forall>row\<in>set rows. fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
        reference_term T' (snd (snd row)) = Some (fst (snd row))"
    using finite_read_rows_exact[OF rep f L] run by auto
  have leaves: "finite_share_leaves_formed q0" using fl run by (simp add: finite_read_check_rows_def)
  have "m \<in> set (map fst rows)" using m setns fsts by simp
  then obtain row where row: "row \<in> set rows" "fst row = m" by auto
  then have "reference_term T' (snd (snd row)) = Some (finite_residual_term (resolution_node_call m))" using rw by auto
  then show ?thesis by (rule finite_share_leaves_formed_reference[OF rep' leaves])
qed

definition finite_formed_table_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_formed_table_graph_check P d t LS nd =
    finite_formed_reached_graph_check P d t LS (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd"

definition finite_formed_table_accepts ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_formed_table_accepts P \<Theta> d t LS nd = (let R = finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd in
    finite_formed_reached_graph_check P d t LS R nd \<and> finite_indexed_reached_entries P \<Theta> LS R)"

lemma finite_formed_table_exact:
  assumes listed: "finite_post_listed (fset N) ns"
    and formed: "\<And>m. m |\<in>| N \<Longrightarrow> finite_term_formed (finite_residual_term (resolution_node_call m))"
  shows "finite_formed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns) =
      finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)"
    and "finite_formed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns) =
      finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)"
proof -
  have rows: "finite_term_formed (finite_residual_term (resolution_node_call m)) \<and>
      fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
    if r: "(m,L,TL) \<in> set (finite_indexed_table_rows \<Theta> ns)" for m L TL
  proof -
    from r have m: "m \<in> set ns" and L: "L = finite_node_links N m"
      unfolding finite_indexed_table_rows_exact[OF listed] by auto
    have mN: "m |\<in>| N" using m listed by (simp add: finite_post_listed_def)
    have "fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
      using L formed finite_node_links_reach(1) by fastforce
    then show ?thesis using formed[OF mN] by blast
  qed
  note e = finite_formed_reached_graph_check_exact[OF rows]
  show "finite_formed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns) =
      finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)"
    by (rule ext) (simp only: finite_formed_table_graph_check_def finite_indexed_table_graph_check_def e)
  show "finite_formed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns) =
      finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)"
    by (rule ext) (simp only: finite_formed_table_accepts_def finite_indexed_table_accepts_def e)
qed

lemma finite_read_check_rows_indexed:
  assumes listed: "finite_post_listed (fset N) ns" and reads: "finite_reads_calls L q N"
  obtains fl where "finite_read_check_rows \<Theta> L q ns = (fl,finite_indexed_table_rows \<Theta> ns)"
    "(if fl then finite_formed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)"
    "(if fl then finite_formed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)"
proof -
  obtain fl LS where r: "finite_read_check_rows \<Theta> L q ns = (fl,LS)" by (cases "finite_read_check_rows \<Theta> L q ns")
  have LS: "LS = finite_indexed_table_rows \<Theta> ns"
    using finite_read_check_rows_rows[of \<Theta> L q ns] r finite_read_table_rows_indexed[OF listed reads] by simp
  have formed: "fl \<Longrightarrow> m |\<in>| N \<Longrightarrow> finite_term_formed (finite_residual_term (resolution_node_call m))" for m
    using finite_read_check_rows_formed[OF listed reads, of \<Theta> m] r by simp
  show ?thesis
  proof (rule that[of fl])
    show "finite_read_check_rows \<Theta> L q ns = (fl,finite_indexed_table_rows \<Theta> ns)" using r LS by simp
    show "(if fl then finite_formed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_graph_check P d t (finite_indexed_table_rows \<Theta> ns)"
      using finite_formed_table_exact(1)[OF listed formed] by (cases fl) simp_all
    show "(if fl then finite_formed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_accepts P \<Theta> d t (finite_indexed_table_rows \<Theta> ns)"
      using finite_formed_table_exact(2)[OF listed formed] by (cases fl) simp_all
  qed
qed

section \<open>The per-node check over references\<close>

text \<open>
  A node of a found state holds its call, its values and its premises' calls; at 11 each holds the artifact's anchors,
  each the whole artifact, so a check that shares a premise instance again or compares two of these terms walks them
  (task 993's measurement). Over a formed table that holds them a term is its reference: two references are equal
  exactly when their terms are (@{text reference_term_injective}), and a pair is read one level through its shape. With
  the node's bindings given as references (@{text finite_bindings_read}), a pattern's instance is a reference: the
  bindings' references substituted at the pattern's variables, and each leaf and pair the substitution makes found in
  the table's keyed index without extending the table (@{text finite_instance_reference}), an instance the table does
  not hold being no node's call (@{text finite_instance_reference_exact}). An interface matches a call by reading the
  call's shapes from its reference (@{text finite_reference_bindings}, @{text finite_reference_matched_exact}). C3's
  admitted instance (@{const finite_admitted_instance_formed_at}) is then read over references
  (@{text finite_admitted_instance_reference_at}), equal to it wherever the references read the terms
  (@{text finite_admitted_instance_reference_exact}).
\<close>

lemma finite_relation_functional_value_image:
  assumes inj: "\<And>u v. u |\<in>| fimage snd R \<Longrightarrow> v |\<in>| fimage snd R \<Longrightarrow> g u = g v \<Longrightarrow> u = v"
  shows "finite_relation_functional (fimage (\<lambda>(s,v). (s,g v)) R) \<longleftrightarrow> finite_relation_functional R"
proof
  assume f: "finite_relation_functional (fimage (\<lambda>(s,v). (s,g v)) R)"
  show "finite_relation_functional R"
  proof (rule finite_relation_functional_intro)
    fix a u v assume u: "(a,u) |\<in>| R" and v: "(a,v) |\<in>| R"
    have "(a,g u) |\<in>| fimage (\<lambda>(s,v). (s,g v)) R" "(a,g v) |\<in>| fimage (\<lambda>(s,v). (s,g v)) R"
      using fimageI[OF u, of "\<lambda>(s,v). (s,g v)"] fimageI[OF v, of "\<lambda>(s,v). (s,g v)"] by simp_all
    then have "g u = g v" by (rule finite_relation_functional_at[OF f])
    moreover have "u |\<in>| fimage snd R" "v |\<in>| fimage snd R"
      using fimageI[OF u, of snd] fimageI[OF v, of snd] by simp_all
    ultimately show "u = v" using inj by blast
  qed
next
  assume f: "finite_relation_functional R"
  show "finite_relation_functional (fimage (\<lambda>(s,v). (s,g v)) R)"
  proof (rule finite_relation_functional_intro)
    fix a u v assume u: "(a,u) |\<in>| fimage (\<lambda>(s,v). (s,g v)) R" and v: "(a,v) |\<in>| fimage (\<lambda>(s,v). (s,g v)) R"
    obtain u' where u': "(a,u') |\<in>| R" "u = g u'" using u by force
    obtain v' where v': "(a,v') |\<in>| R" "v = g v'" using v by force
    show "u = v" using finite_relation_functional_at[OF f u'(1) v'(1)] u'(2) v'(2) by simp
  qed
qed

subsection \<open>A shape the table holds, found in its keyed index\<close>

definition finite_shape_found :: "share_state \<Rightarrow> shape \<Rightarrow> nat option" where
  "finite_shape_found q s = RBT.lookup (fst q) (shape_key s)"

definition finite_shape_at :: "share_state \<Rightarrow> nat \<Rightarrow> shape option" where
  "finite_shape_at q i = RBT.lookup (snd (snd q)) i"

lemma finite_shape_found_read:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
  shows "finite_shape_found q s = Some r \<longleftrightarrow> value_reference_read T r = Some s"
proof -
  obtain M n P where qq: "q = (M,n,P)" by (cases q) auto
  have found: "finite_shape_found q s = value_reference_index s T"
    using rep by (simp add: qq finite_shape_found_def keyed_state_represents_def keyed_table_state_def)
  have d: "distinct T" using tf by (simp add: table_formed_def)
  show ?thesis
  proof
    assume "finite_shape_found q s = Some r"
    then have "r < length T \<and> T!r = s" using found value_reference_index_read by metis
    then show "value_reference_read T r = Some s" by (simp add: read_some)
  next
    assume "value_reference_read T r = Some s"
    then show "finite_shape_found q s = Some r" using found value_reference_index_distinct_read[OF d] by simp
  qed
qed

lemma finite_shape_at_read:
  assumes rep: "keyed_state_represents q T"
  shows "finite_shape_at q i = value_reference_read T i"
proof -
  obtain M n P where qq: "q = (M,n,P)" by (cases q) auto
  show ?thesis using rep by (simp add: qq finite_shape_at_def keyed_state_represents_def keyed_table_state_def)
qed

lemma finite_leaf_found:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T" and i: "reference_term T i = Some y"
  shows "finite_shape_found q (Leaf_Shape l) = Some i \<longleftrightarrow> y = leaf_term l"
proof -
  have "value_reference_read T i = Some (Leaf_Shape l) \<longleftrightarrow> y = leaf_term l"
  proof
    assume "value_reference_read T i = Some (Leaf_Shape l)"
    then have "reference_term T i = Some (leaf_term l)" by (rule reference_factor_leaf)
    then show "y = leaf_term l" using i by simp
  next
    assume "y = leaf_term l"
    then have "reference_term T i = Some (leaf_term l)" using i by simp
    then show "value_reference_read T i = Some (Leaf_Shape l)" by (rule reference_factor_leaf_read)
  qed
  then show ?thesis by (simp only: finite_shape_found_read[OF rep tf])
qed

subsection \<open>Bindings read as references\<close>

text \<open>
  A node's bindings are read by a list of references when each variable the list keys has a reference the table
  decodes, and the node binds exactly the decoded terms at exactly the keyed variables. The bindings are then
  functional, and their domain is the list's keys.
\<close>

definition finite_bindings_read :: "shape list \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> bool" where
  "finite_bindings_read T B V \<longleftrightarrow> (\<forall>a r. map_of B a = Some r \<longrightarrow> (\<exists>u. reference_term T r = Some u)) \<and>
    (\<forall>a x. (a,x) |\<in>| V \<longleftrightarrow> (\<exists>r. map_of B a = Some r \<and> reference_term T r = Some x))"

lemma finite_bindings_read_member:
  "finite_bindings_read T B V \<Longrightarrow> (a,x) |\<in>| V \<longleftrightarrow> (\<exists>r. map_of B a = Some r \<and> reference_term T r = Some x)"
  by (simp add: finite_bindings_read_def)

lemma finite_bindings_read_functional:
  assumes read: "finite_bindings_read T B V"
  shows "finite_relation_functional V"
proof (rule finite_relation_functional_intro)
  fix a u w assume u: "(a,u) |\<in>| V" and w: "(a,w) |\<in>| V"
  obtain r where r: "map_of B a = Some r" "reference_term T r = Some u" using finite_bindings_read_member[OF read] u by blast
  obtain r' where r': "map_of B a = Some r'" "reference_term T r' = Some w" using finite_bindings_read_member[OF read] w by blast
  show "u = w" using r r' by simp
qed

lemma finite_bindings_read_domain:
  assumes read: "finite_bindings_read T B V"
  shows "fimage fst V = fset_of_list (map fst B)"
proof (rule fset_eqI)
  fix a
  have "a |\<in>| fimage fst V \<longleftrightarrow> (\<exists>x. (a,x) |\<in>| V)" by force
  also have "\<dots> \<longleftrightarrow> map_of B a \<noteq> None"
  proof
    assume "\<exists>x. (a,x) |\<in>| V"
    then show "map_of B a \<noteq> None" using finite_bindings_read_member[OF read] by blast
  next
    assume "map_of B a \<noteq> None"
    then obtain r where r: "map_of B a = Some r" by blast
    then obtain x where "reference_term T r = Some x" using read unfolding finite_bindings_read_def by blast
    then show "\<exists>x. (a,x) |\<in>| V" using finite_bindings_read_member[OF read] r by blast
  qed
  also have "\<dots> \<longleftrightarrow> a |\<in>| fset_of_list (map fst B)"
    by (simp add: map_of_eq_None_iff fset_of_list_elem fset_of_list.rep_eq)
  finally show "a |\<in>| fimage fst V \<longleftrightarrow> a |\<in>| fset_of_list (map fst B)" .
qed

lemma finite_bindings_read_extends:
  assumes read: "finite_bindings_read T B V" and ext: "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
  shows "finite_bindings_read T' B V"
proof -
  have held: "\<exists>u. reference_term T r = Some u" if "map_of B a = Some r" for a r
    using read that unfolding finite_bindings_read_def by blast
  have same: "reference_term T' r = Some x \<longleftrightarrow> reference_term T r = Some x" if "map_of B a = Some r" for a r x
    using held[OF that] ext by force
  have "(a,x) |\<in>| V \<longleftrightarrow> (\<exists>r. map_of B a = Some r \<and> reference_term T' r = Some x)" for a x
    using finite_bindings_read_member[OF read, of a x] same by blast
  moreover have "\<exists>u. reference_term T' r = Some u" if "map_of B a = Some r" for a r
    using held[OF that] ext by blast
  ultimately show ?thesis unfolding finite_bindings_read_def by blast
qed

subsection \<open>A pattern's instance by its reference\<close>

text \<open>
  The instance of a pattern under the bindings' references, built bottom-up as the keyed substitution builds it
  (@{text keyed_share_node}), each leaf and pair it makes looked up in the table's keyed index and never added: where
  the table holds the instance its reference is returned, and where it does not, nothing, so an instance is compared
  with a node's call by comparing two numbers. A literal of the pattern is an instance only where it is formed, as
  @{const finite_pattern_instances} has it.
\<close>

fun finite_instance_reference :: "share_state \<Rightarrow> ('a \<Rightarrow> nat option) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> nat option" where
  "finite_instance_reference q \<sigma> (Finite_Variable a) = \<sigma> a"
| "finite_instance_reference q \<sigma> (Finite_Pattern_Target x) =
    (if finite_target_formed x then finite_shape_found q (Leaf_Shape (Target_Leaf x)) else None)"
| "finite_instance_reference q \<sigma> (Finite_Pattern_Payload v) =
    (if octets_formed v then finite_shape_found q (Leaf_Shape (Payload_Leaf v)) else None)"
| "finite_instance_reference q \<sigma> (Finite_Pattern_Pair p r) =
    (case finite_instance_reference q \<sigma> p of None \<Rightarrow> None | Some i \<Rightarrow>
      (case finite_instance_reference q \<sigma> r of None \<Rightarrow> None | Some j \<Rightarrow> finite_shape_found q (Pair_Shape i j)))"

lemma finite_instance_reference_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
    and \<sigma>: "\<And>a x. (a,x) |\<in>| V \<longleftrightarrow> (\<exists>r. \<sigma> a = Some r \<and> reference_term T r = Some x)"
  shows "reference_term T i = Some y \<Longrightarrow>
    finite_instance_reference q \<sigma> p = Some i \<longleftrightarrow> y |\<in>| finite_pattern_instances V p"
proof (induction p arbitrary: i y)
  case (Finite_Variable a)
  have "(a,y) |\<in>| V \<longleftrightarrow> \<sigma> a = Some i"
  proof
    assume "(a,y) |\<in>| V"
    then obtain r where r: "\<sigma> a = Some r" "reference_term T r = Some y" using \<sigma> by blast
    have "r = i" by (rule reference_term_injective[OF tf r(2) Finite_Variable.prems])
    then show "\<sigma> a = Some i" using r by simp
  next
    assume "\<sigma> a = Some i"
    then show "(a,y) |\<in>| V" using \<sigma> Finite_Variable.prems by blast
  qed
  then show ?case by (force simp: fimage_iff)
next
  case (Finite_Pattern_Target x)
  show ?case using finite_leaf_found[OF rep tf Finite_Pattern_Target.prems, of "Target_Leaf x"] by simp
next
  case (Finite_Pattern_Payload v)
  show ?case using finite_leaf_found[OF rep tf Finite_Pattern_Payload.prems, of "Payload_Leaf v"] by simp
next
  case (Finite_Pattern_Pair p r)
  have mem: "y |\<in>| finite_pattern_instances V (Finite_Pattern_Pair p r) \<longleftrightarrow>
      (\<exists>x z. y = Finite_Pair x z \<and> x |\<in>| finite_pattern_instances V p \<and> z |\<in>| finite_pattern_instances V r)"
    by (auto simp: ffUnion_fimage_iff)
  from Finite_Pattern_Pair.prems show ?case
  proof (cases rule: reference_term_cases)
    case (leaf l)
    have "finite_shape_found q (Pair_Shape j k) \<noteq> Some i" for j k
      using leaf(1) by (simp add: finite_shape_found_read[OF rep tf])
    then have "finite_instance_reference q \<sigma> (Finite_Pattern_Pair p r) \<noteq> Some i"
      by (simp split: option.splits)
    moreover have "y |\<notin>| finite_pattern_instances V (Finite_Pattern_Pair p r)"
      using leaf(2) mem leaf_term_not_pair by metis
    ultimately show ?thesis by blast
  next
    case (pair j k x z)
    have found: "finite_shape_found q (Pair_Shape j' k') = Some i \<longleftrightarrow> j' = j \<and> k' = k" for j' k'
      using pair(1) by (auto simp: finite_shape_found_read[OF rep tf])
    have "finite_instance_reference q \<sigma> (Finite_Pattern_Pair p r) = Some i \<longleftrightarrow>
        finite_instance_reference q \<sigma> p = Some j \<and> finite_instance_reference q \<sigma> r = Some k"
      by (auto simp: found split: option.splits)
    then show ?thesis using Finite_Pattern_Pair.IH(1)[OF pair(4)] Finite_Pattern_Pair.IH(2)[OF pair(5)] mem pair(6)
      by auto
  qed
qed

subsection \<open>An interface matched over references\<close>

text \<open>
  Matching reads the call's shapes from its reference: a variable binds the reference it meets, a literal is the leaf
  the table holds there, and a pair is read one level through its shape. Two bindings of one variable are compared as
  references.
\<close>

fun finite_reference_bindings :: "share_state \<Rightarrow> 'a finite_term_pattern \<Rightarrow> nat \<Rightarrow> ('a \<times> nat) fset option" where
  "finite_reference_bindings q (Finite_Variable a) i = Some {|(a,i)|}"
| "finite_reference_bindings q (Finite_Pattern_Target x) i =
    (if finite_target_formed x \<and> finite_shape_found q (Leaf_Shape (Target_Leaf x)) = Some i then Some {||} else None)"
| "finite_reference_bindings q (Finite_Pattern_Payload v) i =
    (if octets_formed v \<and> finite_shape_found q (Leaf_Shape (Payload_Leaf v)) = Some i then Some {||} else None)"
| "finite_reference_bindings q (Finite_Pattern_Pair p r) i = (case finite_shape_at q i of
      Some (Pair_Shape j k) \<Rightarrow> (case finite_reference_bindings q p j of None \<Rightarrow> None
        | Some A \<Rightarrow> (case finite_reference_bindings q r k of None \<Rightarrow> None | Some B \<Rightarrow> Some (A |\<union>| B)))
    | _ \<Rightarrow> None)"

definition finite_reference_matched :: "share_state \<Rightarrow> 'a finite_term_pattern \<Rightarrow> nat \<Rightarrow> bool" where
  "finite_reference_matched q p i \<longleftrightarrow> (case finite_reference_bindings q p i of None \<Rightarrow> False
    | Some A \<Rightarrow> finite_relation_functional A)"

lemma finite_matching_instance_mono:
  "finite_matching_bindings p t |\<subseteq>| W \<Longrightarrow>
    finite_pattern_instance W p t \<longleftrightarrow> finite_pattern_instance (finite_matching_bindings p t) p t"
proof (induction p arbitrary: t W)
  case (Finite_Pattern_Pair p r)
  show ?case
  proof (cases t)
    case (Finite_Pair x z)
    have sub: "finite_matching_bindings p x |\<subseteq>| W" "finite_matching_bindings r z |\<subseteq>| W"
      "finite_matching_bindings p x |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z"
      "finite_matching_bindings r z |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z"
      using Finite_Pattern_Pair.prems Finite_Pair by auto
    show ?thesis using Finite_Pattern_Pair.IH(1)[OF sub(1)] Finite_Pattern_Pair.IH(2)[OF sub(2)]
      Finite_Pattern_Pair.IH(1)[OF sub(3)] Finite_Pattern_Pair.IH(2)[OF sub(4)] Finite_Pair by simp
  qed simp_all
qed simp_all

lemma finite_matching_instance_domain:
  "finite_pattern_instance (finite_matching_bindings p t) p t \<Longrightarrow>
    fimage fst (finite_matching_bindings p t) = finite_pattern_variables p"
proof (induction p arbitrary: t)
  case (Finite_Pattern_Pair p r)
  obtain x z where t: "t = Finite_Pair x z" using Finite_Pattern_Pair.prems by (cases t) simp_all
  have sub: "finite_matching_bindings p x |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z"
    "finite_matching_bindings r z |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z" by auto
  have i: "finite_pattern_instance (finite_matching_bindings p x) p x" "finite_pattern_instance (finite_matching_bindings r z) r z"
    using Finite_Pattern_Pair.prems t finite_matching_instance_mono[OF sub(1)] finite_matching_instance_mono[OF sub(2)]
    by simp_all
  show ?case using Finite_Pattern_Pair.IH(1)[OF i(1)] Finite_Pattern_Pair.IH(2)[OF i(2)] t by (simp add: fimage_funion)
qed simp_all

lemma finite_reference_bindings_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T"
  shows "reference_term T i = Some t \<Longrightarrow>
    (finite_reference_bindings q p i = None \<longleftrightarrow> \<not> finite_pattern_instance (finite_matching_bindings p t) p t) \<and>
    (\<forall>A. finite_reference_bindings q p i = Some A \<longrightarrow> fBall A (\<lambda>(a,j). \<exists>u. reference_term T j = Some u) \<and>
      fimage (\<lambda>(a,j). (a,the (reference_term T j))) A = finite_matching_bindings p t)"
proof (induction p arbitrary: i t)
  case (Finite_Variable a)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  show ?case using finite_leaf_found[OF rep tf Finite_Pattern_Target.prems, of "Target_Leaf x"] by auto
next
  case (Finite_Pattern_Payload v)
  show ?case using finite_leaf_found[OF rep tf Finite_Pattern_Payload.prems, of "Payload_Leaf v"] by auto
next
  case (Finite_Pattern_Pair p r)
  from Finite_Pattern_Pair.prems show ?case
  proof (cases rule: reference_term_cases)
    case (leaf l)
    have none: "finite_reference_bindings q (Finite_Pattern_Pair p r) i = None"
      using leaf(1) by (simp add: finite_shape_at_read[OF rep])
    have "\<not> finite_pattern_instance (finite_matching_bindings (Finite_Pattern_Pair p r) t) (Finite_Pattern_Pair p r) t"
      using leaf(2) by (cases l) simp_all
    then show ?thesis using none by simp
  next
    case (pair j k x z)
    have at: "finite_shape_at q i = Some (Pair_Shape j k)" using pair(1) by (simp add: finite_shape_at_read[OF rep])
    note IHp = Finite_Pattern_Pair.IH(1)[OF pair(4)] and IHr = Finite_Pattern_Pair.IH(2)[OF pair(5)]
    have sub: "finite_matching_bindings p x |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z"
      "finite_matching_bindings r z |\<subseteq>| finite_matching_bindings p x |\<union>| finite_matching_bindings r z" by auto
    have inst: "finite_pattern_instance (finite_matching_bindings (Finite_Pattern_Pair p r) t) (Finite_Pattern_Pair p r) t \<longleftrightarrow>
        finite_pattern_instance (finite_matching_bindings p x) p x \<and> finite_pattern_instance (finite_matching_bindings r z) r z"
      using pair(6) finite_matching_instance_mono[OF sub(1)] finite_matching_instance_mono[OF sub(2)] by simp
    show ?thesis
    proof (cases "finite_reference_bindings q p j")
      case None
      then show ?thesis using at IHp inst by simp
    next
      case (Some A)
      show ?thesis
      proof (cases "finite_reference_bindings q r k")
        case None
        then show ?thesis using at IHr inst Some by simp
      next
        case (Some B)
        then show ?thesis using at IHp IHr inst \<open>finite_reference_bindings q p j = Some A\<close> pair(6)
          by (auto simp: fimage_funion)
      qed
    qed
  qed
qed

lemma finite_reference_matched_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T" and t: "reference_term T i = Some t"
  shows "finite_reference_matched q p i \<longleftrightarrow> finite_pattern_matched p t"
proof (cases "finite_reference_bindings q p i")
  case None
  then have "\<not> finite_pattern_instance (finite_matching_bindings p t) p t"
    using finite_reference_bindings_exact[OF rep tf t, of p] by simp
  then show ?thesis using None by (simp add: finite_reference_matched_def finite_pattern_matched_def)
next
  case (Some A)
  have held: "fBall A (\<lambda>(a,j). \<exists>u. reference_term T j = Some u)"
    and img: "fimage (\<lambda>(a,j). (a,the (reference_term T j))) A = finite_matching_bindings p t"
    and inst: "finite_pattern_instance (finite_matching_bindings p t) p t"
    using finite_reference_bindings_exact[OF rep tf t, of p] Some by simp_all
  have inj: "u = v" if u: "u |\<in>| fimage snd A" and v: "v |\<in>| fimage snd A"
    and e: "the (reference_term T u) = the (reference_term T v)" for u v
  proof -
    obtain a b where au: "(a,u) |\<in>| A" and bv: "(b,v) |\<in>| A" using u v by force
    obtain x where x: "reference_term T u = Some x" using fbspec[OF held au] by auto
    obtain y where y: "reference_term T v = Some y" using fbspec[OF held bv] by auto
    have xy: "x = y" using x y e by simp
    show "u = v" by (rule reference_term_injective[OF tf x]) (use y xy in simp)
  qed
  have "finite_relation_functional (finite_matching_bindings p t) \<longleftrightarrow> finite_relation_functional A"
    unfolding img[symmetric] by (rule finite_relation_functional_value_image[OF inj])
  then show ?thesis using Some inst finite_matching_instance_domain[OF inst]
    by (simp add: finite_reference_matched_def finite_pattern_matched_def)
qed

subsection \<open>The admitted instance over references\<close>

text \<open>
  C3's admitted instance with the call, the bindings and the premise calls read as references: the interfaces matched
  over references, the bindings' domain read off their list, each instance compared with its call as a reference, and
  the premise calls compared as references. The values no call holds are formed and the material satisfied as C3 has
  them, over the values.
\<close>

definition finite_admitted_instance_reference_at ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> share_state \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a \<times> nat) list \<Rightarrow>
      ('a \<times> finite_factor_term) fset \<Rightarrow> nat \<Rightarrow> ('s \<times> ('d \<times> nat)) fset \<Rightarrow> bool" where
  "finite_admitted_instance_reference_at P q d c B V i QR \<longleftrightarrow>
    fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_reference_matched q p i) \<and>
    fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
      fset_of_list (map fst B) = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_instance_reference q (map_of B) (finite_schema_conclusion S) = Some i \<and>
      finite_relation_functional QR \<and> fimage fst QR = fimage fst (finite_schema_premises S) \<and>
      fBall (finite_schema_premises S) (\<lambda>(s,e,p). fBex QR (\<lambda>(r,e',j). r=s \<and> e'=e \<and>
        finite_instance_reference q (map_of B) p = Some j)) \<and>
      finite_schema_material_satisfied S V) \<and>
    fBall QR (\<lambda>(s,e,j). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_reference_matched q p j))"

lemma finite_admitted_instance_reference_exact:
  assumes rep: "keyed_state_represents q T" and tf: "table_formed T" and read: "finite_bindings_read T B V"
    and t: "reference_term T i = Some t"
    and held: "fBall QR (\<lambda>(s,e,j). \<exists>u. reference_term T j = Some u)"
    and Q: "Q = fimage (\<lambda>(s,e,j). (s,e,the (reference_term T j))) QR"
  shows "finite_admitted_instance_reference_at P q d c B V i QR \<longleftrightarrow> finite_admitted_instance_formed_at P d c V t Q"
proof -
  have \<sigma>: "\<And>a x. (a,x) |\<in>| V \<longleftrightarrow> (\<exists>r. map_of B a = Some r \<and> reference_term T r = Some x)"
    by (rule finite_bindings_read_member[OF read])
  have inst: "finite_pattern_instance V p u \<longleftrightarrow> finite_instance_reference q (map_of B) p = Some j"
    if "reference_term T j = Some u" for p u j
    using finite_instance_reference_exact[OF rep tf \<sigma> that, of p] by (simp add: finite_pattern_instances_member)
  have fV: "finite_relation_functional V" by (rule finite_bindings_read_functional[OF read])
  have dV: "fimage fst V = fset_of_list (map fst B)" by (rule finite_bindings_read_domain[OF read])
  have dec: "reference_term T j = Some (the (reference_term T j))" if "(s,e,j) |\<in>| QR" for s e j
    using fbspec[OF held that] by auto
  have I1: "finite_pattern_matched p t \<longleftrightarrow> finite_reference_matched q p i" for p
    by (simp add: finite_reference_matched_exact[OF rep tf t])
  have I3: "fBall Q (\<lambda>(s,e,x). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_pattern_matched p x)) \<longleftrightarrow>
      fBall QR (\<lambda>(s,e,j). fBex (finite_system_interfaces P) (\<lambda>(e',p). e'=e \<and> finite_reference_matched q p j))"
  proof -
    have pw: "finite_pattern_matched p (the (reference_term T j)) \<longleftrightarrow> finite_reference_matched q p j"
      if "(s,e,j) |\<in>| QR" for s e j p
      by (simp add: finite_reference_matched_exact[OF rep tf dec[OF that]])
    have img: "fBall Q Pm \<longleftrightarrow> fBall QR (\<lambda>x. Pm ((\<lambda>(s,e,j). (s,e,the (reference_term T j))) x))" for Pm
      unfolding Q by auto
    show ?thesis unfolding img
    proof (rule fBall_cong[OF refl], goal_cases)
      case (1 x)
      obtain s e j where xx: "x = (s,e,j)" by (cases x) auto
      show ?case using 1 xx by (simp add: pw)
    qed
  qed
  have Qimg: "Q = fimage (\<lambda>(s,v). (s,(\<lambda>(e,j). (e,the (reference_term T j))) v)) QR"
    unfolding Q by (rule fimage_cong[OF refl]) auto
  have injQ: "u = v" if mu: "u |\<in>| fimage snd QR" and mv: "v |\<in>| fimage snd QR"
      and same: "(\<lambda>(e,j). (e,the (reference_term T j))) u = (\<lambda>(e,j). (e,the (reference_term T j))) v" for u v
  proof -
    obtain s e j s' e' j' where u: "u = (e,j)" "(s,e,j) |\<in>| QR" and v: "v = (e',j')" "(s',e',j') |\<in>| QR"
      using mu mv by force
    have tj: "the (reference_term T j) = the (reference_term T j')" and ee: "e = e'" using same u v by simp_all
    have "j = j'" by (rule reference_term_injective[OF tf dec[OF u(2)]]) (use dec[OF v(2)] tj in simp)
    then show "u = v" using u(1) v(1) ee by simp
  qed
  have fQ: "finite_relation_functional Q \<longleftrightarrow> finite_relation_functional QR"
    unfolding Qimg by (rule finite_relation_functional_value_image[OF injQ])
  have kQ: "fimage fst Q = fimage fst QR" unfolding Q by (rule fset_eqI) force
  have pQ: "fBex Q (\<lambda>(r,e,x). r=s \<and> e=d' \<and> finite_pattern_instance V p x) \<longleftrightarrow>
      fBex QR (\<lambda>(r,e',j). r=s \<and> e'=d' \<and> finite_instance_reference q (map_of B) p = Some j)" for s d' p
  proof -
    have pw: "finite_pattern_instance V p (the (reference_term T j)) \<longleftrightarrow>
        finite_instance_reference q (map_of B) p = Some j" if "(r,e,j) |\<in>| QR" for r e j
      by (rule inst[OF dec[OF that]])
    have img: "fBex Q Pm \<longleftrightarrow> fBex QR (\<lambda>x. Pm ((\<lambda>(s,e,j). (s,e,the (reference_term T j))) x))" for Pm
      unfolding Q by auto
    show ?thesis unfolding img
    proof (rule fBex_cong[OF refl], goal_cases)
      case (1 x)
      obtain r e j where xx: "x = (r,e,j)" by (cases x) auto
      show ?case using 1 xx by (simp add: pw)
    qed
  qed
  have prem: "finite_schema_premise_instance S V Q \<longleftrightarrow> finite_relation_functional QR \<and>
      fimage fst QR = fimage fst (finite_schema_premises S) \<and>
      fBall (finite_schema_premises S) (\<lambda>(s,e,p). fBex QR (\<lambda>(r,e',j). r=s \<and> e'=e \<and>
        finite_instance_reference q (map_of B) p = Some j))" for S
    unfolding finite_schema_premise_instance_def fQ kQ by (simp only: pQ)
  have cl: "(e=d \<and> k=c \<and> finite_schema_formed S \<and>
      finite_relation_functional V \<and> fimage fst V = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q \<and>
      finite_schema_material_satisfied S V) \<longleftrightarrow>
    (e=d \<and> k=c \<and> finite_schema_formed S \<and>
      fset_of_list (map fst B) = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_instance_reference q (map_of B) (finite_schema_conclusion S) = Some i \<and>
      finite_relation_functional QR \<and> fimage fst QR = fimage fst (finite_schema_premises S) \<and>
      fBall (finite_schema_premises S) (\<lambda>(s,e,p). fBex QR (\<lambda>(r,e',j). r=s \<and> e'=e \<and>
        finite_instance_reference q (map_of B) p = Some j)) \<and>
      finite_schema_material_satisfied S V)" for e k S
    using fV dV inst[OF t, of "finite_schema_conclusion S"] prem[of S] by simp
  have C: "fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
      finite_relation_functional V \<and> fimage fst V = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q \<and>
      finite_schema_material_satisfied S V) \<longleftrightarrow>
    fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and> finite_schema_formed S \<and>
      fset_of_list (map fst B) = finite_schema_variables S \<and>
      fBall V (\<lambda>(a,x). a |\<in>| finite_schema_call_variables S \<or> finite_term_formed x) \<and>
      finite_instance_reference q (map_of B) (finite_schema_conclusion S) = Some i \<and>
      finite_relation_functional QR \<and> fimage fst QR = fimage fst (finite_schema_premises S) \<and>
      fBall (finite_schema_premises S) (\<lambda>(s,e,p). fBex QR (\<lambda>(r,e',j). r=s \<and> e'=e \<and>
        finite_instance_reference q (map_of B) p = Some j)) \<and>
      finite_schema_material_satisfied S V)"
  proof (rule fBex_cong[OF refl], goal_cases)
    case (1 x)
    obtain e k S where x: "x = ((e,k),S)" by (cases x) auto
    show ?case unfolding x prod.case by (rule cl)
  qed
  show ?thesis unfolding finite_admitted_instance_reference_at_def finite_admitted_instance_formed_at_def I3 C
    by (simp only: I1)
qed

subsection \<open>The premises' nodes found by the instances' references\<close>

text \<open>
  Where a node's bindings are read as references, its premises' nodes are found from the reference of each premise
  instance, made by substituting the bindings (@{const finite_instance_reference}), instead of from every instance shared
  again; where they are not, the instances are shared again as C2's rows do (@{text finite_bound_premise_nodes_none}).
  Either finds the premise's nodes (@{text finite_bound_index_exact}).
\<close>

definition finite_bound_premise_nodes ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      share_state \<Rightarrow> ('a \<times> nat) list option \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'a finite_term_pattern \<Rightarrow>
      ('a,'s,'d,'c) resolution_node fset" where
  "finite_bound_premise_nodes PI G q0 \<beta> nd s e p = finite_premise_reference_nodes PI G (case \<beta> of
      None \<Rightarrow> fimage (\<lambda>x. fst (keyed_share_term x q0)) (finite_pattern_instances (finite_node_values nd) p)
    | Some B \<Rightarrow> (case finite_instance_reference q0 (map_of B) p of None \<Rightarrow> {||} | Some r \<Rightarrow> {|r|})) nd s e"

lemma finite_bound_premise_nodes_none:
  "finite_bound_premise_nodes PI G q0 None nd s e p = finite_indexed_premise_nodes PI G q0 nd s e p"
  by (simp only: finite_bound_premise_nodes_def finite_indexed_premise_nodes_references option.simps)

definition finite_bound_links ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      share_state \<Rightarrow> ('a \<times> nat) list option \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_bound_links PI G q0 \<beta> nd = ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,m))
    (finite_bound_premise_nodes PI G q0 \<beta> nd s e p)) (finite_schema_premises (resolution_node_schema nd)))"

definition finite_bound_table_links ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow>
      (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow> share_state \<Rightarrow> ('a \<times> nat) list option \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_bound_table_links \<Theta> PI G q0 \<beta> nd = ffUnion (fimage (\<lambda>(s,e,p).
      let U = ffilter (\<lambda>u. resolution_table_lookup \<Theta> (e,u) \<noteq> None) (finite_pattern_instances (finite_node_values nd) p) in
    if U={||} then {||} else if finite_bound_premise_nodes PI G q0 \<beta> nd s e p={||}
      then fimage (\<lambda>u. (s,finite_table_node nd s e u)) U else {||})
    (finite_schema_premises (resolution_node_schema nd)))"

lemma finite_bound_index_exact:
  assumes listed: "finite_post_listed (fset N) ns" and rep0: "keyed_state_represents q T" and f0: "table_formed T"
    and L: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    and run: "finite_read_rows L ns q = (rows,q0)"
    and B: "\<And>m B. m |\<in>| N \<Longrightarrow> Bv (resolution_node_position m) = Some B \<Longrightarrow> finite_bindings_read T B (finite_node_values m)"
    and nd: "nd |\<in>| N"
  shows "finite_bound_premise_nodes (finite_position_index rows) (finite_group_index rows) q0
    (Bv (resolution_node_position nd)) nd s e p = finite_premise_nodes N nd s e p"
proof (rule finite_read_index_facts[OF listed rep0 f0 L run])
  fix T'
  assume rep: "keyed_state_represents q0 T'" and ft: "table_formed T'"
    and pres: "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
    and PI: "\<And>q m r. RBT.lookup (finite_position_index rows) q = Some (m,r) \<longleftrightarrow>
      m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and G: "\<And>r m. m \<in> set (finite_group_lookup (finite_group_index rows) r) \<longleftrightarrow>
      m |\<in>| N \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and ex: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and dist: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and refd: "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
      reference_term T' r = Some (finite_residual_term (resolution_node_call m))"
  show ?thesis
  proof (cases "Bv (resolution_node_position nd)")
    case None
    then show ?thesis using finite_read_index_exact[OF listed rep0 f0 L run, of nd s e p]
      by (simp only: finite_bound_premise_nodes_none)
  next
    case (Some B0)
    have read: "finite_bindings_read T' B0 (finite_node_values nd)" by (rule finite_bindings_read_extends[OF B[OF nd Some] pres])
    have \<sigma>: "\<And>a x. (a,x) |\<in>| finite_node_values nd \<longleftrightarrow> (\<exists>r. map_of B0 a = Some r \<and> reference_term T' r = Some x)"
      by (rule finite_bindings_read_member[OF read])
    have IR: "r |\<in>| (case finite_instance_reference q0 (map_of B0) p of None \<Rightarrow> {||} | Some r' \<Rightarrow> {|r'|}) \<longleftrightarrow>
        finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p"
      if m: "m |\<in>| N" and k: "finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))" for m r
      using finite_instance_reference_exact[OF rep ft \<sigma> refd[OF m k], of p] by (auto split: option.splits)
    show ?thesis unfolding Some finite_bound_premise_nodes_def option.simps
      by (rule finite_premise_reference_nodes_exact[OF dist PI G ex IR])
  qed
qed

subsection \<open>The rows a representation gives, with the bindings it reads\<close>

text \<open>
  A representation reads the bindings of a node when, at every table it represents, the list it gives at the node's
  position reads the node's bindings (@{const finite_bindings_read}); the representation that gives no list reads them
  trivially. The rows over it are C2's rows with each premise's nodes found by the instances' references, the sharing
  state and its position index returned beside them for the check over references.
\<close>

definition finite_reads_bindings ::
    "('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node fset \<Rightarrow> bool" where
  "finite_reads_bindings Bv q N \<longleftrightarrow> (\<forall>T. keyed_state_represents q T \<longrightarrow> (\<forall>m B. m |\<in>| N \<longrightarrow>
    Bv (resolution_node_position m) = Some B \<longrightarrow> finite_bindings_read T B (finite_node_values m)))"

lemma finite_reads_bindings_none: "finite_reads_bindings (\<lambda>_. None) q N"
  by (simp add: finite_reads_bindings_def)

definition finite_bound_check_rows ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('s list \<Rightarrow> nat option) \<Rightarrow> ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow>
      ('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow>
      bool \<times> share_state \<times> ('s list, ('a,'s,'d,'c) resolution_node \<times> nat) rbt \<times>
        (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
          ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_bound_check_rows \<Theta> L Bv q ns = (case finite_read_rows L ns q of (rows,q0) \<Rightarrow>
    let PI = finite_position_index rows; G = finite_group_index rows in
    (finite_share_leaves_formed q0,q0,PI,map (\<lambda>m. let \<beta> = Bv (resolution_node_position m) in
      (m,finite_bound_links PI G q0 \<beta> m,finite_bound_table_links \<Theta> PI G q0 \<beta> m)) ns))"

lemma finite_bound_links_none:
  "finite_bound_links PI G q0 None nd = finite_indexed_links PI G q0 nd"
  "finite_bound_table_links \<Theta> PI G q0 None nd = finite_indexed_table_links \<Theta> PI G q0 nd"
  by (simp_all only: finite_bound_links_def finite_indexed_links_def finite_bound_table_links_def
    finite_indexed_table_links_def finite_bound_premise_nodes_none)

lemma finite_bound_check_rows_none:
  "finite_bound_check_rows \<Theta> L (\<lambda>_. None) q ns = (case finite_read_check_rows \<Theta> L q ns of (fl,LS) \<Rightarrow>
    (fl,snd (finite_read_rows L ns q),finite_position_index (fst (finite_read_rows L ns q)),LS))"
  by (simp add: finite_bound_check_rows_def finite_read_check_rows_def Let_def finite_bound_links_none
    split: prod.split)

subsection \<open>The check over references\<close>

text \<open>
  A row whose node's bindings and call the representation reads as references, and which has no table link, is
  checked over references (@{const finite_admitted_instance_reference_at}), its premise calls read from the position
  index; any other row is checked as C3 checks it. Over the rows a representation that reads the calls and bindings
  gives, the check is C's (@{text finite_bound_check_rows_exact}).
\<close>

definition finite_reference_row_check ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> share_state \<Rightarrow> ('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow>
      ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<Rightarrow> bool" where
  "finite_reference_row_check P q0 PI Bv row = (case row of (m,L,TL) \<Rightarrow>
    (case Bv (resolution_node_position m) of None \<Rightarrow> finite_formed_row_check P (m,L,TL)
    | Some B \<Rightarrow> (case RBT.lookup PI (resolution_node_position m) of None \<Rightarrow> finite_formed_row_check P (m,L,TL)
      | Some (m',i) \<Rightarrow> if TL = {||} then finite_admitted_instance_reference_at P q0 (resolution_node_site m)
          (resolution_node_clause m) B (finite_node_values m) i
          (fimage (\<lambda>(s,m''). (s,resolution_node_site m'',snd (the (RBT.lookup PI (resolution_node_position m''))))) L)
        else finite_formed_row_check P (m,L,TL))))"

definition finite_reference_reached_graph_check ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> share_state \<Rightarrow> ('s list, ('a,'s,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow>
      ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> ('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_reference_reached_graph_check P q0 PI Bv d t LS R nd =
    finite_rows_reached_check (finite_reference_row_check P q0 PI Bv) P d t LS R nd"

lemma finite_reference_reached_none:
  "finite_reference_reached_graph_check P q0 PI (\<lambda>_. None) d t LS = finite_formed_reached_graph_check P d t LS"
proof -
  have "finite_reference_row_check P q0 PI (\<lambda>_. None) = finite_formed_row_check P"
    by (rule ext) (simp add: finite_reference_row_check_def split: prod.split)
  then show ?thesis by (intro ext) (simp only: finite_reference_reached_graph_check_def finite_formed_reached_graph_check_def)
qed

lemma finite_reference_row_check_exact:
  assumes rep: "keyed_state_represents q0 T" and tf: "table_formed T"
    and PIc: "\<And>q m r. RBT.lookup PI q = Some (m,r) \<longleftrightarrow>
      m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and ex: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and refd: "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0 r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
      reference_term T r = Some (finite_residual_term (resolution_node_call m))"
    and B: "\<And>m B. m |\<in>| N \<Longrightarrow> Bv (resolution_node_position m) = Some B \<Longrightarrow> finite_bindings_read T B (finite_node_values m)"
    and m: "m |\<in>| N" and Ln: "\<And>s m''. (s,m'') |\<in>| L \<Longrightarrow> m'' |\<in>| N"
  shows "finite_reference_row_check P q0 PI Bv (m,L,TL) = finite_formed_row_check P (m,L,TL)"
proof (cases "Bv (resolution_node_position m)")
  case None
  then show ?thesis by (simp add: finite_reference_row_check_def)
next
  case (Some B0)
  obtain r0 where k0: "finite_term_keyed q0 r0 (finite_residual_term (resolution_node_call m))" using ex[OF m] by blast
  have look: "RBT.lookup PI (resolution_node_position m) = Some (m,r0)" using PIc m k0 by blast
  have i: "reference_term T r0 = Some (finite_residual_term (resolution_node_call m))" by (rule refd[OF m k0])
  show ?thesis
  proof (cases "TL = {||}")
    case False
    then show ?thesis using Some look by (simp add: finite_reference_row_check_def)
  next
    case True
    have lk: "\<exists>r. RBT.lookup PI (resolution_node_position m'') = Some (m'',r) \<and>
        reference_term T r = Some (finite_residual_term (resolution_node_call m''))" if sm: "(s,m'') |\<in>| L" for s m''
    proof -
      have mm: "m'' |\<in>| N" by (rule Ln[OF sm])
      obtain r where k: "finite_term_keyed q0 r (finite_residual_term (resolution_node_call m''))" using ex[OF mm] by blast
      show ?thesis using PIc mm k refd[OF mm k] by blast
    qed
    let ?QR = "fimage (\<lambda>(s,m''). (s,resolution_node_site m'',snd (the (RBT.lookup PI (resolution_node_position m''))))) L"
    let ?Q = "fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L"
    have pt: "the (reference_term T (snd (the (RBT.lookup PI (resolution_node_position m''))))) =
        finite_residual_term (resolution_node_call m'')" and ph: "\<exists>u. reference_term T (snd (the (RBT.lookup PI
        (resolution_node_position m'')))) = Some u" if sm: "(s,m'') |\<in>| L" for s m''
      using lk[OF sm] by auto
    have held: "fBall ?QR (\<lambda>(s,e,j). \<exists>u. reference_term T j = Some u)"
    proof (rule fBallI)
      fix z assume "z |\<in>| ?QR"
      then obtain s m'' where sm: "(s,m'') |\<in>| L"
        and zz: "z = (s,resolution_node_site m'',snd (the (RBT.lookup PI (resolution_node_position m''))))" by force
      show "case z of (s,e,j) \<Rightarrow> \<exists>u. reference_term T j = Some u" using ph[OF sm] zz by simp
    qed
    have Q: "?Q = fimage (\<lambda>(s,e,j). (s,e,the (reference_term T j))) ?QR"
      unfolding fset.map_comp
    proof (rule fimage_cong[OF refl], goal_cases)
      case (1 x)
      obtain s m'' where xx: "x = (s,m'')" by (cases x) auto
      show ?case using pt[of s m''] 1 xx by simp
    qed
    have eq: "finite_admitted_instance_reference_at P q0 (resolution_node_site m) (resolution_node_clause m) B0
        (finite_node_values m) r0 ?QR \<longleftrightarrow>
      finite_admitted_instance_formed_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m)) ?Q"
      by (rule finite_admitted_instance_reference_exact[OF rep tf B[OF m Some] i held Q])
    show ?thesis using Some look True eq by (simp add: finite_reference_row_check_def finite_formed_row_check_def)
  qed
qed

lemma finite_bound_check_rows_exact:
  assumes listed: "finite_post_listed (fset N) ns" and reads: "finite_reads_calls L q N"
    and binds: "finite_reads_bindings Bv q N" and run: "finite_bound_check_rows \<Theta> L Bv q ns = (fl,q0,PI,LS)"
  shows "LS = finite_indexed_table_rows \<Theta> ns"
    and "fl \<Longrightarrow> finite_reference_reached_graph_check P q0 PI Bv d t LS = finite_indexed_reached_graph_check P d t LS"
proof -
  obtain T where rep: "keyed_state_represents q T" and f: "table_formed T"
    and held: "\<And>m i. m |\<in>| N \<Longrightarrow> L (resolution_node_position m) = Some i \<Longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using reads unfolding finite_reads_calls_def by blast
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  have Lh: "\<forall>m\<in>set ns. \<forall>i. L (resolution_node_position m) = Some i \<longrightarrow>
      reference_term T i = Some (finite_residual_term (resolution_node_call m))"
    using held setns by auto
  have B: "\<And>m B. m |\<in>| N \<Longrightarrow> Bv (resolution_node_position m) = Some B \<Longrightarrow> finite_bindings_read T B (finite_node_values m)"
    using binds rep unfolding finite_reads_bindings_def by blast
  obtain rows q0' where rr: "finite_read_rows L ns q = (rows,q0')" by (cases "finite_read_rows L ns q")
  have run': "finite_bound_check_rows \<Theta> L Bv q ns = (finite_share_leaves_formed q0',q0',finite_position_index rows,
      map (\<lambda>m. (m,finite_bound_links (finite_position_index rows) (finite_group_index rows) q0'
        (Bv (resolution_node_position m)) m,
      finite_bound_table_links \<Theta> (finite_position_index rows) (finite_group_index rows) q0'
        (Bv (resolution_node_position m)) m)) ns)"
    using rr by (simp add: finite_bound_check_rows_def Let_def)
  have fields: "fl = finite_share_leaves_formed q0'" "q0 = q0'" "PI = finite_position_index rows"
    "LS = map (\<lambda>m. (m,finite_bound_links (finite_position_index rows) (finite_group_index rows) q0'
        (Bv (resolution_node_position m)) m,
      finite_bound_table_links \<Theta> (finite_position_index rows) (finite_group_index rows) q0'
        (Bv (resolution_node_position m)) m)) ns"
    using run' run by simp_all
  have nodes: "finite_bound_premise_nodes (finite_position_index rows) (finite_group_index rows) q0'
      (Bv (resolution_node_position m)) m s e p = finite_premise_nodes N m s e p" if "m |\<in>| N" for m s e p
    by (rule finite_bound_index_exact[OF listed rep f Lh rr B that])
  have exact: "LS = map (\<lambda>m. (m,finite_node_links N m,finite_table_links \<Theta> N m)) ns"
    unfolding fields(4)
  proof (rule map_cong[OF refl], goal_cases)
    case (1 m)
    have m: "m |\<in>| N" using 1 setns by simp
    show ?case by (simp only: finite_bound_links_def finite_node_links_def finite_bound_table_links_def
      finite_table_links_def nodes[OF m] Let_def finite_guarded_image)
  qed
  show "LS = finite_indexed_table_rows \<Theta> ns" using exact finite_indexed_table_rows_exact[OF listed] by simp
  assume fl: fl
  show "finite_reference_reached_graph_check P q0 PI Bv d t LS = finite_indexed_reached_graph_check P d t LS"
  proof (rule finite_read_index_facts[OF listed rep f Lh rr])
    fix T'
    assume rep': "keyed_state_represents q0' T'" and ft': "table_formed T'"
      and pres: "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
      and PIc: "\<And>q m r. RBT.lookup (finite_position_index rows) q = Some (m,r) \<longleftrightarrow>
        m |\<in>| N \<and> resolution_node_position m = q \<and> finite_term_keyed q0' r (finite_residual_term (resolution_node_call m))"
      and "\<And>r m. m \<in> set (finite_group_lookup (finite_group_index rows) r) \<longleftrightarrow>
        m |\<in>| N \<and> finite_term_keyed q0' r (finite_residual_term (resolution_node_call m))"
      and ex: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0' r (finite_residual_term (resolution_node_call m))"
      and "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
      and refd: "\<And>m r. m |\<in>| N \<Longrightarrow> finite_term_keyed q0' r (finite_residual_term (resolution_node_call m)) \<Longrightarrow>
        reference_term T' r = Some (finite_residual_term (resolution_node_call m))"
    have formed: "finite_term_formed (finite_residual_term (resolution_node_call m))" if mN: "m |\<in>| N" for m
    proof -
      obtain r where k: "finite_term_keyed q0' r (finite_residual_term (resolution_node_call m))" using ex[OF mN] by blast
      have "reference_term T' r = Some (finite_residual_term (resolution_node_call m))" by (rule refd[OF mN k])
      then show ?thesis by (rule finite_share_leaves_formed_reference[OF rep' fl[unfolded fields(1)]])
    qed
    have B': "\<And>m B. m |\<in>| N \<Longrightarrow> Bv (resolution_node_position m) = Some B \<Longrightarrow> finite_bindings_read T' B (finite_node_values m)"
      using finite_bindings_read_extends[OF B pres] by blast
    have rowsF: "finite_term_formed (finite_residual_term (resolution_node_call m)) \<and>
        fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
      if r: "(m,L,TL) \<in> set LS" for m L TL
    proof -
      from r have m: "m \<in> set ns" and Lm: "L = finite_node_links N m" unfolding exact by auto
      have mN: "m |\<in>| N" using m setns by simp
      have "fBall L (\<lambda>(s,m'). finite_term_formed (finite_residual_term (resolution_node_call m')))"
        using Lm formed finite_node_links_reach(1) by fastforce
      then show ?thesis using formed[OF mN] by blast
    qed
    have rowR: "finite_reference_row_check P q0' (finite_position_index rows) Bv row = finite_formed_row_check P row"
      if r: "row \<in> set LS" for row
    proof -
      obtain m L TL where rr': "row = (m,L,TL)" by (cases row) auto
      from r have m: "m \<in> set ns" and Lm: "L = finite_node_links N m" unfolding exact rr' by auto
      have mN: "m |\<in>| N" using m setns by simp
      have Ln: "m'' |\<in>| N" if "(s,m'') |\<in>| L" for s m'' using that Lm finite_node_links_reach(1) by blast
      show ?thesis unfolding rr' by (rule finite_reference_row_check_exact[OF rep' ft' PIc ex refd B' mN Ln])
    qed
    show ?thesis
    proof (intro ext)
      fix R nd
      show "finite_reference_reached_graph_check P q0 PI Bv d t LS R nd = finite_indexed_reached_graph_check P d t LS R nd"
        unfolding fields(2,3) finite_reference_reached_graph_check_def
        by (simp only: finite_rows_reached_cong[OF rowR] finite_formed_reached_graph_check_def[symmetric]
          finite_formed_reached_graph_check_exact[OF rowsF])
    qed
  qed
qed

section \<open>C's readings over a representation, stated once\<close>

text \<open>
  C's three readings of a found state's roots (its verdicts, its graph verdicts and its graph truth) differ only in what
  they read of a root over the rows; each is a per-root reading of the rows and of a reached check
  (@{text finite_verdict_roots}, @{text finite_graph_verdict_roots}, @{text finite_true_roots}). Over a representation
  the rows are read and the reached check is the check over references where the table's leaves are formed, C's
  otherwise (@{text finite_reading_by}), stated once for the three and equal to C's at the projected state wherever
  the representation reads the calls and the bindings (@{text finite_reading_by_exact}). C2's three readings are its
  instances at the representation that reads no binding, their statements kept; the readings over a representation
  that reads the bindings are @{text finite_bound_verdicts_in}, @{text finite_bound_graph_verdicts_in} and
  @{text finite_bound_graph_true_in}.
\<close>

definition finite_reading_by ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> 'r) \<Rightarrow>
      ((('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> (('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool) \<Rightarrow> 'r) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 'r" where
  "finite_reading_by C \<rho> P d t \<Theta> L Bv q st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> C st
    | Some ns \<Rightarrow> (case finite_bound_check_rows \<Theta> L Bv q ns of (fl,q0,PI,LS) \<Rightarrow>
        \<rho> LS (if fl then finite_reference_reached_graph_check P q0 PI Bv d t LS else finite_indexed_reached_graph_check P d t LS)))"

lemma finite_reading_by_none:
  "finite_reading_by C \<rho> P d t \<Theta> L (\<lambda>_. None) q st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> C st
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> L q ns of (fl,LS) \<Rightarrow>
        \<rho> LS (if fl then finite_formed_reached_graph_check P d t LS else finite_indexed_reached_graph_check P d t LS)))"
  by (simp add: finite_reading_by_def finite_bound_check_rows_none finite_reference_reached_none
    split: option.split prod.split)

theorem finite_reading_by_exact:
  assumes reads: "finite_reads_calls L q (resolution_nodes st)" and binds: "finite_reads_bindings Bv q (resolution_nodes st)"
    and code: "\<And>ns. finite_post_listing (fset (resolution_nodes st)) = Some ns \<Longrightarrow>
      C st = \<rho> (finite_indexed_table_rows \<Theta> ns) (finite_indexed_reached_graph_check P d t (finite_indexed_table_rows \<Theta> ns))"
  shows "finite_reading_by C \<rho> P d t \<Theta> L Bv q st = C st"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_reading_by_def)
next
  case (Some ns)
  have listed: "finite_post_listed (fset (resolution_nodes st)) ns" by (rule finite_post_listing_some[OF Some])
  obtain fl q0 PI LS where run: "finite_bound_check_rows \<Theta> L Bv q ns = (fl,q0,PI,LS)"
    by (cases "finite_bound_check_rows \<Theta> L Bv q ns") auto
  note e = finite_bound_check_rows_exact[OF listed reads binds run]
  have g: "(if fl then finite_reference_reached_graph_check P q0 PI Bv d t LS else finite_indexed_reached_graph_check P d t LS) =
      finite_indexed_reached_graph_check P d t LS" using e(2) by simp
  have "finite_reading_by C \<rho> P d t \<Theta> L Bv q st =
      \<rho> LS (if fl then finite_reference_reached_graph_check P q0 PI Bv d t LS else finite_indexed_reached_graph_check P d t LS)"
    using Some run by (simp only: finite_reading_by_def option.simps prod.simps)
  also have "\<dots> = \<rho> LS (finite_indexed_reached_graph_check P d t LS)" by (simp only: g)
  also have "\<dots> = C st" using code[OF Some] e(1) by simp
  finally show ?thesis .
qed

definition finite_true_roots ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> (('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool) \<Rightarrow> bool" where
  "finite_true_roots st LS g = fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
    (\<lambda>nd. g (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd)"

definition finite_graph_verdict_roots ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> (('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_graph_verdict_roots P d t \<Theta> st LS g = (let CT = finite_indexed_certificates_in \<Theta> LS in
    fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
      (c,g (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd \<or> finite_checks_schema_proof P c d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st)))"

definition finite_verdict_roots ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_table \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s::linorder,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset \<times>
        ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list \<Rightarrow> (('s list, unit) rbt \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool) \<Rightarrow>
      (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_verdict_roots P d t \<Theta> st LS g = (let CT = finite_indexed_certificates_in \<Theta> LS in
    fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd));
        R = finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd in
      (c,(g R nd \<and> finite_indexed_reached_entries P \<Theta> LS R) \<or> finite_checks_schema_proof P c d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st)))"

lemma finite_indexed_table_graph_check_reached:
  "finite_indexed_table_graph_check P d t LS =
    (\<lambda>nd. finite_indexed_reached_graph_check P d t LS (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd)"
  by (rule ext) (simp only: finite_indexed_table_graph_check_def)

lemma finite_formed_table_graph_check_reached:
  "finite_formed_table_graph_check P d t LS =
    (\<lambda>nd. finite_formed_reached_graph_check P d t LS (finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd) nd)"
  by (rule ext) (simp only: finite_formed_table_graph_check_def)

lemma finite_indexed_table_accepts_reached:
  "finite_indexed_table_accepts P \<Theta> d t LS = (\<lambda>nd. let R = finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd in
    finite_indexed_reached_graph_check P d t LS R nd \<and> finite_indexed_reached_entries P \<Theta> LS R)"
  by (rule ext) (simp only: finite_indexed_table_accepts_def)

lemma finite_formed_table_accepts_reached:
  "finite_formed_table_accepts P \<Theta> d t LS = (\<lambda>nd. let R = finite_indexed_reach (map (\<lambda>(m,L,TL). (m,L)) LS) nd in
    finite_formed_reached_graph_check P d t LS R nd \<and> finite_indexed_reached_entries P \<Theta> LS R)"
  by (rule ext) (simp only: finite_formed_table_accepts_def)

lemma finite_true_roots_code:
  assumes "finite_post_listing (fset (resolution_nodes st)) = Some ns"
  shows "finite_state_graph_true_in \<Theta> P d t st = finite_true_roots st (finite_indexed_table_rows \<Theta> ns)
    (finite_indexed_reached_graph_check P d t (finite_indexed_table_rows \<Theta> ns))"
  using assms by (simp add: finite_state_graph_true_in_indexed finite_true_roots_def
    finite_indexed_table_graph_check_reached Let_def)

lemma finite_graph_verdict_roots_code:
  assumes "finite_post_listing (fset (resolution_nodes st)) = Some ns"
  shows "finite_state_graph_verdicts_in \<Theta> P d t st = finite_graph_verdict_roots P d t \<Theta> st (finite_indexed_table_rows \<Theta> ns)
    (finite_indexed_reached_graph_check P d t (finite_indexed_table_rows \<Theta> ns))"
  using assms by (simp add: finite_state_graph_verdicts_in_indexed finite_graph_verdict_roots_def
    finite_indexed_table_graph_check_reached Let_def)

lemma finite_verdict_roots_code:
  assumes "finite_post_listing (fset (resolution_nodes st)) = Some ns"
  shows "finite_state_verdicts_in \<Theta> P d t st = finite_verdict_roots P d t \<Theta> st (finite_indexed_table_rows \<Theta> ns)
    (finite_indexed_reached_graph_check P d t (finite_indexed_table_rows \<Theta> ns))"
  using assms by (simp add: finite_state_verdicts_in_accepts finite_verdict_roots_def
    finite_indexed_table_accepts_reached Let_def)

definition finite_bound_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_bound_verdicts_in \<Theta> P d t L Bv q st =
    finite_reading_by (finite_state_verdicts_in \<Theta> P d t) (finite_verdict_roots P d t \<Theta> st) P d t \<Theta> L Bv q st"

definition finite_bound_graph_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_bound_graph_verdicts_in \<Theta> P d t L Bv q st =
    finite_reading_by (finite_state_graph_verdicts_in \<Theta> P d t) (finite_graph_verdict_roots P d t \<Theta> st) P d t \<Theta> L Bv q st"

definition finite_bound_graph_true_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> ('s list \<Rightarrow> ('a \<times> nat) list option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      bool" where
  "finite_bound_graph_true_in \<Theta> P d t L Bv q st =
    finite_reading_by (finite_state_graph_true_in \<Theta> P d t) (finite_true_roots st) P d t \<Theta> L Bv q st"

theorem finite_bound_verdicts_in_exact:
  assumes "finite_reads_calls L q (resolution_nodes st)" "finite_reads_bindings Bv q (resolution_nodes st)"
  shows "finite_bound_verdicts_in \<Theta> P d t L Bv q st = finite_state_verdicts_in \<Theta> P d t st"
  unfolding finite_bound_verdicts_in_def by (rule finite_reading_by_exact[OF assms]) (rule finite_verdict_roots_code)

theorem finite_bound_graph_verdicts_in_exact:
  assumes "finite_reads_calls L q (resolution_nodes st)" "finite_reads_bindings Bv q (resolution_nodes st)"
  shows "finite_bound_graph_verdicts_in \<Theta> P d t L Bv q st = finite_state_graph_verdicts_in \<Theta> P d t st"
  unfolding finite_bound_graph_verdicts_in_def
  by (rule finite_reading_by_exact[OF assms]) (rule finite_graph_verdict_roots_code)

theorem finite_bound_graph_true_in_exact:
  assumes "finite_reads_calls L q (resolution_nodes st)" "finite_reads_bindings Bv q (resolution_nodes st)"
  shows "finite_bound_graph_true_in \<Theta> P d t L Bv q st = finite_state_graph_true_in \<Theta> P d t st"
  unfolding finite_bound_graph_true_in_def by (rule finite_reading_by_exact[OF assms]) (rule finite_true_roots_code)

definition finite_read_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_read_verdicts_in \<Theta> P d t L q st = finite_bound_verdicts_in \<Theta> P d t L (\<lambda>_. None) q st"

definition finite_read_graph_verdicts_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> (('a,'s,'c) finite_schema_proof \<times> bool) fset" where
  "finite_read_graph_verdicts_in \<Theta> P d t L q st = finite_bound_graph_verdicts_in \<Theta> P d t L (\<lambda>_. None) q st"

definition finite_read_graph_true_in ::
    "('a,'s,'d,'c) resolution_table \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow>
      ('s list \<Rightarrow> nat option) \<Rightarrow> share_state \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> bool" where
  "finite_read_graph_true_in \<Theta> P d t L q st = finite_bound_graph_true_in \<Theta> P d t L (\<lambda>_. None) q st"

theorem finite_read_verdicts_in_exact:
  assumes reads: "finite_reads_calls L q (resolution_nodes st)"
  shows "finite_read_verdicts_in \<Theta> P d t L q st = finite_state_verdicts_in \<Theta> P d t st"
  unfolding finite_read_verdicts_in_def by (rule finite_bound_verdicts_in_exact[OF reads finite_reads_bindings_none])

theorem finite_read_graph_verdicts_in_exact:
  assumes reads: "finite_reads_calls L q (resolution_nodes st)"
  shows "finite_read_graph_verdicts_in \<Theta> P d t L q st = finite_state_graph_verdicts_in \<Theta> P d t st"
  unfolding finite_read_graph_verdicts_in_def by (rule finite_bound_graph_verdicts_in_exact[OF reads finite_reads_bindings_none])

theorem finite_read_graph_true_in_exact:
  assumes reads: "finite_reads_calls L q (resolution_nodes st)"
  shows "finite_read_graph_true_in \<Theta> P d t L q st = finite_state_graph_true_in \<Theta> P d t st"
  unfolding finite_read_graph_true_in_def by (rule finite_bound_graph_true_in_exact[OF reads finite_reads_bindings_none])

lemma finite_read_none:
  "finite_read_verdicts_in \<Theta> P d t (\<lambda>_. None) empty_share_state st = finite_state_verdicts_in \<Theta> P d t st"
  "finite_read_graph_verdicts_in \<Theta> P d t (\<lambda>_. None) empty_share_state st = finite_state_graph_verdicts_in \<Theta> P d t st"
  "finite_read_graph_true_in \<Theta> P d t (\<lambda>_. None) empty_share_state st = finite_state_graph_true_in \<Theta> P d t st"
  by (simp_all only: finite_read_verdicts_in_exact finite_read_graph_verdicts_in_exact finite_read_graph_true_in_exact
    finite_reads_calls_none)

text \<open>
  C3 on today's path: the code equations of C's verdicts, graph verdicts and graph truth read their rows with the
  formation of the table the rows share (the representation that reads no reference), each equal to C's on every input
  through the one reading's exactness (@{text finite_reading_by_none}); the empty table's verdicts are the verdicts at
  the empty table (@{text finite_state_verdicts_empty}).
\<close>

declare finite_state_verdicts_in_accepts [code del] finite_state_graph_verdicts_in_indexed [code del]
  finite_state_graph_true_in_indexed [code del] finite_state_verdicts_indexed [code del]

lemma finite_state_verdicts_in_checked [code]:
  "finite_state_verdicts_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table_in \<Theta> N K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,(finite_state_graph_code_in \<Theta> P d t N K nd \<and> finite_table_entries_accepted P \<Theta> N nd) \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns of (fl,LS) \<Rightarrow>
        let CT = finite_indexed_certificates_in \<Theta> LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,(if fl then finite_formed_table_accepts P \<Theta> d t LS else finite_indexed_table_accepts P \<Theta> d t LS) nd \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp only: finite_state_verdicts_in_accepts option.simps)
next
  case (Some ns)
  obtain fl LS where rc: "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns = (fl,LS)"
    by (cases "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns")
  have "finite_state_verdicts_in \<Theta> P d t st = finite_read_verdicts_in \<Theta> P d t (\<lambda>_. None) empty_share_state st"
    by (rule finite_read_none(1)[symmetric])
  also have "\<dots> = finite_verdict_roots P d t \<Theta> st LS
      (if fl then finite_formed_reached_graph_check P d t LS else finite_indexed_reached_graph_check P d t LS)"
    using Some rc by (simp add: finite_read_verdicts_in_def finite_bound_verdicts_in_def finite_reading_by_none)
  also have "\<dots> = (let CT = finite_indexed_certificates_in \<Theta> LS in
      fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
        (c,(if fl then finite_formed_table_accepts P \<Theta> d t LS else finite_indexed_table_accepts P \<Theta> d t LS) nd \<or>
          finite_checks_schema_proof P c d t))
        (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st)))"
    by (cases fl) (simp_all add: finite_verdict_roots_def finite_formed_table_accepts_reached
      finite_indexed_table_accepts_reached Let_def)
  finally show ?thesis using Some rc by simp
qed

lemma finite_state_graph_verdicts_in_checked [code]:
  "finite_state_graph_verdicts_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; K = finite_node_ranked N; T = finite_certificate_table_in \<Theta> N K in
        fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
          (c,finite_state_graph_code_in \<Theta> P d t N K nd \<or> finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns of (fl,LS) \<Rightarrow>
        let CT = finite_indexed_certificates_in \<Theta> LS in
        fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
          (c,(if fl then finite_formed_table_graph_check P d t LS else finite_indexed_table_graph_check P d t LS) nd \<or>
            finite_checks_schema_proof P c d t))
          (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp only: finite_state_graph_verdicts_in_indexed option.simps)
next
  case (Some ns)
  obtain fl LS where rc: "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns = (fl,LS)"
    by (cases "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns")
  have "finite_state_graph_verdicts_in \<Theta> P d t st = finite_read_graph_verdicts_in \<Theta> P d t (\<lambda>_. None) empty_share_state st"
    by (rule finite_read_none(2)[symmetric])
  also have "\<dots> = finite_graph_verdict_roots P d t \<Theta> st LS
      (if fl then finite_formed_reached_graph_check P d t LS else finite_indexed_reached_graph_check P d t LS)"
    using Some rc by (simp add: finite_read_graph_verdicts_in_def finite_bound_graph_verdicts_in_def finite_reading_by_none)
  also have "\<dots> = (let CT = finite_indexed_certificates_in \<Theta> LS in
      fimage (\<lambda>nd. let c = the (RBT.lookup CT (resolution_node_position nd)) in
        (c,(if fl then finite_formed_table_graph_check P d t LS else finite_indexed_table_graph_check P d t LS) nd \<or>
          finite_checks_schema_proof P c d t))
        (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st)))"
    by (cases fl) (simp_all add: finite_graph_verdict_roots_def finite_formed_table_graph_check_reached
      finite_indexed_table_graph_check_reached Let_def)
  finally show ?thesis using Some rc by simp
qed

lemma finite_state_graph_true_in_checked [code]:
  "finite_state_graph_true_in \<Theta> P d t st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
        (finite_state_graph_check_in \<Theta> P d t (resolution_nodes st))
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns of (fl,LS) \<Rightarrow>
        fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
          (if fl then finite_formed_table_graph_check P d t LS else finite_indexed_table_graph_check P d t LS)))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp only: finite_state_graph_true_in_indexed option.simps)
next
  case (Some ns)
  obtain fl LS where rc: "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns = (fl,LS)"
    by (cases "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns")
  have "finite_state_graph_true_in \<Theta> P d t st = finite_read_graph_true_in \<Theta> P d t (\<lambda>_. None) empty_share_state st"
    by (rule finite_read_none(3)[symmetric])
  also have "\<dots> = finite_true_roots st LS
      (if fl then finite_formed_reached_graph_check P d t LS else finite_indexed_reached_graph_check P d t LS)"
    using Some rc by (simp add: finite_read_graph_true_in_def finite_bound_graph_true_in_def finite_reading_by_none)
  also have "\<dots> = fBex (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))
      (if fl then finite_formed_table_graph_check P d t LS else finite_indexed_table_graph_check P d t LS)"
    by (cases fl) (simp_all add: finite_true_roots_def finite_formed_table_graph_check_reached
      finite_indexed_table_graph_check_reached)
  finally show ?thesis using Some rc by simp
qed

lemma finite_state_verdicts_checked [code]: "finite_state_verdicts P d t st = finite_state_verdicts_in resolution_empty_table P d t st"
  by (simp add: finite_state_verdicts_empty)

section \<open>C3 in the table's production checks\<close>

text \<open>
  A table's check and its checked production read their rows with the formation of the table the rows share, as C's
  readings do: where its leaves are formed, the formed check, which forms no call again; each equal to the indexed
  code equation on every input (@{text finite_read_check_rows_indexed}). The table's production checks nothing, so its
  code equation is the indexed one as it stands.
\<close>

declare finite_table_graph_checks_indexed [code del] finite_table_checked_indexed [code del]

lemma finite_table_graph_checks_formed [code]:
  "finite_table_graph_checks P \<Theta> ((e,u,N,nd)#rows) = (case finite_post_listing (fset N) of
      None \<Rightarrow> nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd \<and>
        finite_table_graph_checks P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns of (fl,LS) \<Rightarrow>
        nd |\<in>| N \<and> (if fl then finite_formed_table_graph_check P e u LS else finite_indexed_table_graph_check P e u LS) nd \<and>
        finite_table_graph_checks P (resolution_table_extend \<Theta> e u
          (the (RBT.lookup (finite_indexed_certificates_in \<Theta> LS) (resolution_node_position nd)))) rows))"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by (simp only: finite_table_graph_checks_indexed option.simps)
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  obtain fl where r: "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns = (fl,finite_indexed_table_rows \<Theta> ns)"
    and g: "(if fl then finite_formed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)"
    by (rule finite_read_check_rows_indexed[OF listed finite_reads_calls_none, of \<Theta> P e u]) blast+
  show ?thesis using Some by (simp only: finite_table_graph_checks_indexed r g option.simps prod.simps Let_def)
qed

lemma finite_table_checked_formed [code]:
  "finite_table_checked P \<Theta> ((e,u,N,nd)#rows) = (case finite_post_listing (fset N) of
      None \<Rightarrow> if nd |\<in>| N \<and> finite_state_graph_check_in \<Theta> P e u N nd
        then finite_table_checked P (resolution_table_extend \<Theta> e u (finite_node_proof_in \<Theta> (fcard N) N nd)) rows else None
    | Some ns \<Rightarrow> (case finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns of (fl,LS) \<Rightarrow>
        if nd |\<in>| N \<and> (if fl then finite_formed_table_graph_check P e u LS else finite_indexed_table_graph_check P e u LS) nd
        then finite_table_checked P (resolution_table_extend \<Theta> e u
          (the (RBT.lookup (finite_indexed_certificates_in \<Theta> LS) (resolution_node_position nd)))) rows else None))"
proof (cases "finite_post_listing (fset N)")
  case None
  then show ?thesis by (simp only: finite_table_checked_indexed option.simps)
next
  case (Some ns)
  have listed: "finite_post_listed (fset N) ns" by (rule finite_post_listing_some[OF Some])
  obtain fl where r: "finite_read_check_rows \<Theta> (\<lambda>_. None) empty_share_state ns = (fl,finite_indexed_table_rows \<Theta> ns)"
    and g: "(if fl then finite_formed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)
      else finite_indexed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)) =
      finite_indexed_table_graph_check P e u (finite_indexed_table_rows \<Theta> ns)"
    by (rule finite_read_check_rows_indexed[OF listed finite_reads_calls_none, of \<Theta> P e u]) blast+
  show ?thesis using Some by (simp only: finite_table_checked_indexed r g option.simps prod.simps Let_def)
qed

end
