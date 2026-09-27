theory Factor_Resolution_Graph_Checks
  imports Factor_Resolution_Commitments
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

lemma finite_node_proof_links:
  "finite_node_proof (Suc k) N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_proof k N m)) (finite_node_links N nd))"
proof -
  have "ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,finite_node_proof k N m)) (finite_premise_nodes N nd s e p))
      (finite_schema_premises (resolution_node_schema nd))) =
    fimage (\<lambda>(s,m). (s,finite_node_proof k N m)) (finite_node_links N nd)"
    by (rule fset_eqI) (force simp: finite_node_links_def resolution_fset_simps)
  then show ?thesis by simp
qed

section \<open>A certificate is built once per node\<close>

text \<open>
  The fuel of @{const finite_node_proof} truncates only a chain of reads longer than it; every chain decreases in the
  reach, so fuel at least a node's reach gives the same certificate, on every state. The node's certificate is that one.
\<close>

lemma finite_node_proof_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> fcard (resolution_reach N nd) \<le> k' \<Longrightarrow>
    finite_node_proof k N nd = finite_node_proof k' N nd"
proof (induction k arbitrary: nd k')
  case 0
  then show ?case using finite_reach_positive[OF 0(1)] 0(2) by linarith
next
  case (Suc k)
  have "k' \<noteq> 0" using Suc.prems(3) finite_reach_positive[OF Suc.prems(1)] by linarith
  then obtain k'' where k': "k' = Suc k''" by (cases k') auto
  have "(\<lambda>(s,m). (s,finite_node_proof k N m)) x = (\<lambda>(s,m). (s,finite_node_proof k'' N m)) x"
    if x: "x |\<in>| finite_node_links N nd" for x
  proof -
    obtain s m where xs: "x = (s,m)" by (cases x) auto
    have mN: "m |\<in>| N" and less: "fcard (resolution_reach N m) < fcard (resolution_reach N nd)"
      using finite_node_links_reach[OF x[unfolded xs]] Suc.prems(1) by auto
    have "fcard (resolution_reach N m) \<le> k" using less Suc.prems(2) by linarith
    moreover have "fcard (resolution_reach N m) \<le> k''" using less Suc.prems(3) unfolding k' by linarith
    ultimately have "finite_node_proof k N m = finite_node_proof k'' N m" by (rule Suc.IH[OF mN])
    then show ?thesis using xs by simp
  qed
  from fimage_cong[where N="finite_node_links N nd", OF refl this] show ?case
    unfolding k' finite_node_proof_links by simp
qed

definition finite_node_certificate ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'c) finite_schema_proof" where
  "finite_node_certificate N nd = finite_node_proof (fcard (resolution_reach N nd)) N nd"

lemma finite_node_certificate_fuel:
  "nd |\<in>| N \<Longrightarrow> fcard (resolution_reach N nd) \<le> k \<Longrightarrow> finite_node_proof k N nd = finite_node_certificate N nd"
  unfolding finite_node_certificate_def by (rule finite_node_proof_fuel) simp_all

lemma finite_node_certificate_links:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_certificate N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (fimage (\<lambda>(s,m). (s,finite_node_certificate N m)) (finite_node_links N nd))"
proof -
  obtain j where j: "fcard (resolution_reach N nd) = Suc j"
    using finite_reach_positive[OF nd] by (cases "fcard (resolution_reach N nd)") auto
  have "(\<lambda>(s,m). (s,finite_node_proof j N m)) x = (\<lambda>(s,m). (s,finite_node_certificate N m)) x"
    if x: "x |\<in>| finite_node_links N nd" for x
  proof -
    obtain s m where xs: "x = (s,m)" by (cases x) auto
    have mN: "m |\<in>| N" and "fcard (resolution_reach N m) < fcard (resolution_reach N nd)"
      using finite_node_links_reach[OF x[unfolded xs]] nd by auto
    then have "fcard (resolution_reach N m) \<le> j" using j by simp
    then show ?thesis using finite_node_certificate_fuel[OF mN] xs by simp
  qed
  from fimage_cong[where N="finite_node_links N nd", OF refl this] show ?thesis
    unfolding finite_node_certificate_def[of N nd] j finite_node_proof_links by simp
qed

lemma finite_state_node_certificate:
  assumes nd: "nd |\<in>| N"
  shows "finite_node_proof (fcard N) N nd = finite_node_certificate N nd"
proof (rule finite_node_certificate_fuel[OF nd])
  show "fcard (resolution_reach N nd) \<le> fcard N" by (rule fcard_mono) auto
qed

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

lemma finite_certificate_step_member:
  "x |\<in>| finite_certificate_step (finite_node_ranked N) T r \<longleftrightarrow> x |\<in>| T \<or> (\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and>
    x = (m,Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m))))"
  by (force simp: finite_certificate_step_def finite_node_ranked_def resolution_fset_simps)

lemma finite_certificate_table_fold:
  assumes "sorted_wrt (<) rs"
    and "T = fimage (\<lambda>m. (m,finite_node_certificate N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
    and "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. fcard (resolution_reach N m) < j)"
  shows "foldl (finite_certificate_step (finite_node_ranked N)) T rs = fimage (\<lambda>m. (m,finite_node_certificate N m)) N"
  using assms
proof (induction rs arbitrary: T)
  case Nil
  have "ffilter (\<lambda>m. True) N = N" by (simp add: fset_eq_iff)
  then show ?case using Nil by simp
next
  case (Cons r rs)
  have sorted: "sorted_wrt (<) rs" and above: "\<forall>j\<in>set rs. r < j" using Cons.prems(1) by simp_all
  have child: "the (finite_relation_option T m') = finite_node_certificate N m'"
    if m: "m |\<in>| N" "fcard (resolution_reach N m) = r" and link: "(s,m') |\<in>| finite_node_links N m" for m s m'
  proof -
    have m'N: "m' |\<in>| N" and less: "fcard (resolution_reach N m') < r"
      using finite_node_links_reach(1)[OF link] finite_node_links_reach(2)[OF link m(1)] m(2) by auto
    have "fcard (resolution_reach N m') \<notin> set (r#rs)" using less above by auto
    then have "m' |\<in>| ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set (r#rs)) N" using m'N by simp
    then show ?thesis unfolding Cons.prems(2) by (rule finite_relation_option_keyed)
  qed
  have made: "Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m)) = finite_node_certificate N m"
    if m: "m |\<in>| N" "fcard (resolution_reach N m) = r" for m
  proof -
    have "fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m) =
        fimage (\<lambda>(s,m'). (s,finite_node_certificate N m')) (finite_node_links N m)"
      by (rule fimage_cong[OF refl]) (auto simp: child[OF m])
    then show ?thesis using finite_node_certificate_links[OF m(1)] by simp
  qed
  have rr: "r \<notin> set rs" using above by auto
  have step: "finite_certificate_step (finite_node_ranked N) T r =
      fimage (\<lambda>m. (m,finite_node_certificate N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| finite_certificate_step (finite_node_ranked N) T r \<longleftrightarrow>
      x |\<in>| fimage (\<lambda>m. (m,finite_node_certificate N m)) (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set rs) N)"
    proof -
      have "(\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m)))) \<longleftrightarrow>
          (\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate N m))"
      proof
        assume "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m)))"
        then obtain m where "m |\<in>| N" "fcard (resolution_reach N m) = r" "x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m)))" by blast
        then show "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate N m)" using made by auto
      next
        assume "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,finite_node_certificate N m)"
        then obtain m where "m |\<in>| N" "fcard (resolution_reach N m) = r" "x = (m,finite_node_certificate N m)" by blast
        then show "\<exists>m. m |\<in>| N \<and> fcard (resolution_reach N m) = r \<and> x = (m,Schema_Proof (resolution_node_clause m)
            (finite_node_values m) (fimage (\<lambda>(s,m'). (s,the (finite_relation_option T m'))) (finite_node_links N m)))"
          using made by auto
      qed
      then show ?thesis unfolding finite_certificate_step_member Cons.prems(2) using rr
        by (force simp: resolution_fset_simps)
    qed
  qed
  have processed: "\<forall>m. m |\<in>| N \<longrightarrow> fcard (resolution_reach N m) \<notin> set rs \<longrightarrow> (\<forall>j\<in>set rs. fcard (resolution_reach N m) < j)"
    using Cons.prems(3) above by fastforce
  show ?case using Cons.IH[OF sorted step processed] by simp
qed

lemma finite_certificate_table_exact:
  "finite_certificate_table (finite_node_ranked N) = fimage (\<lambda>m. (m,finite_node_certificate N m)) N"
proof -
  have ranks: "fimage (\<lambda>(m,k,L). k) (finite_node_ranked N) = fimage ((\<lambda>m. fcard (resolution_reach N m))) N"
    by (force simp: fset_eq_iff finite_node_ranked_def resolution_fset_simps)
  have "{||} = fimage (\<lambda>m. (m,finite_node_certificate N m))
      (ffilter (\<lambda>m. fcard (resolution_reach N m) \<notin> set (sorted_list_of_fset (fimage ((\<lambda>m. fcard (resolution_reach N m))) N))) N)"
    by (force simp: fset_eq_iff resolution_fset_simps)
  then show ?thesis unfolding finite_certificate_table_def ranks
    by (rule finite_certificate_table_fold[rotated]) (auto simp: sorted_list_of_fset.rep_eq)
qed

lemma finite_certificate_table_proof:
  "m |\<in>| N \<Longrightarrow> the (finite_relation_option (finite_certificate_table (finite_node_ranked N)) m) = finite_node_proof (fcard N) N m"
  by (simp add: finite_certificate_table_exact finite_relation_option_keyed finite_state_node_certificate)

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

section \<open>The graph reading gives the tree check\<close>

theorem finite_state_graph_check_accepts:
  assumes nd: "nd |\<in>| N" and check: "finite_state_graph_check P d t N nd"
  shows "finite_checks_schema_proof P (finite_node_proof (fcard N) N nd) d t"
proof -
  note char = check[unfolded finite_state_graph_check_iff[OF nd]]
  have node: "finite_checks_schema_proof P (finite_node_certificate N n) (resolution_node_site n)
      (finite_residual_term (resolution_node_call n))" if "n |\<in>| finite_link_reach N nd" for n
    using that
  proof (induction "fcard (resolution_reach N n)" arbitrary: n rule: less_induct)
    case less
    have lf: "finite_relation_functional (finite_node_links N n)"
      and adm: "finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n)"
      using char less.prems by auto
    have nN: "n |\<in>| N" using less.prems finite_link_reach(2)[OF nd] by auto
    let ?B = "fimage (\<lambda>(s,m). (s,finite_node_certificate N m)) (finite_node_links N n)"
    have Bf: "finite_relation_functional ?B"
    proof (rule finite_relation_functional_intro)
      fix s p p' assume "(s,p) |\<in>| ?B" "(s,p') |\<in>| ?B"
      then obtain m m' where "(s,m) |\<in>| finite_node_links N n" "p = finite_node_certificate N m"
          "(s,m') |\<in>| finite_node_links N n" "p' = finite_node_certificate N m'"
        by (force simp: resolution_fset_simps)
      then show "p = p'" using finite_relation_functional_at[OF lf] by metis
    qed
    have read: "finite_node_link_claims N n |\<in>| finite_admitted_premise_readings P (resolution_node_site n)
        (resolution_node_clause n) (finite_node_values n) (finite_residual_term (resolution_node_call n))"
      using adm by (simp add: finite_admitted_premise_reading_exact)
    have dom: "fimage fst ?B = fimage fst (finite_node_link_claims N n)"
      by (rule fset_eqI) (force simp: finite_node_link_claims_def resolution_fset_simps)
    have children: "\<forall>s p. (s,p) |\<in>| ?B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| finite_node_link_claims N n \<and> finite_checks_schema_proof P p e x)"
    proof (intro allI impI)
      fix s p assume "(s,p) |\<in>| ?B"
      then obtain m where link: "(s,m) |\<in>| finite_node_links N n" and p: "p = finite_node_certificate N m"
        by (force simp: resolution_fset_simps)
      have mR: "m |\<in>| finite_link_reach N nd" using finite_link_reach(4)[OF nd less.prems link] .
      have "fcard (resolution_reach N m) < fcard (resolution_reach N n)" using finite_node_links_reach(2)[OF link nN] .
      then have "finite_checks_schema_proof P p (resolution_node_site m) (finite_residual_term (resolution_node_call m))"
        using less.hyps[OF _ mR] p by blast
      moreover have "(s,resolution_node_site m,finite_residual_term (resolution_node_call m)) |\<in>| finite_node_link_claims N n"
        using link by (force simp: finite_node_link_claims_def resolution_fset_simps)
      ultimately show "\<exists>e x. (s,e,x) |\<in>| finite_node_link_claims N n \<and> finite_checks_schema_proof P p e x" by blast
    qed
    show ?case
      unfolding finite_node_certificate_links[OF nN] finite_checks_schema_proof_node
      using Bf read dom children by blast
  qed
  have "finite_checks_schema_proof P (finite_node_certificate N nd) d t"
    using node[OF finite_link_reach(1)[OF nd]] char by simp
  then show ?thesis by (simp add: finite_state_node_certificate[OF nd])
qed

section \<open>At every found state the graph reading holds\<close>

lemma fimage_fst_certificates:
  "fimage fst (fimage (\<lambda>(s,m). (s,f m)) L) = fimage fst L"
  by (rule fset_eqI) (force simp: resolution_fset_simps)

theorem finite_state_graph_check_found:
  assumes I: "resolution_invariant P d t st" and closed: "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and root: "resolution_node_position nd=[]"
  shows "finite_state_graph_check P d t (resolution_nodes st) nd"
proof -
  let ?N = "resolution_nodes st"
  have Pf: "finite_system_formed P" and placed: "resolution_nodes_placed P d t st"
    and distinct: "resolution_positions_distinct st"
    using I by (simp_all add: resolution_invariant_def)
  have dist: "\<And>m m'. m |\<in>| ?N \<Longrightarrow> m' |\<in>| ?N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    using distinct by (simp add: resolution_positions_distinct_def)
  have rootsite: "resolution_node_site nd=d" and rootcall: "resolution_node_call nd=finite_exact_term_pattern t"
    using placed nd root by (simp_all add: resolution_nodes_placed_def)
  have clauses: "finite_relation_functional (finite_system_clauses P)" using Pf by (simp add: finite_system_formed_def)
  have each: "finite_relation_functional (finite_node_links ?N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims ?N n)" if n: "n |\<in>| ?N" for n
  proof -
    have linked: "resolution_node_linked P st n" using placed n by (simp add: resolution_nodes_placed_def)
    have clause: "((resolution_node_site n,resolution_node_clause n),resolution_node_schema n) |\<in>| finite_system_clauses P"
      using linked by (simp add: resolution_node_linked_def)
    have prem: "finite_relation_functional (finite_schema_premises (resolution_node_schema n))"
      using finite_system_clause_formed[OF Pf clause] by (simp add: finite_schema_formed_def)
    have links: "finite_relation_functional (finite_node_links ?N n)" by (rule finite_node_links_functional[OF dist prem])
    have "fcard (resolution_reach ?N n) \<le> fcard ?N" by (rule fcard_mono) auto
    from finite_node_proof_accepted[OF I closed n this]
    have tree: "finite_checks_schema_proof P (finite_node_certificate ?N n) (resolution_node_site n)
        (finite_residual_term (resolution_node_call n))"
      by (simp add: finite_state_node_certificate[OF n])
    let ?B = "fimage (\<lambda>(s,m). (s,finite_node_certificate ?N m)) (finite_node_links ?N n)"
    obtain H where read: "H |\<in>| finite_admitted_premise_readings P (resolution_node_site n) (resolution_node_clause n)
        (finite_node_values n) (finite_residual_term (resolution_node_call n))"
      and dom: "fimage fst ?B = fimage fst H"
      using tree unfolding finite_node_certificate_links[OF n] finite_checks_schema_proof_node by blast
    have adm: "finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) H"
      using read by (simp add: finite_admitted_premise_reading_exact)
    obtain S where Sin: "((resolution_node_site n,resolution_node_clause n),S) |\<in>| finite_system_clauses P"
      and HS: "H = finite_instantiated_premises S (finite_node_values n)"
      using read by (auto simp: finite_admitted_premise_readings_def)
    have S: "S = resolution_node_schema n" using finite_relation_functional_at[OF clauses Sin clause] .
    have Vf: "finite_relation_functional (finite_node_values n)"
      using adm by (auto simp: finite_admitted_schema_instance_def finite_schema_instance_def finite_term_bindings_formed_def)
    have domL: "fimage fst (finite_node_links ?N n) = fimage fst H"
      using trans[OF sym[OF fimage_fst_certificates[of "finite_node_certificate ?N" "finite_node_links ?N n"]] dom] .
    have pt: "(s,e,x) |\<in>| H \<longleftrightarrow> (s,e,x) |\<in>| finite_node_link_claims ?N n" for s e x
      proof
        assume zH: "(s,e,x) |\<in>| H"
        then obtain p where sp: "(s,e,p) |\<in>| finite_schema_premises (resolution_node_schema n)"
          and xp: "x |\<in>| finite_pattern_instances (finite_node_values n) p"
          unfolding HS S finite_instantiated_premises_member by blast
        have "s |\<in>| fimage fst H" using zH by (force simp: resolution_fset_simps)
        then obtain m where sm: "(s,m) |\<in>| finite_node_links ?N n"
          using domL by (force simp: fset_eq_iff resolution_fset_simps)
        then obtain e' p' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and m: "m |\<in>| finite_premise_nodes ?N n s e' p'" by (auto simp: finite_node_links_member)
        have "(e',p') = (e,p)" using finite_relation_functional_at[OF prem sp' sp] .
        then have same: "e'=e \<and> p'=p" by simp
        have site: "resolution_node_site m = e" and inst: "finite_residual_term (resolution_node_call m) |\<in>|
            finite_pattern_instances (finite_node_values n) p"
          using finite_premise_nodes_member(2,3)[OF m] same by auto
        have "x = finite_residual_term (resolution_node_call m)"
          using finite_pattern_instance_unique[OF Vf] xp inst by (simp add: finite_pattern_instances_member)
        then show "(s,e,x) |\<in>| finite_node_link_claims ?N n"
          using sm site by (force simp: finite_node_link_claims_def resolution_fset_simps)
      next
        assume "(s,e,x) |\<in>| finite_node_link_claims ?N n"
        then obtain m where sm: "(s,m) |\<in>| finite_node_links ?N n" and ex: "e=resolution_node_site m"
            "x=finite_residual_term (resolution_node_call m)"
          by (force simp: finite_node_link_claims_def resolution_fset_simps)
        then obtain e' p' where sp': "(s,e',p') |\<in>| finite_schema_premises (resolution_node_schema n)"
          and m: "m |\<in>| finite_premise_nodes ?N n s e' p'" by (auto simp: finite_node_links_member)
        show "(s,e,x) |\<in>| H"
          using finite_premise_nodes_member(2,3)[OF m] sp' ex
          unfolding HS S finite_instantiated_premises_member by blast
      qed
    have "H = finite_node_link_claims ?N n" by (intro fset_eqI) (auto simp: split_paired_all pt)
    then show ?thesis using links adm by simp
  qed
  show ?thesis unfolding finite_state_graph_check_iff[OF nd]
    using rootsite rootcall each finite_link_reach(2)[OF nd] by auto
qed

corollary finite_state_graph_check_found_exact:
  assumes "resolution_invariant P d t st" and "resolution_pending st={||}"
    and nd: "nd |\<in>| resolution_nodes st" and "resolution_node_position nd=[]"
  shows "finite_state_graph_check P d t (resolution_nodes st) nd \<longleftrightarrow>
    finite_checks_schema_proof P (finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st) nd) d t"
  using finite_state_graph_check_found[OF assms] finite_state_graph_check_accepts[OF nd] by blast

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

lemma finite_state_verdicts_accepted:
  "finite_state_verdicts P d t st = fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) (finite_state_proofs st)"
proof -
  let ?N = "resolution_nodes st"
  have "(\<lambda>nd. let c = finite_node_proof (fcard ?N) ?N nd in
      (c,finite_state_graph_check P d t ?N nd \<or> finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. (finite_node_proof (fcard ?N) ?N nd,finite_checks_schema_proof P (finite_node_proof (fcard ?N) ?N nd) d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that finite_state_graph_check_accepts[of x ?N P d t] by (auto simp: Let_def)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this]
  have "finite_state_verdicts P d t st = fimage (\<lambda>nd. (finite_node_proof (fcard ?N) ?N nd,
      finite_checks_schema_proof P (finite_node_proof (fcard ?N) ?N nd) d t)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N)"
    by (simp add: finite_state_verdicts_def Let_def)
  then show ?thesis by (simp add: finite_state_proofs_def fset.map_comp comp_def)
qed

lemma finite_outcome_result_verdicts [code]:
  "finite_outcome_result P d t R = (let V = ffUnion (fimage (finite_state_verdicts P d t) (resolution_found R));
      C = fimage fst V; A = fimage fst (ffilter snd V) in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R |\<union>| fimage Resolution_Refused C))"
proof -
  let ?C = "ffUnion (fimage finite_state_proofs (resolution_found R))"
  have V: "ffUnion (fimage (finite_state_verdicts P d t) (resolution_found R)) =
      fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C"
    by (rule fset_eqI) (force simp: finite_state_verdicts_accepted resolution_fset_simps)
  have C: "fimage fst (fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C) = ?C"
    by (rule fset_eqI) (force simp: resolution_fset_simps)
  have A: "fimage fst (ffilter snd (fimage (\<lambda>c. (c,finite_checks_schema_proof P c d t)) ?C)) =
      ffilter (\<lambda>p. finite_checks_schema_proof P p d t) ?C"
    by (rule fset_eqI) (force simp: resolution_fset_simps)
  show ?thesis unfolding finite_outcome_result_def Let_def V C A ..
qed

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

lemma finite_state_graph_code_check:
  assumes nd: "nd |\<in>| N"
  shows "finite_state_graph_code P d t (finite_node_ranked N) nd = finite_state_graph_check P d t N nd"
proof -
  have "fBall (finite_node_ranked N) (\<lambda>(m,k,L). m |\<in>| finite_link_reach N nd \<longrightarrow> \<Phi> m L) \<longleftrightarrow>
      fBall (finite_link_reach N nd) (\<lambda>m. \<Phi> m (finite_node_links N m))" for \<Phi>
    using finite_link_reach(2)[OF nd] by (force simp: finite_node_ranked_def resolution_fset_simps)
  note ball = this
  let ?Q = "\<lambda>n. fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m')))
    (finite_node_links N n)"
  have formed: "fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (?Q n)) \<longleftrightarrow>
    finite_system_formed P \<and> fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n) \<and>
      finite_admitted_instance_at P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (?Q n))"
    using finite_link_reach(1)[OF nd] by (auto simp: finite_admitted_instance_formed)
  show ?thesis
    using ball[of "\<lambda>m L. finite_relation_functional L \<and> finite_admitted_instance_at P (resolution_node_site m)
      (resolution_node_clause m) (finite_node_values m) (finite_residual_term (resolution_node_call m))
      (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L)"]
    by (simp add: finite_state_graph_code_def finite_state_graph_check_iff[OF nd] Let_def finite_link_reach_def[symmetric]
      finite_node_link_claims_def formed)
qed

lemma finite_state_verdicts_code [code]:
  "finite_state_verdicts P d t st = (let N = resolution_nodes st; K = finite_node_ranked N;
      T = finite_certificate_table K in
    fimage (\<lambda>nd. let c = the (finite_relation_option T nd) in
      (c,finite_state_graph_code P d t K nd \<or> finite_checks_schema_proof P c d t))
      (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
proof -
  let ?N = "resolution_nodes st"
  have "(\<lambda>nd. let c = finite_node_proof (fcard ?N) ?N nd in
      (c,finite_state_graph_check P d t ?N nd \<or> finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (finite_relation_option (finite_certificate_table (finite_node_ranked ?N)) nd) in
      (c,finite_state_graph_code P d t (finite_node_ranked ?N) nd \<or> finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that by (simp add: finite_certificate_table_proof finite_state_graph_code_check)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    by (simp add: finite_state_verdicts_def Let_def)
qed

lemma finite_state_proofs_table [code]:
  "finite_state_proofs st = (let N = resolution_nodes st; T = finite_certificate_table (finite_node_ranked N) in
    fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))"
proof -
  let ?N = "resolution_nodes st"
  have "finite_node_proof (fcard ?N) ?N x = the (finite_relation_option (finite_certificate_table (finite_node_ranked ?N)) x)"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
    using that by (simp add: finite_certificate_table_proof)
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    by (simp add: finite_state_proofs_def Let_def)
qed

export_code finite_program_resolution finite_committed_resolution checking SML

end
