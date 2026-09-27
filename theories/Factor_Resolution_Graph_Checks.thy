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
    using I by (simp_all add: resolution_invariant_in_def)
  have dist: "\<And>m m'. m |\<in>| ?N \<Longrightarrow> m' |\<in>| ?N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    using distinct by (simp add: resolution_positions_distinct_def)
  have rootsite: "resolution_node_site nd=d" and rootcall: "resolution_node_call nd=finite_exact_term_pattern t"
    using placed nd root by (simp_all add: resolution_nodes_placed_in_def)
  have clauses: "finite_relation_functional (finite_system_clauses P)" using Pf by (simp add: finite_system_formed_def)
  have each: "finite_relation_functional (finite_node_links ?N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims ?N n)" if n: "n |\<in>| ?N" for n
  proof -
    have linked: "resolution_node_linked P st n" using placed n by (simp add: resolution_nodes_placed_in_def)
    have clause: "((resolution_node_site n,resolution_node_clause n),resolution_node_schema n) |\<in>| finite_system_clauses P"
      using linked by (simp add: resolution_node_linked_in_def)
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
  then show ?thesis by (simp add: finite_state_proofs_def finite_state_proofs_in_def fset.map_comp comp_def)
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
  show ?thesis unfolding finite_outcome_result_def finite_outcome_result_in_def finite_state_proofs_empty Let_def V C A ..
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
    by (simp add: finite_state_proofs_def finite_state_proofs_in_def Let_def)
qed

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

lemma finite_share_rows_exact:
  assumes "keyed_state_represents q T" "table_formed T"
  shows "\<exists>T'. keyed_state_represents (snd (finite_share_rows ms q)) T' \<and> table_formed T' \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u) \<and>
    map fst (fst (finite_share_rows ms q)) = ms \<and>
    (\<forall>row\<in>set (fst (finite_share_rows ms q)). fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
      reference_term T' (snd (snd row)) = Some (fst (snd row)))"
  using assms
proof (induction ms arbitrary: q T)
  case Nil
  then show ?case by auto
next
  case (Cons m ms)
  let ?x = "finite_residual_term (resolution_node_call m)"
  obtain r q1 where k: "keyed_share_term ?x q = (r,q1)" by (cases "keyed_share_term ?x q")
  let ?T1 = "snd (share_term ?x T)"
  have e: "r = fst (share_term ?x T)" and rep1: "keyed_state_represents q1 ?T1"
    using keyed_share_term_exact[OF Cons.prems(1), of ?x] k by simp_all
  have f1: "table_formed ?T1" and r1: "reference_term ?T1 r = Some ?x"
    using share_term_exact[OF Cons.prems(2), of ?x] e by simp_all
  obtain rows q2 where s: "finite_share_rows ms q1 = (rows,q2)" by (cases "finite_share_rows ms q1")
  from Cons.IH[OF rep1 f1] s obtain T' where T': "keyed_state_represents q2 T'" "table_formed T'"
      "\<forall>i u. reference_term ?T1 i = Some u \<longrightarrow> reference_term T' i = Some u" "map fst rows = ms"
      "\<forall>row\<in>set rows. fst (snd row) = finite_residual_term (resolution_node_call (fst row)) \<and>
        reference_term T' (snd (snd row)) = Some (fst (snd row))"
    by auto
  have pres: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
    using T'(3) share_term_preserves[of T _ _ ?x] by blast
  have r': "reference_term T' r = Some ?x" using T'(3) r1 by blast
  show ?case by (rule exI[of _ T']) (use k s T' pres r' in \<open>auto simp: Let_def\<close>)
qed

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

lemma finite_indexed_premise_nodes_exact:
  assumes distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
    and PI: "\<And>q m r. RBT.lookup PI q = Some (m,r) \<longleftrightarrow> m |\<in>| N \<and> resolution_node_position m = q \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and G: "\<And>r m. m \<in> set (finite_group_lookup G r) \<longleftrightarrow> m |\<in>| N \<and>
      finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
    and keyed: "\<And>m. m |\<in>| N \<Longrightarrow> \<exists>r. finite_term_keyed q0 r (finite_residual_term (resolution_node_call m))"
  shows "finite_indexed_premise_nodes PI G q0 nd s e p = finite_premise_nodes N nd s e p"
proof -
  let ?q = "resolution_node_position nd@[s]"
  let ?I = "finite_pattern_instances (finite_node_values nd) p"
  let ?IR = "fimage (\<lambda>x. fst (keyed_share_term x q0)) ?I"
  let ?res = "\<lambda>m. finite_residual_term (resolution_node_call m)"
  let ?F = "ffilter (\<lambda>m. resolution_node_site m=e \<and> finite_residual_term (resolution_node_call m) |\<in>| ?I) N"
  have K: "r |\<in>| ?IR \<longleftrightarrow> ?res m |\<in>| ?I" if key: "finite_term_keyed q0 r (?res m)" for m r
  proof -
    have kx: "fst (keyed_share_term x q0) = r \<longleftrightarrow> x = ?res m" for x using key by (simp add: finite_term_keyed_def)
    show ?thesis
    proof
      assume "r |\<in>| ?IR"
      then obtain x where x: "x |\<in>| ?I" "r = fst (keyed_share_term x q0)" by auto
      then have "x = ?res m" using kx[of x] by simp
      then show "?res m |\<in>| ?I" using x(1) by simp
    next
      assume "?res m |\<in>| ?I"
      then show "r |\<in>| ?IR" using kx[of "?res m"] by force
    qed
  qed
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
    then show ?thesis using v K[OF m1(3)] by simp
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
  show ?thesis unfolding finite_indexed_premise_nodes_def finite_premise_nodes_def Let_def C L ..
qed

definition finite_indexed_links ::
    "('s list, ('a,'s::linorder,'d,'c) resolution_node \<times> nat) rbt \<Rightarrow> (nat, ('a,'s,'d,'c) resolution_node list) rbt \<Rightarrow>
      share_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('s \<times> ('a,'s,'d,'c) resolution_node) fset" where
  "finite_indexed_links PI G q0 nd = ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,m)) (finite_indexed_premise_nodes PI G q0 nd s e p))
    (finite_schema_premises (resolution_node_schema nd)))"

definition finite_indexed_links_rows ::
    "('a,'s::linorder,'d,'c) resolution_node list \<Rightarrow> (('a,'s,'d,'c) resolution_node \<times> ('s \<times> ('a,'s,'d,'c) resolution_node) fset) list" where
  "finite_indexed_links_rows ns = (case finite_share_rows ns (RBT.empty,0,[]) of (rows,q0) \<Rightarrow>
    map (\<lambda>m. (m,finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m)) ns)"

text \<open>
  The two indexes are invariants of the walk over the nodes: its code equation builds them once from the shared rows,
  beside the definition, which builds them within the function mapped over the nodes (task 873, from #851's
  attribution: once per node, quadratic in the nodes). Equal by definition on every input; every statement
  and proof reads the definition.
\<close>

lemma finite_indexed_links_rows_once [code]:
  "finite_indexed_links_rows ns = (case finite_share_rows ns (RBT.empty,0,[]) of (rows,q0) \<Rightarrow>
    let PI = finite_position_index rows; G = finite_group_index rows in
    map (\<lambda>m. (m,finite_indexed_links PI G q0 m)) ns)"
  by (simp add: finite_indexed_links_rows_def Let_def split: prod.split)

lemma finite_indexed_links_rows_exact:
  assumes listed: "finite_post_listed (fset N) ns"
  shows "finite_indexed_links_rows ns = map (\<lambda>m. (m,finite_node_links N m)) ns"
proof -
  note P = finite_post_listed_positions[OF listed]
  let ?res = "\<lambda>m. finite_residual_term (resolution_node_call m)"
  obtain rows q0 where run: "finite_share_rows ns (RBT.empty,0,[]) = (rows,q0)" by (cases "finite_share_rows ns (RBT.empty,0,[])")
  have start: "keyed_state_represents (RBT.empty,0,[]) []" by (simp add: keyed_state_represents_def keyed_reference_state_def)
  obtain T' where rep: "keyed_state_represents q0 T'" and ft: "table_formed T'" and fsts: "map fst rows = ns"
      and rw: "\<forall>row\<in>set rows. fst (snd row) = ?res (fst row) \<and> reference_term T' (snd (snd row)) = Some (fst (snd row))"
    using finite_share_rows_exact[OF start table_formed_empty, of ns] run by auto
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
  have links: "finite_indexed_links (finite_position_index rows) (finite_group_index rows) q0 m = finite_node_links N m" for m
    by (simp add: finite_indexed_links_def finite_node_links_def finite_indexed_premise_nodes_exact[OF dist PI G ex])
  show ?thesis using run links by (simp add: finite_indexed_links_rows_def)
qed

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

lemma finite_indexed_certificates_fold:
  assumes listed: "finite_post_listed (fset N) (pre @ rest)"
    and T: "\<And>p c. RBT.lookup T p = Some c \<longleftrightarrow> (\<exists>m\<in>set pre. resolution_node_position m = p \<and> c = finite_node_certificate N m)"
  shows "RBT.lookup (foldl finite_indexed_certificate_step T (map (\<lambda>m. (m,finite_node_links N m)) rest)) p = Some c \<longleftrightarrow>
    (\<exists>m\<in>set (pre @ rest). resolution_node_position m = p \<and> c = finite_node_certificate N m)"
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
  have looked: "the (RBT.lookup T (resolution_node_position m')) = finite_node_certificate N m'"
    if "(s,m') |\<in>| finite_node_links N m" for s m'
    using Cons.prems(2)[of "resolution_node_position m'" "finite_node_certificate N m'"] earlier[OF that] by auto
  have made: "Schema_Proof (resolution_node_clause m) (finite_node_values m)
      (fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) (finite_node_links N m)) =
    finite_node_certificate N m"
  proof -
    have "fimage (\<lambda>(s,m'). (s,the (RBT.lookup T (resolution_node_position m')))) (finite_node_links N m) =
        fimage (\<lambda>(s,m'). (s,finite_node_certificate N m')) (finite_node_links N m)"
      by (rule fimage_cong[OF refl]) (auto simp: looked)
    then show ?thesis using finite_node_certificate_links[OF mN] by simp
  qed
  have fresh: "resolution_node_position m' \<noteq> resolution_node_position m" if "m' \<in> set pre" for m'
    using sw that by (auto simp: sorted_wrt_append)
  have T': "RBT.lookup (finite_indexed_certificate_step T (m,finite_node_links N m)) p = Some c \<longleftrightarrow>
      (\<exists>m'\<in>set (pre @ [m]). resolution_node_position m' = p \<and> c = finite_node_certificate N m')" for p c
    using Cons.prems(2)[of p c] made fresh
    by (auto simp: finite_indexed_certificate_step_def finite_tree_insert_lookup)
  have "finite_post_listed (fset N) ((pre @ [m]) @ rest)" using Cons.prems(1) by simp
  from Cons.IH[OF this T'] show ?case by simp
qed

lemma finite_indexed_certificates_exact:
  assumes listed: "finite_post_listed (fset N) ns" and m: "m |\<in>| N"
  shows "the (RBT.lookup (finite_indexed_certificates (map (\<lambda>m. (m,finite_node_links N m)) ns)) (resolution_node_position m)) =
    finite_node_proof (fcard N) N m"
proof -
  have "RBT.lookup (finite_indexed_certificates (map (\<lambda>m. (m,finite_node_links N m)) ns)) (resolution_node_position m) =
      Some (finite_node_certificate N m)"
    using finite_indexed_certificates_fold[of N "[]" ns RBT.empty "resolution_node_position m" "finite_node_certificate N m"]
      listed m by (auto simp: finite_indexed_certificates_def finite_post_listed_def)
  then show ?thesis by (simp add: finite_state_node_certificate[OF m])
qed

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

lemma finite_indexed_graph_check_exact:
  assumes listed: "finite_post_listed (fset N) ns" and nd: "nd |\<in>| N"
  shows "finite_indexed_graph_check P d t (map (\<lambda>m. (m,finite_node_links N m)) ns) nd = finite_state_graph_check P d t N nd"
proof -
  let ?R = "finite_indexed_reach (map (\<lambda>m. (m,finite_node_links N m)) ns) nd"
  let ?\<Phi> = "\<lambda>n. finite_relation_functional (finite_node_links N n) \<and>
    finite_admitted_instance_at P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
      (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n)"
  have setns: "set ns = fset N" using listed by (simp add: finite_post_listed_def)
  have A: "list_all (\<lambda>(m,L). RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional L \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L))
      (map (\<lambda>m. (m,finite_node_links N m)) ns) \<longleftrightarrow> fBall (finite_link_reach N nd) ?\<Phi>"
  proof -
    have "list_all (\<lambda>(m,L). RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> finite_relation_functional L \<and>
      finite_admitted_instance_at P (resolution_node_site m) (resolution_node_clause m) (finite_node_values m)
        (finite_residual_term (resolution_node_call m))
        (fimage (\<lambda>(s,m'). (s,resolution_node_site m',finite_residual_term (resolution_node_call m'))) L))
      (map (\<lambda>m. (m,finite_node_links N m)) ns) \<longleftrightarrow>
      (\<forall>m\<in>fset N. RBT.lookup ?R (resolution_node_position m) \<noteq> None \<longrightarrow> ?\<Phi> m)"
      by (simp add: list_all_iff setns finite_node_link_claims_def)
    also have "\<dots> \<longleftrightarrow> (\<forall>m\<in>fset N. m |\<in>| finite_link_reach N nd \<longrightarrow> ?\<Phi> m)"
      by (rule ball_cong[OF refl]) (simp only: finite_indexed_reach_exact[OF listed nd])
    also have "\<dots> \<longleftrightarrow> fBall (finite_link_reach N nd) ?\<Phi>" using finite_link_reach(2)[OF nd] by auto
    finally show ?thesis .
  qed
  have B: "fBall (finite_link_reach N nd) (\<lambda>n. finite_relation_functional (finite_node_links N n) \<and>
      finite_admitted_schema_instance P (resolution_node_site n) (resolution_node_clause n) (finite_node_values n)
        (finite_residual_term (resolution_node_call n)) (finite_node_link_claims N n)) \<longleftrightarrow>
    finite_system_formed P \<and> fBall (finite_link_reach N nd) ?\<Phi>"
    using finite_link_reach(1)[OF nd] by (auto simp: finite_admitted_instance_formed)
  show ?thesis
    unfolding finite_indexed_graph_check_def Let_def finite_state_graph_check_iff[OF nd] by (simp only: A B)
qed

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
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_state_verdicts_code)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have "(\<lambda>nd. let c = finite_node_proof (fcard ?N) ?N nd in
      (c,finite_state_graph_check P d t ?N nd \<or> finite_checks_schema_proof P c d t)) x =
    (\<lambda>nd. let c = the (RBT.lookup (finite_indexed_certificates (map (\<lambda>m. (m,finite_node_links ?N m)) ns))
        (resolution_node_position nd)) in
      (c,finite_indexed_graph_check P d t (map (\<lambda>m. (m,finite_node_links ?N m)) ns) nd \<or>
        finite_checks_schema_proof P c d t)) x"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
  proof -
    have xN: "x |\<in>| ?N" using that by simp
    note c = finite_indexed_certificates_exact[OF listed xN]
    note g = finite_indexed_graph_check_exact[OF listed xN, of P d t]
    show ?thesis by (simp only: c g)
  qed
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using Some by (simp add: finite_state_verdicts_def finite_indexed_links_rows_exact[OF listed] Let_def)
qed

lemma finite_state_proofs_indexed [code]:
  "finite_state_proofs st = (case finite_post_listing (fset (resolution_nodes st)) of
      None \<Rightarrow> (let N = resolution_nodes st; T = finite_certificate_table (finite_node_ranked N) in
        fimage (\<lambda>nd. the (finite_relation_option T nd)) (ffilter (\<lambda>nd. resolution_node_position nd=[]) N))
    | Some ns \<Rightarrow> (let CT = finite_indexed_certificates (finite_indexed_links_rows ns) in
        fimage (\<lambda>nd. the (RBT.lookup CT (resolution_node_position nd))) (ffilter (\<lambda>nd. resolution_node_position nd=[])
          (resolution_nodes st))))"
proof (cases "finite_post_listing (fset (resolution_nodes st))")
  case None
  then show ?thesis by (simp add: finite_state_proofs_table)
next
  case (Some ns)
  let ?N = "resolution_nodes st"
  have listed: "finite_post_listed (fset ?N) ns" by (rule finite_post_listing_some[OF Some])
  have "finite_node_proof (fcard ?N) ?N x =
      the (RBT.lookup (finite_indexed_certificates (map (\<lambda>m. (m,finite_node_links ?N m)) ns)) (resolution_node_position x))"
    if "x |\<in>| ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N" for x
  proof -
    have xN: "x |\<in>| ?N" using that by simp
    show ?thesis by (rule finite_indexed_certificates_exact[OF listed xN, symmetric])
  qed
  from fimage_cong[where N="ffilter (\<lambda>nd. resolution_node_position nd=[]) ?N", OF refl this] show ?thesis
    using Some by (simp add: finite_state_proofs_def finite_state_proofs_in_def finite_indexed_links_rows_exact[OF listed] Let_def)
qed

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

export_code finite_program_resolution finite_committed_resolution checking SML

end
