theory Ordered_Member_Trees
  imports Tree_Map_Indexes "HOL-Library.FSet"
begin

section \<open>Ordered indexes over complete finite rows\<close>

definition ordered_remdups_step :: "'a::linorder \<Rightarrow> 'a list\<times>('a,unit) rbt \<Rightarrow> 'a list\<times>('a,unit) rbt" where
  "ordered_remdups_step x s=(case s of (acc,seen) \<Rightarrow> (case RBT.lookup seen x of
    None \<Rightarrow> (x#acc,RBT.insert x () seen) | Some u \<Rightarrow> (acc,seen)))"

definition ordered_remdups :: "'a::linorder list \<Rightarrow> 'a list" where
  "ordered_remdups xs=fst (fold ordered_remdups_step (rev xs) ([],RBT.empty))"

lemma remdups_snoc_filter:
  "remdups (zs@[x])=remdups [z\<leftarrow>zs. z\<noteq>x]@[x]"
  by (induction zs) auto

lemma ordered_remdups_fold:
  assumes "dom (RBT.lookup seen)=set acc"
  shows "fst (fold ordered_remdups_step (rev xs) (acc,seen))=remdups [y\<leftarrow>xs. y\<notin>set acc]@acc"
  using assms
proof (induction xs arbitrary: acc seen rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "x\<in>set acc")
    case True
    then have lookup: "RBT.lookup seen x\<noteq>None" using snoc.prems by auto
    then obtain u where "RBT.lookup seen x=Some u" by auto
    then have step: "ordered_remdups_step x (acc,seen)=(acc,seen)" by (simp add: ordered_remdups_step_def)
    show ?thesis using snoc.IH[OF snoc.prems] True by (simp add: step)
  next
    case False
    then have lookup: "RBT.lookup seen x=None" using snoc.prems by auto
    have step: "ordered_remdups_step x (acc,seen)=(x#acc,RBT.insert x () seen)"
      by (simp add: ordered_remdups_step_def lookup)
    have inserted: "k\<in>dom (RBT.lookup (RBT.insert x () seen)) \<longleftrightarrow> k=x \<or> k\<in>dom (RBT.lookup seen)" for k
      using tree_map_updates.updated[where i=seen and k=x and u="()" and k'=k and v="()"]
      by (cases "k=x"; cases "RBT.lookup seen k") (auto simp del: RBT.lookup_insert)
    have domain: "dom (RBT.lookup (RBT.insert x () seen))=set (x#acc)" using snoc.prems inserted by (auto simp del: RBT.lookup_insert)
    have filtered: "[y\<leftarrow>xs@[x]. y\<notin>set acc]=[y\<leftarrow>xs. y\<notin>set acc]@[x]" using False by simp
    show ?thesis
      using snoc.IH[OF domain] False
      by (simp add: step filtered remdups_snoc_filter filter_filter conj_commute)
  qed
qed

theorem ordered_remdups_exact: "ordered_remdups xs=remdups xs"
  using ordered_remdups_fold[of RBT.empty "[]" xs] by (simp add: ordered_remdups_def)

definition ordered_member_tree :: "'a::linorder fset \<Rightarrow> ('a,unit) rbt" where
  "ordered_member_tree A=RBT.bulkload (map (\<lambda>x. (x,())) (sorted_list_of_fset A))"

lemma map_of_unit_rows: "map_of (map (\<lambda>x. (x,())) xs) y=(if y\<in>set xs then Some () else None)"
  by (induction xs) auto

theorem ordered_member_tree_exact:
  "RBT.lookup (ordered_member_tree A) x\<noteq>None \<longleftrightarrow> x\<in>fset A"
  by (simp add: ordered_member_tree_def map_of_unit_rows)

lemma ordered_member_tree_some:
  "RBT.lookup (ordered_member_tree A) x=Some () \<longleftrightarrow> x\<in>fset A"
  by (simp add: ordered_member_tree_def map_of_unit_rows)

lemma ordered_member_tree_none:
  "RBT.lookup (ordered_member_tree A) x=None \<longleftrightarrow> x\<notin>fset A"
  using ordered_member_tree_exact[of A x] by blast

lemma ordered_member_tree_listed:
  "RBT.lookup (ordered_member_tree (fset_of_list xs)) x\<noteq>None \<longleftrightarrow> x\<in>set xs"
  by (simp only: ordered_member_tree_exact fset_of_list.rep_eq)

text \<open>
  A complete finite set of a linearly ordered type is indexed once through its canonical
  listing, and each membership question is then one lookup; a listed set, a list read as the set of its
  members, is indexed the same way (`ordered_member_tree_listed`). Repetitions are removed by one
  pass that records the rows already retained. Both operations compute the original set,
  list and truth values; the index is shared by every use that asks membership questions of
  one set.
\<close>

end
