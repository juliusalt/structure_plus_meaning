theory Keyed_Demanded_Sites
  imports Keyed_Finite_Sets Finite_Demanded_Closures
begin

section \<open>The traversal of demanded sites keeps its sites in an ordered index\<close>

text \<open>
  The traversal of the sites alone asks, at every step, which successors of its frontier have been visited.
  With finite sets, a successor is compared with every visited site and the successors of the frontier with
  one another. Keyed by an ordered key with a left inverse, the visited sites are kept in the ordered member
  index across the steps, the successors of each frontier site are listed once in the order of their keys,
  and the successors of the frontier are joined as one sorted listing of keys; a step then inserts the keys
  of its frontier once and asks each successor one lookup. The traversal returns exactly the sites of the
  traversal it refines; the index is structure the traversal keeps, not a judgment about a site.
\<close>

definition keyed_site_successors ::
  "('s \<Rightarrow> 'k::linorder) \<Rightarrow> ('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's list \<Rightarrow> 'k list" where
  "keyed_site_successors key read succ T=sorted_list_of_set (set (concat
    (map (\<lambda>x. sorted_list_of_fset (fimage key (ffUnion (fimage succ (read x))))) T)))"

lemma keyed_site_successors_set:
  "set (keyed_site_successors key read succ T)=key ` fset (finite_row_successors read succ (fset_of_list T))"
proof -
  have rows: "fset (finite_row_successors read succ (fset_of_list T))=(\<Union>x\<in>set T. fset (ffUnion (fimage succ (read x))))"
  proof (rule set_eqI, rule iffI)
    fix y assume "y\<in>fset (finite_row_successors read succ (fset_of_list T))"
    then obtain d x where d: "d |\<in>| fset_of_list T" and x: "x |\<in>| read d" and y: "y |\<in>| succ x"
      by (auto simp: finite_row_successors_member)
    have "y |\<in>| ffUnion (fimage succ (read d))" using x y by (auto simp: ffUnion_membership finite_image_member)
    then show "y\<in>(\<Union>x\<in>set T. fset (ffUnion (fimage succ (read x))))" using d by (auto simp: fset_of_list_elem)
  next
    fix y assume "y\<in>(\<Union>x\<in>set T. fset (ffUnion (fimage succ (read x))))"
    then obtain d where d: "d\<in>set T" and u: "y |\<in>| ffUnion (fimage succ (read d))" by auto
    obtain x where x: "x |\<in>| read d" and y: "y |\<in>| succ x"
      using u by (auto simp: ffUnion_membership finite_image_member)
    show "y\<in>fset (finite_row_successors read succ (fset_of_list T))"
      using d x y by (auto simp: finite_row_successors_member fset_of_list_elem)
  qed
  have "set (keyed_site_successors key read succ T)=(\<Union>x\<in>set T. key ` fset (ffUnion (fimage succ (read x))))"
    by (simp add: keyed_site_successors_def)
  then show ?thesis by (simp add: rows image_UN)
qed

definition keyed_sites_step ::
  "('s \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow>
    ('k,unit) rbt\<times>'s list\<times>'s list \<Rightarrow> ('k,unit) rbt\<times>'s list\<times>'s list" where
  "keyed_sites_step key unkey read succ q=(case q of (M,S,T) \<Rightarrow>
    (let M'=fold (\<lambda>x N. RBT.insert (key x) () N) T M in
      (M',S@T,map unkey (filter (\<lambda>k. RBT.lookup M' k=None) (keyed_site_successors key read succ T)))))"

definition keyed_demanded_sites ::
  "('s \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> 's fset option" where
  "keyed_demanded_sites key unkey read succ roots=map_option (\<lambda>(M,S,T). fset_of_list S)
    (while_option (\<lambda>(M,S,T). T\<noteq>[]) (keyed_sites_step key unkey read succ) (RBT.empty,[],keyed_rows key unkey roots))"

lemma keyed_fold_insert:
  "RBT.lookup (fold (\<lambda>x N. RBT.insert (key x) () N) T M) k\<noteq>None \<longleftrightarrow> RBT.lookup M k\<noteq>None \<or> k\<in>key ` set T"
  by (induction T arbitrary: M) auto

lemma keyed_sites_step_frontier:
  assumes inverse: "\<And>x. unkey (key x)=x"
    and inv: "\<forall>x. RBT.lookup M (key x)\<noteq>None \<longleftrightarrow> x\<in>set S"
  shows "fset_of_list (map unkey (filter (\<lambda>k. RBT.lookup (fold (\<lambda>x N. RBT.insert (key x) () N) T M) k=None)
      (keyed_site_successors key read succ T)))=
    finite_row_successors read succ (fset_of_list T) |-| (fset_of_list S |\<union>| fset_of_list T)"
proof (rule fset_eqI)
  fix y
  let ?M="fold (\<lambda>x N. RBT.insert (key x) () N) T M"
  let ?A="finite_row_successors read succ (fset_of_list T)"
  have visited: "RBT.lookup ?M (key z)\<noteq>None \<longleftrightarrow> z\<in>set S \<or> z\<in>set T" for z
  proof -
    have same: "key z\<in>key ` set T \<longleftrightarrow> z\<in>set T"
    proof
      assume "key z\<in>key ` set T"
      then obtain w where "w\<in>set T" "key z=key w" by blast
      then show "z\<in>set T" using inverse by metis
    qed blast
    show ?thesis using keyed_fold_insert[of key T M "key z"] inv same by auto
  qed
  have "y |\<in>| fset_of_list (map unkey (filter (\<lambda>k. RBT.lookup ?M k=None) (keyed_site_successors key read succ T)))
      \<longleftrightarrow> (\<exists>k. k\<in>set (keyed_site_successors key read succ T) \<and> RBT.lookup ?M k=None \<and> y=unkey k)"
    by (auto simp: fset_of_list_elem)
  also have "\<dots> \<longleftrightarrow> (\<exists>z. z |\<in>| ?A \<and> RBT.lookup ?M (key z)=None \<and> y=z)"
    by (auto simp: keyed_site_successors_set inverse)
  also have "\<dots> \<longleftrightarrow> y |\<in>| ?A \<and> RBT.lookup ?M (key y)=None" by blast
  also have "\<dots> \<longleftrightarrow> y |\<in>| ?A |-| (fset_of_list S |\<union>| fset_of_list T)"
  proof -
    have absent: "RBT.lookup ?M (key y)=None \<longleftrightarrow> \<not>(y\<in>set S \<or> y\<in>set T)" using visited[of y] by blast
    show ?thesis by (simp only: absent fminus_iff funion_iff fset_of_list_elem)
  qed
  finally show "y |\<in>| fset_of_list (map unkey (filter (\<lambda>k. RBT.lookup ?M k=None) (keyed_site_successors key read succ T)))
      \<longleftrightarrow> y |\<in>| ?A |-| (fset_of_list S |\<union>| fset_of_list T)" .
qed

theorem keyed_demanded_sites_exact:
  fixes key :: "'s \<Rightarrow> 'k::linorder" and unkey :: "'k \<Rightarrow> 's"
    and read :: "'s \<Rightarrow> 'r fset" and succ :: "'r \<Rightarrow> 's fset"
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_demanded_sites key unkey read succ roots=finite_demanded_sites read succ roots"
proof -
  define s0 where "s0=((RBT.empty::('k,unit) rbt),([]::'s list),keyed_rows key unkey roots)"
  let ?P="\<lambda>(M,S,T). \<forall>x. RBT.lookup M (key x)\<noteq>None \<longleftrightarrow> x\<in>set S"
  let ?f="\<lambda>(M::('k,unit) rbt,S::'s list,T::'s list). (fset_of_list S,fset_of_list T)"
  have commute: "map_option ?f (while_option (\<lambda>(M,S,T). T\<noteq>[]) (keyed_sites_step key unkey read succ) s0)=
      while_option (\<lambda>(S,T). T\<noteq>{||}) (finite_demanded_sites_step read succ) (?f s0)"
  proof (rule while_option_commute_invariant[where P="?P"])
    show "?P (keyed_sites_step key unkey read succ s)" if inv: "?P s" and active: "(\<lambda>(M,S,T). T\<noteq>[]) s" for s
    proof -
      obtain M S T where s: "s=(M,S,T)" by (cases s) auto
      have old: "\<forall>x. RBT.lookup M (key x)\<noteq>None \<longleftrightarrow> x\<in>set S" using inv s by simp
      have "RBT.lookup (fold (\<lambda>x N. RBT.insert (key x) () N) T M) (key x)\<noteq>None \<longleftrightarrow> x\<in>set (S@T)" for x
      proof -
        have same: "key x\<in>key ` set T \<longleftrightarrow> x\<in>set T"
        proof
          assume "key x\<in>key ` set T"
          then obtain w where "w\<in>set T" "key x=key w" by blast
          then show "x\<in>set T" using inverse by metis
        qed blast
        show ?thesis using keyed_fold_insert[of key T M "key x"] old same by auto
      qed
      then show ?thesis by (simp add: s keyed_sites_step_def Let_def)
    qed
    show "(\<lambda>(M,S,T). T\<noteq>[]) s=(\<lambda>(S,T). T\<noteq>{||}) (?f s)" if inv: "?P s" for s
    proof -
      obtain M S T where s: "s=(M,S,T)" by (cases s) auto
      show ?thesis by (cases T) (simp_all add: s)
    qed
    show "?f (keyed_sites_step key unkey read succ s)=finite_demanded_sites_step read succ (?f s)"
      if inv: "?P s" and active: "(\<lambda>(M,S,T). T\<noteq>[]) s" for s
    proof -
      obtain M S T where s: "s=(M,S,T)" by (cases s) auto
      have old: "\<forall>x. RBT.lookup M (key x)\<noteq>None \<longleftrightarrow> x\<in>set S" using inv s by simp
      show ?thesis
        using keyed_sites_step_frontier[OF inverse old, where read=read and succ=succ and T=T]
        by (simp add: s keyed_sites_step_def finite_demanded_sites_step_def Let_def fset_of_list_append)
    qed
    show "?P s0" by (simp add: s0_def)
  qed
  have start: "?f s0=({||},roots)" by (simp add: s0_def keyed_rows_fset[OF inverse])
  have "keyed_demanded_sites key unkey read succ roots=map_option fst (map_option ?f
      (while_option (\<lambda>(M,S,T). T\<noteq>[]) (keyed_sites_step key unkey read succ) s0))"
    by (simp add: keyed_demanded_sites_def s0_def option.map_comp comp_def split_def)
  then show ?thesis by (simp add: commute start finite_demanded_sites_def)
qed

end
