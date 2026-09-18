theory Finite_Demanded_Closures
  imports Bootstrap_Finite_Closure Finite_Set_Composition "HOL-Library.While_Combinator"
begin

section \<open>Rows are read at the sites the roots demand, and at no other site\<close>

text \<open>
  A rooted reading reads rows at sites and follows the sites those rows demand. Formulated
  over a universe of sites it reads every site of that universe, closes the edges the rows
  supply and keeps the rows at the sites the roots reach: a site no root reaches is read
  all the same, so the reading costs the whole universe however small the reached part is.
  The frontier traversal below reads a site once, and only once a root has reached it.

  Both return the same sites and the same rows there whenever every site with a row belongs
  to the universe. That premise is the reading's own boundary, not a condition on the roots:
  it says that the universe accounts for every row, which is what makes the universe
  formulation a reading of the same rows in the first place.
\<close>

lemma finite_edge_closure_empty [simp]: "finite_edge_closure {||}={||}"
  using finite_edge_closure_correct[of "{||}"] by (auto simp: fset_eq_iff)

definition finite_site_rows :: "('s \<Rightarrow> 'r fset) \<Rightarrow> 's fset \<Rightarrow> ('s \<times> 'r) fset" where
  "finite_site_rows read S=ffUnion (fimage (\<lambda>d. fimage (Pair d) (read d)) S)"

lemma finite_site_rows_member:
  "(d,x) |\<in>| finite_site_rows read S \<longleftrightarrow> d |\<in>| S \<and> x |\<in>| read d"
  by (auto simp: finite_site_rows_def finite_union_image_member finite_image_member)

lemma finite_site_rows_empty [simp]: "finite_site_rows read {||}={||}"
  by (simp add: finite_site_rows_def)

lemma finite_site_rows_union:
  "finite_site_rows read (S |\<union>| T)=finite_site_rows read S |\<union>| finite_site_rows read T"
  by (auto simp: fset_eq_iff split_paired_All finite_site_rows_member)

definition finite_row_successors ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> 's fset" where
  "finite_row_successors read succ S=
    ffUnion (fimage (\<lambda>(d,x). succ x) (finite_site_rows read S))"

lemma finite_row_successors_member:
  "e |\<in>| finite_row_successors read succ S \<longleftrightarrow>
    (\<exists>d x. d |\<in>| S \<and> x |\<in>| read d \<and> e |\<in>| succ x)"
  by (auto simp: finite_row_successors_def finite_union_image_member finite_site_rows_member
      split_paired_Ex prod.case_eq_if; force)

definition finite_row_edges ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> ('s \<times> 's) fset" where
  "finite_row_edges read succ U=
    ffUnion (fimage (\<lambda>(d,x). fimage (Pair d) (succ x)) (finite_site_rows read U))"

lemma finite_row_edges_member:
  "(d,e) |\<in>| finite_row_edges read succ U \<longleftrightarrow>
    (\<exists>x. d |\<in>| U \<and> x |\<in>| read d \<and> e |\<in>| succ x)"
  by (auto simp: finite_row_edges_def finite_union_image_member finite_image_member
      finite_site_rows_member split_paired_Ex prod.case_eq_if; force)

lemma finite_row_successors_edges:
  assumes rows: "\<And>d. read d \<noteq> {||} \<Longrightarrow> d |\<in>| U"
  shows "e |\<in>| finite_row_successors read succ S \<longleftrightarrow>
    (\<exists>d. d |\<in>| S \<and> (d,e) |\<in>| finite_row_edges read succ U)"
proof
  assume "e |\<in>| finite_row_successors read succ S"
  then obtain d x where site: "d |\<in>| S" and reading: "x |\<in>| read d" and demanded: "e |\<in>| succ x"
    by (auto simp: finite_row_successors_member)
  have inside: "d |\<in>| U" using rows[of d] reading by auto
  show "\<exists>d. d |\<in>| S \<and> (d,e) |\<in>| finite_row_edges read succ U"
    using site inside reading demanded by (auto simp: finite_row_edges_member)
next
  assume "\<exists>d. d |\<in>| S \<and> (d,e) |\<in>| finite_row_edges read succ U"
  then obtain d x where site: "d |\<in>| S" and reading: "x |\<in>| read d" and demanded: "e |\<in>| succ x"
    by (auto simp: finite_row_edges_member)
  show "e |\<in>| finite_row_successors read succ S"
    using site reading demanded by (auto simp: finite_row_successors_member)
qed

definition finite_rooted_sites ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> 's fset \<Rightarrow> 's fset" where
  "finite_rooted_sites read succ U roots=roots |\<union>|
    fimage snd (ffilter (\<lambda>(d,e). d |\<in>| roots)
      (finite_edge_closure (finite_row_edges read succ U)))"

lemma finite_rooted_sites_member:
  "d |\<in>| finite_rooted_sites read succ U roots \<longleftrightarrow>
    (\<exists>r. r |\<in>| roots \<and> (r,d) \<in> (fset (finite_row_edges read succ U))\<^sup>*)"
  by (auto simp: finite_rooted_sites_def finite_image_member finite_edge_closure_correct
      rtrancl_eq_or_trancl split: prod.splits; force)

lemma finite_rooted_sites_roots: "roots |\<subseteq>| finite_rooted_sites read succ U roots"
  by (auto simp: finite_rooted_sites_def)

lemma finite_rooted_sites_step:
  assumes site: "d |\<in>| finite_rooted_sites read succ U roots"
    and edge: "(d,e) |\<in>| finite_row_edges read succ U"
  shows "e |\<in>| finite_rooted_sites read succ U roots"
proof -
  obtain r where root: "r |\<in>| roots"
    and path: "(r,d) \<in> (fset (finite_row_edges read succ U))\<^sup>*"
    using site by (auto simp: finite_rooted_sites_member)
  have reached: "(r,e) \<in> (fset (finite_row_edges read succ U))\<^sup>*"
    using path edge by (rule rtrancl.rtrancl_into_rtrancl)
  show ?thesis using root reached by (auto simp: finite_rooted_sites_member)
qed

lemma finite_rooted_sites_least:
  assumes roots: "roots |\<subseteq>| S"
    and closed: "\<And>d e. d |\<in>| S \<Longrightarrow> (d,e) |\<in>| finite_row_edges read succ U \<Longrightarrow> e |\<in>| S"
  shows "finite_rooted_sites read succ U roots |\<subseteq>| S"
proof (rule fsubsetI)
  fix d assume "d |\<in>| finite_rooted_sites read succ U roots"
  then obtain r where root: "r |\<in>| roots"
    and path: "(r,d) \<in> (fset (finite_row_edges read succ U))\<^sup>*"
    by (auto simp: finite_rooted_sites_member)
  show "d |\<in>| S" using path
  proof (induction rule: rtrancl_induct)
    case base
    show ?case using root roots by auto
  next
    case (step y z)
    show ?case using closed[OF step.IH step.hyps(2)] .
  qed
qed

section \<open>The frontier traversal reads each demanded site once\<close>

text \<open>
  The state of the traversal is the sites already read, the frontier of sites a read row has
  demanded and not yet been read, and the rows read so far. A step reads the whole frontier,
  so every site is read exactly once, and the sites its rows demand that are not already
  read become the next frontier. The traversal stops when the frontier is empty.
\<close>

definition finite_demanded_step ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow>
    's fset \<times> 's fset \<times> ('s \<times> 'r) fset \<Rightarrow> 's fset \<times> 's fset \<times> ('s \<times> 'r) fset" where
  "finite_demanded_step read succ q=(case q of (S,T,A) \<Rightarrow>
    (let visited=S |\<union>| T in
      (visited,finite_row_successors read succ T |-| visited,A |\<union>| finite_site_rows read T)))"

definition finite_demanded_readings ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> ('s fset \<times> ('s \<times> 'r) fset) option" where
  "finite_demanded_readings read succ roots=map_option (\<lambda>(S,T,A). (S,A))
    (while_option (\<lambda>(S,T,A). T \<noteq> {||}) (finite_demanded_step read succ) ({||},roots,{||}))"

definition finite_demanded_invariant ::
  "('s \<Rightarrow> 'r fset) \<Rightarrow> ('r \<Rightarrow> 's fset) \<Rightarrow> 's fset \<Rightarrow> 's fset \<Rightarrow>
    's fset \<times> 's fset \<times> ('s \<times> 'r) fset \<Rightarrow> bool" where
  "finite_demanded_invariant read succ U roots q \<longleftrightarrow> (case q of (S,T,A) \<Rightarrow>
    S |\<inter>| T={||} \<and> S |\<union>| T |\<subseteq>| finite_rooted_sites read succ U roots \<and>
    roots |\<subseteq>| S |\<union>| T \<and>
    (\<forall>d e. d |\<in>| S \<longrightarrow> (d,e) |\<in>| finite_row_edges read succ U \<longrightarrow> e |\<in>| S |\<union>| T) \<and>
    A=finite_site_rows read S)"

lemma finite_demanded_step_invariant:
  assumes rows: "\<And>d. read d \<noteq> {||} \<Longrightarrow> d |\<in>| U"
    and inv: "finite_demanded_invariant read succ U roots (S,T,A)"
    and active: "T \<noteq> {||}"
  shows "finite_demanded_invariant read succ U roots (finite_demanded_step read succ (S,T,A))"
    and "fcard (finite_rooted_sites read succ U roots |-|
        fst (finite_demanded_step read succ (S,T,A)))
      < fcard (finite_rooted_sites read succ U roots |-| S)"
proof -
  let ?Sites="finite_rooted_sites read succ U roots"
  let ?Edges="finite_row_edges read succ U"
  let ?visited="S |\<union>| T"
  let ?next="finite_row_successors read succ T |-| ?visited"
  have step: "finite_demanded_step read succ (S,T,A)=
      (?visited,?next,A |\<union>| finite_site_rows read T)"
    by (simp add: finite_demanded_step_def Let_def)
  have disjoint: "S |\<inter>| T={||}" using inv by (simp add: finite_demanded_invariant_def)
  have bound: "?visited |\<subseteq>| ?Sites" using inv by (simp add: finite_demanded_invariant_def)
  have rooted: "roots |\<subseteq>| ?visited" using inv by (simp add: finite_demanded_invariant_def)
  have collected: "A=finite_site_rows read S" using inv by (simp add: finite_demanded_invariant_def)
  have closed: "e |\<in>| ?visited" if "d |\<in>| S" "(d,e) |\<in>| ?Edges" for d e
    using inv that by (simp add: finite_demanded_invariant_def)
  have successors_edges: "e |\<in>| finite_row_successors read succ T \<longleftrightarrow>
      (\<exists>d. d |\<in>| T \<and> (d,e) |\<in>| ?Edges)" for e
    by (rule finite_row_successors_edges[OF rows])
  have next_site: "e |\<in>| ?Sites" if reached: "e |\<in>| ?next" for e
  proof -
    have demanded: "e |\<in>| finite_row_successors read succ T" using reached by simp
    obtain d where site: "d |\<in>| T" and edge: "(d,e) |\<in>| ?Edges"
      using demanded successors_edges by blast
    have reached: "d |\<in>| ?Sites" using bound site by auto
    show ?thesis by (rule finite_rooted_sites_step[OF reached edge])
  qed
  have disjoint': "?visited |\<inter>| ?next={||}" by auto
  have bound': "?visited |\<union>| ?next |\<subseteq>| ?Sites"
  proof (rule fsubsetI)
    fix e assume "e |\<in>| ?visited |\<union>| ?next"
    then show "e |\<in>| ?Sites" using bound next_site by auto
  qed
  have rooted': "roots |\<subseteq>| ?visited |\<union>| ?next"
  proof (rule fsubsetI)
    fix r assume "r |\<in>| roots"
    then show "r |\<in>| ?visited |\<union>| ?next" using rooted by auto
  qed
  have closed': "e |\<in>| ?visited |\<union>| ?next" if "d |\<in>| ?visited" "(d,e) |\<in>| ?Edges" for d e
  proof (cases "d |\<in>| S")
    case True
    show ?thesis using closed[OF True that(2)] by auto
  next
    case False
    have site: "d |\<in>| T" using that(1) False by auto
    have successor: "e |\<in>| finite_row_successors read succ T"
      using site that(2) successors_edges by auto
    show ?thesis using successor by auto
  qed
  have rows_read: "A |\<union>| finite_site_rows read T=finite_site_rows read ?visited"
    by (simp add: collected finite_site_rows_union)
  show "finite_demanded_invariant read succ U roots (finite_demanded_step read succ (S,T,A))"
    unfolding step finite_demanded_invariant_def prod.case
    using disjoint' bound' rooted' closed' rows_read by blast
  obtain t where member: "t |\<in>| T" using active by auto
  have inside: "t |\<in>| ?Sites" using bound member by auto
  have fresh: "t |\<notin>| S" using disjoint member by auto
  have subset: "?Sites |-| ?visited |\<subseteq>| ?Sites |-| S" by auto
  have strict: "?Sites |-| ?visited \<noteq> ?Sites |-| S"
  proof
    assume equal: "?Sites |-| ?visited=?Sites |-| S"
    have "t |\<in>| ?Sites |-| S" using inside fresh by simp
    then have "t |\<in>| ?Sites |-| ?visited" using equal by simp
    then show False using member by simp
  qed
  have proper: "?Sites |-| ?visited |\<subset>| ?Sites |-| S"
    using subset strict by (simp add: less_le)
  show "fcard (?Sites |-| fst (finite_demanded_step read succ (S,T,A))) < fcard (?Sites |-| S)"
    using pfsubset_fcard_mono[OF proper] by (simp add: step)
qed

theorem finite_demanded_readings_exact:
  assumes rows: "\<And>d. read d \<noteq> {||} \<Longrightarrow> d |\<in>| U"
  shows "finite_demanded_readings read succ roots=
    Some (finite_rooted_sites read succ U roots,
      finite_site_rows read (finite_rooted_sites read succ U roots))"
proof -
  let ?Sites="finite_rooted_sites read succ U roots"
  let ?P="finite_demanded_invariant read succ U roots"
  let ?b="\<lambda>(S,T,A). T \<noteq> {||}"
  let ?c="finite_demanded_step read succ"
  let ?f="\<lambda>q. fcard (?Sites |-| fst q)"
  have initial: "?P ({||},roots,{||})"
    by (simp add: finite_demanded_invariant_def finite_rooted_sites_roots)
  have advance: "?P (?c s) \<and> ?f (?c s) < ?f s" if inv: "?P s" and active: "?b s" for s
  proof -
    obtain S T A where shape: "s=(S,T,A)" by (cases s) auto
    have frontier: "T \<noteq> {||}" using active shape by simp
    show ?thesis
      using finite_demanded_step_invariant[OF rows inv[unfolded shape] frontier] shape by simp
  qed
  obtain t where run: "while_option ?b ?c ({||},roots,{||})=Some t"
    using measure_while_option_Some[of ?P ?b ?c ?f "({||},roots,{||})"] advance initial by blast
  have inv: "?P t"
  proof (rule while_option_rule[where b="?b" and c="?c" and s="({||},roots,{||})"])
    show "?P (?c s)" if "?P s" "?b s" for s using advance[OF that] by simp
    show "while_option ?b ?c ({||},roots,{||})=Some t" by (rule run)
    show "?P ({||},roots,{||})" by (rule initial)
  qed
  have stop: "\<not> ?b t" by (rule while_option_stop[OF run])
  obtain S T A where shape: "t=(S,T,A)" by (cases t) auto
  have empty: "T={||}" using stop shape by simp
  have bound: "S |\<subseteq>| ?Sites" using inv shape empty by (simp add: finite_demanded_invariant_def)
  have rooted: "roots |\<subseteq>| S" using inv shape empty by (simp add: finite_demanded_invariant_def)
  have collected: "A=finite_site_rows read S"
    using inv shape by (simp add: finite_demanded_invariant_def)
  have closed: "e |\<in>| S" if "d |\<in>| S" "(d,e) |\<in>| finite_row_edges read succ U" for d e
    using inv shape empty that by (simp add: finite_demanded_invariant_def)
  have sites: "S=?Sites"
  proof (rule fsubset_antisym[OF bound])
    show "?Sites |\<subseteq>| S" by (rule finite_rooted_sites_least[OF rooted closed])
  qed
  show ?thesis
    by (simp add: finite_demanded_readings_def run shape collected sites)
qed

text \<open>
  The traversal returns the rooted sites and exactly the rows at them. Sites the roots do
  not reach are never read, so a reading whose universe is large and whose reached part is
  small costs the reached part alone. Nothing here judges what a row means: the universe,
  the reading and the demanded sites are the caller's, and the premise that every row lies
  in the universe is the caller's to establish for its own reading.
\<close>

end
