theory Bootstrap_Finite_Closure
  imports Bootstrap_Relations "HOL-Library.FSet"
begin

section \<open>Closure and well-foundedness of complete finite edge relations\<close>

definition finite_edge_compose :: "('a \<times> 'b) fset \<Rightarrow> ('b \<times> 'c) fset \<Rightarrow> ('a \<times> 'c) fset" where
  "finite_edge_compose R S = ffUnion (fimage (\<lambda>(x,y).
    fimage (\<lambda>(u,v). (x,v)) (ffilter (\<lambda>(u,v). u=y) S)) R)"

lemma finite_edge_compose_correct:
  "fset (finite_edge_compose R S) = fset R O fset S"
  by (auto simp: finite_edge_compose_def fimage.rep_eq ffUnion.rep_eq split: prod.splits; force)

fun finite_path_bound :: "nat \<Rightarrow> ('a \<times> 'a) fset \<Rightarrow> ('a \<times> 'a) fset" where
  "finite_path_bound 0 E = E"
| "finite_path_bound (Suc n) E =
    finite_path_bound n E |\<union>| finite_edge_compose (finite_path_bound n E) E"

lemma finite_path_bound_correct:
  "fset (finite_path_bound n E) = ntrancl n (fset E)"
  by (induction n) (auto simp: finite_edge_compose_correct)

definition finite_edge_closure :: "('a \<times> 'a) fset \<Rightarrow> ('a \<times> 'a) fset" where
  "finite_edge_closure E = finite_path_bound (fcard E - 1) E"

lemma finite_edge_closure_correct:
  "fset (finite_edge_closure E) = (fset E)\<^sup>+"
  by (simp add: finite_edge_closure_def finite_path_bound_correct fcard.rep_eq finite_trancl_ntranl)

definition finite_edge_reaches :: "('a \<times> 'a) fset \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finite_edge_reaches E x y \<longleftrightarrow> x=y \<or> (x,y) |\<in>| finite_edge_closure E"

lemma finite_edge_reaches_correct:
  "finite_edge_reaches E x y \<longleftrightarrow> (x,y) \<in> (fset E)\<^sup>*"
  by (auto simp: finite_edge_reaches_def finite_edge_closure_correct rtrancl_eq_or_trancl)

definition finite_edge_wellfounded :: "('a \<times> 'a) fset \<Rightarrow> bool" where
  "finite_edge_wellfounded E \<longleftrightarrow> fBall (finite_edge_closure E) (\<lambda>(x,y). x\<noteq>y)"

lemma finite_edge_wellfounded_correct:
  "finite_edge_wellfounded E \<longleftrightarrow> wf (fset E)"
  by (auto simp: finite_edge_wellfounded_def finite_edge_closure_correct
      wf_iff_acyclic_if_finite acyclic_def Ball_def split_paired_All)

section \<open>Finite labelled transitions recover every reachable output\<close>

definition finite_transition_keys :: "('a \<Rightarrow> 'k) \<Rightarrow> ('k \<times> 'a) fset \<Rightarrow> ('k \<times> 'k) fset" where
  "finite_transition_keys key R = fimage (\<lambda>(k,a). (k,key a)) R"

definition finite_reachable_outputs :: "('a \<Rightarrow> 'k) \<Rightarrow> ('k \<times> 'a) fset \<Rightarrow> 'a \<Rightarrow> 'a fset" where
  "finite_reachable_outputs key R root = finsert root
    (fimage snd (ffilter (\<lambda>(k,a). finite_edge_reaches (finite_transition_keys key R) (key root) k) R))"

lemma finite_transition_keys_member:
  "(k,l) |\<in>| finite_transition_keys key R \<longleftrightarrow> (\<exists>a. (k,a) |\<in>| R \<and> l=key a)"
  by (auto simp: finite_transition_keys_def fimage.rep_eq)

lemma finite_reachable_outputs_member:
  "a |\<in>| finite_reachable_outputs key R root \<longleftrightarrow>
    a=root \<or> (\<exists>k. (k,a) |\<in>| R \<and> (key root,k) \<in> (fset (finite_transition_keys key R))\<^sup>*)"
  by (auto simp: finite_reachable_outputs_def finite_edge_reaches_correct fimage.rep_eq
      split: prod.splits intro: rev_image_eqI; force)

lemma finite_reachable_outputs_invariant:
  fixes root :: 'a and key :: "'a \<Rightarrow> 'k"
  assumes initial: "root \<in> A"
    and advance: "\<And>a b. a \<in> A \<Longrightarrow> (key a,b) |\<in>| R \<Longrightarrow> b \<in> A"
  shows "fset (finite_reachable_outputs key R root) \<subseteq> A"
proof -
  have reachable: "\<And>k. (key root,k) \<in> (fset (finite_transition_keys key R))\<^sup>* \<Longrightarrow>
      (\<exists>a\<in>A. key a=k)"
  proof -
    fix k assume path: "(key root,k) \<in> (fset (finite_transition_keys key R))\<^sup>*"
    show "\<exists>a\<in>A. key a=k"
      using path
    proof (induction rule: rtrancl_induct)
      case base
      show ?case using initial by blast
    next
      case (step k l)
      obtain a where a: "a \<in> A" "key a=k" using step.IH by blast
      obtain b where b: "(k,b) |\<in>| R" "l=key b"
        using step.hyps(2) by (simp only: finite_transition_keys_member) blast
      have member: "b \<in> A" by (rule advance[OF a(1)]) (use a(2) b(1) in simp)
      show ?case using member b(2) by blast
    qed
  qed
  show ?thesis
  proof
    fix a assume member: "a \<in> fset (finite_reachable_outputs key R root)"
    show "a \<in> A"
    proof (cases "a=root")
      case True
      show ?thesis using initial True by simp
    next
      case False
      obtain k where row: "(k,a) |\<in>| R" and path: "(key root,k) \<in> (fset (finite_transition_keys key R))\<^sup>*"
        using member False by (auto simp: finite_reachable_outputs_member)
      obtain b where b: "b \<in> A" "key b=k" using reachable[OF path] by blast
      show ?thesis by (rule advance[OF b(1)]) (use b(2) row in simp)
    qed
  qed
qed

export_code finite_edge_closure finite_edge_reaches finite_edge_wellfounded finite_reachable_outputs checking SML

text \<open>
  The iteration bound is derived from the number of supplied edges. The empty
  relation is included. Closure contains every finite path, and a finite
  relation is well-founded exactly when its closure contains no self-edge.
  No enumeration order or additional edge is part of the input.
\<close>

end
