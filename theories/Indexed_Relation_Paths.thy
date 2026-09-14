theory Indexed_Relation_Paths
  imports Bootstrap_Relations
begin

fun indexed_relation_path :: "('n\<Rightarrow>('s\<times>'n) set)\<Rightarrow>'n\<Rightarrow>'s list\<Rightarrow>'n\<Rightarrow>bool" where
  "indexed_relation_path R n [] m \<longleftrightarrow> m=n"
| "indexed_relation_path R n (s#ss) m \<longleftrightarrow>
    (\<exists>k. (s,k)\<in>R n \<and> indexed_relation_path R k ss m)"

definition indexed_path_family where
  "indexed_path_family R n={(ss,m). indexed_relation_path R n ss m}"

lemma indexed_path_family_member [simp]:
  "(ss,m)\<in>indexed_path_family R n \<longleftrightarrow> indexed_relation_path R n ss m"
  by (simp only: indexed_path_family_def mem_Collect_eq case_prod_conv)

lemma indexed_path_family_unfold:
  fixes R :: "'n\<Rightarrow>('s\<times>'n) set"
    and n :: 'n
  shows
  "indexed_path_family R n=insert ([],n)
    (\<Union>(s,k)\<in>R n. map_prod (Cons s) id ` indexed_path_family R k)"
proof (rule set_eqI)
  fix z :: "'s list\<times>'n"
  obtain ss m where shape: "z=(ss,m)" by (cases z) auto
  show "z\<in>indexed_path_family R n \<longleftrightarrow>
    z\<in>insert ([],n) (\<Union>(s,k)\<in>R n. map_prod (Cons s) id ` indexed_path_family R k)"
    unfolding shape
    by (cases ss;
      simp only: indexed_path_family_member indexed_relation_path.simps insert_iff prod.inject
        UN_iff Bex_def split_paired_Ex case_prod_conv key_image_member list.distinct list.inject simp_thms; blast)
qed

lemma indexed_relation_path_invariant:
  assumes initial: "Q n"
    and step: "\<And>n s m. Q n \<Longrightarrow> (s,m)\<in>R n \<Longrightarrow> Q m"
    and path: "indexed_relation_path R n ss m"
  shows "Q m"
  using initial path
proof (induction ss arbitrary: n m)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  obtain k where first: "(s,k)\<in>R n" and tail: "indexed_relation_path R k ss m"
    using Cons.prems(2) by simp blast
  show ?case by (rule Cons.IH[OF step[OF Cons.prems(1) first] tail])
qed

lemma indexed_relation_path_image:
  assumes rows: "\<And>n. S (f n)=map_prod id f ` R n"
  shows "indexed_relation_path S (f n) ss y \<longleftrightarrow>
    (\<exists>m. indexed_relation_path R n ss m \<and> y=f m)"
proof (induction ss arbitrary: n y)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  have row: "(s,z)\<in>S (f n) \<longleftrightarrow> (\<exists>k. (s,k)\<in>R n \<and> z=f k)" for z
    by (simp only: rows map_prod_def id_apply map_relation_values_def[symmetric] map_relation_values_member)
  show ?case
  proof
    assume path: "indexed_relation_path S (f n) (s#ss) y"
    obtain z where head: "(s,z)\<in>S (f n)" and tail: "indexed_relation_path S z ss y"
      using path by auto
    obtain k where child: "(s,k)\<in>R n" and mapped: "z=f k" using head by (simp only: row; blast)
    obtain m where rest: "indexed_relation_path R k ss m" and result: "y=f m"
      using tail by (simp only: mapped Cons.IH; blast)
    show "\<exists>m. indexed_relation_path R n (s#ss) m \<and> y=f m"
      by (rule exI[of _ m]) (simp only: indexed_relation_path.simps; use child rest result in blast)
  next
    assume "\<exists>m. indexed_relation_path R n (s#ss) m \<and> y=f m"
    then obtain m k where child: "(s,k)\<in>R n" and rest: "indexed_relation_path R k ss m"
      and result: "y=f m" by auto
    have head: "(s,f k)\<in>S (f n)" by (simp only: row; use child in blast)
    have tail: "indexed_relation_path S (f k) ss y"
      by (simp only: Cons.IH; use rest result in blast)
    show "indexed_relation_path S (f n) (s#ss) y"
      by (simp only: indexed_relation_path.simps; use head tail in blast)
  qed
qed

theorem indexed_path_family_image:
  assumes rows: "\<And>n. S (f n)=map_prod id f ` R n"
  shows "indexed_path_family S (f n)=map_prod id f ` indexed_path_family R n"
  by (rule set_eqI)
    (simp only: split_paired_all indexed_path_family_member map_prod_def id_apply
      map_relation_values_def[symmetric] map_relation_values_member
      indexed_relation_path_image[where R=R and S=S and f=f, OF rows])

theorem indexed_path_family_range:
  assumes edges: "\<And>m n. (m,n)\<in>r \<longleftrightarrow> (\<exists>s. (s,m)\<in>R n)"
  shows "rel_ran (indexed_path_family R n)={m. (m,n)\<in>r\<^sup>*}"
proof -
  have reaches: "(m,n)\<in>r\<^sup>*" if "indexed_relation_path R n ss m" for n ss m
    using that
  proof (induction ss arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons s ss)
    obtain k where head: "(s,k)\<in>R n" and tail: "indexed_relation_path R k ss m"
      using Cons.prems by auto
    have edge: "(k,n)\<in>r" using head by (simp only: edges; blast)
    show ?case by (rule rtrancl_trans[OF Cons.IH[OF tail] r_into_rtrancl[OF edge]])
  qed
  have zero: "\<exists>ss. indexed_relation_path R n ss n" for n
    by (rule exI[of _ "[]"]) simp
  have extend: "\<exists>tt. indexed_relation_path R z tt m"
    if source_path: "\<exists>ss. indexed_relation_path R y ss m" and edge: "(y,z)\<in>r" for y z m
  proof -
    obtain ss where tail: "indexed_relation_path R y ss m" using source_path by blast
    obtain s where head: "(s,y)\<in>R z" using edge by (simp only: edges; blast)
    show ?thesis by (rule exI[of _ "s#ss"])
      (simp only: indexed_relation_path.simps; use head tail in blast)
  qed
  have paths: "\<exists>ss. indexed_relation_path R n ss m" if "(m,n)\<in>r\<^sup>*" for n m
    using that by (induction rule: rtrancl_induct) (use zero extend in blast)+
  show ?thesis using reaches paths by (auto simp: rel_ran_def)
qed

theorem indexed_path_family_functional:
  assumes initial: "Q n"
    and step: "\<And>n s m. Q n \<Longrightarrow> (s,m)\<in>R n \<Longrightarrow> Q m"
    and rows: "\<And>n. Q n \<Longrightarrow> single_valued (R n)"
  shows "single_valued (indexed_path_family R n)"
proof -
  have unique: "x=y" if "Q n" "indexed_relation_path R n ss x"
      "indexed_relation_path R n ss y" for n ss x y
    using that
  proof (induction ss arbitrary: n x y)
    case Nil
    then show ?case by simp
  next
    case (Cons s ss)
    obtain a where left: "(s,a)\<in>R n" and left_tail: "indexed_relation_path R a ss x"
      using Cons.prems(2) by auto
    obtain b where right: "(s,b)\<in>R n" and right_tail: "indexed_relation_path R b ss y"
      using Cons.prems(3) by auto
    have same: "a=b" by (rule single_valued_outputs[OF rows[OF Cons.prems(1)] left right])
    have other: "indexed_relation_path R a ss y" using right_tail by (simp only: same)
    show ?case by (rule Cons.IH[OF step[OF Cons.prems(1) left] left_tail other])
  qed
  show ?thesis using unique initial by (auto simp: single_valued_def)
qed

text \<open>
  A complete path retains its source index at every actual relation step.
  The path family follows the original relation, including the empty root
  path. A preserved state condition and functional rows make each full path
  identify one node; they do not identify different paths to a shared node.
\<close>

end
