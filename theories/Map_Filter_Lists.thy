theory Map_Filter_Lists
  imports Main
begin

section \<open>Selecting from a list by an optional reading\<close>

text \<open>
  A list read by an optional reading keeps the results the reading returns, in order
  (\<open>List.map_filter\<close>). Its membership is the optional image of the reading, it depends only on the
  reading at the list's members, and when its results are distinct the reading takes each value at one
  member only; among distinct members that is exactly distinctness of the results. These facts are
  stated once here, for every theory that reads a list so.
\<close>

lemma map_filter_member:
  "y\<in>set (List.map_filter f xs) \<longleftrightarrow> (\<exists>x\<in>set xs. f x=Some y)"
  by (induction xs) (auto simp: List.map_filter_simps split: option.splits)

lemma map_filter_agree:
  "(\<And>x. x\<in>set xs \<Longrightarrow> f x=g x) \<Longrightarrow> List.map_filter f xs=List.map_filter g xs"
proof (induction xs)
  case Nil
  then show ?case by (simp add: List.map_filter_simps)
next
  case (Cons x xs)
  have head: "f x=g x" by (rule Cons.prems) simp
  have tail: "List.map_filter f xs=List.map_filter g xs" by (rule Cons.IH) (rule Cons.prems, simp)
  show ?case by (simp only: List.map_filter_simps head tail)
qed

lemma map_filter_unique:
  assumes distinct: "distinct (List.map_filter g xs)" and x: "x\<in>set xs" and y: "y\<in>set xs"
    and same: "g x=Some v" "g y=Some v"
  shows "x=y"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons z zs)
  show ?case
  proof (cases "g z")
    case None
    then have "distinct (List.map_filter g zs)" using Cons.prems(1) by (simp add: List.map_filter_simps)
    moreover have "x\<in>set zs" "y\<in>set zs" using Cons.prems(2,3,4,5) None by auto
    ultimately show ?thesis using Cons.IH Cons.prems(4,5) by blast
  next
    case (Some w)
    then have rest: "distinct (List.map_filter g zs)" and fresh: "w\<notin>set (List.map_filter g zs)"
      using Cons.prems(1) by (simp_all add: List.map_filter_simps)
    have inside: False if u: "u\<in>set zs" "g u=Some w" for u
    proof -
      have "w\<in>set (List.map_filter g zs)"
        unfolding map_filter_member using u by blast
      then show False using fresh by (rule notE[rotated])
    qed
    show ?thesis
    proof (cases "x=z")
      case True
      then have "w=v" using Some Cons.prems(4) by simp
      then show ?thesis using True Cons.prems(3,5) inside by auto
    next
      case False
      then have x': "x\<in>set zs" using Cons.prems(2) by simp
      show ?thesis
      proof (cases "y=z")
        case True
        then have "w=v" using Some Cons.prems(5) by simp
        then show ?thesis using x' Cons.prems(4) inside by auto
      next
        case False
        then have "y\<in>set zs" using Cons.prems(3) by simp
        then show ?thesis using Cons.IH[OF rest x'] Cons.prems(4,5) by blast
      qed
    qed
  qed
qed

text \<open>
  Among distinct members, distinct results are exactly a reading that takes each value at one member.
\<close>

lemma map_filter_distinct_iff:
  assumes members: "distinct xs"
  shows "distinct (List.map_filter g xs) \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<forall>y\<in>set xs. \<forall>v. g x=Some v \<longrightarrow> g y=Some v \<longrightarrow> x=y)"
proof
  assume d: "distinct (List.map_filter g xs)"
  show "\<forall>x\<in>set xs. \<forall>y\<in>set xs. \<forall>v. g x=Some v \<longrightarrow> g y=Some v \<longrightarrow> x=y"
  proof (intro ballI allI impI)
    fix x y v assume "x\<in>set xs" "y\<in>set xs" "g x=Some v" "g y=Some v"
    then show "x=y" by (rule map_filter_unique[OF d])
  qed
next
  assume once: "\<forall>x\<in>set xs. \<forall>y\<in>set xs. \<forall>v. g x=Some v \<longrightarrow> g y=Some v \<longrightarrow> x=y"
  from members once show "distinct (List.map_filter g xs)"
  proof (induction xs)
    case Nil
    then show ?case by (simp add: List.map_filter_simps)
  next
    case (Cons z zs)
    have dz: "distinct zs" using Cons.prems(1) by simp
    have oz: "\<forall>x\<in>set zs. \<forall>y\<in>set zs. \<forall>v. g x=Some v \<longrightarrow> g y=Some v \<longrightarrow> x=y"
    proof (intro ballI allI impI)
      fix x y v assume "x\<in>set zs" "y\<in>set zs" "g x=Some v" "g y=Some v"
      then show "x=y" by (intro Cons.prems(2)[rule_format, of x y v]) simp_all
    qed
    have rest: "distinct (List.map_filter g zs)" by (rule Cons.IH[OF dz oz])
    show ?case
    proof (cases "g z")
      case None
      then show ?thesis using rest by (simp add: List.map_filter_simps)
    next
      case (Some w)
      have "w\<notin>set (List.map_filter g zs)"
      proof
        assume "w\<in>set (List.map_filter g zs)"
        then obtain u where u: "u\<in>set zs" "g u=Some w" by (auto simp only: map_filter_member)
        have "u=z" by (rule Cons.prems(2)[rule_format, of u z w]) (simp_all add: u Some)
        then show False using u(1) Cons.prems(1) by simp
      qed
      then show ?thesis using Some rest by (simp add: List.map_filter_simps)
    qed
  qed
qed

end
