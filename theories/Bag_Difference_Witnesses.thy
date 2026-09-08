theory Bag_Difference_Witnesses
  imports Bootstrap_Relations "HOL-Library.Multiset"
begin

section \<open>Positive witnesses for a difference in multiplicities\<close>

inductive bag_difference_witness ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
    'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for same apart where
  extra: "bag_difference_witness same apart [] (y#ys)"
| missing: "(\<forall>y\<in>set ys. apart x y) \<Longrightarrow> bag_difference_witness same apart (x#xs) ys"
| matching: "same x y \<Longrightarrow> bag_difference_witness same apart xs (pre@post) \<Longrightarrow>
    bag_difference_witness same apart (x#xs) (pre@y#post)"

lemma bag_difference_witness_nil:
  "bag_difference_witness same apart [] ys \<longleftrightarrow> ys\<noteq>[]"
  by (cases ys) (auto elim: bag_difference_witness.cases intro: bag_difference_witness.extra)

lemma bag_difference_witness_cons:
  "bag_difference_witness same apart (x#xs) ys \<longleftrightarrow>
    (\<forall>y\<in>set ys. apart x y) \<or>
    (\<exists>y pre post. ys=pre@y#post \<and> same x y \<and> bag_difference_witness same apart xs (pre@post))"
  by (auto elim: bag_difference_witness.cases
    intro: bag_difference_witness.missing bag_difference_witness.matching)

theorem bag_difference_witness_map:
  assumes equal: "\<forall>x\<in>set xs. \<forall>y\<in>set ys. same x y \<longleftrightarrow> f x=f y"
    and unequal: "\<forall>x\<in>set xs. \<forall>y\<in>set ys. apart x y \<longleftrightarrow> f x\<noteq>f y"
  shows "bag_difference_witness same apart xs ys \<longleftrightarrow> mset (map f xs)\<noteq>mset (map f ys)"
  using equal unequal
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by (simp add: bag_difference_witness_nil)
next
  case (Cons x xs)
  have residual:
    "bag_difference_witness same apart xs (pre@post) \<longleftrightarrow>
      mset (map f xs)\<noteq>mset (map f (pre@post))"
    if "ys=pre@y#post" for y pre post
    by (rule Cons.IH) (use Cons.prems that in auto)
  show ?case
  proof
    assume witness: "bag_difference_witness same apart (x#xs) ys"
    then consider (missing) "\<forall>y\<in>set ys. apart x y"
      | (matching) y pre post where "ys=pre@y#post" "same x y"
        "bag_difference_witness same apart xs (pre@post)"
      by (auto simp: bag_difference_witness_cons)
    then show "mset (map f (x#xs))\<noteq>mset (map f ys)"
    proof cases
      case missing
      have absent: "f x\<notin>set (map f ys)" using missing Cons.prems(2) by auto
      show ?thesis using absent mset_eq_setD[of "map f (x#xs)" "map f ys"] by auto
    next
      case (matching y pre post)
      have same: "f x=f y" using Cons.prems(1) matching(1,2) by auto
      have different: "mset (map f xs)\<noteq>mset (map f (pre@post))"
        using residual[OF matching(1)] matching(3) by blast
      show ?thesis using different by (simp add: matching(1) same)
    qed
  next
    assume different: "mset (map f (x#xs))\<noteq>mset (map f ys)"
    show "bag_difference_witness same apart (x#xs) ys"
    proof (cases "f x\<in>set (map f ys)")
      case True
      then obtain y where member: "y\<in>set ys" and same_value: "f x=f y" by auto
      obtain pre post where split: "ys=pre@y#post" using split_list[OF member] by blast
      have same: "same x y" using Cons.prems(1) member same_value by auto
      have tail_difference: "mset (map f xs)\<noteq>mset (map f (pre@post))"
        using different by (simp add: split same_value)
      have tail: "bag_difference_witness same apart xs (pre@post)"
        using residual[OF split] tail_difference by blast
      show ?thesis using bag_difference_witness.matching[OF same tail] by (simp only: split)
    next
      case False
      have absent: "\<forall>y\<in>set ys. apart x y" using Cons.prems(2) False by auto
      show ?thesis by (rule bag_difference_witness.missing) (rule absent)
    qed
  qed
qed

theorem bag_difference_witness_readings:
  assumes first: "list_all2 read xs ps" and second: "list_all2 read ys qs"
    and recovery: "\<And>a b p. read a p \<Longrightarrow> read b p \<Longrightarrow> a=b"
    and equal: "\<And>a b p q. read a p \<Longrightarrow> read b q \<Longrightarrow> same p q \<longleftrightarrow> a=b"
    and unequal: "\<And>a b p q. read a p \<Longrightarrow> read b q \<Longrightarrow> apart p q \<longleftrightarrow> a\<noteq>b"
  shows "bag_difference_witness same apart ps qs \<longleftrightarrow> mset xs\<noteq>mset ys"
proof -
  let ?f="\<lambda>p. THE a. read a p"
  have decode: "?f p=a" if "read a p" for a p
    by (rule the_equality[where P="\<lambda>z. read z p" and a=a]) (use recovery that in blast)+
  have decoded: "map ?f us=zs \<and> (\<forall>p\<in>set us. read (?f p) p)"
    if "list_all2 read zs us" for zs us
    using that
  proof (induction zs arbitrary: us)
    case Nil
    then show ?case by simp
  next
    case (Cons z zs)
    obtain p ps where parts: "us=p#ps" "read z p" "list_all2 read zs ps"
      using Cons.prems by (auto simp: list_all2_Cons1)
    show ?case using Cons.IH[OF parts(3)] parts(2) decode[OF parts(2)]
      by (simp add: parts(1))
  qed
  have first_values: "map ?f ps=xs" "\<forall>p\<in>set ps. read (?f p) p"
    and second_values: "map ?f qs=ys" "\<forall>q\<in>set qs. read (?f q) q"
    using decoded[OF first] decoded[OF second] by auto
  have same: "\<forall>p\<in>set ps. \<forall>q\<in>set qs. same p q \<longleftrightarrow> ?f p=?f q"
    and apart: "\<forall>p\<in>set ps. \<forall>q\<in>set qs. apart p q \<longleftrightarrow> ?f p\<noteq>?f q"
    using first_values(2) second_values(2) equal unequal by blast+
  show ?thesis using bag_difference_witness_map[OF same apart]
    by (simp only: first_values(1) second_values(1))
qed

text \<open>
  The subject being compared is a multiset. A difference has a finite positive
  witness: an excess occurrence, a member absent from the other side, or a
  remaining difference after one equal occurrence has been removed.
  The witnesses retain multiplicity. They impose no ordering on the subject.

  Two supplied relations can implement the equality and inequality tests.
  Their equations are required only on the compared member presentations.
  Under those equations the witness relation is exactly multiset inequality,
  for every enumeration and every permitted member presentation. Without the
  equations the raw witness relation has its stated recursive meaning; it
  does not acquire a claim about equality of an unspecified subject.

  The decoder in the proof is uniquely determined wherever a reading exists.
  It is not a selected presentation and is not part of an operative program.
\<close>

end
