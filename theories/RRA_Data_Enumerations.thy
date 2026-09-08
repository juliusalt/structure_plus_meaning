theory RRA_Data_Enumerations
  imports RRA_Data
begin

section \<open>Finite attachment transport preserves every counted occurrence\<close>

abbreviation pushed_attachment_list ::
  "('a\<Rightarrow>'b) \<Rightarrow> ('a\<times>'v) list \<Rightarrow> ('b\<times>'v) list" where
  "pushed_attachment_list f B \<equiv> map (\<lambda>(a,v). (f a,v)) B"

theorem pushed_count_list:
  assumes finite: "finite U" and inside: "fst ` set B\<subseteq>U"
  shows "count_list (pushed_attachment_list f B)=pushed_count U f (count_list B)"
proof -
  have counts: "count_list (pushed_attachment_list f B) (y,v)=
      (\<Sum>a\<in>U. if f a=y then count_list B (a,v) else 0)" for y v
    using inside
  proof (induction B)
    case Nil
    then show ?case by (simp add: sum.neutral)
  next
    case (Cons z B)
    obtain a w where row: "z=(a,w)" by (cases z) auto
    have member: "a\<in>U" and rest: "fst ` set B\<subseteq>U"
      using Cons.prems by (auto simp: row)
    have summand: "(if f b=y then count_list ((a,w)#B) (b,v) else 0)=
        (if b=a then (if f a=y \<and> w=v then 1 else 0) else 0)+
        (if f b=y then count_list B (b,v) else 0)" for b
      by auto
    have sum: "(\<Sum>b\<in>U. if f b=y then count_list ((a,w)#B) (b,v) else 0)=
        (if f a=y \<and> w=v then 1 else 0)+
        (\<Sum>b\<in>U. if f b=y then count_list B (b,v) else 0)"
      by (simp only: summand sum.distrib) (simp add: finite member)
    show ?case unfolding row by (subst sum) (simp add: Cons.IH[OF rest])
  qed
  show ?thesis by (rule ext) (use counts in \<open>auto simp: pushed_count_def\<close>)
qed

theorem push_basis_enumeration:
  assumes finite: "finite U" and formed: "basis_formed U D"
    and counts: "count_list B=bag_count D"
    and bindings: "set F=functional_bindings D"
  shows "push_basis U f D=\<lparr>
    bag_count=count_list (pushed_attachment_list f B),
    functional_bindings=set (pushed_attachment_list f F)\<rparr>"
proof -
  have support: "set B=bag_support D"
    by (auto simp: bag_support_def counts[symmetric] count_list_0_iff)
  have inside: "fst ` set B\<subseteq>U"
    using formed support by (auto simp: basis_formed_def)
  have transported: "count_list (pushed_attachment_list f B)=pushed_count U f (bag_count D)"
    using pushed_count_list[OF finite inside, of f] by (simp only: counts)
  show ?thesis by (simp add: push_basis_def transported bindings)
qed

corollary enumerated_functional_compatibility:
  assumes "set F=functional_bindings D"
  shows "single_valued (set (pushed_attachment_list f F)) \<longleftrightarrow> basis_compatible f D"
  using pushed_functional_single_valued[of U f D] assms
  by (simp add: push_basis_def)

text \<open>
  Mapping a finite attachment list changes its atom coordinate and retains
  every occurrence and opaque value. The count at a destination is exactly
  the existing finite sum over its source atoms. No injectivity condition is
  imposed on the map.

  The same mapped list describes the functional component by its set. Equal
  bindings may merge there; their counted counterparts still add. Functionality
  of that complete image is exactly the original compatibility condition.
  These laws apply to arbitrary carrier and value types, without a byte encoding
  or a new data basis.
\<close>

end
