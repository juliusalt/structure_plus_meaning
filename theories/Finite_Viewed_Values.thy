theory Finite_Viewed_Values
 imports Finite_Presented_Coordinates
begin

definition finite_viewed_value :: "('v \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> finite_factor_term" where
 "finite_viewed_value present view x=present (view x)"

lemma finite_viewed_value_injective [intro]:
 "inj present \<Longrightarrow> inj view \<Longrightarrow> inj (finite_viewed_value present view)"
 by (auto simp: inj_def finite_viewed_value_def)

lemma map_injective_at_left:
 "map g xs=map g ys \<Longrightarrow> (\<And>x y. x\<in>set xs \<Longrightarrow> g x=g y \<Longrightarrow> x=y) \<Longrightarrow> xs=ys"
proof (induction xs arbitrary: ys)
 case Nil
 then show ?case by simp
next
 case (Cons x xs)
 then obtain z zs where "ys=z#zs" "g x=g z" "map g xs=map g zs"
   by (auto simp: Cons_eq_map_conv)
 then show ?case using Cons.prems(2) Cons.IH[of zs] by auto
qed

text \<open>A value is presented through an injective view of its complete original
 identity, such as the ordered fields of a record or another nesting of the same
 components. The view supplies no derived observation; injectivity of the view
 and of the presentation of its values are the only contracts.\<close>
end
