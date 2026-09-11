theory List_Relation_Folds
  imports Main
begin

section \<open>A right fold composes the actual step relations\<close>

abbreviation fold_relation ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "fold_relation R xs \<equiv> foldr (\<lambda>x S. S OO R x) xs (=)"

lemma fold_relation_simps [simp]:
  "fold_relation R [] z y \<longleftrightarrow> y=z"
  "fold_relation R (x#xs) z y \<longleftrightarrow> (\<exists>w. fold_relation R xs z w \<and> R x w y)"
  by (auto simp: relcompp_apply)

lemma foldr_preserves_domain:
  assumes elements: "\<forall>x\<in>set xs. D x" and seed: "E z"
    and step: "\<And>x a. D x \<Longrightarrow> E a \<Longrightarrow> E (f x a)"
  shows "E (foldr f xs z)"
  using elements by (induction xs) (use seed step in auto)

theorem fold_relation_encoded:
  assumes seed: "E z"
    and step: "\<And>a p q. E a \<Longrightarrow>
      R p (g a) q \<longleftrightarrow> (\<exists>x. D x \<and> p=h x \<and> q=g (f x a))"
    and closed: "\<And>x a. D x \<Longrightarrow> E a \<Longrightarrow> E (f x a)"
  shows "fold_relation R ps (g z) q \<longleftrightarrow>
    (\<exists>xs. (\<forall>x\<in>set xs. D x) \<and> ps=map h xs \<and> q=g (foldr f xs z))"
  using seed
proof (induction ps arbitrary: z q)
  case Nil
  then show ?case by (simp add: eq_commute)
next
  case (Cons p ps)
  show ?case
  proof
    assume accepted: "fold_relation R (p#ps) (g z) q"
    obtain a where tail: "fold_relation R ps (g z) a" and first: "R p a q"
      using accepted by auto
    obtain xs where readings: "\<forall>x\<in>set xs. D x" "ps=map h xs" "a=g (foldr f xs z)"
      using tail Cons.IH[OF Cons.prems, of a] by blast
    have state: "E (foldr f xs z)" by (rule foldr_preserves_domain[where D=D and E=E and f=f and xs=xs and z=z, OF readings(1) Cons.prems closed])
    obtain x where element: "D x" "p=h x" "q=g (f x (foldr f xs z))"
      using first step[OF state, of p q] readings(3) by blast
    show "\<exists>xs. (\<forall>x\<in>set xs. D x) \<and> p#ps=map h xs \<and> q=g (foldr f xs z)"
      by (rule exI[of _ "x#xs"]) (use readings element in auto)
  next
    assume accepted: "\<exists>xs. (\<forall>x\<in>set xs. D x) \<and> p#ps=map h xs \<and> q=g (foldr f xs z)"
    obtain x xs where readings: "D x" "\<forall>x\<in>set xs. D x" "p=h x" "ps=map h xs"
      "q=g (f x (foldr f xs z))"
      using accepted by (auto simp: Cons_eq_map_conv)
    have tail: "fold_relation R ps (g z) (g (foldr f xs z))"
      using Cons.IH[OF Cons.prems, of "g (foldr f xs z)"] readings(2,4) by blast
    have state: "E (foldr f xs z)" by (rule foldr_preserves_domain[where D=D and E=E and f=f and xs=xs and z=z, OF readings(2) Cons.prems closed])
    have first: "R p (g (foldr f xs z)) q"
      using step[OF state, of p q] readings(1,3,5) by blast
    show "fold_relation R (p#ps) (g z) q" using tail first by auto
  qed
qed

text \<open>
  Relational composition and the existing right fold determine this relation.
  Each step consumes the current element and the result of the complete tail.
  A partial operation remains partial, and a relation may have several results.

  One local step equation and one state closure condition determine the whole
  encoded fold. Input encodings need not be injective for this equation; a
  complete presentation class separately requires recovery. The empty fold
  returns the supplied seed literally, including when the step admits nothing.
\<close>

end
