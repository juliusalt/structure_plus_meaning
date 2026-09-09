theory List_Relation_Indexing
  imports Bootstrap_Relations
begin

section \<open>Distinct source occurrences index their actual corresponding values\<close>

theorem list_all2_distinct_indexing:
  assumes distinct: "distinct xs"
  shows "list_all2 R xs ys \<longleftrightarrow>
    (\<exists>f. ys=map f xs \<and> (\<forall>x\<in>set xs. R x (f x)))"
proof
  assume related: "list_all2 R xs ys"
  show "\<exists>f. ys=map f xs \<and> (\<forall>x\<in>set xs. R x (f x))"
    using distinct related
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    obtain y zs where parts: "ys=y#zs" "R x y" "list_all2 R xs zs"
      using Cons.prems(2) by (auto simp: list_all2_Cons1)
    obtain f where tail: "zs=map f xs" "\<forall>z\<in>set xs. R z (f z)"
      using Cons.IH Cons.prems(1) parts(3) by auto
    let ?g="\<lambda>z. if z=x then y else f z"
    have same: "map ?g xs=map f xs"
      by (rule map_cong) (use Cons.prems(1) in auto)
    show ?case by (rule exI[of _ ?g])
      (use Cons.prems(1) parts(1,2) tail same in auto)
  qed
next
  assume "\<exists>f. ys=map f xs \<and> (\<forall>x\<in>set xs. R x (f x))"
  then show "list_all2 R xs ys" by (auto simp: list_all2_map2 list_all2_same)
qed

lemma functional_list_at_keys:
  assumes relation: "single_valued Q" and complete: "set xs=Q"
  shows "map (\<lambda>k. (k,rel_value Q k)) (map fst xs)=xs"
proof (simp only: map_map comp_def, rule map_idI)
  fix z assume member: "z\<in>set xs"
  obtain k v where shape: "z=(k,v)" by (cases z)
  have row: "(k,v)\<in>Q" using member complete shape by simp
  show "(fst z,rel_value Q (fst z))=z"
    using rel_value_eq[OF relation row] by (simp add: shape)
qed

text \<open>
  A distinct list supplies enough occurrence identity to index the values
  actually paired with it. No choice of a new output order is involved.
  Different source entries may have equal values. The indexing function's
  values outside the listed source have no role in this correspondence.

  For a functional relation, its complete row list is recovered from its
  actual key order and the relation's value at those keys. Neither result
  chooses a preferred enumeration of a finite collection.
\<close>

end
