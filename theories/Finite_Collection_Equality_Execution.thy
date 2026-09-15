theory Finite_Collection_Equality_Execution
  imports "HOL-Library.FSet"
begin

definition execution_set_equal :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "execution_set_equal A B=(A\<subseteq>B \<and> B\<subseteq>A)"

lemma execution_set_equal_exact:
  "execution_set_equal A B \<longleftrightarrow> A=B"
  by (auto simp: execution_set_equal_def)

declare execution_set_equal_def[code del]

lemma execution_set_equal_lists_code [code]:
  "execution_set_equal (set xs) (set ys)=(xs=ys \<or>
    (list_all (\<lambda>x. x\<in>set ys) xs \<and> list_all (\<lambda>y. y\<in>set xs) ys))"
  by (auto simp: execution_set_equal_def list_all_iff)

lemma execution_set_equal_list_coset_code [code]:
  "execution_set_equal (set xs) (List.coset ys)=
    (set xs\<subseteq>List.coset ys \<and> List.coset ys\<subseteq>set xs)"
  by (simp only: execution_set_equal_def)

lemma execution_set_equal_coset_list_code [code]:
  "execution_set_equal (List.coset xs) (set ys)=
    (List.coset xs\<subseteq>set ys \<and> set ys\<subseteq>List.coset xs)"
  by (simp only: execution_set_equal_def)

lemma execution_set_equal_cosets_code [code]:
  "execution_set_equal (List.coset xs) (List.coset ys)=
    (List.coset xs\<subseteq>List.coset ys \<and> List.coset ys\<subseteq>List.coset xs)"
  by (simp only: execution_set_equal_def)

lemma finite_collection_equal_execution_code [code]:
  "HOL.equal (A::'a::equal fset) B=execution_set_equal (fset A) (fset B)"
  by (simp only: equal_eq execution_set_equal_exact fset_inject)

text \<open>Identical complete list presentations establish equal finite
  collections by one ordered comparison. Other presentations execute both
  original inclusions, so permutations and duplicates retain set semantics.
  Equality is not inferred from length, a digest, sampled members or an
  external identity. Every nested element still uses its exact equality.\<close>

end
