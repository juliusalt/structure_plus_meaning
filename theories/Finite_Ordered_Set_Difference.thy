theory Finite_Ordered_Set_Difference
  imports Finite_Sorted_Set_Execution RRA_Finite_Role_Projections "HOL-Library.List_Lexorder"
begin

section \<open>A difference of two listings ordered by a key is one merge pass\<close>

text \<open>
  Two listings ordered by a key are subtracted by one merge: it compares the keys of the two heads and keeps
  a member of the first listing whose key the second lacks. On listings sorted by a key injective on their
  members it is the filter of the first listing by absence from the second
  (@{text keyed_difference_filter}). A listing is paired with its keys once, and the merge and the sort then
  compare keys already computed (@{text keyed_difference_paired}).
\<close>

fun keyed_difference :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "keyed_difference f [] ys=[]"
| "keyed_difference f xs []=xs"
| "keyed_difference f (x#xs) (y#ys)=(if f x<f y then x#keyed_difference f xs (y#ys)
    else if f y<f x then keyed_difference f (x#xs) ys else keyed_difference f xs (y#ys))"

lemma keyed_difference_subset: "set (keyed_difference f xs ys)\<subseteq>set xs"
  by (induction f xs ys rule: keyed_difference.induct) auto

theorem keyed_difference_filter:
  "sorted (map f xs) \<Longrightarrow> sorted (map f ys) \<Longrightarrow> inj_on f (set xs\<union>set ys) \<Longrightarrow>
    keyed_difference f xs ys=filter (\<lambda>z. z\<notin>set ys) xs"
proof (induction f xs ys rule: keyed_difference.induct)
  case (3 f x xs y ys)
  have xs: "sorted (map f xs)" and x_least: "\<forall>z\<in>set xs. f x\<le>f z" using "3.prems"(1) by simp_all
  have ys: "sorted (map f ys)" and y_least: "\<forall>z\<in>set ys. f y\<le>f z" using "3.prems"(2) by simp_all
  have inj: "inj_on f (set (x#xs)\<union>set (y#ys))" by (rule "3.prems"(3))
  show ?case
  proof (cases "f x" "f y" rule: linorder_cases)
    case less
    have absent: "x\<notin>set (y#ys)" using less y_least by auto
    have inj': "inj_on f (set xs\<union>set (y#ys))" by (rule inj_on_subset[OF inj]) auto
    show ?thesis using less absent "3.IH"(1)[OF less xs "3.prems"(2) inj'] by simp
  next
    case greater
    have "y\<notin>set (x#xs)" using greater x_least by auto
    then have same: "filter (\<lambda>z. z\<notin>set (y#ys)) (x#xs)=filter (\<lambda>z. z\<notin>set ys) (x#xs)"
      by (intro filter_cong) auto
    have inj': "inj_on f (set (x#xs)\<union>set ys)" by (rule inj_on_subset[OF inj]) auto
    have "\<not>f x<f y" using greater by simp
    then show ?thesis using greater same "3.IH"(2)[OF _ greater "3.prems"(1) ys inj'] by simp
  next
    case equal
    have eq: "x=y" by (rule inj_onD[OF inj equal]) simp_all
    have inj': "inj_on f (set xs\<union>set (y#ys))" by (rule inj_on_subset[OF inj]) auto
    have "\<not>f x<f y" "\<not>f y<f x" using equal by simp_all
    then show ?thesis using eq "3.IH"(3)[OF _ _ xs "3.prems"(2) inj'] by simp
  qed
qed simp_all

lemma insort_key_paired:
  "insort_key fst (f x,x) (map (\<lambda>y. (f y,y)) ys)=map (\<lambda>y. (f y,y)) (insort_key f x ys)"
  by (induction ys) simp_all

lemma sort_key_paired: "sort_key fst (map (\<lambda>x. (f x,x)) xs)=map (\<lambda>x. (f x,x)) (sort_key f xs)"
  by (induction xs) (simp_all add: insort_key_paired)

lemma keyed_difference_pairs:
  "keyed_difference fst (map (\<lambda>x. (f x,x)) xs) (map (\<lambda>x. (f x,x)) ys)=map (\<lambda>x. (f x,x)) (keyed_difference f xs ys)"
  by (induction f xs ys rule: keyed_difference.induct) simp_all

theorem keyed_difference_paired:
  "keyed_difference f (sort_key f xs) (sort_key f ys)=
    map snd (keyed_difference fst (sort_key fst (map (\<lambda>x. (f x,x)) xs)) (sort_key fst (map (\<lambda>x. (f x,x)) ys)))"
  by (simp add: sort_key_paired keyed_difference_pairs comp_def)

section \<open>A difference of canonical listings is its identity-key instance\<close>

definition ascending_difference :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ascending_difference=keyed_difference id"

lemma ascending_difference_simps [simp, code]:
  "ascending_difference [] ys=[]"
  "ascending_difference (x#xs) []=x#xs"
  "ascending_difference (x#xs) (y#ys)=(if x<y then x#ascending_difference xs (y#ys)
    else if y<x then ascending_difference (x#xs) ys else ascending_difference xs (y#ys))"
  by (simp_all add: ascending_difference_def)

lemma ascending_difference_filter:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> ascending_difference xs ys=filter (\<lambda>z. z\<notin>set ys) xs"
  using keyed_difference_filter[of id xs ys] by (simp add: ascending_difference_def)

lemma fset_of_sorted_listing [simp]: "fset_of_list (sorted_list_of_fset A)=A"
  by (rule fset_eqI) (simp add: fset_of_list_elem sorted_list_of_fset.rep_eq)

theorem ascending_difference_listing:
  "ascending_difference (sorted_list_of_fset A) (sorted_list_of_fset B)=sorted_list_of_fset (A |-| B)"
proof -
  have "ascending_difference (sorted_list_of_fset A) (sorted_list_of_fset B)=
      filter (\<lambda>z. z\<notin>fset B) (sorted_list_of_fset A)"
    by (simp add: ascending_difference_filter sorted_list_of_fset.rep_eq)
  also have "\<dots>=sorted_list_of_fset (A |-| B)"
    by (rule sorted_distinct_set_unique)
      (simp_all add: sorted_list_of_fset.rep_eq sorted_wrt_filter minus_fset.rep_eq set_eq_iff)
  finally show ?thesis .
qed

section \<open>Unreferenced positions are listed once\<close>

declare finite_unreferenced_positions_def[code del]

lemma finite_unreferenced_positions_listing_code [code]:
  "finite_unreferenced_positions S=fset_of_list (ascending_difference
    (ascending_difference (sorted_list_of_fset (finite_carrier S))
      (sorted_list_of_fset (finite_participation_occurrences S)))
    (sorted_list_of_fset (finite_reached_occurrences S)))"
proof -
  have difference: "finite_unreferenced_positions S=
      finite_carrier S |-| finite_participation_occurrences S |-| finite_reached_occurrences S"
    by (auto simp: finite_unreferenced_positions_def)
  show ?thesis
    by (simp only: difference ascending_difference_listing fset_of_sorted_listing)
qed

text \<open>
  Two canonical listings are subtracted by one merge pass that keeps every
  member of the first listing absent from the second, so the canonical listing
  of a finite set difference needs no membership search per member. The
  unreferenced positions of a structure subtract the canonical participations
  and then the canonical reached occurrences from its canonical carrier. The
  result is the original set on every structure, including repeated incidence
  endpoints; only its computation changes.
\<close>

end
