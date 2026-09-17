theory Finite_Ordered_Set_Difference
  imports Finite_Sorted_Set_Execution RRA_Finite_Role_Projections "HOL-Library.List_Lexorder"
begin

section \<open>A difference of canonical listings is one merge pass\<close>

fun ascending_difference :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ascending_difference [] ys=[]"
| "ascending_difference xs []=xs"
| "ascending_difference (x#xs) (y#ys)=(if x<y then x#ascending_difference xs (y#ys)
    else if y<x then ascending_difference (x#xs) ys else ascending_difference xs (y#ys))"

lemma ascending_difference_filter:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> ascending_difference xs ys=filter (\<lambda>z. z\<notin>set ys) xs"
proof (induction xs ys rule: ascending_difference.induct)
  case (3 x xs y ys)
  have xs: "sorted xs" and x_least: "\<forall>z\<in>set xs. x\<le>z" using "3.prems"(1) by simp_all
  have ys: "sorted ys" and y_least: "\<forall>z\<in>set ys. y\<le>z" using "3.prems"(2) by simp_all
  show ?case
  proof (cases x y rule: linorder_cases)
    case less
    have absent: "x\<notin>set (y#ys)" using less y_least by auto
    show ?thesis using less absent "3.IH"(1)[OF less xs "3.prems"(2)] by simp
  next
    case greater
    have "y\<notin>set (x#xs)" using greater x_least by auto
    then have same: "filter (\<lambda>z. z\<notin>set (y#ys)) (x#xs)=filter (\<lambda>z. z\<notin>set ys) (x#xs)"
      by (intro filter_cong) auto
    have "\<not>x<y" using greater by simp
    then show ?thesis using greater same "3.IH"(2)[OF _ greater "3.prems"(1) ys] by simp
  next
    case equal
    have "\<not>x<y" "\<not>y<x" using equal by simp_all
    then show ?thesis using equal "3.IH"(3)[OF _ _ xs "3.prems"(2)] by simp
  qed
qed simp_all

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
