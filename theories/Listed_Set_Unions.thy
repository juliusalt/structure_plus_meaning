theory Listed_Set_Unions
  imports Main "HOL-Library.FSet"
begin

section \<open>A union computed once is the concatenation of the listings it joins\<close>

text \<open>
  A finite set is executed as a listing of its members, and the library executes the union of two
  listings by inserting the members of one into the other one at a time, testing each insertion
  against every member already present: the union costs the product of the two sizes, and a union of
  many parts costs the square of the whole. A union that is computed once and then only read does not
  need the listings kept free of repetitions, since a set is the same set whatever its listing
  repeats. The listed union below concatenates the listings instead. It is the union exactly; only
  its listing differs, and the listing may repeat a member present in both parts. An accumulation
  iterated to a fixed point keeps the library's union, because repetitions would grow with every
  round.
\<close>

definition listed_union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "listed_union A B=A \<union> B"

lemma listed_union_code [code]:
  "listed_union (set xs) (set ys)=set (xs@ys)"
  "listed_union (set xs) (List.coset ys)=List.coset (filter (\<lambda>y. y\<notin>set xs) ys)"
  "listed_union (List.coset xs) B=List.coset (filter (\<lambda>x. x\<notin>B) xs)"
  by (auto simp: listed_union_def)

definition listed_image_union :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "listed_image_union f A=(\<Union>x\<in>A. f x)"

lemma listed_image_union_fold:
  "fold (\<lambda>x acc. listed_union (f x) acc) xs B=listed_image_union f (set xs) \<union> B"
  by (induction xs arbitrary: B) (auto simp: listed_union_def listed_image_union_def)

lemma listed_image_union_code [code]:
  "listed_image_union f (set xs)=fold (\<lambda>x acc. listed_union (f x) acc) xs {}"
  by (simp add: listed_image_union_fold)

text \<open>
  The union of the images of a listed set is built by one pass over its listing, each image joined by
  the listed union, so the whole costs the size of the result. The listing of a set that is not
  finite has no such pass, and the listed image union states no code for it.
\<close>

text \<open>
  A finite set built once as the union of a list of finite sets, and then only read, is the listed union
  of their listings: each part is listed once, the parts one after another.
\<close>

definition finite_listed_union :: "'a fset list \<Rightarrow> 'a fset" where
  "finite_listed_union Fs=ffUnion (fset_of_list Fs)"

lemma finite_listed_union_code [code abstract]:
  "fset (finite_listed_union Fs)=listed_image_union fset (set Fs)"
  by (simp add: finite_listed_union_def listed_image_union_def ffUnion.rep_eq fset_of_list.rep_eq)

text \<open>
  A list's members are those of its first @{term n} elements and of the rest: the split a join of two rule
  programs sharing a leading prefix of definitions reads.
\<close>

lemma set_take_drop_union: "set xs=set (take n xs)\<union>set (drop n xs)"
  by (metis append_take_drop_id set_append)

end
