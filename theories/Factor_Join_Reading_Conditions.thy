theory Factor_Join_Reading_Conditions
  imports Factor_Executable_Quotation
begin

section \<open>Join admissibility is decided by pairwise disjointness\<close>

definition finite_disjoint :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "finite_disjoint A B \<longleftrightarrow> fBall A (\<lambda>a. a |\<notin>| B)"

lemma finite_disjoint_inter: "finite_disjoint A B \<longleftrightarrow> A |\<inter>| B={||}"
  by (auto simp: finite_disjoint_def fset_eq_iff)

lemma finite_join_condition_split:
  "(F |\<inter>| (L |\<union>| Q)={||} \<and> L |\<inter>| Q={||} \<and> (F |\<union>| L |\<union>| Q) |\<inter>| (A |\<union>| B |\<union>| V)={||}) \<longleftrightarrow>
    finite_disjoint F V \<and>
    (finite_disjoint F L \<and> finite_disjoint F A \<and> finite_disjoint L A \<and> finite_disjoint L V) \<and>
    (finite_disjoint F Q \<and> finite_disjoint F B \<and> finite_disjoint Q B \<and> finite_disjoint Q V) \<and>
    (finite_disjoint L Q \<and> finite_disjoint L B \<and> finite_disjoint Q A)"
  by (auto simp: finite_disjoint_def fset_eq_iff)

lemma ffUnion_fimage_empty: "ffUnion (fimage (\<lambda>y. {||}) Y)={||}"
  by (simp add: fset_eq_iff ffUnion.rep_eq fimage.rep_eq)

lemma ffUnion_fimage_if_const:
  "ffUnion (fimage (\<lambda>y. if P then T y else {||}) Y)=(if P then ffUnion (fimage T Y) else {||})"
  by (cases P) (simp_all add: ffUnion_fimage_empty)

lemma ffUnion_fimage_if_conj:
  "ffUnion (fimage (\<lambda>y. if P \<and> Q y then T y else {||}) Y)=
    (if P then ffUnion (fimage (\<lambda>y. if Q y then T y else {||}) Y) else {||})"
  by (cases P) (simp_all add: ffUnion_fimage_empty)

lemma ffUnion_fimage_if_filter:
  "ffUnion (fimage (\<lambda>y. if P y \<and> Q y then T y else {||}) Y)=
    ffUnion (fimage (\<lambda>y. if Q y then T y else {||}) (ffilter P Y))"
  by (auto simp: fset_eq_iff ffUnion.rep_eq fimage.rep_eq ffilter.rep_eq split: if_splits)

declare finite_join_readings_def[code del]

lemma finite_join_readings_disjoint_code [code]:
  "finite_join_readings f V r ps X Y=(let F=finsert r (fset_of_list ps) in
    if finite_disjoint F V then
      (let Z=ffilter (\<lambda>(y,Q,B). finite_disjoint F Q \<and> finite_disjoint F B \<and>
          finite_disjoint Q B \<and> finite_disjoint Q V) Y in
        ffUnion (fimage (\<lambda>(x,L,A).
          if finite_disjoint F L \<and> finite_disjoint F A \<and> finite_disjoint L A \<and> finite_disjoint L V
          then ffUnion (fimage (\<lambda>(y,Q,B).
            if finite_disjoint L Q \<and> finite_disjoint L B \<and> finite_disjoint Q A
            then {|(f x y,F |\<union>| L |\<union>| Q,A |\<union>| B)|} else {||}) Z)
          else {||}) X))
    else {||})"
  unfolding finite_join_readings_def Let_def finite_join_condition_split case_prod_unfold
  by (simp only: ffUnion_fimage_if_conj ffUnion_fimage_if_filter ffUnion_fimage_if_const)

text \<open>
  A join of two readings is admissible exactly when twelve pairwise footprint
  disjointness conditions hold. One depends on neither reading, four on the
  left reading, four on the right reading and three on both, so each is checked
  once at its own level. The combined footprints of an admitted join and the
  traversal of both readings are unchanged; a skipped right reading contributed
  only empty results.
\<close>

end
