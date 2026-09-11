theory RRA_Executable_Records
  imports RRA_Executable_Syntax
begin

section \<open>Finite candidates of the grammar's stated arity\<close>

fun finite_lists_of_length :: "nat \<Rightarrow> 'a fset \<Rightarrow> 'a list fset" where
  "finite_lists_of_length 0 A = {|[]|}"
| "finite_lists_of_length (Suc n) A =
    ffUnion (fimage (\<lambda>x. fimage (Cons x) (finite_lists_of_length n A)) A)"

lemma finite_lists_of_length_member:
  "xs |\<in>| finite_lists_of_length n A \<longleftrightarrow> length xs=n \<and> set xs \<subseteq> fset A"
proof (induction n arbitrary: xs)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case using Suc.IH by (cases xs; auto simp: fimage.rep_eq ffUnion.rep_eq; force)
qed

definition finite_record_candidates ::
  "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a list) fset" where
  "finite_record_candidates C r n =
    (let H=finite_headed_incidence (finite_structure C) r in
     if fcard H=n then
       ffilter (\<lambda>(ps,xs). finite_record_at C r ps xs)
         (fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_lists_of_length n H))
     else {||})"

theorem finite_record_candidates_correct:
  "(ps,xs) |\<in>| finite_record_candidates C r n \<longleftrightarrow>
    record_at (decode_finite_object C) r ps xs \<and> length xs=n"
proof
  assume member: "(ps,xs) |\<in>| finite_record_candidates C r n"
  show "record_at (decode_finite_object C) r ps xs \<and> length xs=n"
    using member by (auto simp: finite_record_candidates_def Let_def finite_lists_of_length_member
        finite_record_at_correct fimage.rep_eq split: if_splits)
next
  assume read: "record_at (decode_finite_object C) r ps xs \<and> length xs=n"
  have rec: "record_at (decode_finite_object C) r ps xs" and arity: "length xs=n" using read by auto
  have len: "length ps=length xs" using record_at_preserves_socket_occurrences[OF rec] by blast
  let ?H = "finite_headed_incidence (finite_structure C) r"
  have head: "fset ?H=set (zip ps xs)"
    using rec by (auto simp: record_at_def raw_record_at_def finite_headed_incidence_correct)
  have degree: "fcard ?H=n"
    using record_head_card[OF rec] arity
    by (simp add: fcard.rep_eq finite_headed_incidence_correct)
  have listed: "zip ps xs |\<in>| finite_lists_of_length n ?H"
    by (simp add: finite_lists_of_length_member head len arity)
  have mapped: "(ps,xs) |\<in>| fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_lists_of_length n ?H)"
  proof -
    have "(map fst (zip ps xs),map snd (zip ps xs)) |\<in>|
        fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_lists_of_length n ?H)"
      by (rule fimageI[OF listed])
    then show ?thesis using len by simp
  qed
  show "(ps,xs) |\<in>| finite_record_candidates C r n"
    using rec degree mapped by (simp add: finite_record_candidates_def Let_def finite_record_at_correct)
qed

corollary finite_record_candidates_unique:
  assumes "(ps,xs) |\<in>| finite_record_candidates C r n"
    "(qs,ys) |\<in>| finite_record_candidates C r n"
  shows "ps=qs \<and> xs=ys"
proof -
  have first: "record_at (decode_finite_object C) r ps xs"
    using assms(1) by (simp add: finite_record_candidates_correct)
  have second: "record_at (decode_finite_object C) r qs ys"
    using assms(2) by (simp add: finite_record_candidates_correct)
  show ?thesis by (rule record_at_unique[OF first second])
qed

section \<open>A family exposes its complete headed relation\<close>

definition finite_family_candidates ::
  "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) fset fset" where
  "finite_family_candidates C r =
    (let H=finite_headed_incidence (finite_structure C) r in
     if finite_family_at C r H then {|H|} else {||})"

theorem finite_family_candidates_correct:
  "M |\<in>| finite_family_candidates C r \<longleftrightarrow> family_at (decode_finite_object C) r (fset M)"
  by (auto simp: finite_family_candidates_def Let_def finite_family_at_correct[symmetric] finite_family_at_def)

lemma finite_family_candidates_complete:
  assumes read: "family_at (decode_finite_object C) r M"
  shows "\<exists>F. F |\<in>| finite_family_candidates C r \<and> fset F=M"
proof -
  have represented: "fset (finite_headed_incidence (finite_structure C) r)=M"
    using read by (simp add: family_at_def finite_headed_incidence_correct)
  have member: "finite_headed_incidence (finite_structure C) r |\<in>| finite_family_candidates C r"
    using read represented by (simp add: finite_family_candidates_correct)
  show ?thesis using member represented by blast
qed

export_code finite_record_candidates finite_family_candidates checking SML

text \<open>
  Record candidates use only incidences actually headed at the selected root.
  The number of those incidences must equal the grammar's arity before candidates
  are constructed. Exact record checking then follows the represented order
  and returns at most one result. Family recovery returns the complete actual
  socket relation when its formation check succeeds. Neither reader sorts
  occurrences or supplies an unrepresented order.
\<close>

end
