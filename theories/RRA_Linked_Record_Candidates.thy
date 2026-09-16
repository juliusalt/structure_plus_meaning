theory RRA_Linked_Record_Candidates
  imports RRA_Finite_Syntax_Bodies
begin

section \<open>A record's rows follow its successor chain\<close>

definition finite_record_successors :: "'a finite_rra_structure \<Rightarrow> 'a \<Rightarrow> 'a fset" where
  "finite_record_successors S p=fimage snd (ffilter (\<lambda>(q,y). q=p) (finite_headed_incidence S p))"

fun finite_linked_rows :: "'a finite_rra_structure \<Rightarrow> ('a\<times>'a) fset \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a\<times>'a) list fset" where
  "finite_linked_rows S H 0 p={||}"
| "finite_linked_rows S H (Suc n) p=ffUnion (fimage (\<lambda>(q,x). if n=0 then {|[(q,x)]|}
      else fimage (Cons (q,x)) (ffUnion (fimage (finite_linked_rows S H n) (finite_record_successors S q))))
    (ffilter (\<lambda>(q,x). q=p) H))"

lemma finite_linked_rows_sound:
  "rows |\<in>| finite_linked_rows S H n p \<Longrightarrow> length rows=n \<and> (\<forall>row\<in>set rows. row |\<in>| H)"
proof (induction n arbitrary: rows p)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "n=0")
    case True
    then show ?thesis using Suc.prems by (auto simp: ffUnion.rep_eq fimage.rep_eq split: prod.splits)
  next
    case False
    from Suc.prems False obtain q x rest s where
      row: "(q,x) |\<in>| H" "q=p" and shape: "rows=(q,x)#rest"
      and successor: "s |\<in>| finite_record_successors S q"
      and rest: "rest |\<in>| finite_linked_rows S H n s"
      by (auto simp: ffUnion.rep_eq fimage.rep_eq split: prod.splits)
    have "length rest=n \<and> (\<forall>row\<in>set rest. row |\<in>| H)" by (rule Suc.IH[OF rest])
    then show ?thesis using row shape by simp
  qed
qed

lemma finite_linked_rows_complete:
  assumes "finite_record_path S r ps xs" "\<forall>row\<in>set (zip ps xs). row |\<in>| H" "length ps=n"
  shows "zip ps xs |\<in>| finite_linked_rows S H n (hd ps)"
  using assms
proof (induction ps arbitrary: xs n)
  case Nil
  then show ?case by simp
next
  case (Cons p qs)
  obtain x ys where xs: "xs=x#ys"
    using Cons.prems(1) by (cases xs) auto
  obtain m where n: "n=Suc m" using Cons.prems(3) by (cases n) auto
  have row: "(p,x) |\<in>| H" using Cons.prems(2) xs by auto
  show ?case
  proof (cases "qs=[]")
    case True
    then have "ys=[]" "m=0" using Cons.prems(1,3) xs n by auto
    then show ?thesis using row True xs n
      by (auto simp: ffUnion.rep_eq fimage.rep_eq intro!: bexI[of _ "(p,x)"])
  next
    case False
    have path: "finite_record_path S r qs ys"
      and next_row: "finite_headed_incidence S p={|(p,hd qs)|}"
      using Cons.prems(1) xs False by auto
    have successor: "hd qs |\<in>| finite_record_successors S p"
      using next_row by (simp add: finite_record_successors_def)
    have rest: "zip qs ys |\<in>| finite_linked_rows S H m (hd qs)"
      by (rule Cons.IH[OF path]) (use Cons.prems(2,3) xs n in auto)
    have positive: "m\<noteq>0" using False Cons.prems(3) n by (cases qs) auto
    show ?thesis using row successor rest positive xs n
      by (auto simp: ffUnion.rep_eq fimage.rep_eq intro!: bexI[of _ "(p,x)"] bexI[of _ "hd qs"])
  qed
qed

definition finite_linked_record_rows :: "'a finite_rra_structure \<Rightarrow> ('a\<times>'a) fset \<Rightarrow> nat \<Rightarrow> ('a\<times>'a) list fset" where
  "finite_linked_record_rows S H n=(if n=0 then {|[]|}
    else ffUnion (fimage (\<lambda>(p,x). finite_linked_rows S H n p) H))"

lemma finite_linked_record_rows_candidates:
  assumes arity: "fcard (finite_headed_incidence (finite_structure C) r)=n"
  shows "ffilter (\<lambda>(ps,xs). finite_record_body C r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows))
        (finite_linked_record_rows (finite_structure C) (finite_headed_incidence (finite_structure C) r) n))=
    ffilter (\<lambda>(ps,xs). finite_record_body C r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows))
        (finite_lists_of_length n (finite_headed_incidence (finite_structure C) r)))"
    (is "ffilter ?B (fimage ?split ?linked)=ffilter ?B (fimage ?split ?all)")
proof (rule fset_eqI)
  fix c :: "'a list\<times>'a list"
  obtain ps xs where c: "c=(ps,xs)" by (cases c)
  let ?H="finite_headed_incidence (finite_structure C) r"
  show "c |\<in>| ffilter ?B (fimage ?split ?linked) \<longleftrightarrow> c |\<in>| ffilter ?B (fimage ?split ?all)"
  proof
    assume "c |\<in>| ffilter ?B (fimage ?split ?linked)"
    then obtain rows where rows: "rows |\<in>| ?linked" "c=?split rows" and body: "?B c" by auto
    have linked: "length rows=n \<and> (\<forall>row\<in>set rows. row |\<in>| ?H)"
    proof (cases "n=0")
      case True
      then show ?thesis using rows(1) by (simp add: finite_linked_record_rows_def)
    next
      case False
      then obtain p x where "(p,x) |\<in>| ?H" and chain: "rows |\<in>| finite_linked_rows (finite_structure C) ?H n p"
        using rows(1) by (auto simp: finite_linked_record_rows_def ffUnion.rep_eq fimage.rep_eq split: prod.splits)
      show ?thesis by (rule finite_linked_rows_sound[OF chain])
    qed
    then have "rows |\<in>| ?all" by (auto simp: finite_lists_of_length_member)
    then show "c |\<in>| ffilter ?B (fimage ?split ?all)" using rows(2) body by auto
  next
    assume "c |\<in>| ffilter ?B (fimage ?split ?all)"
    then obtain rows where rows: "rows |\<in>| ?all" "c=?split rows" and body: "?B c" by auto
    have length: "length rows=n" and within: "set rows\<subseteq>fset ?H"
      using rows(1) by (simp_all add: finite_lists_of_length_member)
    have split: "ps=map fst rows" "xs=map snd rows" using rows(2) c by simp_all
    have zipped: "zip ps xs=rows" by (simp add: split zip_map_fst_snd)
    show "c |\<in>| ffilter ?B (fimage ?split ?linked)"
    proof (cases "n=0")
      case True
      then have "rows=[]" using length by simp
      then show ?thesis using rows(2) body True by (simp add: finite_linked_record_rows_def)
    next
      case False
      have lengths: "length ps=n" "length xs=n" using split length by simp_all
      have path: "finite_record_path (finite_structure C) r ps xs"
        using body False lengths by (auto simp: c finite_record_body_def)
      obtain p qs where ps: "ps=p#qs" using lengths False by (cases ps) auto
      obtain x ys where xs: "xs=x#ys" using lengths False by (cases xs) auto
      have member: "rows |\<in>| finite_linked_rows (finite_structure C) ?H n p"
        using finite_linked_rows_complete[OF path, of ?H n] zipped within lengths ps by auto
      have start: "(p,x) |\<in>| ?H" using within zipped ps xs by auto
      have "rows |\<in>| ?linked"
        using member start False
        by (auto simp: finite_linked_record_rows_def ffUnion.rep_eq fimage.rep_eq intro!: bexI[of _ "(p,x)"])
      then show ?thesis using rows(2) body by auto
    qed
  qed
qed

declare finite_record_body_candidates_def[code del]

lemma finite_record_body_candidates_linked_code [code]:
  "finite_record_body_candidates C r n=(let H=finite_headed_incidence (finite_structure C) r in
    if fcard H=n then ffilter (\<lambda>(ps,xs). finite_record_body C r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_linked_record_rows (finite_structure C) H n))
    else {||})"
  using finite_linked_record_rows_candidates[of C r n]
  by (simp add: finite_record_body_candidates_def Let_def)

declare finite_record_candidates_def[code del]

lemma finite_record_candidates_formed_once_code [code]:
  "finite_record_candidates C r n=(
    if fcard (finite_headed_incidence (finite_structure C) r)=n \<and> finite_object_formed C
    then finite_record_body_candidates C r n else {||})"
proof (cases "finite_object_formed C")
  case True
  then show ?thesis
    by (simp add: finite_record_body_candidates_exact[OF True, symmetric] finite_record_body_candidates_def Let_def)
next
  case False
  then show ?thesis
    by (auto simp: finite_record_candidates_def Let_def finite_record_at_def)
qed

export_code finite_record_candidates finite_record_body_candidates checking SML

text \<open>
  The complete original candidate filter is unchanged. Only candidate rows that
  follow the actual successor incidences from each actual headed row are
  constructed: every exact record is among them, and each constructed list has
  the stated arity and uses only actual headed rows. Formation of the whole
  object is checked once for the read rather than once per enumerated list.
  Malformed objects, other arities and every original body condition retain
  their original results.
\<close>

end
