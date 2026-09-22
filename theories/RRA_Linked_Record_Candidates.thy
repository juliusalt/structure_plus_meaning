theory RRA_Linked_Record_Candidates
  imports RRA_Finite_Syntax_Bodies Established_Premises Candidate_Generators
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
proof -
  let ?H="finite_headed_incidence (finite_structure C) r"
  have generator: "candidate_generator (fimage ?split ?all) ?B (fimage ?split ?linked)"
  proof (rule candidate_generator.intro)
    fix c :: "'a list\<times>'a list"
    assume "c |\<in>| fimage ?split ?linked"
    then obtain rows where rows: "rows |\<in>| ?linked" "c=?split rows" by auto
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
    then show "c |\<in>| fimage ?split ?all" using rows(2) by auto
  next
    fix c :: "'a list\<times>'a list"
    obtain ps xs where c: "c=(ps,xs)" by (cases c)
    assume "c |\<in>| fimage ?split ?all" and body: "?B c"
    then obtain rows where rows: "rows |\<in>| ?all" "c=?split rows" by auto
    have length: "length rows=n" and within: "set rows\<subseteq>fset ?H"
      using rows(1) by (simp_all add: finite_lists_of_length_member)
    have split: "ps=map fst rows" "xs=map snd rows" using rows(2) c by simp_all
    have zipped: "zip ps xs=rows" by (simp add: split zip_map_fst_snd)
    show "c |\<in>| fimage ?split ?linked"
    proof (cases "n=0")
      case True
      then have "rows=[]" using length by simp
      then show ?thesis using rows(2) True by (simp add: finite_linked_record_rows_def)
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
      then show ?thesis using rows(2) by auto
    qed
  qed
  show ?thesis by (rule candidate_generator.accepted_generated[OF generator])
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

text \<open>
  The premise, formation of the whole object, is the first argument's: the equation is stated at that
  arity, so a partial application checks it once. The arity condition stays where the definition puts
  it, in the guard of @{const finite_record_body_candidates}.
\<close>

lemma finite_record_candidates_checked_premise:
  "checked_premise finite_record_candidates finite_object_formed finite_record_body_candidates (\<lambda>C r n. {||})"
proof (unfold_locales)
  fix C :: "('a,'v) finite_structured_object"
  assume formed: "finite_object_formed C"
  show "finite_record_candidates C=finite_record_body_candidates C"
    by (rule ext, rule ext, rule finite_record_body_candidates_exact[OF formed, symmetric])
next
  fix C :: "('a,'v) finite_structured_object"
  assume unformed: "\<not> finite_object_formed C"
  show "finite_record_candidates C=(\<lambda>r n. {||})"
    using unformed by (intro ext) (auto simp: finite_record_candidates_def Let_def finite_record_at_def)
qed

lemma finite_record_candidates_formed_once_code [code]:
  "finite_record_candidates C=(
    if finite_object_formed C then finite_record_body_candidates C else (\<lambda>r n. {||}))"
  by (rule checked_premise.checked_at_entry[OF finite_record_candidates_checked_premise])

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
