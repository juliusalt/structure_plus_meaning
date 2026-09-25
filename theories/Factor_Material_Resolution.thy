theory Factor_Material_Resolution
  imports Factor_Finite_Material_Arguments Factor_Executable_Matching
begin

text \<open>
  A material premise is solved, not only checked. Its fields' skeleton -- the addresses of its atoms,
  the address triples of its incidences, the addresses and values of its attachments -- determines the
  observed artifact when it is ground, and the solution is then the one binding that binds the source
  to that artifact's whole target and every anchor to its occurrence, or none. A premise whose source is
  ground has as solutions the enumerations of that source. A premise with neither waits: that outcome
  is kept apart from a premise with no solution. The solution reads the atoms' payloads as addresses,
  the material equation's own reading, and compares variables for equality alone.
\<close>

section \<open>Every list with the same multiset\<close>

function rearrangements :: "'a list \<Rightarrow> 'a list list" where
  "rearrangements [] = [[]]"
| "rearrangements (x#xs) = concat (map (\<lambda>y. map (Cons y) (rearrangements (remove1 y (x#xs))))
    (remdups (x#xs)))"
  by pat_completeness auto
termination
  by (relation "measure length") (auto simp: length_remove1 split: if_splits dest: length_pos_if_in_set)

theorem rearrangements_member:
  "ys \<in> set (rearrangements xs) \<longleftrightarrow> mset ys = mset xs"
proof (induction xs arbitrary: ys rule: rearrangements.induct)
  case 1
  show ?case by simp
next
  case (2 x xs)
  show ?case
  proof
    assume "ys \<in> set (rearrangements (x#xs))"
    then obtain y zs where y: "y \<in> set (x#xs)" and zs: "zs \<in> set (rearrangements (remove1 y (x#xs)))"
      and ys: "ys = y#zs" by (auto simp del: remove1.simps remdups.simps)
    have "mset zs = mset (remove1 y (x#xs))"
      using 2(1)[of y zs] y zs by (simp del: remove1.simps remdups.simps)
    then show "mset ys = mset (x#xs)" using y ys
      by (metis insert_DiffM mset.simps(2) mset_remove1 set_mset_mset)
  next
    assume eq: "mset ys = mset (x#xs)"
    then obtain y zs where ys: "ys = y#zs" by (cases ys) auto
    have y: "y \<in> set (x#xs)" using eq ys by (metis list.set_intros(1) mset_eq_setD)
    have "mset zs = mset (remove1 y (x#xs))" using eq ys
      by (metis add_mset_remove_trivial mset.simps(2) mset_remove1)
    then have "zs \<in> set (rearrangements (remove1 y (x#xs)))"
      using 2(1)[of y zs] y by (simp del: remove1.simps remdups.simps)
    then show "ys \<in> set (rearrangements (x#xs))" using y ys
      by (auto simp del: remove1.simps remdups.simps)
  qed
qed

lemma distinct_set_mset_eq:
  assumes "distinct ys"
  shows "distinct xs \<and> set xs = set ys \<longleftrightarrow> mset xs = mset ys"
  using assms by (metis card_distinct distinct_card mset_eq_length mset_eq_setD set_eq_iff_mset_eq_distinct)

section \<open>The enumerations of a finite artifact\<close>

text \<open>
  Every enumeration of an artifact rearranges any one of them: distinct lists of its carrier, its
  incidence and its functional data, and a list of its counted data with every repetition. The
  enumeration the artifact rows present is the one rearranged.
\<close>

lemma finite_artifact_enumeration_rearranged:
  assumes base: "finite_artifact_enumeration C A0 E0 B0 F0"
  shows "finite_artifact_enumeration C A E B F \<longleftrightarrow>
    mset A = mset A0 \<and> mset E = mset E0 \<and> mset B = mset B0 \<and> mset F = mset F0"
proof -
  have fset_list: "\<And>xs ys. fset_of_list xs = fset_of_list ys \<longleftrightarrow> set xs = set ys"
    by (metis fset_of_list.rep_eq fset_inject)
  have same: "finite_enumerated_artifact A E B F = finite_enumerated_artifact A0 E0 B0 F0 \<longleftrightarrow>
      set A = set A0 \<and> set E = set E0 \<and> mset B = mset B0 \<and> set F = set F0"
    by (simp add: finite_enumerated_artifact_def fset_list)
  from base have d: "distinct A0" "distinct E0" "distinct F0"
    and C: "C = finite_enumerated_artifact A0 E0 B0 F0" and formed: "finite_exact_formed C"
    using base unfolding finite_artifact_enumeration_def by blast+
  have c: "C = finite_enumerated_artifact A E B F \<longleftrightarrow>
      set A = set A0 \<and> set E = set E0 \<and> mset B = mset B0 \<and> set F = set F0"
    by (simp only: C eq_commute[of "finite_enumerated_artifact A0 E0 B0 F0"] same)
  show ?thesis
    unfolding finite_artifact_enumeration_def c
    using formed distinct_set_mset_eq[OF d(1), of A] distinct_set_mset_eq[OF d(2), of E]
      distinct_set_mset_eq[OF d(3), of F]
    by blast
qed

definition finite_artifact_enumerations :: "finite_exact_artifact \<Rightarrow>
    (local_address list \<times> (local_address \<times> local_address \<times> local_address) list \<times>
      (local_address \<times> octets) list \<times> (local_address \<times> octets) list) list" where
  "finite_artifact_enumerations C = (case finite_artifact_rows C of (A,E,B,F) \<Rightarrow>
    [(A',E',B',F'). A' \<leftarrow> rearrangements A, E' \<leftarrow> rearrangements E, B' \<leftarrow> rearrangements B,
      F' \<leftarrow> rearrangements F])"

theorem finite_artifact_enumerations_exact:
  assumes formed: "finite_exact_formed C"
  shows "(A,E,B,F) \<in> set (finite_artifact_enumerations C) \<longleftrightarrow> finite_artifact_enumeration C A E B F"
proof -
  obtain A0 E0 B0 F0 where rows: "finite_artifact_rows C = (A0,E0,B0,F0)"
    by (cases "finite_artifact_rows C") auto
  have base: "finite_artifact_enumeration C A0 E0 B0 F0"
    using finite_artifact_rows_enumeration[OF rows] formed by (simp add: finite_artifact_enumeration_correct)
  show ?thesis
    by (auto simp: finite_artifact_enumerations_def rows rearrangements_member image_iff
      finite_artifact_enumeration_rearranged[OF base])
qed

section \<open>The material operands of an enumeration\<close>

fun finite_material_tuple :: "finite_exact_artifact \<Rightarrow>
    local_address list \<times> (local_address \<times> local_address \<times> local_address) list \<times>
      (local_address \<times> octets) list \<times> (local_address \<times> octets) list \<Rightarrow>
    finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term" where
  "finite_material_tuple C (A,E,B,F) = (Finite_Target (Finite_Whole C),
    finite_enumeration_term (map (finite_atom_term C) A),
    finite_enumeration_term (map (finite_incidence_term C) E),
    finite_enumeration_term (map (finite_attachment_term C) B),
    finite_enumeration_term (map (finite_attachment_term C) F))"

lemma finite_material_arguments_tuple:
  "finite_material_arguments C = finite_material_tuple C (finite_artifact_rows C)"
  by (simp add: finite_material_arguments_def split: prod.split)

lemma finite_material_term_reads:
  "finite_atom_read C (finite_atom_term C a) = Some a"
  "finite_incidence_read C (finite_incidence_term C e) = Some e"
  "finite_attachment_read C (finite_attachment_term C p) = Some p"
  by (auto simp: finite_atom_term_def finite_occurrence_term_def finite_incidence_term_def
    finite_attachment_term_def split: prod.splits)

lemma finite_enumeration_read_term:
  assumes "\<And>x. rd (mk x) = Some x"
  shows "finite_enumeration_read rd (finite_enumeration_term (map mk xs)) = Some xs"
  using assms by (induction xs) simp_all

lemma finite_material_read_injective:
  "finite_atom_read C u = Some x \<Longrightarrow> finite_atom_read C u' = Some x \<Longrightarrow> u = u'"
  "finite_incidence_read C u = Some e \<Longrightarrow> finite_incidence_read C u' = Some e \<Longrightarrow> u = u'"
  "finite_attachment_read C u = Some p \<Longrightarrow> finite_attachment_read C u' = Some p \<Longrightarrow> u = u'"
    apply (metis finite_atom_read_correct decode_finite_term_injective)
   apply (metis finite_incidence_read_correct decode_finite_term_injective)
  apply (metis finite_attachment_read_correct decode_finite_term_injective)
  done

lemma finite_enumeration_read_injective:
  assumes inj: "\<And>u u' x. rd u = Some x \<Longrightarrow> rd u' = Some x \<Longrightarrow> u = u'"
  shows "finite_enumeration_read rd t = Some xs \<Longrightarrow> finite_enumeration_read rd t' = Some xs \<Longrightarrow> t = t'"
proof (induction t arbitrary: t' xs)
  case (Finite_Target x)
  then show ?case by (cases t') (auto split: finite_exact_target.splits if_splits option.splits)
next
  case (Finite_Payload v)
  then show ?case by simp
next
  case (Finite_Pair u w)
  from Finite_Pair.prems(1) obtain y ys where ru: "rd u = Some y"
    and rw: "finite_enumeration_read rd w = Some ys" and xs: "xs = y#ys"
    by (auto split: option.splits)
  from Finite_Pair.prems(2) xs obtain u' w' where t': "t' = Finite_Pair u' w'" and ru': "rd u' = Some y"
    and rw': "finite_enumeration_read rd w' = Some ys"
    by (cases t') (auto split: finite_exact_target.splits if_splits option.splits)
  show ?case using inj[OF ru ru'] Finite_Pair.IH(2)[OF rw rw'] t' by simp
qed

text \<open>
  A satisfied material premise is satisfied at the operands of an enumeration: the observation reads
  each operand as the enumeration of its entries, and the reading determines the operand.
\<close>

lemma finite_material_satisfied_witness:
  assumes "finite_material_satisfied V M"
  obtains C A E B F where "finite_artifact_enumeration C A E B F"
    "finite_pattern_instance V (finite_material_source M) (Finite_Target (Finite_Whole C))"
    "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
    "finite_pattern_instance V (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C) E))"
    "finite_pattern_instance V (finite_material_counts M) (finite_enumeration_term (map (finite_attachment_term C) B))"
    "finite_pattern_instance V (finite_material_functions M)
      (finite_enumeration_term (map (finite_attachment_term C) F))"
proof -
  obtain s a e b f where inst: "finite_pattern_instance V (finite_material_source M) s"
      "finite_pattern_instance V (finite_material_atoms M) a"
      "finite_pattern_instance V (finite_material_edges M) e"
      "finite_pattern_instance V (finite_material_counts M) b"
      "finite_pattern_instance V (finite_material_functions M) f"
    and obs: "finite_material_observation s a e b f"
    using assms by (auto simp: finite_material_satisfied_def finite_pattern_instances_member)
  obtain C where s: "s = Finite_Target (Finite_Whole C)"
  proof (cases s)
    case (Finite_Target x)
    then show ?thesis using obs that by (cases x) auto
  qed (use obs in auto)
  obtain A E B F where en: "finite_artifact_enumeration C A E B F"
    and ra: "finite_enumeration_read (finite_atom_read C) a = Some A"
    and re: "finite_enumeration_read (finite_incidence_read C) e = Some E"
    and rb: "finite_enumeration_read (finite_attachment_read C) b = Some B"
    and rf: "finite_enumeration_read (finite_attachment_read C) f = Some F"
    using obs unfolding s finite_material_observation_whole by blast
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    "finite_enumeration_read (finite_incidence_read C) (finite_enumeration_term (map (finite_incidence_term C) E)) = Some E"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) B)) = Some B"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) F)) = Some F"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)+
  have terms: "a = finite_enumeration_term (map (finite_atom_term C) A)"
    "e = finite_enumeration_term (map (finite_incidence_term C) E)"
    "b = finite_enumeration_term (map (finite_attachment_term C) B)"
    "f = finite_enumeration_term (map (finite_attachment_term C) F)"
    using finite_enumeration_read_injective[OF finite_material_read_injective(1) ra reads(1)]
      finite_enumeration_read_injective[OF finite_material_read_injective(2) re reads(2)]
      finite_enumeration_read_injective[OF finite_material_read_injective(3) rb reads(3)]
      finite_enumeration_read_injective[OF finite_material_read_injective(3) rf reads(4)]
    by simp_all
  show thesis using inst unfolding s terms by (rule that[OF en])
qed

section \<open>The skeleton of a material premise\<close>

text \<open>
  A skeleton position is read, has no reading though it holds no variable, or is open. The atoms field
  is an enumeration pattern whose entries pair a payload, the atom's address, with an anchor pattern.
  An anchor of an incidence or an attachment is read when it is a ground occurrence, whose address it
  states, or a variable an atom's entry holds, whose address is that atom's; a variable no atom's entry
  holds is open. The skeleton is read when every position is; it is open when some position holds a
  variable or an unheld anchor variable; otherwise some position has no reading, and no binding
  satisfies the premise.
\<close>

datatype 'x material_reading = Reading 'x | Unreadable | Open_Reading

fun reading_pair :: "'x material_reading \<Rightarrow> 'y material_reading \<Rightarrow> ('x \<times> 'y) material_reading" where
  "reading_pair Open_Reading r = Open_Reading"
| "reading_pair r Open_Reading = Open_Reading"
| "reading_pair (Reading x) (Reading y) = Reading (x,y)"
| "reading_pair r s = Unreadable"

lemma reading_pair_reading:
  "reading_pair r s = Reading z \<longleftrightarrow> (\<exists>x y. r = Reading x \<and> s = Reading y \<and> z = (x,y))"
  by (cases r; cases s) auto

lemma reading_pair_unreadable:
  "reading_pair r s = Unreadable \<Longrightarrow> r = Unreadable \<or> s = Unreadable"
  by (cases r; cases s) auto

lemma map_reading_cases:
  "map_material_reading f r = Reading z \<longleftrightarrow> (\<exists>x. r = Reading x \<and> z = f x)"
  "map_material_reading f r = Unreadable \<longleftrightarrow> r = Unreadable"
  "map_material_reading f r = Open_Reading \<longleftrightarrow> r = Open_Reading"
  by (cases r; auto)+

definition ground_reading :: "'a finite_term_pattern \<Rightarrow> 'x material_reading" where
  "ground_reading p = (if finite_pattern_variables p = {||} then Unreadable else Open_Reading)"

lemma ground_reading_cases [simp]:
  "ground_reading p \<noteq> Reading x"
  "ground_reading (Finite_Variable v) = Open_Reading"
  by (simp_all add: ground_reading_def)

fun finite_enumeration_pattern_read ::
    "('a finite_term_pattern \<Rightarrow> 'x material_reading) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'x list material_reading" where
  "finite_enumeration_pattern_read rd (Finite_Variable v) = Open_Reading"
| "finite_enumeration_pattern_read rd (Finite_Pattern_Target t) =
    (if t=Finite_Whole finite_empty_artifact then Reading [] else Unreadable)"
| "finite_enumeration_pattern_read rd (Finite_Pattern_Payload v) = Unreadable"
| "finite_enumeration_pattern_read rd (Finite_Pattern_Pair p q) =
    map_material_reading (\<lambda>(x,xs). x#xs) (reading_pair (rd p) (finite_enumeration_pattern_read rd q))"

lemma finite_enumeration_pattern_instance:
  assumes items: "\<And>q u x y. rd q = Reading x \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> tread u = Some y \<Longrightarrow> R x y"
  shows "finite_enumeration_pattern_read rd p = Reading xs \<Longrightarrow> finite_pattern_instance V p t \<Longrightarrow>
    finite_enumeration_read tread t = Some ys \<Longrightarrow> list_all2 R xs ys"
proof (induction p arbitrary: t xs ys)
  case (Finite_Variable v)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto split: if_splits)
next
  case (Finite_Pattern_Payload v)
  then show ?case by simp
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems(1) obtain x xs' where px: "rd p = Reading x"
    and qx: "finite_enumeration_pattern_read rd q = Reading xs'" and xs: "xs = x#xs'"
    by (auto simp: map_reading_cases reading_pair_reading)
  from Finite_Pattern_Pair.prems(2) obtain u w where t: "t = Finite_Pair u w"
    and pu: "finite_pattern_instance V p u" and qw: "finite_pattern_instance V q w"
    by (cases t) auto
  from Finite_Pattern_Pair.prems(3) t obtain y ys' where uy: "tread u = Some y"
    and wy: "finite_enumeration_read tread w = Some ys'" and ys: "ys = y#ys'"
    by (auto split: option.splits)
  show ?case using items[OF px pu uy] Finite_Pattern_Pair.IH(2)[OF qx qw wy] xs ys by simp
qed

lemma finite_enumeration_pattern_unreadable:
  assumes items: "\<forall>q u y. rd q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow> tread u \<noteq> Some y"
  shows "finite_enumeration_pattern_read rd p = Unreadable \<Longrightarrow> finite_pattern_instance V p t \<Longrightarrow>
    finite_enumeration_read tread t = Some ys \<Longrightarrow> False"
proof (induction p arbitrary: t ys)
  case (Finite_Variable v)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto split: if_splits finite_exact_target.splits)
next
  case (Finite_Pattern_Payload v)
  then show ?case by simp
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems(2) obtain u w where t: "t = Finite_Pair u w"
    and pu: "finite_pattern_instance V p u" and qw: "finite_pattern_instance V q w"
    by (cases t) auto
  from Finite_Pattern_Pair.prems(3) t obtain y ys' where uy: "tread u = Some y"
    and wy: "finite_enumeration_read tread w = Some ys'"
    by (auto split: option.splits)
  have "rd p = Unreadable \<or> finite_enumeration_pattern_read rd q = Unreadable"
    using Finite_Pattern_Pair.prems(1) by (auto simp: map_reading_cases dest: reading_pair_unreadable)
  then show ?case using items pu uy Finite_Pattern_Pair.IH(2)[OF _ qw wy] by blast
qed

definition finite_atom_entry ::
    "'a finite_term_pattern \<Rightarrow> (local_address \<times> 'a finite_term_pattern) material_reading" where
  "finite_atom_entry p = (case p of Finite_Pattern_Pair x q \<Rightarrow>
      (case x of Finite_Pattern_Payload a \<Rightarrow> Reading (a,q) | _ \<Rightarrow> ground_reading x)
    | _ \<Rightarrow> ground_reading p)"

definition finite_anchor_address ::
    "(local_address \<times> 'a finite_term_pattern) list \<Rightarrow> 'a finite_term_pattern \<Rightarrow> local_address material_reading" where
  "finite_anchor_address es q = (case q of
      Finite_Variable v \<Rightarrow> (case map_of (map (\<lambda>(a,p). (p,a)) es) q of Some a \<Rightarrow> Reading a | None \<Rightarrow> Open_Reading)
    | Finite_Pattern_Target (Finite_Anchor D a) \<Rightarrow> Reading a
    | _ \<Rightarrow> ground_reading q)"

definition finite_incidence_entry :: "(local_address \<times> 'a finite_term_pattern) list \<Rightarrow>
    'a finite_term_pattern \<Rightarrow> (local_address \<times> local_address \<times> local_address) material_reading" where
  "finite_incidence_entry es p = (case p of Finite_Pattern_Pair x (Finite_Pattern_Pair y z) \<Rightarrow>
      reading_pair (finite_anchor_address es x) (reading_pair (finite_anchor_address es y) (finite_anchor_address es z))
    | _ \<Rightarrow> ground_reading p)"

definition finite_attachment_value :: "'a finite_term_pattern \<Rightarrow> octets material_reading" where
  "finite_attachment_value w = (case w of Finite_Pattern_Payload v \<Rightarrow> Reading v | _ \<Rightarrow> ground_reading w)"

definition finite_attachment_entry :: "(local_address \<times> 'a finite_term_pattern) list \<Rightarrow>
    'a finite_term_pattern \<Rightarrow> (local_address \<times> octets) material_reading" where
  "finite_attachment_entry es p = (case p of Finite_Pattern_Pair x w \<Rightarrow>
      reading_pair (finite_anchor_address es x) (finite_attachment_value w)
    | _ \<Rightarrow> ground_reading p)"

fun finite_atom_entries :: "'a finite_term_pattern \<Rightarrow> (local_address \<times> 'a finite_term_pattern) list" where
  "finite_atom_entries (Finite_Pattern_Pair p q) =
    (case finite_atom_entry p of Reading e \<Rightarrow> [e] | _ \<Rightarrow> []) @ finite_atom_entries q"
| "finite_atom_entries p = []"

lemma finite_atom_entries_read:
  "finite_enumeration_pattern_read finite_atom_entry p = Reading es \<Longrightarrow> finite_atom_entries p = es"
  by (induction p arbitrary: es) (auto simp: map_reading_cases reading_pair_reading split: if_splits)

definition finite_material_skeleton :: "'a finite_material_pattern \<Rightarrow>
    (local_address list \<times> (local_address \<times> local_address \<times> local_address) list \<times>
      (local_address \<times> octets) list \<times> (local_address \<times> octets) list) material_reading" where
  "finite_material_skeleton M = (let es = finite_atom_entries (finite_material_atoms M) in
    map_material_reading (\<lambda>(es,E,B,F). (map fst es,E,B,F))
      (reading_pair (finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M))
        (reading_pair (finite_enumeration_pattern_read (finite_incidence_entry es) (finite_material_edges M))
          (reading_pair (finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_counts M))
            (finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_functions M))))))"

lemma finite_pattern_instance_shapes:
  "finite_pattern_instance V p (Finite_Pair a b) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or>
    (\<exists>x y. p = Finite_Pattern_Pair x y \<and> finite_pattern_instance V x a \<and> finite_pattern_instance V y b)"
  "finite_pattern_instance V p (Finite_Payload c) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or> p = Finite_Pattern_Payload c"
  "finite_pattern_instance V p (Finite_Target t) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or> p = Finite_Pattern_Target t"
  by (cases p; auto)+

lemma finite_material_read_shapes:
  "finite_occurrence_read C u = Some a \<Longrightarrow> u = Finite_Target (Finite_Anchor C a)"
  "finite_atom_read C u = Some y \<Longrightarrow> \<exists>x. u = Finite_Pair (Finite_Payload y) x \<and> finite_occurrence_read C x = Some y"
  "finite_incidence_read C u = Some e \<Longrightarrow> \<exists>ux uy uz. u = Finite_Pair ux (Finite_Pair uy uz) \<and>
    finite_occurrence_read C ux = Some (fst e) \<and> finite_occurrence_read C uy = Some (fst (snd e)) \<and>
    finite_occurrence_read C uz = Some (snd (snd e))"
  "finite_attachment_read C u = Some p \<Longrightarrow> \<exists>ux. u = Finite_Pair ux (Finite_Payload (snd p)) \<and>
    finite_occurrence_read C ux = Some (fst p)"
     apply (cases u; auto split: finite_exact_target.splits if_splits)
    apply (induction C u rule: finite_atom_read.induct; auto split: if_splits)
   apply (induction C u rule: finite_incidence_read.induct; auto split: option.splits)
  apply (induction C u rule: finite_attachment_read.induct; auto split: option.splits)
  done

lemma finite_atom_entry_instance:
  "finite_atom_entry q = Reading e \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> finite_atom_read C u = Some y \<Longrightarrow>
    y = fst e \<and> (\<exists>u'. finite_pattern_instance V (snd e) u' \<and> finite_occurrence_read C u' = Some (fst e))"
  by (auto simp: finite_atom_entry_def split: finite_term_pattern.splits finite_factor_term.splits if_splits)

lemma finite_atom_entry_unreadable:
  assumes entry: "finite_atom_entry q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_atom_read C u = Some y"
  shows False
proof -
  obtain x where u: "u = Finite_Pair (Finite_Payload y) x" using finite_material_read_shapes(2)[OF read] by blast
  show False using finite_pattern_instance_shapes(1)[OF inst_u[unfolded u]] entry
    by (auto simp: finite_atom_entry_def dest!: finite_pattern_instance_shapes(2))
qed

lemma finite_anchor_address_instance:
  assumes functional: "finite_relation_functional V"
    and held: "\<forall>e\<in>set es. \<exists>u. finite_pattern_instance V (snd e) u \<and> finite_occurrence_read C u = Some (fst e)"
    and address: "finite_anchor_address es q = Reading a0"
    and inst_u: "finite_pattern_instance V q u" and read: "finite_occurrence_read C u = Some a"
  shows "a0 = a"
proof (cases q)
  case (Finite_Variable v)
  then have "(a0,q) \<in> set es" using address map_of_SomeD[of "map (\<lambda>(a,p). (p,a)) es" q a0]
    by (auto simp: finite_anchor_address_def split: option.splits)
  then obtain u' where u': "finite_pattern_instance V q u'" "finite_occurrence_read C u' = Some a0"
    using held by fastforce
  have "u' = u" using functional u'(1) inst_u Finite_Variable
    by (auto simp: finite_relation_functional_correct single_valued_def)
  then show ?thesis using u'(2) read by simp
next
  case (Finite_Pattern_Target x)
  then show ?thesis using address inst_u read
    by (cases x) (auto simp: finite_anchor_address_def split: if_splits)
next
  case (Finite_Pattern_Payload v)
  then show ?thesis using address by (simp add: finite_anchor_address_def)
next
  case (Finite_Pattern_Pair p p')
  then show ?thesis using address by (simp add: finite_anchor_address_def)
qed

lemma finite_anchor_address_unreadable:
  assumes entry: "finite_anchor_address es q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_occurrence_read C u = Some a"
  shows False
  using finite_pattern_instance_shapes(3)[OF inst_u[unfolded finite_material_read_shapes(1)[OF read]]] entry
  by (auto simp: finite_anchor_address_def split: option.splits)

lemma finite_incidence_entry_instance:
  assumes functional: "finite_relation_functional V"
    and held: "\<forall>e\<in>set es. \<exists>u. finite_pattern_instance V (snd e) u \<and> finite_occurrence_read C u = Some (fst e)"
  shows "finite_incidence_entry es q = Reading e0 \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_incidence_read C u = Some e \<Longrightarrow> e0 = e"
proof -
  assume entry: "finite_incidence_entry es q = Reading e0" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_incidence_read C u = Some e"
  obtain x y z where q: "q = Finite_Pattern_Pair x (Finite_Pattern_Pair y z)"
    using entry by (auto simp: finite_incidence_entry_def split: finite_term_pattern.splits)
  obtain a0 b0 c0 where anchors: "finite_anchor_address es x = Reading a0" "finite_anchor_address es y = Reading b0"
      "finite_anchor_address es z = Reading c0" and e0: "e0 = (a0,b0,c0)"
    using entry by (auto simp: q finite_incidence_entry_def reading_pair_reading)
  obtain ux uy uz where u: "u = Finite_Pair ux (Finite_Pair uy uz)" and ix: "finite_pattern_instance V x ux"
      and iy: "finite_pattern_instance V y uy" and iz: "finite_pattern_instance V z uz"
    using inst_u by (auto simp: q split: finite_factor_term.splits)
  obtain a b c where e: "e = (a,b,c)" by (cases e) auto
  have reads: "finite_occurrence_read C ux = Some a \<and> finite_occurrence_read C uy = Some b \<and>
      finite_occurrence_read C uz = Some c"
    using read by (simp only: u e finite_incidence_read_pair)
  show "e0 = e"
    using finite_anchor_address_instance[OF functional held anchors(1) ix]
      finite_anchor_address_instance[OF functional held anchors(2) iy]
      finite_anchor_address_instance[OF functional held anchors(3) iz] reads e0 e by simp
qed

lemma finite_incidence_entry_unreadable:
  assumes entry: "finite_incidence_entry es q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_incidence_read C u = Some e"
  shows False
proof -
  obtain ux uy uz where u: "u = Finite_Pair ux (Finite_Pair uy uz)"
    and reads: "finite_occurrence_read C ux = Some (fst e)" "finite_occurrence_read C uy = Some (fst (snd e))"
      "finite_occurrence_read C uz = Some (snd (snd e))"
    using finite_material_read_shapes(3)[OF read] by blast
  show False
  proof (cases "\<exists>x y z. q = Finite_Pattern_Pair x (Finite_Pattern_Pair y z)")
    case True
    then obtain x y z where q: "q = Finite_Pattern_Pair x (Finite_Pattern_Pair y z)" by blast
    have ix: "finite_pattern_instance V x ux" and iy: "finite_pattern_instance V y uy"
      and iz: "finite_pattern_instance V z uz" using inst_u by (simp_all add: q u)
    have "finite_anchor_address es x = Unreadable \<or> finite_anchor_address es y = Unreadable \<or>
        finite_anchor_address es z = Unreadable"
      using entry by (auto simp: q finite_incidence_entry_def dest!: reading_pair_unreadable)
    then show False using finite_anchor_address_unreadable[OF _ ix reads(1)]
      finite_anchor_address_unreadable[OF _ iy reads(2)] finite_anchor_address_unreadable[OF _ iz reads(3)] by blast
  next
    case False
    show False using finite_pattern_instance_shapes(1)[OF inst_u[unfolded u]] entry False
      by (auto simp: finite_incidence_entry_def ground_reading_def dest!: finite_pattern_instance_shapes(1)
        split: finite_term_pattern.splits)
  qed
qed

lemma finite_attachment_entry_instance:
  assumes functional: "finite_relation_functional V"
    and held: "\<forall>e\<in>set es. \<exists>u. finite_pattern_instance V (snd e) u \<and> finite_occurrence_read C u = Some (fst e)"
  shows "finite_attachment_entry es q = Reading e0 \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_attachment_read C u = Some e \<Longrightarrow> e0 = e"
proof -
  assume entry: "finite_attachment_entry es q = Reading e0" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_attachment_read C u = Some e"
  obtain x w where q: "q = Finite_Pattern_Pair x w"
    using entry by (auto simp: finite_attachment_entry_def split: finite_term_pattern.splits)
  obtain a0 v where anchor: "finite_anchor_address es x = Reading a0" and val_w: "finite_attachment_value w = Reading v"
    and e0: "e0 = (a0,v)"
    using entry by (auto simp: q finite_attachment_entry_def reading_pair_reading)
  have w: "w = Finite_Pattern_Payload v"
    using val_w by (auto simp: finite_attachment_value_def split: finite_term_pattern.splits)
  obtain ux where u: "u = Finite_Pair ux (Finite_Payload v)" and ix: "finite_pattern_instance V x ux"
    using inst_u by (auto simp: q w split: finite_factor_term.splits)
  obtain a b where e: "e = (a,b)" by (cases e) auto
  have reads: "b = v \<and> finite_occurrence_read C ux = Some a"
    using read by (simp only: u e finite_attachment_read_pair)
  show "e0 = e" using finite_anchor_address_instance[OF functional held anchor ix] reads e0 e by simp
qed

lemma finite_attachment_entry_unreadable:
  assumes entry: "finite_attachment_entry es q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_attachment_read C u = Some p"
  shows False
proof -
  obtain ux where u: "u = Finite_Pair ux (Finite_Payload (snd p))"
    and occ: "finite_occurrence_read C ux = Some (fst p)"
    using finite_material_read_shapes(4)[OF read] by blast
  show False
  proof (cases q)
    case (Finite_Pattern_Pair x w)
    have ix: "finite_pattern_instance V x ux" and iw: "finite_pattern_instance V w (Finite_Payload (snd p))"
      using inst_u by (simp_all add: Finite_Pattern_Pair u)
    have "finite_anchor_address es x = Unreadable \<or> finite_attachment_value w = Unreadable"
      using entry by (auto simp: Finite_Pattern_Pair finite_attachment_entry_def dest!: reading_pair_unreadable)
    then show False using finite_anchor_address_unreadable[OF _ ix occ] finite_pattern_instance_shapes(2)[OF iw]
      by (auto simp: finite_attachment_value_def)
  qed (use entry inst_u u in \<open>auto simp: finite_attachment_entry_def\<close>)
qed

lemma finite_material_entries_unreadable:
  "finite_atom_entry q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> finite_atom_read C u \<noteq> Some y"
  "finite_incidence_entry es q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_incidence_read C u \<noteq> Some e"
  "finite_attachment_entry es q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_attachment_read C u \<noteq> Some p"
  using finite_atom_entry_unreadable finite_incidence_entry_unreadable finite_attachment_entry_unreadable by blast+

lemma finite_material_skeleton_read:
  assumes skeleton: "finite_material_skeleton M = Reading (A0,E0,B0,F0)"
  obtains es where "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    "finite_enumeration_pattern_read (finite_incidence_entry es) (finite_material_edges M) = Reading E0"
    "finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_counts M) = Reading B0"
    "finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_functions M) = Reading F0"
    "A0 = map fst es"
proof -
  obtain es where es: "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    and rest: "finite_enumeration_pattern_read (finite_incidence_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_edges M) = Reading E0"
      "finite_enumeration_pattern_read (finite_attachment_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_counts M) = Reading B0"
      "finite_enumeration_pattern_read (finite_attachment_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_functions M) = Reading F0"
    and A0: "A0 = map fst es"
    using skeleton by (auto simp: finite_material_skeleton_def Let_def map_reading_cases reading_pair_reading)
  show thesis using that[OF es] rest A0 unfolding finite_atom_entries_read[OF es] by blast
qed

theorem finite_material_skeleton_determined:
  assumes skeleton: "finite_material_skeleton M = Reading (A0,E0,B0,F0)"
    and functional: "finite_relation_functional V"
    and atoms: "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
    and edges: "finite_pattern_instance V (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C) E))"
    and counts: "finite_pattern_instance V (finite_material_counts M)
      (finite_enumeration_term (map (finite_attachment_term C) B))"
    and fns: "finite_pattern_instance V (finite_material_functions M)
      (finite_enumeration_term (map (finite_attachment_term C) F))"
  shows "A = A0 \<and> E = E0 \<and> B = B0 \<and> F = F0"
proof -
  obtain es where es: "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    and E0: "finite_enumeration_pattern_read (finite_incidence_entry es) (finite_material_edges M) = Reading E0"
    and B0: "finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_counts M) = Reading B0"
    and F0: "finite_enumeration_pattern_read (finite_attachment_entry es) (finite_material_functions M) = Reading F0"
    and A0: "A0 = map fst es"
    by (rule finite_material_skeleton_read[OF skeleton])
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    "finite_enumeration_read (finite_incidence_read C) (finite_enumeration_term (map (finite_incidence_term C) E)) = Some E"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) B)) = Some B"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) F)) = Some F"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)+
  have rows: "list_all2 (\<lambda>e y. y = fst e \<and> (\<exists>u'. finite_pattern_instance V (snd e) u' \<and>
      finite_occurrence_read C u' = Some (fst e))) es A"
    by (rule finite_enumeration_pattern_instance[OF finite_atom_entry_instance es atoms reads(1)])
  then have A: "A = map fst es"
    and held: "\<forall>e\<in>set es. \<exists>u. finite_pattern_instance V (snd e) u \<and> finite_occurrence_read C u = Some (fst e)"
    by (simp_all add: list_all2_function_restricted)
  have "list_all2 (=) E0 E"
    by (rule finite_enumeration_pattern_instance[OF finite_incidence_entry_instance[OF functional held] E0 edges reads(2)])
  moreover have "list_all2 (=) B0 B"
    by (rule finite_enumeration_pattern_instance[OF finite_attachment_entry_instance[OF functional held] B0 counts reads(3)])
  moreover have "list_all2 (=) F0 F"
    by (rule finite_enumeration_pattern_instance[OF finite_attachment_entry_instance[OF functional held] F0 fns reads(4)])
  ultimately show ?thesis using A A0 by (simp add: list.rel_eq)
qed

text \<open>A skeleton without a reading has no satisfying binding, functional or not.\<close>

theorem finite_material_skeleton_unreadable:
  assumes skeleton: "finite_material_skeleton M = Unreadable"
  shows "\<not> finite_material_satisfied V M"
proof
  assume sat: "finite_material_satisfied V M"
  obtain C A E B F where en: "finite_artifact_enumeration C A E B F"
    and inst: "finite_pattern_instance V (finite_material_source M) (Finite_Target (Finite_Whole C))"
      "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
      "finite_pattern_instance V (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C) E))"
      "finite_pattern_instance V (finite_material_counts M) (finite_enumeration_term (map (finite_attachment_term C) B))"
      "finite_pattern_instance V (finite_material_functions M)
        (finite_enumeration_term (map (finite_attachment_term C) F))"
    by (rule finite_material_satisfied_witness[OF sat])
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    "finite_enumeration_read (finite_incidence_read C) (finite_enumeration_term (map (finite_incidence_term C) E)) = Some E"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) B)) = Some B"
    "finite_enumeration_read (finite_attachment_read C) (finite_enumeration_term (map (finite_attachment_term C) F)) = Some F"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)+
  have i1: "\<forall>q u y. finite_atom_entry q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_atom_read C u \<noteq> Some y"
    using finite_material_entries_unreadable(1) by blast
  have i2: "\<forall>q u y. finite_incidence_entry es q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_incidence_read C u \<noteq> Some y" for es
    using finite_material_entries_unreadable(2) by blast
  have i3: "\<forall>q u y. finite_attachment_entry es q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_attachment_read C u \<noteq> Some y" for es
    using finite_material_entries_unreadable(3) by blast
  have "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Unreadable \<or>
      finite_enumeration_pattern_read (finite_incidence_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_edges M) = Unreadable \<or>
      finite_enumeration_pattern_read (finite_attachment_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_counts M) = Unreadable \<or>
      finite_enumeration_pattern_read (finite_attachment_entry (finite_atom_entries (finite_material_atoms M)))
        (finite_material_functions M) = Unreadable"
    using skeleton by (auto simp: finite_material_skeleton_def Let_def map_reading_cases dest!: reading_pair_unreadable)
  then show False
    using finite_enumeration_pattern_unreadable[OF i1 _ inst(2) reads(1)]
      finite_enumeration_pattern_unreadable[OF i2 _ inst(3) reads(2)]
      finite_enumeration_pattern_unreadable[OF i3 _ inst(4) reads(3)]
      finite_enumeration_pattern_unreadable[OF i3 _ inst(5) reads(4)]
    by blast
qed

section \<open>Bindings of a material premise\<close>

text \<open>
  A solution binds exactly the premise's variables, functionally, to formed terms, and satisfies the
  premise. The binding of candidate operands is what matching each field against them binds; it is
  a solution exactly when it passes that check.
\<close>

definition finite_material_solution :: "'a finite_material_pattern \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> bool" where
  "finite_material_solution M W \<longleftrightarrow>
    finite_term_bindings_formed (finite_material_variables M) W \<and> finite_material_satisfied W M"

fun finite_material_tuple_binding :: "'a finite_material_pattern \<Rightarrow>
    finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<Rightarrow>
    ('a \<times> finite_factor_term) fset" where
  "finite_material_tuple_binding M (s,a,e,b,f) =
    finite_matching_bindings (finite_material_source M) s |\<union>| finite_matching_bindings (finite_material_atoms M) a |\<union>|
    finite_matching_bindings (finite_material_edges M) e |\<union>| finite_matching_bindings (finite_material_counts M) b |\<union>|
    finite_matching_bindings (finite_material_functions M) f"

definition finite_material_candidates :: "'a finite_material_pattern \<Rightarrow>
    (finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term \<times> finite_factor_term) list \<Rightarrow>
    ('a \<times> finite_factor_term) fset fset" where
  "finite_material_candidates M ts =
    ffilter (finite_material_solution M) (fset_of_list (map (finite_material_tuple_binding M) ts))"

lemma finite_matching_bindings_instance:
  assumes functional: "finite_relation_functional V"
  shows "finite_pattern_instance V p t \<Longrightarrow>
    finite_matching_bindings p t = ffilter (\<lambda>x. fst x |\<in>| finite_pattern_variables p) V"
proof (induction p arbitrary: t)
  case (Finite_Variable v)
  then have "(v,t) |\<in>| V" by simp
  then show ?case using functional
    by (auto simp: finite_relation_functional_correct single_valued_def fset_eq_iff)
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto simp: fset_eq_iff)
next
  case (Finite_Pattern_Payload v)
  then show ?case by (auto simp: fset_eq_iff)
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems obtain x y where t: "t = Finite_Pair x y"
    and px: "finite_pattern_instance V p x" and qy: "finite_pattern_instance V q y"
    by (cases t) auto
  show ?case using Finite_Pattern_Pair.IH(1)[OF px] Finite_Pattern_Pair.IH(2)[OF qy] t
    by (auto simp: fset_eq_iff)
qed

lemma finite_material_tuple_binding_instance:
  assumes functional: "finite_relation_functional V"
    and "finite_pattern_instance V (finite_material_source M) s" "finite_pattern_instance V (finite_material_atoms M) a"
      "finite_pattern_instance V (finite_material_edges M) e" "finite_pattern_instance V (finite_material_counts M) b"
      "finite_pattern_instance V (finite_material_functions M) f"
  shows "finite_material_tuple_binding M (s,a,e,b,f) = ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V"
  using assms(2-6) by (simp add: finite_matching_bindings_instance[OF functional] finite_material_variables_def
    fset_eq_iff) auto

lemma finite_pattern_instance_restrict:
  "finite_pattern_variables p |\<subseteq>| X \<Longrightarrow>
    finite_pattern_instance (ffilter (\<lambda>x. fst x |\<in>| X) V) p t \<longleftrightarrow> finite_pattern_instance V p t"
  by (induction p arbitrary: t) (auto split: finite_factor_term.splits)

lemma finite_pattern_instances_restrict:
  "finite_pattern_variables p |\<subseteq>| X \<Longrightarrow>
    finite_pattern_instances (ffilter (\<lambda>x. fst x |\<in>| X) V) p = finite_pattern_instances V p"
  by (simp add: fset_eq_iff finite_pattern_instances_member finite_pattern_instance_restrict)

lemma finite_material_satisfied_restrict:
  assumes "finite_material_variables M |\<subseteq>| X"
  shows "finite_material_satisfied (ffilter (\<lambda>x. fst x |\<in>| X) V) M \<longleftrightarrow> finite_material_satisfied V M"
  using assms by (simp add: finite_material_satisfied_def finite_material_variables_def finite_pattern_instances_restrict)

lemma finite_pattern_instance_bound:
  "finite_pattern_instance V p t \<Longrightarrow> finite_pattern_variables p |\<subseteq>| fimage fst V"
  by (induction p arbitrary: t) (force split: finite_factor_term.splits)+

lemma finite_pattern_instance_unique:
  assumes functional: "finite_relation_functional V"
  shows "finite_pattern_instance V p t \<Longrightarrow> finite_pattern_instance V p t' \<Longrightarrow> t = t'"
  using functional
  by (induction p arbitrary: t t')
    (auto simp: finite_relation_functional_correct single_valued_def split: finite_factor_term.splits)

lemma finite_material_solution_restrict:
  assumes formed: "finite_term_bindings_formed B V" and sat: "finite_material_satisfied V M"
  shows "finite_material_solution M (ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V)"
proof -
  have functional: "finite_relation_functional V" and vals: "fBall V (\<lambda>(a,t). finite_term_formed t)"
    using formed by (simp_all add: finite_term_bindings_formed_def)
  obtain s a e b f where inst: "finite_pattern_instance V (finite_material_source M) s"
      "finite_pattern_instance V (finite_material_atoms M) a"
      "finite_pattern_instance V (finite_material_edges M) e"
      "finite_pattern_instance V (finite_material_counts M) b"
      "finite_pattern_instance V (finite_material_functions M) f"
    using sat by (auto simp: finite_material_satisfied_def finite_pattern_instances_member)
  have bound: "finite_material_variables M |\<subseteq>| fimage fst V"
    using finite_pattern_instance_bound[OF inst(1)] finite_pattern_instance_bound[OF inst(2)]
      finite_pattern_instance_bound[OF inst(3)] finite_pattern_instance_bound[OF inst(4)]
      finite_pattern_instance_bound[OF inst(5)]
    by (simp add: finite_material_variables_def)
  have keys: "fimage fst (ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V) = finite_material_variables M"
    using bound by (auto simp: fset_eq_iff fsubset_iff fimage_iff)
  show ?thesis
    unfolding finite_material_solution_def finite_term_bindings_formed_def
    using functional vals keys sat finite_material_satisfied_restrict[of M "finite_material_variables M" V]
    by (auto simp: finite_relation_functional_correct single_valued_def)
qed

lemma finite_material_candidates_single:
  "finite_material_candidates M [t] = (if finite_material_solution M (finite_material_tuple_binding M t)
    then {|finite_material_tuple_binding M t|} else {||})"
  by (cases "finite_material_solution M (finite_material_tuple_binding M t)")
    (auto simp: finite_material_candidates_def fset_inject[symmetric] ffilter.rep_eq fset_of_list.rep_eq)

lemma finite_material_candidates_sound:
  "W |\<in>| finite_material_candidates M ts \<Longrightarrow> finite_material_solution M W"
  by (simp add: finite_material_candidates_def)

lemma finite_material_candidates_complete:
  assumes formed: "finite_term_bindings_formed B V" and sat: "finite_material_satisfied V M"
    and member: "(s,a,e,b,f) \<in> set ts"
    and inst: "finite_pattern_instance V (finite_material_source M) s" "finite_pattern_instance V (finite_material_atoms M) a"
      "finite_pattern_instance V (finite_material_edges M) e" "finite_pattern_instance V (finite_material_counts M) b"
      "finite_pattern_instance V (finite_material_functions M) f"
  shows "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V |\<in>| finite_material_candidates M ts"
proof -
  have functional: "finite_relation_functional V" using formed by (simp add: finite_term_bindings_formed_def)
  have "finite_material_tuple_binding M (s,a,e,b,f) = ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V"
    by (rule finite_material_tuple_binding_instance[OF functional inst])
  then show ?thesis using member finite_material_solution_restrict[OF formed sat]
    by (force simp: finite_material_candidates_def fset_of_list_elem)
qed

section \<open>The material premise solved\<close>

datatype 'a finite_material_outcome =
    Material_Waits
  | Material_Solutions "('a \<times> finite_factor_term) fset fset"

definition finite_material_resolution :: "'a finite_material_pattern \<Rightarrow> 'a finite_material_outcome" where
  "finite_material_resolution M = (case finite_material_skeleton M of
      Reading (A,E,B,F) \<Rightarrow> Material_Solutions (finite_material_candidates M
        [finite_material_tuple (finite_enumerated_artifact A E B F) (A,E,B,F)])
    | Unreadable \<Rightarrow> Material_Solutions {||}
    | Open_Reading \<Rightarrow> if finite_pattern_variables (finite_material_source M)={||} then
        Material_Solutions (case finite_material_source M of
          Finite_Pattern_Target (Finite_Whole C) \<Rightarrow>
            finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))
        | _ \<Rightarrow> {||})
      else Material_Waits)"

theorem finite_material_resolution_waits:
  "finite_material_resolution M = Material_Waits \<longleftrightarrow>
    finite_material_skeleton M = Open_Reading \<and> finite_pattern_variables (finite_material_source M) \<noteq> {||}"
  by (auto simp: finite_material_resolution_def split: material_reading.splits prod.splits)

theorem finite_material_resolution_sound:
  assumes res: "finite_material_resolution M = Material_Solutions S" and member: "W |\<in>| S"
  shows "finite_term_bindings_formed (finite_material_variables M) W \<and> finite_material_satisfied W M"
proof -
  have "S = {||} \<or> (\<exists>ts. S = finite_material_candidates M ts)"
  proof (cases "finite_material_skeleton M")
    case Open_Reading
    then show ?thesis using res
      by (cases "finite_material_source M")
        (auto simp: finite_material_resolution_def split: if_splits finite_exact_target.splits)
  next
    case (Reading sk)
    then show ?thesis using res by (cases sk) (auto simp: finite_material_resolution_def)
  next
    case Unreadable
    then show ?thesis using res by (simp add: finite_material_resolution_def)
  qed
  then show ?thesis using member finite_material_candidates_sound
    by (auto simp: finite_material_solution_def)
qed

theorem finite_material_resolution_complete:
  assumes res: "finite_material_resolution M = Material_Solutions S"
    and formed: "finite_term_bindings_formed B V" and sat: "finite_material_satisfied V M"
  shows "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V |\<in>| S"
proof -
  have functional: "finite_relation_functional V" using formed by (simp add: finite_term_bindings_formed_def)
  obtain C A E B F where en: "finite_artifact_enumeration C A E B F"
    and inst: "finite_pattern_instance V (finite_material_source M) (Finite_Target (Finite_Whole C))"
      "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
      "finite_pattern_instance V (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C) E))"
      "finite_pattern_instance V (finite_material_counts M) (finite_enumeration_term (map (finite_attachment_term C) B))"
      "finite_pattern_instance V (finite_material_functions M)
        (finite_enumeration_term (map (finite_attachment_term C) F))"
    by (rule finite_material_satisfied_witness[OF sat])
  have member: "\<And>ts. finite_material_tuple C (A,E,B,F) \<in> set ts \<Longrightarrow>
      ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) V |\<in>| finite_material_candidates M ts"
    using finite_material_candidates_complete[OF formed sat _ inst] by simp
  show ?thesis
  proof (cases "finite_material_skeleton M")
    case Open_Reading
    have ground: "finite_pattern_variables (finite_material_source M) = {||}"
      using res Open_Reading by (auto simp: finite_material_resolution_def split: if_splits)
    have source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
      using inst(1) ground by (cases "finite_material_source M") (auto split: finite_factor_term.splits)
    have formedC: "finite_exact_formed C" using en unfolding finite_artifact_enumeration_def by blast
    have S: "S = finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))"
      using res Open_Reading ground source by (simp add: finite_material_resolution_def)
    have "finite_material_tuple C (A,E,B,F) \<in> set (map (finite_material_tuple C) (finite_artifact_enumerations C))"
      using finite_artifact_enumerations_exact[OF formedC] en by (metis imageI list.set_map)
    then show ?thesis using member S by simp
  next
    case (Reading sk)
    obtain A0 E0 B0 F0 where sk: "sk = (A0,E0,B0,F0)" by (cases sk) auto
    have same: "A = A0 \<and> E = E0 \<and> B = B0 \<and> F = F0"
      using finite_material_skeleton_determined[OF Reading[unfolded sk] functional inst(2-5)] .
    have C: "C = finite_enumerated_artifact A E B F" using en unfolding finite_artifact_enumeration_def by blast
    have "S = finite_material_candidates M [finite_material_tuple C (A,E,B,F)]"
      using res Reading sk same C by (simp add: finite_material_resolution_def)
    then show ?thesis using member by simp
  next
    case Unreadable
    then show ?thesis using finite_material_skeleton_unreadable sat by blast
  qed
qed

theorem finite_material_resolution_exact:
  assumes res: "finite_material_resolution M = Material_Solutions S"
  shows "W |\<in>| S \<longleftrightarrow> finite_material_solution M W"
proof
  assume "W |\<in>| S"
  then show "finite_material_solution M W"
    using finite_material_resolution_sound[OF res] by (simp add: finite_material_solution_def)
next
  assume "finite_material_solution M W"
  then have formed: "finite_term_bindings_formed (finite_material_variables M) W"
    and sat: "finite_material_satisfied W M" by (simp_all add: finite_material_solution_def)
  have keys: "fimage fst W = finite_material_variables M"
    using formed by (simp add: finite_term_bindings_formed_def)
  have "ffilter (\<lambda>x. fst x |\<in>| fimage fst W) W = W" by (force simp: fset_eq_iff)
  then have "ffilter (\<lambda>x. fst x |\<in>| finite_material_variables M) W = W" by (simp only: keys)
  then show "W |\<in>| S" using finite_material_resolution_complete[OF res formed sat] by simp
qed

theorem finite_material_resolution_none:
  assumes res: "finite_material_resolution M = Material_Solutions S"
  shows "S = {||} \<longleftrightarrow> \<not>(\<exists>B V. finite_term_bindings_formed B V \<and> finite_material_satisfied V M)"
proof
  assume "S = {||}"
  then show "\<not>(\<exists>B V. finite_term_bindings_formed B V \<and> finite_material_satisfied V M)"
    using finite_material_resolution_complete[OF res] by auto
next
  assume none: "\<not>(\<exists>B V. finite_term_bindings_formed B V \<and> finite_material_satisfied V M)"
  show "S = {||}"
  proof (rule ccontr)
    assume "S \<noteq> {||}"
    then obtain W where "W |\<in>| S" by blast
    then show False using none finite_material_resolution_sound[OF res] by blast
  qed
qed

text \<open>
  A ground skeleton has one solution or none, and it determines the source and every anchor: a binding
  that satisfies the premise instantiates the source as the whole target of the skeleton's artifact
  and the atoms as the enumeration of its atoms, each anchor its occurrence.
\<close>

theorem finite_material_resolution_skeleton:
  assumes "finite_material_skeleton M = Reading (A,E,B,F)"
  shows "finite_material_resolution M = Material_Solutions
    (let W = finite_material_tuple_binding M (finite_material_tuple (finite_enumerated_artifact A E B F) (A,E,B,F))
     in if finite_material_solution M W then {|W|} else {||})"
  using assms by (simp add: finite_material_resolution_def finite_material_candidates_single Let_def)

theorem finite_material_skeleton_source_anchors:
  assumes skeleton: "finite_material_skeleton M = Reading (A,E,B,F)"
    and functional: "finite_relation_functional V" and sat: "finite_material_satisfied V M"
  shows "finite_artifact_enumeration (finite_enumerated_artifact A E B F) A E B F"
    "finite_pattern_instance V (finite_material_source M) s \<longleftrightarrow>
      s = Finite_Target (Finite_Whole (finite_enumerated_artifact A E B F))"
    "finite_pattern_instance V (finite_material_atoms M) a \<longleftrightarrow>
      a = finite_enumeration_term (map (finite_atom_term (finite_enumerated_artifact A E B F)) A)"
proof -
  obtain C A' E' B' F' where en: "finite_artifact_enumeration C A' E' B' F'"
    and inst: "finite_pattern_instance V (finite_material_source M) (Finite_Target (Finite_Whole C))"
      "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A'))"
      "finite_pattern_instance V (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C) E'))"
      "finite_pattern_instance V (finite_material_counts M) (finite_enumeration_term (map (finite_attachment_term C) B'))"
      "finite_pattern_instance V (finite_material_functions M)
        (finite_enumeration_term (map (finite_attachment_term C) F'))"
    by (rule finite_material_satisfied_witness[OF sat])
  have same: "A' = A \<and> E' = E \<and> B' = B \<and> F' = F"
    using finite_material_skeleton_determined[OF skeleton functional inst(2-5)] .
  have C: "C = finite_enumerated_artifact A E B F"
    using en same unfolding finite_artifact_enumeration_def by blast
  show "finite_artifact_enumeration (finite_enumerated_artifact A E B F) A E B F"
    using en same unfolding C by blast
  show "finite_pattern_instance V (finite_material_source M) s \<longleftrightarrow>
      s = Finite_Target (Finite_Whole (finite_enumerated_artifact A E B F))"
    using inst(1) C finite_pattern_instance_unique[OF functional] by blast
  show "finite_pattern_instance V (finite_material_atoms M) a \<longleftrightarrow>
      a = finite_enumeration_term (map (finite_atom_term (finite_enumerated_artifact A E B F)) A)"
    using inst(2) C same finite_pattern_instance_unique[OF functional] by blast
qed

text \<open>
  A ground source that is a whole artifact has as solutions its enumerations: each enumeration's
  operands give one binding, and every binding that is a solution is one of these.
\<close>

theorem finite_material_resolution_source:
  assumes skeleton: "finite_material_skeleton M = Open_Reading"
    and source: "finite_material_source M = Finite_Pattern_Target (Finite_Whole C)"
  shows "finite_material_resolution M =
      Material_Solutions (finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C)))"
    "W |\<in>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C)) \<longleftrightarrow>
      (\<exists>A E B F. finite_artifact_enumeration C A E B F \<and>
        W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F)) \<and> finite_material_solution M W)"
proof -
  show res: "finite_material_resolution M =
      Material_Solutions (finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C)))"
    using skeleton source by (simp add: finite_material_resolution_def)
  show "W |\<in>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C)) \<longleftrightarrow>
      (\<exists>A E B F. finite_artifact_enumeration C A E B F \<and>
        W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F)) \<and> finite_material_solution M W)"
  proof
    assume member: "W |\<in>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))"
    then have solution: "finite_material_solution M W" by (rule finite_material_candidates_sound)
    obtain A E B F where listed: "(A,E,B,F) \<in> set (finite_artifact_enumerations C)"
      and W: "W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F))"
      using member by (auto simp: finite_material_candidates_def fset_of_list_elem)
    have sat: "finite_material_satisfied W M" using solution by (simp add: finite_material_solution_def)
    obtain C' A' E' B' F' where en: "finite_artifact_enumeration C' A' E' B' F'"
      and inst: "finite_pattern_instance W (finite_material_source M) (Finite_Target (Finite_Whole C'))"
        "finite_pattern_instance W (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C') A'))"
        "finite_pattern_instance W (finite_material_edges M) (finite_enumeration_term (map (finite_incidence_term C') E'))"
        "finite_pattern_instance W (finite_material_counts M)
          (finite_enumeration_term (map (finite_attachment_term C') B'))"
        "finite_pattern_instance W (finite_material_functions M)
          (finite_enumeration_term (map (finite_attachment_term C') F'))"
      by (rule finite_material_satisfied_witness[OF sat])
    have "C' = C" using inst(1) source by simp
    then have "finite_exact_formed C" using en unfolding finite_artifact_enumeration_def by blast
    then show "\<exists>A E B F. finite_artifact_enumeration C A E B F \<and>
        W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F)) \<and> finite_material_solution M W"
      using listed W solution finite_artifact_enumerations_exact by blast
  next
    assume "\<exists>A E B F. finite_artifact_enumeration C A E B F \<and>
        W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F)) \<and> finite_material_solution M W"
    then obtain A E B F where en: "finite_artifact_enumeration C A E B F"
      and W: "W = finite_material_tuple_binding M (finite_material_tuple C (A,E,B,F))"
      and solution: "finite_material_solution M W" by blast
    have "(A,E,B,F) \<in> set (finite_artifact_enumerations C)"
      using en finite_artifact_enumerations_exact by (auto simp: finite_artifact_enumeration_def)
    then show "W |\<in>| finite_material_candidates M (map (finite_material_tuple C) (finite_artifact_enumerations C))"
      using W solution by (force simp: finite_material_candidates_def fset_of_list_elem)
  qed
qed

end
