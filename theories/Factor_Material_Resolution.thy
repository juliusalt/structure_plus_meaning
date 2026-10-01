theory Factor_Material_Resolution
  imports Factor_Finite_Material_Arguments Factor_Executable_Matching
begin

text \<open>
  A material premise is solved, not only checked. Its fields' skeleton -- the addresses of its atoms,
  the address triples of its incidences, the addresses and values of its attachments -- determines the
  observed artifact when it is ground, and the solution is then the one binding that binds the source
  to that artifact's whole target and every anchor to its occurrence, or none. A premise whose source is
  ground has as solutions the enumerations of that source. A premise with neither waits: that outcome
  is kept apart from a premise with no solution. The solution reads the payloads of the atoms, the
  incidences and the attachments as addresses, the material equation's own reading, and compares
  variables for equality alone.
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
    finite_data_sequence (map finite_incidence_data E),
    finite_data_sequence (map finite_address_pair_data B),
    finite_data_sequence (map finite_address_pair_data F))"

lemma finite_material_arguments_tuple:
  "finite_material_arguments C = finite_material_tuple C (finite_artifact_rows C)"
  by (simp add: finite_material_arguments_def split: prod.split)

lemma finite_material_term_reads:
  "finite_atom_read C (finite_atom_term C a) = Some a"
  "finite_incidence_read (finite_incidence_data e) = Some e"
  "finite_attachment_read (finite_address_pair_data p) = Some p"
  by (auto simp: finite_atom_term_def finite_occurrence_term_def finite_incidence_data_def
    finite_address_pair_data_def split: prod.splits)

lemma finite_enumeration_read_term:
  assumes "\<And>x. rd (mk x) = Some x"
  shows "finite_enumeration_read rd (finite_enumeration_term (map mk xs)) = Some xs"
  using assms by (rule finite_list_read_term) simp

lemma finite_data_list_read_term:
  assumes "\<And>x. rd (mk x) = Some x"
  shows "finite_list_read (Finite_Payload []) rd (finite_data_sequence (map mk xs)) = Some xs"
  using assms by (rule finite_list_read_term) simp

lemma finite_material_read_injective:
  "finite_atom_read C u = Some x \<Longrightarrow> finite_atom_read C u' = Some x \<Longrightarrow> u = u'"
  "finite_incidence_read u = Some e \<Longrightarrow> finite_incidence_read u' = Some e \<Longrightarrow> u = u'"
  "finite_attachment_read u = Some p \<Longrightarrow> finite_attachment_read u' = Some p \<Longrightarrow> u = u'"
    apply (metis finite_atom_read_correct decode_finite_term_injective)
   apply (metis finite_incidence_read_correct decode_finite_term_injective)
  apply (metis finite_attachment_read_correct decode_finite_term_injective)
  done

lemmas finite_enumeration_read_injective =
  finite_list_read_injective[where z="Finite_Target (Finite_Whole finite_empty_artifact)"]

text \<open>
  A satisfied material premise is satisfied at the operands of an enumeration: the observation reads
  each operand as the enumeration of its entries, and the reading determines the operand.
\<close>

lemma finite_material_satisfied_witness:
  assumes "finite_material_satisfied V M"
  obtains C A E B F where "finite_artifact_enumeration C A E B F"
    "finite_pattern_instance V (finite_material_source M) (Finite_Target (Finite_Whole C))"
    "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
    "finite_pattern_instance V (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E))"
    "finite_pattern_instance V (finite_material_counts M) (finite_data_sequence (map finite_address_pair_data B))"
    "finite_pattern_instance V (finite_material_functions M) (finite_data_sequence (map finite_address_pair_data F))"
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
    and re: "finite_list_read (Finite_Payload []) finite_incidence_read e = Some E"
    and rb: "finite_list_read (Finite_Payload []) finite_attachment_read b = Some B"
    and rf: "finite_list_read (Finite_Payload []) finite_attachment_read f = Some F"
    using obs unfolding s finite_material_observation_whole by blast
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)
  have data_reads:
    "finite_list_read (Finite_Payload []) finite_incidence_read (finite_data_sequence (map finite_incidence_data E)) = Some E"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data B)) = Some B"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data F)) = Some F"
    by (rule finite_data_list_read_term, rule finite_material_term_reads)+
  have terms: "a = finite_enumeration_term (map (finite_atom_term C) A)"
    "e = finite_data_sequence (map finite_incidence_data E)"
    "b = finite_data_sequence (map finite_address_pair_data B)"
    "f = finite_data_sequence (map finite_address_pair_data F)"
    using finite_enumeration_read_injective[OF finite_material_read_injective(1) ra reads]
      finite_list_read_injective[OF finite_material_read_injective(2) re data_reads(1)]
      finite_list_read_injective[OF finite_material_read_injective(3) rb data_reads(2)]
      finite_list_read_injective[OF finite_material_read_injective(3) rf data_reads(3)]
    by simp_all
  show thesis using inst unfolding s terms by (rule that[OF en])
qed

section \<open>The skeleton of a material premise\<close>

text \<open>
  A skeleton position is read, has no reading though it holds no variable, or is open. The atoms field
  is an enumeration pattern whose entries pair a payload, the atom's address, with an anchor pattern.
  The incidences and the attachments are data-list patterns whose entries pair payloads: an address or a
  value is read where a payload stands and is open where a variable does. The skeleton has no reading
  when some position has none, whatever else is still open:
  an entry with no reading has none under every substitution of the open parts, while every solution's
  instance reads, so no binding satisfies the premise. Otherwise the skeleton is read when every
  position is, and open when some position holds a variable or an unheld anchor variable.
\<close>

datatype 'x material_reading = Reading 'x | Unreadable | Open_Reading

fun reading_pair :: "'x material_reading \<Rightarrow> 'y material_reading \<Rightarrow> ('x \<times> 'y) material_reading" where
  "reading_pair (Reading x) (Reading y) = Reading (x,y)"
| "reading_pair Unreadable r = Unreadable"
| "reading_pair r Unreadable = Unreadable"
| "reading_pair r s = Open_Reading"

lemma reading_pair_reading:
  "reading_pair r s = Reading z \<longleftrightarrow> (\<exists>x y. r = Reading x \<and> s = Reading y \<and> z = (x,y))"
  by (cases r; cases s) auto

text \<open>
  A pairing has no reading exactly when a part has none, whatever the other; it is open exactly when neither
  part lacks a reading and one is open. Pairing an open part with one that has no reading is the one pairing
  whose value this reading gives as unreadable rather than open.
\<close>

lemma reading_pair_unreadable_iff:
  "reading_pair r s = Unreadable \<longleftrightarrow> r = Unreadable \<or> s = Unreadable"
  by (cases r; cases s) auto

lemma reading_pair_unreadable:
  "reading_pair r s = Unreadable \<Longrightarrow> r = Unreadable \<or> s = Unreadable"
  by (simp add: reading_pair_unreadable_iff)

lemma reading_pair_open:
  "reading_pair r s = Open_Reading \<longleftrightarrow>
    r \<noteq> Unreadable \<and> s \<noteq> Unreadable \<and> (r = Open_Reading \<or> s = Open_Reading)"
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

text \<open>
  A list field is read over its terminator, as the term reader @{const finite_list_read} reads its value: the
  terminator reads the empty list, any other leaf has no reading under any substitution, a variable is open,
  and a pair reads its entry and then the rest. The enumeration fields are read at the empty artifact's whole
  target.
\<close>

fun finite_list_pattern_read ::
    "finite_factor_term \<Rightarrow> ('a finite_term_pattern \<Rightarrow> 'x material_reading) \<Rightarrow> 'a finite_term_pattern \<Rightarrow>
      'x list material_reading" where
  "finite_list_pattern_read z rd (Finite_Variable v) = Open_Reading"
| "finite_list_pattern_read z rd (Finite_Pattern_Target t) =
    (if Finite_Target t = z then Reading [] else Unreadable)"
| "finite_list_pattern_read z rd (Finite_Pattern_Payload v) =
    (if Finite_Payload v = z then Reading [] else Unreadable)"
| "finite_list_pattern_read z rd (Finite_Pattern_Pair p q) =
    map_material_reading (\<lambda>(x,xs). x#xs) (reading_pair (rd p) (finite_list_pattern_read z rd q))"

abbreviation finite_enumeration_pattern_read ::
    "('a finite_term_pattern \<Rightarrow> 'x material_reading) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'x list material_reading" where
  "finite_enumeration_pattern_read \<equiv> finite_list_pattern_read (Finite_Target (Finite_Whole finite_empty_artifact))"

lemma finite_list_pattern_instance:
  assumes items: "\<And>q u x y. rd q = Reading x \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> tread u = Some y \<Longrightarrow> R x y"
  shows "finite_list_pattern_read z rd p = Reading xs \<Longrightarrow> finite_pattern_instance V p t \<Longrightarrow>
    finite_list_read z tread t = Some ys \<Longrightarrow> list_all2 R xs ys"
proof (induction p arbitrary: t xs ys)
  case (Finite_Variable v)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto split: if_splits)
next
  case (Finite_Pattern_Payload v)
  then show ?case by (auto split: if_splits)
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems(1) obtain x xs' where px: "rd p = Reading x"
    and qx: "finite_list_pattern_read z rd q = Reading xs'" and xs: "xs = x#xs'"
    by (auto simp: map_reading_cases reading_pair_reading)
  from Finite_Pattern_Pair.prems(2) obtain u w where t: "t = Finite_Pair u w"
    and pu: "finite_pattern_instance V p u" and qw: "finite_pattern_instance V q w"
    by (cases t) auto
  from Finite_Pattern_Pair.prems(3) t obtain y ys' where uy: "tread u = Some y"
    and wy: "finite_list_read z tread w = Some ys'" and ys: "ys = y#ys'"
    by (auto split: option.splits)
  show ?case using items[OF px pu uy] Finite_Pattern_Pair.IH(2)[OF qx qw wy] xs ys by simp
qed

lemma finite_list_pattern_unreadable:
  assumes items: "\<forall>q u y. rd q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow> tread u \<noteq> Some y"
  shows "finite_list_pattern_read z rd p = Unreadable \<Longrightarrow> finite_pattern_instance V p t \<Longrightarrow>
    finite_list_read z tread t = Some ys \<Longrightarrow> False"
proof (induction p arbitrary: t ys)
  case (Finite_Variable v)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  then show ?case by (auto split: if_splits)
next
  case (Finite_Pattern_Payload v)
  then show ?case by (auto split: if_splits)
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems(2) obtain u w where t: "t = Finite_Pair u w"
    and pu: "finite_pattern_instance V p u" and qw: "finite_pattern_instance V q w"
    by (cases t) auto
  from Finite_Pattern_Pair.prems(3) t obtain y ys' where uy: "tread u = Some y"
    and wy: "finite_list_read z tread w = Some ys'"
    by (auto split: option.splits)
  have "rd p = Unreadable \<or> finite_list_pattern_read z rd q = Unreadable"
    using Finite_Pattern_Pair.prems(1) by (auto simp: map_reading_cases dest: reading_pair_unreadable)
  then show ?case using items pu uy Finite_Pattern_Pair.IH(2)[OF _ qw wy] by blast
qed

lemmas finite_enumeration_pattern_instance =
  finite_list_pattern_instance[where z="Finite_Target (Finite_Whole finite_empty_artifact)"]

lemmas finite_enumeration_pattern_unreadable =
  finite_list_pattern_unreadable[where z="Finite_Target (Finite_Whole finite_empty_artifact)"]

definition finite_atom_entry ::
    "'a finite_term_pattern \<Rightarrow> (local_address \<times> 'a finite_term_pattern) material_reading" where
  "finite_atom_entry p = (case p of Finite_Pattern_Pair x q \<Rightarrow>
      (case x of Finite_Pattern_Payload a \<Rightarrow> Reading (a,q) | _ \<Rightarrow> ground_reading x)
    | _ \<Rightarrow> ground_reading p)"

text \<open>
  A payload entry reads the payload it states, an address or a value. An attachment entry pairs two, as
  @{const address_pair_data} pairs an address and a value; an incidence entry pairs a payload with an
  attachment-shaped entry, as @{const incidence_data} pairs an address with a pair of addresses.
\<close>

definition finite_payload_entry :: "'a finite_term_pattern \<Rightarrow> octets material_reading" where
  "finite_payload_entry w = (case w of Finite_Pattern_Payload v \<Rightarrow> Reading v | _ \<Rightarrow> ground_reading w)"

definition finite_attachment_entry :: "'a finite_term_pattern \<Rightarrow> (local_address \<times> octets) material_reading" where
  "finite_attachment_entry p = (case p of Finite_Pattern_Pair x w \<Rightarrow>
      reading_pair (finite_payload_entry x) (finite_payload_entry w)
    | _ \<Rightarrow> ground_reading p)"

definition finite_incidence_entry ::
    "'a finite_term_pattern \<Rightarrow> (local_address \<times> local_address \<times> local_address) material_reading" where
  "finite_incidence_entry p = (case p of Finite_Pattern_Pair x q \<Rightarrow>
      reading_pair (finite_payload_entry x) (finite_attachment_entry q)
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
  "finite_material_skeleton M = map_material_reading (\<lambda>(es,E,B,F). (map fst es,E,B,F))
      (reading_pair (finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M))
        (reading_pair (finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M))
          (reading_pair (finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M))
            (finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M)))))"

lemma finite_pattern_instance_shapes:
  "finite_pattern_instance V p (Finite_Pair a b) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or>
    (\<exists>x y. p = Finite_Pattern_Pair x y \<and> finite_pattern_instance V x a \<and> finite_pattern_instance V y b)"
  "finite_pattern_instance V p (Finite_Payload c) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or> p = Finite_Pattern_Payload c"
  "finite_pattern_instance V p (Finite_Target t) \<Longrightarrow> (\<exists>v. p = Finite_Variable v) \<or> p = Finite_Pattern_Target t"
  by (cases p; auto)+

lemma finite_material_read_shapes:
  "finite_occurrence_read C u = Some a \<Longrightarrow> u = Finite_Target (Finite_Anchor C a)"
  "finite_atom_read C u = Some y \<Longrightarrow> \<exists>x. u = Finite_Pair (Finite_Payload y) x \<and> finite_occurrence_read C x = Some y"
  "finite_incidence_read u = Some e \<Longrightarrow> u = finite_incidence_data e"
  "finite_attachment_read u = Some p \<Longrightarrow> u = finite_address_pair_data p"
     apply (cases u; auto split: finite_exact_target.splits if_splits)
    apply (induction C u rule: finite_atom_read.induct; auto split: if_splits)
   apply (metis finite_incidence_read_correct decode_finite_term_injective finite_material_entry_decodings(3))
  apply (metis finite_attachment_read_correct decode_finite_term_injective finite_material_entry_decodings(4))
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

lemma finite_payload_entry_instance:
  "finite_payload_entry q = Reading v \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> u = Finite_Payload v"
  by (auto simp: finite_payload_entry_def split: finite_term_pattern.splits finite_factor_term.splits)

lemma finite_payload_entry_unreadable:
  "finite_payload_entry q = Unreadable \<Longrightarrow> finite_pattern_instance V q (Finite_Payload v) \<Longrightarrow> False"
  using finite_pattern_instance_shapes(2)[of V q v] by (auto simp: finite_payload_entry_def ground_reading_def)

lemma finite_attachment_entry_instance:
  assumes entry: "finite_attachment_entry q = Reading e0" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_attachment_read u = Some e"
  shows "e0 = e"
proof -
  obtain x w where q: "q = Finite_Pattern_Pair x w"
    using entry by (auto simp: finite_attachment_entry_def split: finite_term_pattern.splits)
  obtain a v where ax: "finite_payload_entry x = Reading a" and vw: "finite_payload_entry w = Reading v"
    and e0: "e0 = (a,v)"
    using entry by (auto simp: q finite_attachment_entry_def reading_pair_reading)
  obtain ux uw where u: "u = Finite_Pair ux uw" and ix: "finite_pattern_instance V x ux"
      and iw: "finite_pattern_instance V w uw"
    using inst_u by (auto simp: q split: finite_factor_term.splits)
  have "u = finite_address_pair_data (a,v)"
    using finite_payload_entry_instance[OF ax ix] finite_payload_entry_instance[OF vw iw] u
    by (simp add: finite_address_pair_data_def)
  then show "e0 = e" using read e0 finite_material_term_reads(3) by simp
qed

lemma finite_incidence_entry_instance:
  assumes entry: "finite_incidence_entry q = Reading e0" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_incidence_read u = Some e"
  shows "e0 = e"
proof -
  obtain x w where q: "q = Finite_Pattern_Pair x w"
    using entry by (auto simp: finite_incidence_entry_def split: finite_term_pattern.splits)
  obtain a p where ax: "finite_payload_entry x = Reading a" and pw: "finite_attachment_entry w = Reading p"
    and e0: "e0 = (a,p)"
    using entry by (auto simp: q finite_incidence_entry_def reading_pair_reading)
  obtain ux uw where u: "u = Finite_Pair ux uw" and ix: "finite_pattern_instance V x ux"
      and iw: "finite_pattern_instance V w uw"
    using inst_u by (auto simp: q split: finite_factor_term.splits)
  obtain a' p' where e: "e = (a',p')" by (cases e)
  have parts: "ux = Finite_Payload a'" "uw = finite_address_pair_data p'"
    using finite_material_read_shapes(3)[OF read] u e by (simp_all add: finite_incidence_data_def)
  have "a = a'" using finite_payload_entry_instance[OF ax ix] parts(1) by simp
  moreover have "p = p'"
    using finite_attachment_entry_instance[OF pw iw, of p'] parts(2) finite_material_term_reads(3) by simp
  ultimately show "e0 = e" using e0 e by simp
qed

lemma finite_attachment_entry_unreadable:
  assumes entry: "finite_attachment_entry q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_attachment_read u = Some p"
  shows False
proof -
  have u: "u = Finite_Pair (Finite_Payload (fst p)) (Finite_Payload (snd p))"
    using finite_material_read_shapes(4)[OF read] by (cases p) (simp add: finite_address_pair_data_def)
  show False
  proof (cases q)
    case (Finite_Pattern_Pair x w)
    have ix: "finite_pattern_instance V x (Finite_Payload (fst p))"
      and iw: "finite_pattern_instance V w (Finite_Payload (snd p))"
      using inst_u by (simp_all add: Finite_Pattern_Pair u)
    have "finite_payload_entry x = Unreadable \<or> finite_payload_entry w = Unreadable"
      using entry by (auto simp: Finite_Pattern_Pair finite_attachment_entry_def dest!: reading_pair_unreadable)
    then show False using finite_payload_entry_unreadable[OF _ ix] finite_payload_entry_unreadable[OF _ iw] by blast
  qed (use entry inst_u u in \<open>auto simp: finite_attachment_entry_def\<close>)
qed

lemma finite_incidence_entry_unreadable:
  assumes entry: "finite_incidence_entry q = Unreadable" and inst_u: "finite_pattern_instance V q u"
    and read: "finite_incidence_read u = Some e"
  shows False
proof -
  have u: "u = Finite_Pair (Finite_Payload (fst e)) (finite_address_pair_data (snd e))"
    using finite_material_read_shapes(3)[OF read] by (cases e) (simp add: finite_incidence_data_def)
  show False
  proof (cases q)
    case (Finite_Pattern_Pair x w)
    have ix: "finite_pattern_instance V x (Finite_Payload (fst e))"
      and iw: "finite_pattern_instance V w (finite_address_pair_data (snd e))"
      using inst_u by (simp_all add: Finite_Pattern_Pair u)
    have "finite_payload_entry x = Unreadable \<or> finite_attachment_entry w = Unreadable"
      using entry by (auto simp: Finite_Pattern_Pair finite_incidence_entry_def dest!: reading_pair_unreadable)
    then show False using finite_payload_entry_unreadable[OF _ ix]
      finite_attachment_entry_unreadable[OF _ iw finite_material_term_reads(3)] by blast
  qed (use entry inst_u u in \<open>auto simp: finite_incidence_entry_def\<close>)
qed

lemma finite_material_entries_unreadable:
  "finite_atom_entry q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow> finite_atom_read C u \<noteq> Some y"
  "finite_incidence_entry q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_incidence_read u \<noteq> Some e"
  "finite_attachment_entry q = Unreadable \<Longrightarrow> finite_pattern_instance V q u \<Longrightarrow>
    finite_attachment_read u \<noteq> Some p"
  using finite_atom_entry_unreadable finite_incidence_entry_unreadable finite_attachment_entry_unreadable by blast+

lemma finite_material_skeleton_read:
  assumes skeleton: "finite_material_skeleton M = Reading (A0,E0,B0,F0)"
  obtains es where "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    "finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M) = Reading E0"
    "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M) = Reading B0"
    "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M) = Reading F0"
    "A0 = map fst es"
proof -
  from skeleton obtain es where es: "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    and rest: "finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M) = Reading E0"
      "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M) = Reading B0"
      "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M) = Reading F0"
    and A0: "A0 = map fst es"
    by (auto simp: finite_material_skeleton_def map_reading_cases reading_pair_reading)
  show thesis by (rule that[OF es rest A0])
qed

text \<open>
  The skeleton has no reading exactly when one of its four fields has none: an entry with no reading, a
  ground term where an anchor, an address or a formed attachment must stand, or a payload or a nonempty
  target where a list continues, makes its field unreadable whatever the field's other entries hold, and the
  field makes the skeleton unreadable whatever the other fields hold.
\<close>

lemma finite_list_pattern_read_pair_unreadable:
  "finite_list_pattern_read z rd (Finite_Pattern_Pair p q) = Unreadable \<longleftrightarrow>
    rd p = Unreadable \<or> finite_list_pattern_read z rd q = Unreadable"
  by (simp add: map_reading_cases reading_pair_unreadable_iff)

lemmas finite_enumeration_pattern_read_pair_unreadable =
  finite_list_pattern_read_pair_unreadable[where z="Finite_Target (Finite_Whole finite_empty_artifact)"]

lemma finite_material_skeleton_unreadable_iff:
  "finite_material_skeleton M = Unreadable \<longleftrightarrow>
    finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Unreadable \<or>
    finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M) = Unreadable \<or>
    finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M) = Unreadable \<or>
    finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M) = Unreadable"
  by (simp add: finite_material_skeleton_def map_reading_cases reading_pair_unreadable_iff)

theorem finite_material_skeleton_determined:
  assumes skeleton: "finite_material_skeleton M = Reading (A0,E0,B0,F0)"
    and functional: "finite_relation_functional V"
    and atoms: "finite_pattern_instance V (finite_material_atoms M) (finite_enumeration_term (map (finite_atom_term C) A))"
    and edges: "finite_pattern_instance V (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E))"
    and counts: "finite_pattern_instance V (finite_material_counts M) (finite_data_sequence (map finite_address_pair_data B))"
    and fns: "finite_pattern_instance V (finite_material_functions M) (finite_data_sequence (map finite_address_pair_data F))"
  shows "A = A0 \<and> E = E0 \<and> B = B0 \<and> F = F0"
proof -
  obtain es where es: "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Reading es"
    and E0: "finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M) = Reading E0"
    and B0: "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M) = Reading B0"
    and F0: "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M) = Reading F0"
    and A0: "A0 = map fst es"
    by (rule finite_material_skeleton_read[OF skeleton])
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)
  have data_reads:
    "finite_list_read (Finite_Payload []) finite_incidence_read (finite_data_sequence (map finite_incidence_data E)) = Some E"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data B)) = Some B"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data F)) = Some F"
    by (rule finite_data_list_read_term, rule finite_material_term_reads)+
  have rows: "list_all2 (\<lambda>e y. y = fst e \<and> (\<exists>u'. finite_pattern_instance V (snd e) u' \<and>
      finite_occurrence_read C u' = Some (fst e))) es A"
    by (rule finite_enumeration_pattern_instance[OF finite_atom_entry_instance es atoms reads])
  then have A: "A = map fst es" by (simp add: list_all2_function_restricted)
  have "list_all2 (=) E0 E"
    by (rule finite_list_pattern_instance[OF finite_incidence_entry_instance E0 edges data_reads(1)])
  moreover have "list_all2 (=) B0 B"
    by (rule finite_list_pattern_instance[OF finite_attachment_entry_instance B0 counts data_reads(2)])
  moreover have "list_all2 (=) F0 F"
    by (rule finite_list_pattern_instance[OF finite_attachment_entry_instance F0 fns data_reads(3)])
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
      "finite_pattern_instance V (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E))"
      "finite_pattern_instance V (finite_material_counts M) (finite_data_sequence (map finite_address_pair_data B))"
      "finite_pattern_instance V (finite_material_functions M) (finite_data_sequence (map finite_address_pair_data F))"
    by (rule finite_material_satisfied_witness[OF sat])
  have reads: "finite_enumeration_read (finite_atom_read C) (finite_enumeration_term (map (finite_atom_term C) A)) = Some A"
    by (rule finite_enumeration_read_term, rule finite_material_term_reads)
  have data_reads:
    "finite_list_read (Finite_Payload []) finite_incidence_read (finite_data_sequence (map finite_incidence_data E)) = Some E"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data B)) = Some B"
    "finite_list_read (Finite_Payload []) finite_attachment_read (finite_data_sequence (map finite_address_pair_data F)) = Some F"
    by (rule finite_data_list_read_term, rule finite_material_term_reads)+
  have i1: "\<forall>q u y. finite_atom_entry q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_atom_read C u \<noteq> Some y"
    using finite_material_entries_unreadable(1) by blast
  have i2: "\<forall>q u y. finite_incidence_entry q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_incidence_read u \<noteq> Some y"
    using finite_material_entries_unreadable(2) by blast
  have i3: "\<forall>q u y. finite_attachment_entry q = Unreadable \<longrightarrow> finite_pattern_instance V q u \<longrightarrow>
      finite_attachment_read u \<noteq> Some y"
    using finite_material_entries_unreadable(3) by blast
  have "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M) = Unreadable \<or>
      finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M) = Unreadable \<or>
      finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M) = Unreadable \<or>
      finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M) = Unreadable"
    using skeleton by (simp add: finite_material_skeleton_unreadable_iff)
  then show False
    using finite_enumeration_pattern_unreadable[OF i1 _ inst(2) reads]
      finite_list_pattern_unreadable[OF i2 _ inst(3) data_reads(1)]
      finite_list_pattern_unreadable[OF i3 _ inst(4) data_reads(2)]
      finite_list_pattern_unreadable[OF i3 _ inst(5) data_reads(3)]
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

text \<open>
  Where a field of the skeleton has no reading the material premise has no solution, and its resolution says so
  whatever the rest of the skeleton or the source still leaves open: this is where the reading above changes the
  resolution's value, from @{const Material_Waits} (an open field beside it, the source open) to no solution.
  Every other value is as it was.
\<close>

theorem finite_material_resolution_unreadable_field:
  assumes "finite_material_skeleton M = Unreadable"
  shows "finite_material_resolution M = Material_Solutions {||}"
  using assms by (simp add: finite_material_resolution_def)

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
      "finite_pattern_instance V (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E))"
      "finite_pattern_instance V (finite_material_counts M) (finite_data_sequence (map finite_address_pair_data B))"
      "finite_pattern_instance V (finite_material_functions M)
        (finite_data_sequence (map finite_address_pair_data F))"
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
      "finite_pattern_instance V (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E'))"
      "finite_pattern_instance V (finite_material_counts M) (finite_data_sequence (map finite_address_pair_data B'))"
      "finite_pattern_instance V (finite_material_functions M)
        (finite_data_sequence (map finite_address_pair_data F'))"
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
        "finite_pattern_instance W (finite_material_edges M) (finite_data_sequence (map finite_incidence_data E'))"
        "finite_pattern_instance W (finite_material_counts M)
          (finite_data_sequence (map finite_address_pair_data B'))"
        "finite_pattern_instance W (finite_material_functions M)
          (finite_data_sequence (map finite_address_pair_data F'))"
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
