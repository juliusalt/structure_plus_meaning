theory Factor_Executable_Material
  imports Factor_Executable_Terms Factor_Finite_Artifact_Enumeration
begin

section \<open>Reading a list over its terminator\<close>

text \<open>
  A list term pairs its entries in order before a terminator leaf. Its reader takes the terminator as a
  parameter: the terminator reads the empty list, any other leaf has no reading, and a pair reads its entry
  and then the rest. A material field's enumeration is this reader at the empty artifact's whole target, a
  data list at the empty payload: one reader, at each list notion's terminator.
\<close>

fun finite_list_read ::
  "finite_factor_term \<Rightarrow> (finite_factor_term \<Rightarrow> 'a option) \<Rightarrow> finite_factor_term \<Rightarrow> 'a list option" where
  "finite_list_read z read (Finite_Target t) = (if Finite_Target t = z then Some [] else None)"
| "finite_list_read z read (Finite_Payload v) = (if Finite_Payload v = z then Some [] else None)"
| "finite_list_read z read (Finite_Pair x xs) =
    (case read x of None \<Rightarrow> None
      | Some a \<Rightarrow> map_option (Cons a) (finite_list_read z read xs))"

lemma finite_list_read_correct:
  fixes read :: "finite_factor_term \<Rightarrow> 'a option" and make :: "'a \<Rightarrow> factor_term"
    and mk_list :: "factor_term list \<Rightarrow> factor_term"
  assumes reads: "\<And>t a. read t = Some a \<longleftrightarrow> decode_finite_term t = make a"
    and leaf: "\<And>x y. z \<noteq> Finite_Pair x y"
    and nil: "mk_list [] = decode_finite_term z"
    and cons: "\<And>u us. mk_list (u#us) = Pair_Term u (mk_list us)"
  shows "finite_list_read z read t = Some xs \<longleftrightarrow> decode_finite_term t = mk_list (map make xs)"
proof (induction t arbitrary: xs)
  case (Finite_Target u)
  show ?case
  proof (cases xs)
    case Nil
    have "decode_finite_term (Finite_Target u) = mk_list (map make xs) \<longleftrightarrow> Finite_Target u = z"
      by (simp only: Nil list.map nil decode_finite_term_injective)
    then show ?thesis by (simp add: Nil)
  next
    case (Cons a as)
    then show ?thesis by (simp add: cons)
  qed
next
  case (Finite_Payload v)
  show ?case
  proof (cases xs)
    case Nil
    have "decode_finite_term (Finite_Payload v) = mk_list (map make xs) \<longleftrightarrow> Finite_Payload v = z"
      by (simp only: Nil list.map nil decode_finite_term_injective)
    then show ?thesis by (simp add: Nil)
  next
    case (Cons a as)
    then show ?thesis by (simp add: cons)
  qed
next
  case (Finite_Pair x tail)
  have nil_read: "finite_list_read z read (Finite_Pair x tail) \<noteq> Some []"
    by (cases "read x"; cases "finite_list_read z read tail") auto
  have cons_read: "finite_list_read z read (Finite_Pair x tail) = Some (a#as) \<longleftrightarrow>
    read x = Some a \<and> finite_list_read z read tail = Some as" for a as
    by (cases "read x"; cases "finite_list_read z read tail") auto
  show ?case
  proof (cases xs)
    case Nil
    have "Finite_Pair x tail \<noteq> z" using leaf[of x tail] by auto
    then have "decode_finite_term (Finite_Pair x tail) \<noteq> mk_list (map make xs)"
      by (simp only: Nil list.map nil decode_finite_term_injective not_False_eq_True)
    then show ?thesis using nil_read Nil by simp
  next
    case (Cons a as)
    have parse: "finite_list_read z read (Finite_Pair x tail) = Some xs \<longleftrightarrow>
      read x = Some a \<and> finite_list_read z read tail = Some as"
      by (simp only: Cons cons_read)
    have encoded: "decode_finite_term (Finite_Pair x tail) = mk_list (map make xs) \<longleftrightarrow>
      decode_finite_term x = make a \<and> decode_finite_term tail = mk_list (map make as)"
      by (simp add: Cons cons)
    show ?thesis by (simp only: parse encoded reads Finite_Pair.IH(2))
  qed
qed

lemma finite_list_read_term:
  assumes reads: "\<And>x. rd (mk x) = Some x" and leaf: "\<And>x y. z \<noteq> Finite_Pair x y"
  shows "finite_list_read z rd (foldr Finite_Pair (map mk xs) z) = Some xs"
proof (induction xs)
  case Nil
  show ?case using leaf by (cases z) auto
next
  case (Cons x xs)
  then show ?case by (simp add: reads)
qed

lemma finite_list_read_injective:
  assumes inj: "\<And>u u' x. rd u = Some x \<Longrightarrow> rd u' = Some x \<Longrightarrow> u = u'"
  shows "finite_list_read z rd t = Some xs \<Longrightarrow> finite_list_read z rd t' = Some xs \<Longrightarrow> t = t'"
proof (induction t arbitrary: t' xs)
  case (Finite_Target x)
  then show ?case by (cases t') (auto split: if_splits option.splits)
next
  case (Finite_Payload v)
  then show ?case by (cases t') (auto split: if_splits option.splits)
next
  case (Finite_Pair u w)
  from Finite_Pair.prems(1) obtain y ys where ru: "rd u = Some y"
    and rw: "finite_list_read z rd w = Some ys" and xs: "xs = y#ys"
    by (auto split: option.splits)
  from Finite_Pair.prems(2) xs obtain u' w' where t': "t' = Finite_Pair u' w'" and ru': "rd u' = Some y"
    and rw': "finite_list_read z rd w' = Some ys"
    by (cases t') (auto split: if_splits option.splits)
  show ?case using inj[OF ru ru'] Finite_Pair.IH(2)[OF rw rw'] t' by simp
qed

text \<open>The enumeration of a material field and a data list are the reader at their terminators.\<close>

abbreviation finite_enumeration_read ::
  "(finite_factor_term \<Rightarrow> 'a option) \<Rightarrow> finite_factor_term \<Rightarrow> 'a list option" where
  "finite_enumeration_read \<equiv> finite_list_read (Finite_Target (Finite_Whole finite_empty_artifact))"

lemma finite_enumeration_read_correct:
  fixes read :: "finite_factor_term \<Rightarrow> 'a option" and make :: "'a \<Rightarrow> factor_term"
  assumes reads: "\<And>t a. read t = Some a \<longleftrightarrow> decode_finite_term t = make a"
  shows "finite_enumeration_read read t = Some xs \<longleftrightarrow>
    decode_finite_term t = enumeration_term (map make xs)"
  by (rule finite_list_read_correct[where mk_list=enumeration_term, OF reads]) simp_all

lemma finite_list_read_data_correct:
  fixes read :: "finite_factor_term \<Rightarrow> 'a option" and make :: "'a \<Rightarrow> factor_term"
  assumes reads: "\<And>t a. read t = Some a \<longleftrightarrow> decode_finite_term t = make a"
  shows "finite_list_read (Finite_Payload []) read t = Some xs \<longleftrightarrow>
    decode_finite_term t = data_list_term (map make xs)"
  by (rule finite_list_read_correct[where mk_list=data_list_term, OF reads]) simp_all

fun finite_occurrence_read ::
  "finite_exact_artifact \<Rightarrow> finite_factor_term \<Rightarrow> local_address option" where
  "finite_occurrence_read C (Finite_Target t) =
    (case t of Finite_Anchor D a \<Rightarrow> if C=D then Some a else None | _ \<Rightarrow> None)"
| "finite_occurrence_read C (Finite_Payload v) = None"
| "finite_occurrence_read C (Finite_Pair x y) = None"

lemma finite_occurrence_read_correct:
  "finite_occurrence_read C t = Some a \<longleftrightarrow>
    decode_finite_term t = occurrence_term (decode_finite_object C) a"
  by (cases t) (auto simp: occurrence_term_def split: finite_exact_target.splits if_splits)

fun finite_atom_read ::
  "finite_exact_artifact \<Rightarrow> finite_factor_term \<Rightarrow> local_address option" where
  "finite_atom_read C (Finite_Pair (Finite_Payload a) x) =
    (if finite_occurrence_read C x = Some a then Some a else None)"
| "finite_atom_read C t = None"

lemma finite_atom_read_correct:
  "finite_atom_read C t = Some a \<longleftrightarrow>
    decode_finite_term t = atom_term (decode_finite_object C) a"
proof (cases t)
  case (Finite_Target x)
  then show ?thesis by (simp add: atom_term_def)
next
  case (Finite_Payload v)
  then show ?thesis by (simp add: atom_term_def)
next
  case (Finite_Pair x y)
  then show ?thesis by (cases x)
    (auto simp: atom_term_def finite_occurrence_read_correct occurrence_term_def split: if_splits)
qed

text \<open>
  An attachment and an incidence are read in the artifact data class's address form: an attachment a pair of
  payloads, its address and its value, an incidence a payload, its first address, before an attachment-shaped
  pair of addresses. No artifact is consulted: the addresses are opaque payloads, related to the atoms' anchors
  by the observation's own check.
\<close>

fun finite_attachment_read :: "finite_factor_term \<Rightarrow> (local_address \<times> octets) option" where
  "finite_attachment_read (Finite_Pair (Finite_Payload a) (Finite_Payload v)) = Some (a,v)"
| "finite_attachment_read t = None"

lemma finite_attachment_read_correct:
  "finite_attachment_read t = Some z \<longleftrightarrow> decode_finite_term t = address_pair_data z"
  by (cases t rule: finite_attachment_read.cases; cases z) (auto simp: address_pair_data_def)

fun finite_incidence_read ::
  "finite_factor_term \<Rightarrow> (local_address \<times> local_address \<times> local_address) option" where
  "finite_incidence_read (Finite_Pair (Finite_Payload a) p) = map_option (Pair a) (finite_attachment_read p)"
| "finite_incidence_read t = None"

lemma finite_incidence_read_correct:
  "finite_incidence_read t = Some z \<longleftrightarrow> decode_finite_term t = incidence_data z"
  by (cases t rule: finite_incidence_read.cases; cases z)
    (auto simp: incidence_data_def finite_attachment_read_correct[symmetric])

section \<open>Checking the complete artifact equation\<close>

fun finite_material_observation ::
  "finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_material_observation (Finite_Target (Finite_Whole C)) atoms edges counts functions =
    (case (finite_enumeration_read (finite_atom_read C) atoms,
           finite_list_read (Finite_Payload []) finite_incidence_read edges,
           finite_list_read (Finite_Payload []) finite_attachment_read counts,
           finite_list_read (Finite_Payload []) finite_attachment_read functions) of
      (Some A,Some E,Some B,Some F) \<Rightarrow> finite_artifact_enumeration C A E B F | _ \<Rightarrow> False)"
| "finite_material_observation source atoms edges counts functions = False"

lemma finite_material_observation_whole:
  "finite_material_observation (Finite_Target (Finite_Whole C)) atoms edges counts functions \<longleftrightarrow>
    (\<exists>A E B F. finite_artifact_enumeration C A E B F \<and>
      finite_enumeration_read (finite_atom_read C) atoms = Some A \<and>
      finite_list_read (Finite_Payload []) finite_incidence_read edges = Some E \<and>
      finite_list_read (Finite_Payload []) finite_attachment_read counts = Some B \<and>
      finite_list_read (Finite_Payload []) finite_attachment_read functions = Some F)"
  by (auto split: option.splits)

theorem finite_material_observation_correct:
  "finite_material_observation source atoms edges counts functions \<longleftrightarrow>
    material_observation (decode_finite_term source) (decode_finite_term atoms)
      (decode_finite_term edges) (decode_finite_term counts) (decode_finite_term functions)"
proof (cases source)
  case (Finite_Target t)
  then show ?thesis
  proof (cases t)
    case (Finite_Whole C)
    have atom: "\<And>a A. finite_enumeration_read (finite_atom_read C) a = Some A \<longleftrightarrow>
      decode_finite_term a = enumeration_term (map (atom_term (decode_finite_object C)) A)"
      by (rule finite_enumeration_read_correct[OF finite_atom_read_correct])
    have edge: "\<And>e E. finite_list_read (Finite_Payload []) finite_incidence_read e = Some E \<longleftrightarrow>
      decode_finite_term e = data_list_term (map incidence_data E)"
      by (rule finite_list_read_data_correct[OF finite_incidence_read_correct])
    have attach: "\<And>b B. finite_list_read (Finite_Payload []) finite_attachment_read b = Some B \<longleftrightarrow>
      decode_finite_term b = data_list_term (map address_pair_data B)"
      by (rule finite_list_read_data_correct[OF finite_attachment_read_correct])
    show ?thesis
      using Finite_Target Finite_Whole
      by (simp only: finite_material_observation_whole atom edge attach finite_artifact_enumeration_correct)
         (auto simp: material_observation_def)
  next
    case (Finite_Anchor C a)
    then show ?thesis using Finite_Target by (simp add: material_observation_def)
  qed
next
  case (Finite_Payload v)
  then show ?thesis by (simp add: material_observation_def)
next
  case (Finite_Pair x y)
  then show ?thesis by (simp add: material_observation_def)
qed

text \<open>
  The checker reads the atoms' enumeration and the three data lists and compares
  the reconstructed finite value with the complete supplied artifact. Distinctness applies to the
  carrier, incidence, and functional relation; anonymous repetitions are counted
  as a multiset. Every allowed enumeration is checked by the same equation.
  All recursion follows supplied term structure, including on malformed inputs.
\<close>

end
