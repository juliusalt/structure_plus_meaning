theory RRA_Exact
  imports RRA_Footprint RRA_Digit_Natural_Paths Prefix_Code_Words
begin

section \<open>Exact addressed artifacts\<close>

type_synonym local_address = octets
type_synonym exact_artifact = "(local_address,octets) structured_object"

lemma basis_values_restrictD:
  assumes "v \<in> basis_values (restrict_basis A D)"
  shows "v \<in> basis_values D"
  using assms basis_values_restrict[of A D] by blast

definition exact_formed :: "exact_artifact \<Rightarrow> bool" where
  "exact_formed R \<longleftrightarrow>
     object_formed R \<and>
     (\<forall>a \<in> rra_carrier (object_structure R). octets_formed a) \<and>
     (\<forall>v \<in> basis_values (object_data R). octets_formed v)"

definition empty_artifact :: exact_artifact where
  "empty_artifact =
    \<lparr>object_structure = \<lparr>rra_carrier = {}, rra_incidence = {}\<rparr>,
     object_data = empty_basis\<rparr>"

lemma empty_artifact_formed [simp]: "exact_formed empty_artifact"
  by (simp add: empty_artifact_def exact_formed_def object_formed_def rra_formed_def)

text \<open>
  Exact artifact identity is ordinary equality of the complete mathematical
  record.  A digest or reference may identify that value externally, but is not
  substituted for it here.
\<close>

lemma exact_identity_iff:
  fixes R R' :: exact_artifact
  shows "R = R' \<longleftrightarrow>
   object_structure R = object_structure R' \<and> object_data R = object_data R'"
  by (cases R; cases R') auto

lemma local_star_does_not_determine_exact_identity:
  "\<exists>R S :: exact_artifact. exact_formed R \<and> exact_formed S \<and>
    footprint_of R {[]} = footprint_of S {[]} \<and>
    [] \<in> rra_carrier (object_structure R) \<and>
    [] \<in> rra_carrier (object_structure S) \<and>
    R \<noteq> S \<and> (R,[]) \<noteq> (S,[])"
proof -
  let ?R = "\<lparr>object_structure = \<lparr>rra_carrier = {[]}, rra_incidence = {}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  let ?S = "\<lparr>object_structure = \<lparr>rra_carrier = {[],[0]}, rra_incidence = {}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  show ?thesis
    by (rule exI[of _ ?R], rule exI[of _ ?S])
       (auto simp: exact_formed_def object_formed_def rra_formed_def octets_formed_def
         basis_values_def basis_formed_def single_valued_def bag_support_def empty_basis_def footprint_of_def Let_def
         touching_incidence_def exact_identity_iff rra_identity)
qed

section \<open>Anchors are values\<close>

type_synonym exact_anchor = "exact_artifact \<times> local_address"

definition anchor_formed :: "exact_anchor \<Rightarrow> bool" where
  "anchor_formed a \<longleftrightarrow>
    exact_formed (fst a) \<and> snd a \<in> rra_carrier (object_structure (fst a))"

lemma empty_artifact_has_no_anchor:
  "\<not> anchor_formed (empty_artifact,a)"
  by (simp add: anchor_formed_def empty_artifact_def)

datatype exact_target =
    Whole_Artifact exact_artifact
  | Occurrence_Anchor exact_anchor

fun target_formed :: "exact_target \<Rightarrow> bool" where
  "target_formed (Whole_Artifact R) = exact_formed R"
| "target_formed (Occurrence_Anchor a) = anchor_formed a"

fun target_artifact :: "exact_target \<Rightarrow> exact_artifact" where
  "target_artifact (Whole_Artifact R) = R"
| "target_artifact (Occurrence_Anchor a) = fst a"

fun target_occurrence :: "exact_target \<Rightarrow> local_address option" where
  "target_occurrence (Whole_Artifact R) = None"
| "target_occurrence (Occurrence_Anchor a) = Some (snd a)"

lemma exact_anchor_identity:
  "(R,a) = (S,b) \<longleftrightarrow> R = S \<and> a = b"
  by simp

lemma exact_target_identity:
  "x = y \<longleftrightarrow>
    target_artifact x = target_artifact y \<and> target_occurrence x = target_occurrence y"
  by (cases x; cases y) auto

lemma target_formed_artifact:
  assumes "target_formed x"
  shows "exact_formed (target_artifact x)"
  using assms by (cases x) (auto simp: anchor_formed_def)

text \<open>
  An occurrence anchor is the complete artifact value paired with one of its
  addresses. A whole-artifact target also denotes the empty artifact, which has
  no occurrence anchor. Neither form contains a retrieval token.
\<close>

section \<open>Concrete local-address realizations\<close>

text \<open>
  The index code is the library's digit code of a natural, written in octets: the digit path's
  True is the octet 0 and its False the octet 1. Its facts are those of the digit path, instantiated
  through the injective map of the two symbols; none of them is argued again.
\<close>

definition index_address :: "nat \<Rightarrow> local_address" where
  "index_address i = map (\<lambda>b. if b then 0 else 1) (digit_natural_path i)"

lemma index_address_formed:
  "octets_formed (index_address i)"
  by (auto simp: index_address_def octets_formed_def)

lemma index_address_nonempty [simp]:
  "index_address i \<noteq> []"
  by (simp add: index_address_def)

lemma index_symbol_inj: "inj (\<lambda>b::bool. if b then (0::nat) else 1)"
proof (rule injI)
  fix x y :: bool
  assume "(if x then (0::nat) else 1) = (if y then 0 else 1)"
  then show "x = y" by (cases x; cases y) simp_all
qed

theorem index_address_cancel:
  "index_address m @ xs = index_address n @ ys \<longleftrightarrow> m = n \<and> xs = ys"
  unfolding index_address_def
  by (rule mapped_prefix_cancel[where code=digit_natural_path, OF digit_natural_path_cancel index_symbol_inj])

lemma index_address_inj: "inj index_address"
  by (rule injI) (use index_address_cancel[of _ "[]" _ "[]"] in simp)

lemma index_address_eq_iff [simp]:
  "index_address m = index_address n \<longleftrightarrow> m = n"
  using index_address_inj by (auto simp: inj_def)

lemma index_address_length:
  "length (index_address i) = 2 * length (natural_binary_digits i) + 1"
  by (simp add: index_address_def digit_natural_path_length)

theorem index_address_bound:
  "i < 2^k \<Longrightarrow> length (index_address i) \<le> 2 * k + 1"
  using digit_natural_path_bound[of i k] by (simp add: index_address_def)

text \<open>
  The code of every nonzero index begins with the same octet, the digit path's continuation mark, so
  its tail after that octet is a code of its own: the tails of nonzero indices cancel as the codes do.
\<close>

lemma index_address_nonzero:
  assumes "i \<noteq> 0"
  shows "index_address i = 0 # tl (index_address i)"
proof -
  obtain w where "digit_natural_path i = True # w" using digit_natural_path_nonzero[OF assms] by blast
  then show ?thesis by (simp add: index_address_def)
qed

theorem index_address_tail_cancel:
  assumes "m \<noteq> 0" "n \<noteq> 0"
  shows "tl (index_address m) @ xs = tl (index_address n) @ ys \<longleftrightarrow> m = n \<and> xs = ys"
proof -
  have "tl (index_address m) @ xs = tl (index_address n) @ ys \<longleftrightarrow>
      (0 # tl (index_address m)) @ xs = (0 # tl (index_address n)) @ ys" by simp
  also have "\<dots> \<longleftrightarrow> index_address m @ xs = index_address n @ ys"
    by (simp only: index_address_nonzero[OF assms(1), symmetric] index_address_nonzero[OF assms(2), symmetric])
  finally show ?thesis by (simp only: index_address_cancel)
qed

text \<open>
  The reader takes the octets 0 and 1 that begin an address as digit-path symbols and reads a digit
  path from them; the rest of the address after the code is returned whole.
\<close>

definition read_index_address :: "local_address \<Rightarrow> (nat \<times> local_address) option" where
  "read_index_address source = (case read_digit_natural_path
      (map (\<lambda>x. x = 0) (takeWhile (\<lambda>x. x \<le> 1) source)) of None \<Rightarrow> None
    | Some (i,r) \<Rightarrow> Some (i,drop (length (index_address i)) source))"

theorem read_index_address_exact:
  "read_index_address source = Some (i,rest) \<longleftrightarrow> source = index_address i @ rest"
proof
  assume read: "read_index_address source = Some (i,rest)"
  let ?T = "takeWhile (\<lambda>x. x \<le> (1::nat)) source"
  obtain r where bits: "read_digit_natural_path (map (\<lambda>x. x = 0) ?T) = Some (i,r)"
    and dropped: "rest = drop (length (index_address i)) source"
    using read by (auto simp: read_index_address_def split: option.splits)
  have "map (\<lambda>x. x = 0) ?T = digit_natural_path i @ r"
    using bits by (simp only: read_digit_natural_path_exact)
  then have "map (\<lambda>b. if b then 0 else 1) (map (\<lambda>x. x = 0) ?T) =
      map (\<lambda>b. if b then 0 else 1) (digit_natural_path i @ r)" by (simp only:)
  moreover have "map (\<lambda>b. if b then 0 else 1) (map (\<lambda>x. x = 0) ?T) = ?T"
    unfolding map_map by (rule map_idI) (auto dest!: set_takeWhileD)
  ultimately have "?T = map (\<lambda>b. if b then 0 else 1) (digit_natural_path i @ r)"
    by (rule box_equals[OF _ _ refl])
  then have "?T = index_address i @ map (\<lambda>b. if b then 0 else 1) r"
    by (simp only: index_address_def map_append)
  then have whole: "source = index_address i @ (map (\<lambda>b. if b then 0 else 1) r @
      dropWhile (\<lambda>x. x \<le> 1) source)"
    using takeWhile_dropWhile_id[of "\<lambda>x. x \<le> (1::nat)" source] by (metis append.assoc)
  have "drop (length (index_address i)) source = map (\<lambda>b. if b then 0 else 1) r @
      dropWhile (\<lambda>x. x \<le> 1) source"
    by (subst whole) simp
  then show "source = index_address i @ rest" using whole dropped by simp
next
  assume source: "source = index_address i @ rest"
  have small: "\<forall>x\<in>set (index_address i). x \<le> (1::nat)" by (auto simp: index_address_def)
  have tw: "takeWhile (\<lambda>x. x \<le> 1) source = index_address i @ takeWhile (\<lambda>x. x \<le> 1) rest"
    unfolding source by (rule takeWhile_append2) (use small in blast)
  have restored: "map (\<lambda>x. x = 0) (index_address i) = digit_natural_path i"
    unfolding index_address_def map_map by (rule map_idI) simp
  have "map (\<lambda>x. x = 0) (takeWhile (\<lambda>x. x \<le> 1) source) =
      digit_natural_path i @ map (\<lambda>x. x = 0) (takeWhile (\<lambda>x. x \<le> 1) rest)"
    by (simp only: tw map_append restored)
  then show "read_index_address source = Some (i,rest)"
    by (simp add: read_index_address_def source)
qed

text \<open>
  The positions of the first indices, the checks the layout's tests read.
\<close>

lemma index_address_first:
  "map index_address [0,1,2,3,4] = [[1],[0,0,1],[0,1,0,0,1],[0,0,0,0,1],[0,1,0,1,0,0,1]]"
  using digit_natural_path_first by (simp add: index_address_def)

text \<open>
  An index is blocked in a set of addresses when some address starts with its code. Each address
  starts with at most one code, the one the reader returns, so a finite set blocks finitely many
  indices, and the empty address blocks none. The fresh address of a set is the code of the least
  index it does not block.
\<close>

definition index_blocked :: "local_address set \<Rightarrow> nat set" where
  "index_blocked A = {j. \<exists>a\<in>A. \<exists>b. a = index_address j @ b}"

lemma index_blocked_read:
  "j \<in> index_blocked A \<longleftrightarrow> (\<exists>a\<in>A. \<exists>b. read_index_address a = Some (j,b))"
  by (simp add: index_blocked_def read_index_address_exact)

lemma index_blocked_finite:
  assumes "finite A"
  shows "finite (index_blocked A)"
proof (rule finite_subset)
  show "index_blocked A \<subseteq> (\<lambda>a. fst (the (read_index_address a))) ` A"
  proof
    fix j assume "j \<in> index_blocked A"
    then obtain a b where a: "a \<in> A" "read_index_address a = Some (j,b)" by (auto simp: index_blocked_read)
    show "j \<in> (\<lambda>a. fst (the (read_index_address a))) ` A"
      by (rule rev_image_eqI[OF a(1)]) (simp add: a(2))
  qed
  show "finite ((\<lambda>a. fst (the (read_index_address a))) ` A)" using assms by simp
qed

lemma index_blocked_insert_empty [simp]: "index_blocked (insert [] A) = index_blocked A"
  by (auto simp: index_blocked_def)

definition fresh_address :: "local_address set \<Rightarrow> local_address" where
  "fresh_address A = index_address (LEAST j. j \<notin> index_blocked A)"

lemma fresh_address_formed [simp]:
  "octets_formed (fresh_address A)"
  unfolding fresh_address_def by (rule index_address_formed)

text \<open>
  No extension of the fresh address of a finite set belongs to it: a proof that places material after
  a fresh address takes this fact, and the address's own freshness is its instance.
\<close>

lemma fresh_address_extension_outside:
  assumes "finite A"
  shows "fresh_address A @ xs \<notin> A"
proof
  assume member: "fresh_address A @ xs \<in> A"
  obtain k where "k \<notin> index_blocked A"
    using ex_new_if_finite[OF infinite_UNIV_nat index_blocked_finite[OF assms]] by blast
  then have least: "(LEAST j. j \<notin> index_blocked A) \<notin> index_blocked A"
    using LeastI[of "\<lambda>j. j \<notin> index_blocked A" k] by blast
  have "(LEAST j. j \<notin> index_blocked A) \<in> index_blocked A"
    using member unfolding fresh_address_def index_blocked_def by blast
  then show False using least by blast
qed

lemma fresh_address_not_in:
  assumes "finite A"
  shows "fresh_address A \<notin> A"
  using fresh_address_extension_outside[OF assms, of "[]"] by simp

fun fresh_addresses :: "local_address set \<Rightarrow> nat \<Rightarrow> local_address list" where
  "fresh_addresses A 0 = []"
| "fresh_addresses A (Suc n) =
    fresh_address A # fresh_addresses (insert (fresh_address A) A) n"

lemma fresh_addresses_length [simp]:
  "length (fresh_addresses A n) = n"
  by (induction n arbitrary: A) auto

lemma fresh_addresses_formed:
  "\<forall>a\<in>set (fresh_addresses A n). octets_formed a"
  by (induction n arbitrary: A) auto

lemma fresh_addresses_disjoint:
  assumes "finite A"
  shows "distinct (fresh_addresses A n) \<and> set (fresh_addresses A n) \<inter> A = {}"
  using assms
proof (induction n arbitrary: A)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have fresh: "fresh_address A \<notin> A" by (rule fresh_address_not_in[OF Suc.prems])
  have tail: "distinct (fresh_addresses (insert (fresh_address A) A) n) \<and>
    set (fresh_addresses (insert (fresh_address A) A) n) \<inter> insert (fresh_address A) A = {}"
    by (rule Suc.IH) (use Suc.prems in simp)
  show ?case using fresh tail by auto
qed

lemma fresh_four_addresses:
  assumes "finite U"
  shows "\<exists>b r p q. distinct [b,r,p,q] \<and> {b,r,p,q} \<inter> U = {} \<and>
    (\<forall>a\<in>{b,r,p,q}. octets_formed a)"
proof -
  let ?b = "fresh_address U"
  let ?r = "fresh_address (insert ?b U)"
  let ?p = "fresh_address (insert ?r (insert ?b U))"
  let ?q = "fresh_address (insert ?p (insert ?r (insert ?b U)))"
  have separate: "distinct (fresh_addresses U 4) \<and> set (fresh_addresses U 4) \<inter> U = {}"
    by (rule fresh_addresses_disjoint[OF assms])
  have formed: "\<forall>a\<in>set (fresh_addresses U 4). octets_formed a" by (rule fresh_addresses_formed)
  have shape: "fresh_addresses U 4 = [?b,?r,?p,?q]" by (simp add: numeral_eq_Suc)
  have result: "distinct [?b,?r,?p,?q] \<and> {?b,?r,?p,?q} \<inter> U = {} \<and>
    (\<forall>a\<in>{?b,?r,?p,?q}. octets_formed a)" using separate formed shape by simp
  show ?thesis by (rule exI[of _ ?b], rule exI[of _ ?r], rule exI[of _ ?p], rule exI[of _ ?q]) (rule result)
qed

definition finite_addressing :: "'a set \<Rightarrow> ('a \<Rightarrow> local_address) \<Rightarrow> bool" where
  "finite_addressing U f \<longleftrightarrow>
     inj_on f U \<and> (\<forall>x \<in> U. octets_formed (f x))"

lemma finite_addressing_exists:
  assumes "finite U"
  shows "\<exists>f. finite_addressing U f"
proof -
  obtain g :: "'a \<Rightarrow> nat" where g: "inj_on g U"
    using finite_imp_inj_to_nat_seg[OF assms] by blast
  have i: "inj_on (index_address \<circ> g) U"
    using g index_address_inj
    by (auto simp: inj_on_def inj_def)
  have entry: "\<forall>x \<in> U. octets_formed ((index_address \<circ> g) x)"
    using index_address_formed by auto
  show ?thesis
    using i entry by (auto simp: finite_addressing_def)
qed

definition exact_realization ::
  "('a \<Rightarrow> local_address) \<Rightarrow> ('a,octets) structured_object \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "exact_realization f obj R \<longleftrightarrow>
     object_formed obj \<and> exact_formed R \<and>
     finite_addressing (rra_carrier (object_structure obj)) f \<and>
     object_structure R = push_structure f (object_structure obj) \<and>
     object_data R = push_basis (rra_carrier (object_structure obj)) f (object_data obj)"

lemma exact_realization_structure_iso:
  assumes "exact_realization f obj R"
  shows "rra_isomorphism f (object_structure obj) (object_structure R)"
proof -
  from assms have inj: "inj_on f (rra_carrier (object_structure obj))"
    and eq: "object_structure R = push_structure f (object_structure obj)"
    by (auto simp: exact_realization_def finite_addressing_def)
  have source: "rra_formed (object_structure obj)"
    using assms by (simp add: exact_realization_def object_formed_def)
  have "rra_isomorphism f (object_structure obj)
          (push_structure f (object_structure obj))"
    using push_structure_iso[OF source inj] .
  with eq show ?thesis by simp
qed

lemma exact_realization_exists:
  assumes formed: "object_formed obj"
    and vals: "\<forall>v\<in>basis_values (object_data obj). octets_formed v"
  shows "\<exists>f R. exact_realization f obj R"
proof -
  have fin: "finite (rra_carrier (object_structure obj))"
    using formed by (simp add: object_formed_def rra_formed_def)
  obtain f where fa: "finite_addressing (rra_carrier (object_structure obj)) f"
    using finite_addressing_exists[OF fin] by blast
  have compat: "basis_compatible f (object_data obj)"
    by (rule injective_gluing_compatible)
       (use formed fa in \<open>auto simp: object_formed_def finite_addressing_def\<close>)
  have pf: "object_formed (push_object f obj)"
    using push_object_formed_iff[OF formed, where f=f] compat by simp
  have ev: "\<forall>v\<in>basis_values (object_data (push_object f obj)). octets_formed v"
    using vals pushed_basis_values[of "rra_carrier (object_structure obj)" f "object_data obj"]
    by (auto simp: push_object_def)
  have ef: "exact_formed (push_object f obj)"
    using pf fa ev
    by (auto simp: exact_formed_def finite_addressing_def push_object_def push_structure_def)
  show ?thesis
    by (rule exI[of _ f], rule exI[of _ "push_object f obj"])
       (use formed fa ef in \<open>simp add: exact_realization_def push_object_def\<close>)
qed

lemma exact_realization_object_iso:
  assumes "exact_realization f obj R"
  shows "object_isomorphism f obj R"
  using assms exact_realization_structure_iso[OF assms]
  by (simp add: object_isomorphism_def exact_realization_def exact_formed_def push_object_def)

lemma exact_push_formed:
  assumes formed: "exact_formed R"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
  shows "exact_formed (push_object f R)"
proof -
  have source: "object_formed R" using formed by (simp add: exact_formed_def)
  have injective: "inj_on f (rra_carrier (object_structure R))"
    using addressing by (simp add: finite_addressing_def)
  have target: "object_formed (push_object f R)"
    using object_push_isomorphism[OF source injective] by (simp add: object_isomorphism_def)
  have payloads: "\<forall>v\<in>basis_values (object_data (push_object f R)). octets_formed v"
    using formed pushed_basis_values[of "rra_carrier (object_structure R)" f "object_data R"]
    by (auto simp: exact_formed_def push_object_def)
  show ?thesis using target payloads addressing
    by (auto simp: exact_formed_def finite_addressing_def push_object_def)
qed

text \<open>
  The spelling of a local address belongs to exact artifact identity, but has no
  structural meaning.  Any semantic invariance under exact re-addressing must
  be established through the isomorphism just exposed, never by treating two
  exact artifacts as literally equal.
\<close>

end
