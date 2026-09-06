theory RRA_Structural_Syntax
  imports RRA_Environment
begin

section \<open>Primitive structural projections\<close>

definition headed_incidence :: "'a rra_structure \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set" where
  "headed_incidence S r = {(p,x). (r,p,x) \<in> rra_incidence S}"

lemma headed_incidence_member [simp]:
  "(p,x) \<in> headed_incidence S r \<longleftrightarrow> (r,p,x) \<in> rra_incidence S"
  by (simp add: headed_incidence_def)

lemma headed_targets_in_carrier:
  assumes "rra_formed S"
  shows "snd ` headed_incidence S r \<subseteq> rra_carrier S"
  using assms by (auto simp: rra_formed_def headed_incidence_def)

lemma headed_members_in_carrier:
  assumes "rra_formed S" "(p,x) \<in> headed_incidence S r"
  shows "r \<in> rra_carrier S \<and> p \<in> rra_carrier S \<and> x \<in> rra_carrier S"
  using assms by (auto simp: rra_formed_def)

lemma headed_incidence_push:
  fixes S :: "'a rra_structure" and f :: "'a \<Rightarrow> 'b"
  assumes formed: "rra_formed S" and injective: "inj_on f (rra_carrier S)"
    and member: "r \<in> rra_carrier S"
  shows "headed_incidence (push_structure f S) (f r) =
    (\<lambda>(p,x). (f p,f x)) ` headed_incidence S r"
proof (rule set_eqI)
  fix pair :: "'b \<times> 'b"
  obtain p x where pair: "pair = (p,x)" by (cases pair)
  show "pair \<in> headed_incidence (push_structure f S) (f r) \<longleftrightarrow>
    pair \<in> (\<lambda>(p,x). (f p,f x)) ` headed_incidence S r"
  proof
    assume "pair \<in> headed_incidence (push_structure f S) (f r)"
    then obtain s a b where edge: "(s,a,b) \<in> rra_incidence S"
      and eq: "f r = f s" "p = f a" "x = f b"
      by (auto simp: pair push_structure_def)
    have source: "s \<in> rra_carrier S" using formed edge by (auto simp: rra_formed_def)
    have same: "r = s" by (rule inj_onD[OF injective eq(1) member source])
    show "pair \<in> (\<lambda>(p,x). (f p,f x)) ` headed_incidence S r"
      using edge eq same by (auto simp: pair headed_incidence_def intro: rev_image_eqI)
  next
    assume "pair \<in> (\<lambda>(p,x). (f p,f x)) ` headed_incidence S r"
    then show "pair \<in> headed_incidence (push_structure f S) (f r)"
      by (auto simp: pair headed_incidence_def push_structure_def intro: rev_image_eqI)
  qed
qed

definition payload_at ::
  "('a,'v) structured_object \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool" where
  "payload_at obj a v \<longleftrightarrow>
    restrict_basis {a} (object_data obj) =
      \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {(a,v)}\<rparr>"

lemma payload_at_unique:
  assumes "payload_at obj a v" "payload_at obj a w"
  shows "v = w"
  using assms by (auto simp: payload_at_def basis_identity)

lemma payload_at_binding:
  assumes "payload_at obj a v"
  shows "(a,v) \<in> functional_bindings (object_data obj)"
  using assms by (auto simp: payload_at_def basis_identity set_eq_iff)

lemma payload_at_nonempty:
  assumes "payload_at obj a v"
  shows "restrict_basis {a} (object_data obj) \<noteq> empty_basis"
  using assms by (auto simp: payload_at_def empty_basis_def basis_identity)

definition payload_leaf_at :: "('a,'v) structured_object \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool" where
  "payload_leaf_at obj a v \<longleftrightarrow>
    object_formed obj \<and> headed_incidence (object_structure obj) a = {} \<and> payload_at obj a v"

lemma payload_leaf_unique:
  assumes "payload_leaf_at obj a v" "payload_leaf_at obj a w"
  shows "v = w"
  using assms unfolding payload_leaf_at_def by (blast intro: payload_at_unique)

lemma payload_leaf_carrier:
  assumes "payload_leaf_at obj a v"
  shows "a \<in> rra_carrier (object_structure obj)"
proof -
  have payload: "payload_at obj a v" using assms by (simp add: payload_leaf_at_def)
  have binding: "(a,v) \<in> functional_bindings (object_data obj)" by (rule payload_at_binding[OF payload])
  show ?thesis using assms binding by (auto simp: payload_leaf_at_def object_formed_def basis_formed_def)
qed

lemma payload_leaf_octets:
  assumes "exact_formed R" "payload_leaf_at R a v"
  shows "octets_formed v"
proof -
  have binding: "(a,v) \<in> functional_bindings (object_data R)"
    using assms(2) payload_at_binding by (auto simp: payload_leaf_at_def)
  have "v \<in> basis_values (object_data R)"
    using binding by (auto simp: basis_values_def intro: rev_image_eqI)
  then show ?thesis using assms(1) by (auto simp: exact_formed_def)
qed

lemma payload_at_characterization:
  "payload_at obj a v \<longleftrightarrow>
    (\<forall>w. bag_count (object_data obj) (a,w) = 0) \<and>
    (\<forall>w. (a,w) \<in> functional_bindings (object_data obj) \<longleftrightarrow> w = v)"
  by (auto simp: payload_at_def basis_identity restrict_basis_def fun_eq_iff set_eq_iff)

lemma payload_at_push:
  assumes formed: "object_formed obj"
    and injective: "inj_on f (rra_carrier (object_structure obj))"
    and member: "a \<in> rra_carrier (object_structure obj)"
  shows "payload_at (push_object f obj) (f a) v \<longleftrightarrow> payload_at obj a v"
proof -
  have finite: "finite (rra_carrier (object_structure obj))"
    and data: "basis_formed (rra_carrier (object_structure obj)) (object_data obj)"
    using formed by (auto simp: object_formed_def rra_formed_def)
  have counts: "\<And>w. bag_count (object_data (push_object f obj)) (f a,w) =
    bag_count (object_data obj) (a,w)"
    using pushed_count_injective[OF finite injective member]
    by (simp add: push_object_def push_basis_def)
  have bindings: "\<And>w. (f a,w) \<in> functional_bindings (object_data (push_object f obj)) \<longleftrightarrow>
    (a,w) \<in> functional_bindings (object_data obj)"
    using functional_at_injective[OF data injective member]
    by (simp add: push_object_def)
  show ?thesis by (simp add: payload_at_characterization counts bindings)
qed

lemma payload_leaf_push:
  assumes leaf: "payload_leaf_at obj a v"
    and injective: "inj_on f (rra_carrier (object_structure obj))"
  shows "payload_leaf_at (push_object f obj) (f a) v"
proof -
  have formed: "object_formed obj" and head: "headed_incidence (object_structure obj) a = {}"
    and data: "payload_at obj a v" using leaf by (auto simp: payload_leaf_at_def)
  have member: "a \<in> rra_carrier (object_structure obj)" by (rule payload_leaf_carrier[OF leaf])
  have sf: "rra_formed (object_structure obj)" using formed by (simp add: object_formed_def)
  have target_head: "headed_incidence (object_structure (push_object f obj)) (f a) = {}"
    using headed_incidence_push[OF sf injective member] head by (simp add: push_object_def)
  have target_data: "payload_at (push_object f obj) (f a) v"
    using payload_at_push[OF formed injective member, of v] data by simp
  show ?thesis using object_push_isomorphism[OF formed injective] target_head target_data
    by (simp add: payload_leaf_at_def object_isomorphism_def)
qed

section \<open>Local and external citation patterns\<close>

inductive raw_citation_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> citation \<Rightarrow> local_address set \<Rightarrow> bool"
  for R r where
  local:
    "headed_incidence (object_structure R) r = {(r,a)} \<Longrightarrow>
     raw_citation_at R r (Local a) {r}"
| local_whole:
    "headed_incidence (object_structure R) r = {} \<Longrightarrow>
     raw_citation_at R r Local_Whole {r}"
| external_whole:
    "r \<noteq> k \<Longrightarrow>
     headed_incidence (object_structure R) r = {(k,k)} \<Longrightarrow>
     raw_citation_at R r (External_Whole k) {r}"
| external:
    "distinct [r,k,d] \<Longrightarrow>
     headed_incidence (object_structure R) r = {(r,k),(k,d)} \<Longrightarrow>
     headed_incidence (object_structure R) d = {} \<Longrightarrow>
     payload_at R d a \<Longrightarrow>
     raw_citation_at R r (External k a) {r,d}"

definition citation_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> citation \<Rightarrow> local_address set \<Rightarrow> bool" where
  "citation_at R r c I \<longleftrightarrow>
    exact_formed R \<and> r \<in> rra_carrier (object_structure R) \<and>
    restrict_basis {r} (object_data R) = empty_basis \<and> raw_citation_at R r c I"

text \<open>
  Equality of tuple positions distinguishes the local and external patterns.
  A local citation reaches its atom directly. An external citation reaches a
  slot occurrence and, for an occurrence target, a leaf carrying the target
  address. The root has no data. That leaf has one functional value and no
  counted data. Whole-artifact forms omit the address leaf.

  The root and leaf are interior occurrences. Slot and target occurrences
  belong to the exposed boundary whenever they are not already interior.
  Incoming incidence is retained in the complete relative footprint.
\<close>

lemma citation_two_fields_unique:
  assumes "r \<noteq> k" "r \<noteq> l" "{(r,k),(k,d)} = {(r,l),(l,e)}"
  shows "k = l \<and> d = e"
proof -
  have first: "(r,k) \<in> {(r,l),(l,e)}"
    using assms(3) by auto
  have kl: "k = l" using first assms(2) by auto
  have second: "(k,d) \<in> {(r,l),(l,e)}"
    using assms(3) by auto
  show ?thesis using second assms(1) kl by auto
qed

lemma citation_two_fields_iff:
  assumes "r \<noteq> k" "r \<noteq> l"
  shows "{(r,k),(k,d)} = {(r,l),(l,e)} \<longleftrightarrow> k = l \<and> d = e"
  using citation_two_fields_unique[OF assms, of d e] by auto

lemma raw_citation_field_count:
  assumes "raw_citation_at R r c I"
  shows "card (headed_incidence (object_structure R) r) =
    (case c of Local a \<Rightarrow> 1 | Local_Whole \<Rightarrow> 0 |
       External k a \<Rightarrow> 2 | External_Whole k \<Rightarrow> 1)"
  using assms by (cases rule: raw_citation_at.cases) auto

lemma raw_citation_at_unique:
  assumes first: "raw_citation_at R r c I" and second: "raw_citation_at R r d J"
  shows "c = d \<and> I = J"
  using raw_citation_field_count[OF first] raw_citation_field_count[OF second]
  by (cases rule: raw_citation_at.cases[OF first];
      cases rule: raw_citation_at.cases[OF second];
      auto simp: citation_two_fields_iff dest: payload_at_unique)

lemma citation_at_unique:
  assumes "citation_at R r c I" "citation_at R r d J"
  shows "c = d" "I = J"
  using assms raw_citation_at_unique[of R r c I d J] by (auto simp: citation_at_def)

lemma raw_citation_interior:
  assumes "raw_citation_at R r c I"
  shows "finite I" "r \<in> I"
    and "\<forall>a\<in>I. a \<noteq> r \<longrightarrow> headed_incidence (object_structure R) a = {}"
proof -
  show "finite I" using assms by (cases rule: raw_citation_at.cases) auto
  show "r \<in> I" using assms by (cases rule: raw_citation_at.cases) auto
  show "\<forall>a\<in>I. a \<noteq> r \<longrightarrow> headed_incidence (object_structure R) a = {}"
    using assms by (cases rule: raw_citation_at.cases) auto
qed

lemma citation_interior_in_carrier:
  assumes "citation_at R r c I"
  shows "I \<subseteq> rra_carrier (object_structure R)"
proof -
  have rf: "rra_formed (object_structure R)" and root: "r \<in> rra_carrier (object_structure R)"
    and raw: "raw_citation_at R r c I"
    using assms by (auto simp: citation_at_def exact_formed_def object_formed_def)
  have sub: "I \<subseteq> insert r (snd ` headed_incidence (object_structure R) r)"
    using raw
    by (cases rule: raw_citation_at.cases) auto
  show ?thesis using sub root headed_targets_in_carrier[OF rf, of r] by blast
qed

fun citation_slots :: "citation \<Rightarrow> local_address set" where
  "citation_slots (Local a) = {}"
| "citation_slots Local_Whole = {}"
| "citation_slots (External k a) = {k}"
| "citation_slots (External_Whole k) = {k}"

lemma citation_slots_in_carrier:
  assumes "citation_at R r c I"
  shows "citation_slots c \<subseteq> rra_carrier (object_structure R)"
proof -
  have rf: "rra_formed (object_structure R)" and raw: "raw_citation_at R r c I"
    using assms by (auto simp: citation_at_def exact_formed_def object_formed_def)
  have sub: "citation_slots c \<subseteq> snd ` headed_incidence (object_structure R) r"
    using raw
    by (cases rule: raw_citation_at.cases) auto
  show ?thesis using sub headed_targets_in_carrier[OF rf, of r] by blast
qed

lemma citation_slots_outside_interior:
  assumes "citation_at R r c I"
  shows "I \<inter> citation_slots c = {}"
proof -
  have raw: "raw_citation_at R r c I" using assms by (simp add: citation_at_def)
  show ?thesis using raw by (cases rule: raw_citation_at.cases) auto
qed

lemma citation_footprint_star:
  assumes cite: "citation_at R r c I"
  shows "footprint_star (footprint_of R I) =
    {(r,p,x) |p x. (p,x) \<in> headed_incidence (object_structure R) r} \<union>
    {(s,p,x) \<in> touching_incidence (object_structure R) I. s \<notin> I}"
proof -
  have inside: "rra_carrier (object_structure R) \<inter> I = I"
    using citation_interior_in_carrier[OF cite] by blast
  have raw: "raw_citation_at R r c I"
    using cite by (simp add: citation_at_def)
  have root: "r \<in> I" and empty: "\<forall>a\<in>I. a \<noteq> r \<longrightarrow>
    headed_incidence (object_structure R) a = {}"
    using raw_citation_interior[OF raw] by auto
  show ?thesis
    using root empty
    by (auto simp: footprint_of_def Let_def inside touching_incidence_def headed_incidence_def)
qed

lemma citation_incoming_is_boundary:
  assumes "citation_at R r c I" "(s,p,x) \<in> touching_incidence (object_structure R) I" "s \<notin> I"
  shows "(s,p,x) \<in> crossing_incidence (object_structure R) I"
  using assms by (auto simp: crossing_incidence_def internal_incidence_def)

section \<open>Recognition depends on the complete relative footprint\<close>

lemma headed_footprint_locality:
  assumes eq: "footprint_of obj A = footprint_of other A"
    and inside: "a \<in> footprint_interior (footprint_of obj A)"
  shows "headed_incidence (object_structure obj) a = headed_incidence (object_structure other) a"
proof -
  have same: "\<forall>p x. ((a,p,x) \<in> rra_incidence (object_structure obj)) =
    ((a,p,x) \<in> rra_incidence (object_structure other))"
    by (intro allI; rule equal_footprint_observations(2)[OF eq inside])
  show ?thesis using same by (auto simp: headed_incidence_def)
qed

lemma payload_footprint_locality:
  assumes eq: "footprint_of obj A = footprint_of other A"
    and inside: "a \<in> footprint_interior (footprint_of obj A)"
  shows "payload_at obj a v = payload_at other a v"
proof -
  have sub: "{a} \<subseteq> footprint_interior (footprint_of obj A)"
    using inside by simp
  have deq: "restrict_basis {a} (object_data obj) = restrict_basis {a} (object_data other)"
    by (rule equal_footprint_data_restrictions[OF eq sub])
  show ?thesis using deq by (simp add: payload_at_def)
qed

lemma citation_recognition_locality:
  assumes cite: "citation_at R r c I" and formed: "exact_formed S"
    and eq: "footprint_of R I = footprint_of S I"
  shows "citation_at S r c I"
proof -
  have raw: "raw_citation_at R r c I"
    and empty: "restrict_basis {r} (object_data R) = empty_basis"
    using cite by (auto simp: citation_at_def)
  have inside: "footprint_interior (footprint_of R I) = I"
    using citation_interior_in_carrier[OF cite]
    by (auto simp: footprint_of_def Let_def)
  have root: "r \<in> I" using raw_citation_interior(2)[OF raw] .
  have hlocal: "\<And>a. a \<in> I \<Longrightarrow>
    headed_incidence (object_structure R) a = headed_incidence (object_structure S) a"
    by (rule headed_footprint_locality[OF eq]) (simp add: inside)
  have plocal: "\<And>a v. a \<in> I \<Longrightarrow> payload_at R a v = payload_at S a v"
    by (rule payload_footprint_locality[OF eq]) (simp add: inside)
  have target: "r \<in> rra_carrier (object_structure S)"
    by (rule equal_footprint_observations(1)[OF eq]) (use root in \<open>simp add: inside\<close>)
  have deq: "restrict_basis {r} (object_data R) = restrict_basis {r} (object_data S)"
    by (rule equal_footprint_data_restrictions[OF eq]) (use root in \<open>simp add: inside\<close>)
  have recovered: "raw_citation_at S r c I"
  proof (cases rule: raw_citation_at.cases[OF raw, case_names local local_whole external_whole external])
    case (local a)
    have head: "headed_incidence (object_structure S) r = {(r,a)}"
      using local hlocal[OF root] by simp
    have "raw_citation_at S r (Local a) {r}"
      by (rule raw_citation_at.local[OF head])
    then show ?thesis using local by simp
  next
    case local_whole
    have head: "headed_incidence (object_structure S) r = {}"
      using local_whole hlocal[OF root] by simp
    have "raw_citation_at S r Local_Whole {r}"
      by (rule raw_citation_at.local_whole[OF head])
    then show ?thesis using local_whole by simp
  next
    case (external_whole k)
    have different: "r \<noteq> k" using external_whole by simp
    have head: "headed_incidence (object_structure S) r = {(k,k)}"
      using external_whole hlocal[OF root] by simp
    have "raw_citation_at S r (External_Whole k) {r}"
      by (rule raw_citation_at.external_whole[OF different head])
    then show ?thesis using external_whole by simp
  next
    case (external k d a)
    have di: "d \<in> I" using external by simp
    have different: "distinct [r,k,d]" using external by simp
    have head: "headed_incidence (object_structure S) r = {(r,k),(k,d)}"
      using external hlocal[OF root] by simp
    have leaf: "headed_incidence (object_structure S) d = {}"
      using external hlocal[OF di] by simp
    have payload: "payload_at S d a"
      using external plocal[OF di, of a] by simp
    have "raw_citation_at S r (External k a) {r,d}"
      by (rule raw_citation_at.external[OF different head leaf payload])
    then show ?thesis using external by simp
  qed
  show ?thesis using formed target empty deq recovered by (simp add: citation_at_def)
qed

section \<open>Existence of citation representations\<close>

fun citation_projection_formed :: "citation \<Rightarrow> bool" where
  "citation_projection_formed (Local a) = octets_formed a"
| "citation_projection_formed Local_Whole = True"
| "citation_projection_formed (External k a) = (octets_formed k \<and> octets_formed a)"
| "citation_projection_formed (External_Whole k) = octets_formed k"

lemma local_self_citation_exists:
  assumes "octets_formed a"
  shows "\<exists>R. citation_at R a (Local a) {a} \<and> anchor_formed (R,a) \<and>
    object_data R = empty_basis"
proof -
  let ?R = "\<lparr>object_structure = \<lparr>rra_carrier = {a}, rra_incidence = {(a,a,a)}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  have rf: "exact_formed ?R"
    using assms by (simp add: exact_formed_def object_formed_def rra_formed_def)
  have raw: "raw_citation_at ?R a (Local a) {a}"
    by (rule raw_citation_at.local) (auto simp: headed_incidence_def)
  have cite: "citation_at ?R a (Local a) {a}"
    using rf raw
    by (simp add: citation_at_def)
  show ?thesis
    by (rule exI[of _ ?R]) (use cite rf in \<open>simp add: anchor_formed_def\<close>)
qed

lemma local_whole_citation_exists:
  "\<exists>R r I. citation_at R r Local_Whole I"
proof -
  let ?R = "\<lparr>object_structure = \<lparr>rra_carrier = {[]}, rra_incidence = {}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  have rf: "exact_formed ?R"
    by (simp add: exact_formed_def object_formed_def rra_formed_def octets_formed_def)
  have raw: "raw_citation_at ?R [] Local_Whole {[]}"
    by (rule raw_citation_at.local_whole) (simp add: headed_incidence_def)
  have cite: "citation_at ?R [] Local_Whole {[]}"
    using rf raw
    by (simp add: citation_at_def)
  show ?thesis using cite by blast
qed

lemma external_whole_citation_exists:
  assumes "octets_formed k"
  shows "\<exists>R r I. citation_at R r (External_Whole k) I"
proof -
  let ?r = "fresh_address {k}"
  let ?R = "\<lparr>object_structure = \<lparr>rra_carrier = {?r,k}, rra_incidence = {(?r,k,k)}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  have rk: "?r \<noteq> k" using fresh_address_not_in[of "{k}"] by simp
  have rf: "exact_formed ?R"
    using assms by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have raw: "raw_citation_at ?R ?r (External_Whole k) {?r}"
    by (rule raw_citation_at.external_whole[OF rk]) (auto simp: headed_incidence_def)
  have cite: "citation_at ?R ?r (External_Whole k) {?r}"
    using rf raw
    by (simp add: citation_at_def)
  show ?thesis using cite by blast
qed

lemma external_occurrence_citation_exists:
  assumes kformed: "octets_formed k" and aformed: "octets_formed a"
  shows "\<exists>R r I. citation_at R r (External k a) I"
proof -
  let ?r = "fresh_address {k}"
  let ?d = "fresh_address {?r,k}"
  let ?R = "\<lparr>object_structure =
    \<lparr>rra_carrier = {?r,k,?d}, rra_incidence = {(?r,?r,k),(?r,k,?d)}\<rparr>,
    object_data = \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {(?d,a)}\<rparr>\<rparr> :: exact_artifact"
  have distinct: "distinct [?r,k,?d]"
    using fresh_address_not_in[of "{k}"] fresh_address_not_in[of "{?r,k}"] by auto
  have rf: "exact_formed ?R"
    using kformed aformed
    by (auto simp: exact_formed_def object_formed_def rra_formed_def
      basis_formed_def basis_values_def bag_support_def single_valued_def)
  have head: "headed_incidence (object_structure ?R) ?r = {(?r,k),(k,?d)}"
    by (auto simp: headed_incidence_def)
  have leaf: "headed_incidence (object_structure ?R) ?d = {}"
    using distinct by (auto simp: headed_incidence_def)
  have payload: "payload_at ?R ?d a"
    by (auto simp: payload_at_def restrict_basis_def basis_identity fun_eq_iff)
  have raw: "raw_citation_at ?R ?r (External k a) {?r,?d}"
    by (rule raw_citation_at.external[OF distinct head leaf payload])
  have cite: "citation_at ?R ?r (External k a) {?r,?d}"
    using rf raw distinct
    by (auto simp: citation_at_def restrict_basis_def empty_basis_def basis_identity fun_eq_iff)
  show ?thesis using cite by blast
qed

lemma citation_representation_total:
  assumes "citation_projection_formed c"
  shows "\<exists>R r I. citation_at R r c I"
proof (cases c)
  case (Local a)
  with assms show ?thesis using local_self_citation_exists[of a] by auto
next
  case (External k a)
  with assms show ?thesis using external_occurrence_citation_exists[of k a] by simp
next
  case Local_Whole
  then show ?thesis using local_whole_citation_exists by simp
next
  case (External_Whole k)
  with assms show ?thesis using external_whole_citation_exists[of k] by simp
qed

section \<open>Structural recognition joined to interpretation\<close>

definition anchored_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> exact_target \<Rightarrow> bool" where
  "anchored_at E u r t \<longleftrightarrow>
    (\<exists>R c I. artifact_at E u R \<and> citation_at R r c I \<and> interpret_citation E u c t)"

lemma anchored_atI:
  assumes "artifact_at E u R" "citation_at R r c I" "interpret_citation E u c t"
  shows "anchored_at E u r t"
  using assms unfolding anchored_at_def by blast

lemma anchored_at_unique:
  assumes formed: "environment_formed E" and first: "anchored_at E u r x" and second: "anchored_at E u r y"
  shows "x = y"
proof -
  from first obtain R c I where a: "artifact_at E u R" "citation_at R r c I" "interpret_citation E u c x"
    by (auto simp: anchored_at_def)
  from second obtain S d J where b: "artifact_at E u S" "citation_at S r d J" "interpret_citation E u d y"
    by (auto simp: anchored_at_def)
  have rs: "R = S" by (rule environment_artifact_unique[OF formed a(1) b(1)])
  have cd: "c = d" using citation_at_unique(1)[OF a(2)] b(2) rs by blast
  show ?thesis
    using citation_interpretation_functional[OF formed a(3)] b(3) cd by blast
qed

lemma anchored_at_target_formed:
  assumes "anchored_at E u r t"
  shows "target_formed t"
  using assms unfolding anchored_at_def
  by (meson citation_interpretation_formed)

lemma anchored_at_environment_locality:
  assumes agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "anchored_at E u r t = anchored_at F u r t"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have citations: "\<forall>c t. interpret_citation E u c t = interpret_citation F u c t"
    using citation_environment_locality[OF agree closed member] by blast
  show ?thesis using arts citations unfolding anchored_at_def by blast
qed

lemma anchored_at_use_renaming:
  assumes "inj h"
  shows "anchored_at (rename_environment h E) (h u) r t \<longleftrightarrow> anchored_at E u r t"
  by (simp only: anchored_at_def artifact_at_renamed_use[OF assms]
      citation_use_renaming[OF assms])

definition located_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow>
   local_address \<Rightarrow> bool" where
  "located_at E u r v a \<longleftrightarrow>
    (\<exists>R c I. artifact_at E u R \<and> citation_at R r c I \<and> citation_location E u c v a)"

lemma located_at_unique:
  assumes formed: "environment_formed E"
    and first: "located_at E u r v a" and second: "located_at E u r w b"
  shows "v = w \<and> a = b"
proof -
  obtain R c I where left: "artifact_at E u R" "citation_at R r c I"
    "citation_location E u c v a" using first unfolding located_at_def by blast
  obtain S d J where right: "artifact_at E u S" "citation_at S r d J"
    "citation_location E u d w b" using second unfolding located_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF formed left(1) right(1)])
  have code: "c = d" using citation_at_unique(1)[OF left(2)] right(2) same by blast
  show ?thesis using citation_location_unique[OF formed left(3)] right(3) code by blast
qed

lemma located_at_target:
  assumes formed: "environment_formed E" and loc: "located_at E u r v a"
    and art: "artifact_at E v R"
  shows "anchored_at E u r (Occurrence_Anchor (R,a))"
proof -
  obtain S c I where source: "artifact_at E u S" "citation_at S r c I"
    "citation_location E u c v a" using loc unfolding located_at_def by blast
  have interpreted: "interpret_citation E u c (Occurrence_Anchor (R,a))"
    by (rule citation_location_target[OF formed source(3) art])
  show ?thesis by (rule anchored_atI[OF source(1,2) interpreted])
qed

lemma located_at_has_artifact:
  assumes "located_at E u r v a"
  shows "\<exists>R. artifact_at E v R \<and> anchor_formed (R,a)"
  using assms unfolding located_at_def by (meson citation_location_has_artifact)

lemma anchored_occurrence_location:
  assumes "anchored_at E u r (Occurrence_Anchor (C,a))"
  shows "\<exists>v. located_at E u r v a \<and> artifact_at E v C"
proof -
  obtain S c I where syntax_fields: "artifact_at E u S" "citation_at S r c I"
    and interpreted: "interpret_citation E u c (Occurrence_Anchor (C,a))"
    using assms unfolding anchored_at_def by blast
  obtain v where location: "citation_location E u c v a" "artifact_at E v C"
    using citation_occurrence_location[OF interpreted] by blast
  show ?thesis using syntax_fields location unfolding located_at_def by blast
qed

lemma located_at_environment_locality:
  assumes agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "located_at E u r v a = located_at F u r v a"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have locations: "\<forall>c v a. citation_location E u c v a = citation_location F u c v a"
    using citation_location_locality[OF agree closed member] by blast
  show ?thesis by (simp only: located_at_def arts locations)
qed

lemma located_at_use_renaming:
  assumes "inj h"
  shows "located_at (rename_environment h E) (h u) r (h v) a \<longleftrightarrow>
    located_at E u r v a"
  by (simp only: located_at_def artifact_at_renamed_use[OF assms]
      citation_location_use_renaming[OF assms])

lemma located_at_stays_in_boundary:
  assumes "environment_edge_closed E U" "u \<in> U" "located_at E u r v a"
  shows "v \<in> U"
  using assms unfolding located_at_def by (meson citation_location_stays_in_boundary)

text \<open>
  Recovering a referenced structure needs its use occurrence as well as its
  artifact and address. Location preserves that scope for recursive reading.
  The exact target projection continues to identify the artifact value alone.
\<close>

lemma local_self_citation_in_closed_use:
  assumes "octets_formed a"
  shows "\<exists>R E. object_data R = empty_basis \<and>
    environment_closed E {()} {} \<and> artifact_at E () R \<and>
    citation_at R a (Local a) {a} \<and> anchored_at E () a (Occurrence_Anchor (R,a))"
proof -
  obtain R where cite: "citation_at R a (Local a) {a}"
    and anchor: "anchor_formed (R,a)" and empty: "object_data R = empty_basis"
    using local_self_citation_exists[OF assms] by blast
  let ?E = "singleton_environment R"
  have rf: "exact_formed R" using cite by (simp add: citation_at_def)
  have closed: "environment_closed ?E {()} {}" by (rule singleton_environment_closed[OF rf])
  have source: "artifact_at ?E () R" by (simp add: artifact_at_def singleton_environment_def)
  have interpreted: "interpret_citation ?E () (Local a) (Occurrence_Anchor (R,a))"
    using source anchor by auto
  have anchored: "anchored_at ?E () a (Occurrence_Anchor (R,a))"
    by (rule anchored_atI[OF source cite interpreted])
  show ?thesis
    by (rule exI[of _ R], rule exI[of _ ?E]) (use empty closed source cite anchored in blast)
qed

lemma external_citation_has_distinct_closed_uses:
  assumes cite: "citation_at R r (External_Whole k) I"
  shows "\<exists>E F :: bool artifact_environment.
    environment_closed E {False} {(False,k)} \<and>
    environment_closed F {False} {(False,k)} \<and>
    artifact_at E False R \<and> artifact_at F False R \<and>
    anchored_at E False r (Whole_Artifact empty_artifact) \<and>
    anchored_at F False r (Whole_Artifact R) \<and>
    Whole_Artifact empty_artifact \<noteq> Whole_Artifact R"
proof -
  have rf: "exact_formed R" and root: "r \<in> rra_carrier (object_structure R)"
    using cite by (auto simp: citation_at_def)
  have slot: "k \<in> rra_carrier (object_structure R)"
    using citation_slots_in_carrier[OF cite] by simp
  let ?E = "one_binding_environment R k empty_artifact"
  let ?F = "one_binding_environment R k R"
  have ec: "environment_closed ?E {False} {(False,k)}"
    by (rule one_binding_environment_closed[OF rf empty_artifact_formed slot])
  have fc: "environment_closed ?F {False} {(False,k)}"
    by (rule one_binding_environment_closed[OF rf rf slot])
  have es: "artifact_at ?E False R" and fs: "artifact_at ?F False R"
    by (simp_all add: one_binding_environment_def artifact_at_def)
  have ei: "interpret_citation ?E False (External_Whole k) (Whole_Artifact empty_artifact)"
    by (auto simp: one_binding_environment_def artifact_at_def binds_slot_def)
  have fi: "interpret_citation ?F False (External_Whole k) (Whole_Artifact R)"
    using rf by (auto simp: one_binding_environment_def artifact_at_def binds_slot_def)
  have ea: "anchored_at ?E False r (Whole_Artifact empty_artifact)"
    by (rule anchored_atI[OF es cite ei])
  have fa: "anchored_at ?F False r (Whole_Artifact R)"
    by (rule anchored_atI[OF fs cite fi])
  have neq: "Whole_Artifact empty_artifact \<noteq> Whole_Artifact R"
    using root by (auto simp: empty_artifact_def)
  show ?thesis
    by (rule exI[of _ ?E], rule exI[of _ ?F]) (use ec fc es fs ea fa neq in blast)
qed

definition citation_family_formed :: "exact_artifact \<Rightarrow> local_address set \<Rightarrow> bool" where
  "citation_family_formed R roots \<longleftrightarrow>
    exact_formed R \<and> (\<forall>r\<in>roots. \<exists>c I. citation_at R r c I)"

definition citation_demands :: "exact_artifact \<Rightarrow> local_address set \<Rightarrow> local_address set" where
  "citation_demands R roots =
    {k. \<exists>r\<in>roots. \<exists>c I. citation_at R r c I \<and> k \<in> citation_slots c}"

lemma citation_demands_finite:
  assumes "citation_family_formed R roots"
  shows "finite (citation_demands R roots)"
proof -
  have sub: "citation_demands R roots \<subseteq> rra_carrier (object_structure R)"
    by (auto simp: citation_demands_def dest: citation_slots_in_carrier[THEN subsetD])
  have fin: "finite (rra_carrier (object_structure R))"
    using assms by (simp add: citation_family_formed_def exact_formed_def object_formed_def rra_formed_def)
  show ?thesis by (rule finite_subset[OF sub fin])
qed

section \<open>Order represented only by successor incidence\<close>

definition field_endpoint ::
  "'a rra_structure \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "field_endpoint S r p x \<longleftrightarrow> {y. (r,p,y) \<in> rra_incidence S} = {x}"

lemma field_endpoint_unique:
  assumes "field_endpoint S r p x" "field_endpoint S r p y"
  shows "x = y"
  using assms by (auto simp: field_endpoint_def)

lemma field_endpoint_incident:
  assumes "field_endpoint S r p x"
  shows "(r,p,x) \<in> rra_incidence S"
  using assms by (auto simp: field_endpoint_def set_eq_iff)

inductive record_path ::
  "'a rra_structure \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  for S r where
  path_last:
    "p \<noteq> r \<Longrightarrow> headed_incidence S p = {} \<Longrightarrow>
     field_endpoint S r p x \<Longrightarrow> record_path S r p [p] [x]"
| path_slot:
    "p \<noteq> r \<Longrightarrow>
     headed_incidence S p = {(p,q)} \<Longrightarrow>
     field_endpoint S r p x \<Longrightarrow>
     record_path S r q ps xs \<Longrightarrow>
     record_path S r p (p # ps) (x # xs)"

lemma record_path_unique:
  assumes first: "record_path S r p ps xs" and second: "record_path S r p qs ys"
  shows "ps = qs \<and> xs = ys"
  using first second
proof (induction arbitrary: qs ys rule: record_path.induct)
  case (path_last p x)
  from path_last.prems obtain y where parts:
    "qs = [p]" "ys = [y]" "field_endpoint S r p y"
    using path_last.hyps(2) by (cases rule: record_path.cases) auto
  have "x = y" by (rule field_endpoint_unique[OF path_last.hyps(3) parts(3)])
  then show ?case using parts(1,2) by simp
next
  case (path_slot p q x ps xs)
  from path_slot.prems obtain successor y tail vals where
    parts: "qs = p # tail" "ys = y # vals"
      "headed_incidence S p = {(p,successor)}" "field_endpoint S r p y"
      "record_path S r successor tail vals"
    using path_slot.hyps(2) by (cases rule: record_path.cases) auto
  have nq: "successor = q" using path_slot.hyps(2) parts(3) by simp
  have yx: "y = x" by (rule field_endpoint_unique[OF parts(4) path_slot.hyps(3)])
  have tails: "ps = tail \<and> xs = vals"
    using path_slot.IH parts(5) nq by blast
  show ?case using parts(1,2) yx tails by simp
qed

lemma record_path_lengths:
  assumes "record_path S r p ps xs"
  shows "length ps = length xs"
  using assms by (induction rule: record_path.induct) auto

lemma record_path_root_notin:
  assumes "record_path S r p ps xs"
  shows "r \<notin> set ps"
  using assms by (induction rule: record_path.induct) auto

lemma record_path_nonempty:
  assumes "record_path S r p ps xs"
  shows "ps \<noteq> []"
  using assms by (cases rule: record_path.cases) auto

lemma record_path_fields:
  assumes "record_path S r p ps xs" "a \<in> set ps"
  shows "\<exists>x. field_endpoint S r a x"
  using assms by (induction rule: record_path.induct) auto

lemma record_path_suffix:
  assumes path: "record_path S r p ps xs" and index: "i < length ps"
  shows "record_path S r (ps ! i) (drop i ps) (drop i xs)"
  using path index
proof (induction arbitrary: i rule: record_path.induct)
  case (path_last p x)
  then show ?case by (auto intro: record_path.path_last)
next
  case (path_slot p q x ps xs)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis using path_slot.hyps by (auto intro: record_path.path_slot)
  next
    case (Suc n)
    then show ?thesis using path_slot.IH path_slot.prems by simp
  qed
qed

lemma record_path_distinct:
  assumes "record_path S r p ps xs"
  shows "distinct ps"
  using assms
proof (induction rule: record_path.induct)
  case path_last
  then show ?case by simp
next
  case (path_slot p q x ps xs)
  have absent: "p \<notin> set ps"
  proof
    assume "p \<in> set ps"
    then obtain i where i: "i < length ps" "ps ! i = p"
      by (meson in_set_conv_nth)
    have suffix: "record_path S r p (drop i ps) (drop i xs)"
      using record_path_suffix[OF path_slot.hyps(4) i(1)] i(2) by simp
    have full: "record_path S r p (p # ps) (x # xs)"
      by (rule record_path.path_slot[OF path_slot.hyps(1-4)])
    have "(p # ps) = drop i ps"
      using record_path_unique[OF full suffix] by simp
    then have "Suc (length ps) = length ps - i"
      by (metis length_Cons length_drop)
    then show False by arith
  qed
  show ?case using absent path_slot.IH by simp
qed

definition raw_record_at ::
  "'a rra_structure \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "raw_record_at S r ps xs \<longleftrightarrow>
    (ps = [] \<and> xs = [] \<and> headed_incidence S r = {}) \<or>
    (record_path S r (hd ps) ps xs \<and> headed_incidence S r = set (zip ps xs))"

lemma raw_record_lengths:
  assumes "raw_record_at S r ps xs"
  shows "length ps = length xs"
  using assms record_path_lengths[of S r "hd ps" ps xs]
  by (auto simp: raw_record_at_def)

lemma raw_record_distinct:
  assumes "raw_record_at S r ps xs"
  shows "distinct ps \<and> r \<notin> set ps"
  using assms record_path_distinct[of S r "hd ps" ps xs]
    record_path_root_notin[of S r "hd ps" ps xs]
  by (auto simp: raw_record_at_def)

lemma raw_record_port_set:
  assumes raw: "raw_record_at S r ps xs"
  shows "rel_dom (headed_incidence S r) = set ps"
proof -
  have len: "length ps = length xs" by (rule raw_record_lengths[OF raw])
  have head: "headed_incidence S r = set (zip ps xs)"
    using raw by (auto simp: raw_record_at_def)
  have "rel_dom (set (zip ps xs)) = set (map fst (zip ps xs))"
    by (simp add: rel_dom_image)
  with head len show ?thesis by simp
qed

lemma raw_record_at_unique:
  assumes first: "raw_record_at S r ps xs" and second: "raw_record_at S r qs ys"
  shows "ps = qs \<and> xs = ys"
proof -
  have sets: "set ps = set qs"
    using raw_record_port_set[OF first] raw_record_port_set[OF second] by simp
  have lens: "length ps = length qs"
    using raw_record_distinct[OF first] raw_record_distinct[OF second] sets distinct_card by metis
  show ?thesis
  proof (cases "ps = []")
    case True
    then show ?thesis
      using sets raw_record_lengths[OF first] raw_record_lengths[OF second] by auto
  next
    case False
    have qne: "qs \<noteq> []" using False sets by auto
    have a: "record_path S r (hd ps) ps xs"
      using first False by (auto simp: raw_record_at_def)
    have b: "record_path S r (hd qs) qs ys"
      using second qne by (auto simp: raw_record_at_def)
    have "hd qs \<in> set ps" using qne sets by simp
    then obtain i where i: "i < length ps" "ps ! i = hd qs"
      by (meson in_set_conv_nth)
    have suffix: "record_path S r (hd qs) (drop i ps) (drop i xs)"
      using record_path_suffix[OF a i(1)] i(2) by simp
    have eq: "drop i ps = qs \<and> drop i xs = ys"
      by (rule record_path_unique[OF suffix b])
    have "length ps - i = length qs" using eq by (metis length_drop)
    then have zero: "i = 0" using lens i(1) by arith
    show ?thesis using eq zero by simp
  qed
qed

definition record_at ::
  "('a,'v) structured_object \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "record_at obj r ps xs \<longleftrightarrow>
    object_formed obj \<and> r \<in> rra_carrier (object_structure obj) \<and>
    raw_record_at (object_structure obj) r ps xs \<and>
    restrict_basis (insert r (set ps)) (object_data obj) = empty_basis"

lemma record_at_unique:
  assumes "record_at obj r ps xs" "record_at obj r qs ys"
  shows "ps = qs \<and> xs = ys"
  using assms raw_record_at_unique[of "object_structure obj" r ps xs qs ys]
  by (auto simp: record_at_def)

lemma record_at_preserves_socket_occurrences:
  assumes "record_at obj r ps xs"
  shows "distinct ps \<and> r \<notin> set ps \<and> length ps = length xs"
  using raw_record_distinct[of "object_structure obj" r ps xs]
    raw_record_lengths[of "object_structure obj" r ps xs] assms
  by (simp add: record_at_def)

lemma field_endpoint_from_head:
  "field_endpoint S r p x \<longleftrightarrow>
    {y. (p,y) \<in> headed_incidence S r} = {x}"
  by (simp add: field_endpoint_def)

lemma field_endpoint_incidence:
  assumes "field_endpoint S r p x"
  shows "(r,p,x) \<in> rra_incidence S"
  using assms by (auto simp: field_endpoint_def set_eq_iff)

lemma field_endpoint_push:
  assumes formed: "rra_formed S" and injective: "inj_on f (rra_carrier S)"
    and field: "field_endpoint S r p x"
  shows "field_endpoint (push_structure f S) (f r) (f p) (f x)"
proof -
  have edge: "(r,p,x) \<in> rra_incidence S" by (rule field_endpoint_incidence[OF field])
  have rin: "r \<in> rra_carrier S" and pin: "p \<in> rra_carrier S"
    using formed edge by (auto simp: rra_formed_def)
  have head: "headed_incidence (push_structure f S) (f r) =
    (\<lambda>(a,b). (f a,f b)) ` headed_incidence S r"
    by (rule headed_incidence_push[OF formed injective rin])
  have fibre: "{y. (f p,y) \<in> headed_incidence (push_structure f S) (f r)} = {f x}"
  proof (rule set_eqI)
    fix y
    show "y \<in> {y. (f p,y) \<in> headed_incidence (push_structure f S) (f r)} \<longleftrightarrow> y \<in> {f x}"
    proof
      assume "y \<in> {y. (f p,y) \<in> headed_incidence (push_structure f S) (f r)}"
      then obtain a b where source: "(a,b) \<in> headed_incidence S r"
        and eq: "f p = f a" "y = f b" using head by auto
      have ain: "a \<in> rra_carrier S" using headed_members_in_carrier[OF formed source] by blast
      have same: "p = a" by (rule inj_onD[OF injective eq(1) pin ain])
      have endpoint: "b = x" using source field same
        by (auto simp: field_endpoint_from_head set_eq_iff)
      show "y \<in> {f x}" using eq(2) endpoint by simp
    next
      assume "y \<in> {f x}"
      then show "y \<in> {y. (f p,y) \<in> headed_incidence (push_structure f S) (f r)}"
        using edge head by (auto intro: rev_image_eqI)
    qed
  qed
  show ?thesis using fibre by (simp add: field_endpoint_from_head)
qed

lemma record_path_push:
  assumes path: "record_path S r p ps xs" and formed: "rra_formed S"
    and injective: "inj_on f (rra_carrier S)"
  shows "record_path (push_structure f S) (f r) (f p) (map f ps) (map f xs)"
  using path
proof (induction rule: record_path.induct)
  case (path_last p x)
  have edge: "(r,p,x) \<in> rra_incidence S" by (rule field_endpoint_incidence[OF path_last.hyps(3)])
  have rin: "r \<in> rra_carrier S" and pin: "p \<in> rra_carrier S"
    using formed edge by (auto simp: rra_formed_def)
  have apart: "f p \<noteq> f r"
    using inj_onD[OF injective _ pin rin] path_last.hyps(1) by blast
  have head: "headed_incidence (push_structure f S) (f p) = {}"
    using headed_incidence_push[OF formed injective pin] path_last.hyps(2) by simp
  have field: "field_endpoint (push_structure f S) (f r) (f p) (f x)"
    by (rule field_endpoint_push[OF formed injective path_last.hyps(3)])
  show ?case using record_path.path_last[OF apart head field] by simp
next
  case (path_slot p q x ps xs)
  have edge: "(r,p,x) \<in> rra_incidence S" by (rule field_endpoint_incidence[OF path_slot.hyps(3)])
  have rin: "r \<in> rra_carrier S" and pin: "p \<in> rra_carrier S"
    using formed edge by (auto simp: rra_formed_def)
  have apart: "f p \<noteq> f r"
    using inj_onD[OF injective _ pin rin] path_slot.hyps(1) by blast
  have head: "headed_incidence (push_structure f S) (f p) = {(f p,f q)}"
    using headed_incidence_push[OF formed injective pin] path_slot.hyps(2) by simp
  have field: "field_endpoint (push_structure f S) (f r) (f p) (f x)"
    by (rule field_endpoint_push[OF formed injective path_slot.hyps(3)])
  show ?case using record_path.path_slot[OF apart head field path_slot.IH] by simp
qed

lemma raw_record_push:
  assumes raw: "raw_record_at S r ps xs" and formed: "rra_formed S"
    and injective: "inj_on f (rra_carrier S)" and root: "r \<in> rra_carrier S"
  shows "raw_record_at (push_structure f S) (f r) (map f ps) (map f xs)"
proof (cases "ps = []")
  case True
  have xs: "xs = []" using raw_record_lengths[OF raw] True by simp
  have head: "headed_incidence S r = {}" using raw True xs
    record_path_nonempty[of S r "hd ps" ps xs] by (auto simp: raw_record_at_def)
  have pushed: "headed_incidence (push_structure f S) (f r) = {}"
    using headed_incidence_push[OF formed injective root] head by simp
  show ?thesis using True xs pushed by (simp add: raw_record_at_def)
next
  case False
  have path: "record_path S r (hd ps) ps xs" and head: "headed_incidence S r = set (zip ps xs)"
    using raw False by (auto simp: raw_record_at_def)
  have pushed_path: "record_path (push_structure f S) (f r) (hd (map f ps)) (map f ps) (map f xs)"
    using record_path_push[OF path formed injective] False by (simp add: hd_map)
  have pushed_head: "headed_incidence (push_structure f S) (f r) = set (zip (map f ps) (map f xs))"
    using headed_incidence_push[OF formed injective root] head by (simp add: zip_map_map)
  show ?thesis using pushed_path pushed_head by (simp add: raw_record_at_def)
qed

lemma record_endpoints_in_carrier:
  assumes rec: "record_at obj r ps xs"
  shows "set xs \<subseteq> rra_carrier (object_structure obj)"
proof -
  have raw: "raw_record_at (object_structure obj) r ps xs"
    and formed: "rra_formed (object_structure obj)"
    using rec by (auto simp: record_at_def object_formed_def)
  have len: "length ps = length xs" by (rule raw_record_lengths[OF raw])
  have head: "headed_incidence (object_structure obj) r = set (zip ps xs)"
    using raw by (auto simp: raw_record_at_def)
  have range: "snd ` headed_incidence (object_structure obj) r = set xs"
  proof -
    have "snd ` headed_incidence (object_structure obj) r = set (map snd (zip ps xs))"
      by (simp only: head set_map)
    also have "\<dots> = set xs" using len by simp
    finally show ?thesis .
  qed
  show ?thesis using headed_targets_in_carrier[OF formed, of r] range by simp
qed

lemma record_interior_in_carrier:
  assumes source: "record_at obj r ps xs"
  shows "insert r (set ps) \<subseteq> rra_carrier (object_structure obj)"
proof -
  have formed: "rra_formed (object_structure obj)" and root: "r \<in> rra_carrier (object_structure obj)"
    and raw: "raw_record_at (object_structure obj) r ps xs"
    using source by (auto simp: record_at_def object_formed_def)
  have ports: "set ps = rel_dom (headed_incidence (object_structure obj) r)"
    using raw_record_port_set[OF raw] by simp
  show ?thesis using formed root
    by (auto simp: ports rel_dom_def headed_incidence_def rra_formed_def)
qed

lemma record_at_push:
  assumes source: "record_at obj r ps xs"
    and injective: "inj_on f (rra_carrier (object_structure obj))"
  shows "record_at (push_object f obj) (f r) (map f ps) (map f xs)"
proof -
  let ?U = "rra_carrier (object_structure obj)"
  let ?I = "insert r (set ps)"
  have oformed: "object_formed obj" and root: "r \<in> ?U"
    and raw: "raw_record_at (object_structure obj) r ps xs"
    and data: "restrict_basis ?I (object_data obj) = empty_basis"
    using source by (auto simp: record_at_def)
  have sformed: "rra_formed (object_structure obj)" and dformed: "basis_formed ?U (object_data obj)"
    using oformed by (auto simp: object_formed_def)
  have fin: "finite ?U" using sformed by (simp add: rra_formed_def)
  have subset: "?I \<subseteq> ?U" by (rule record_interior_in_carrier[OF source])
  have target: "object_formed (push_object f obj)"
    using object_push_isomorphism[OF oformed injective] by (auto simp: object_isomorphism_def)
  have pushed: "raw_record_at (object_structure (push_object f obj)) (f r) (map f ps) (map f xs)"
    using raw_record_push[OF raw sformed injective root] by (simp add: push_object_def)
  have pushed_data: "restrict_basis (insert (f r) (set (map f ps))) (object_data (push_object f obj)) = empty_basis"
    using empty_restriction_push_iff[OF fin dformed injective subset] data
    by (simp add: push_object_def)
  show ?thesis using target root pushed pushed_data
    by (simp add: record_at_def push_object_def)
qed

lemma record_path_same_heads:
  assumes path: "record_path S r p ps xs"
    and root: "headed_incidence S r = headed_incidence T r"
    and heads: "\<And>a. a \<in> set ps \<Longrightarrow> headed_incidence S a = headed_incidence T a"
  shows "record_path T r p ps xs"
  using path heads
proof (induction rule: record_path.induct)
  case (path_last p x)
  have head: "headed_incidence T p = {}" using path_last by simp
  have field: "field_endpoint T r p x"
    using path_last.hyps(3) root by (simp add: field_endpoint_from_head)
  show ?case by (rule record_path.path_last[OF path_last.hyps(1) head field])
next
  case (path_slot p q x ps xs)
  have head: "headed_incidence T p = {(p,q)}" using path_slot.hyps(2) path_slot.prems by simp
  have field: "field_endpoint T r p x"
    using path_slot.hyps(3) root by (simp add: field_endpoint_from_head)
  have tail: "record_path T r q ps xs" by (rule path_slot.IH) (use path_slot.prems in auto)
  show ?case by (rule record_path.path_slot[OF path_slot.hyps(1) head field tail])
qed

lemma record_at_same_heads:
  assumes source: "record_at obj r ps xs"
    and formed: "object_formed target" and member: "r \<in> rra_carrier (object_structure target)"
    and heads: "\<And>a. a \<in> insert r (set ps) \<Longrightarrow>
      headed_incidence (object_structure obj) a = headed_incidence (object_structure target) a"
    and data: "restrict_basis (insert r (set ps)) (object_data target) = empty_basis"
  shows "record_at target r ps xs"
proof -
  have root: "headed_incidence (object_structure obj) r = headed_incidence (object_structure target) r"
    by (rule heads) simp
  have raw: "raw_record_at (object_structure obj) r ps xs" using source by (simp add: record_at_def)
  have raw_target: "raw_record_at (object_structure target) r ps xs"
    using raw record_path_same_heads[OF _ root] heads root
    by (auto simp: raw_record_at_def)
  show ?thesis using formed member raw_target data by (simp add: record_at_def)
qed

lemma record_path_from_equations:
  assumes nonempty: "ps \<noteq> []" and length: "length ps = length xs" and root: "r \<notin> set ps"
    and fields: "\<forall>i<length ps. field_endpoint S r (ps ! i) (xs ! i)"
    and successors: "\<forall>i<length ps. headed_incidence S (ps ! i) =
      (if Suc i < length ps then {(ps ! i,ps ! Suc i)} else {})"
  shows "record_path S r (hd ps) ps xs"
  using nonempty length root fields successors
proof (induction ps arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain x tail where xs: "xs = x # tail"
    using Cons.prems(2) by (cases xs) auto
  have len: "length ps = length tail" using Cons.prems(2) xs by simp
  have rt: "r \<notin> set ps" and pr: "p \<noteq> r" using Cons.prems(3) by auto
  have field: "field_endpoint S r p x"
    using Cons.prems(4)[rule_format, of 0] xs by simp
  have head: "headed_incidence S p = (if ps = [] then {} else {(p,hd ps)})"
    using Cons.prems(5)[rule_format, of 0] by (cases ps) auto
  show ?case
  proof (cases "ps = []")
    case True
    have last: "record_path S r p [p] [x]"
      by (rule record_path.path_last[OF pr _ field]) (use head True in simp)
    show ?thesis using last True len xs by simp
  next
    case False
    have ft: "\<forall>i<length ps. field_endpoint S r (ps ! i) (tail ! i)"
    proof (intro allI impI)
      fix i assume i: "i < length ps"
      show "field_endpoint S r (ps ! i) (tail ! i)"
        using Cons.prems(4)[rule_format, of "Suc i"] i xs by simp
    qed
    have st: "\<forall>i<length ps. headed_incidence S (ps ! i) =
      (if Suc i < length ps then {(ps ! i,ps ! Suc i)} else {})"
    proof (intro allI impI)
      fix i assume i: "i < length ps"
      show "headed_incidence S (ps ! i) =
        (if Suc i < length ps then {(ps ! i,ps ! Suc i)} else {})"
        using Cons.prems(5)[rule_format, of "Suc i"] i by simp
    qed
    have tail_path: "record_path S r (hd ps) ps tail"
      by (rule Cons.IH[OF False len rt ft st])
    have "record_path S r p (p # ps) (x # tail)"
      by (rule record_path.path_slot[OF pr _ field tail_path]) (use head False in simp)
    then show ?thesis using xs by simp
  qed
qed

definition record_structure ::
  "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a rra_structure" where
  "record_structure r ps xs =
    \<lparr>rra_carrier = insert r (set ps \<union> set xs),
     rra_incidence = (\<lambda>(p,x). (r,p,x)) ` set (zip ps xs) \<union>
       (\<lambda>(p,q). (p,p,q)) ` set (zip ps (tl ps))\<rparr>"

definition record_object ::
  "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> ('a,'v) structured_object" where
  "record_object r ps xs =
    \<lparr>object_structure = record_structure r ps xs, object_data = empty_basis\<rparr>"

lemma record_structure_push:
  "push_structure f (record_structure r ps xs) =
    record_structure (f r) (map f ps) (map f xs)"
  by (auto simp: rra_identity push_structure_def record_structure_def zip_map_map
    map_tl[symmetric] image_image intro: rev_image_eqI)

lemma record_object_formed:
  "object_formed (record_object r ps xs)"
proof -
  have tail: "set (tl ps) \<subseteq> set ps" by (cases ps) auto
  have reaches: "\<And>a b. (a,b) \<in> set (zip ps (tl ps)) \<Longrightarrow> b \<in> set ps"
  proof -
    fix a b assume pair: "(a,b) \<in> set (zip ps (tl ps))"
    have "b \<in> set (tl ps)" by (rule set_zip_rightD[OF pair])
    then show "b \<in> set ps" using tail by auto
  qed
  show ?thesis
    by (auto simp: record_object_def record_structure_def object_formed_def rra_formed_def
      dest: set_zip_leftD set_zip_rightD reaches)
qed

lemma record_object_root_head:
  assumes "r \<notin> set ps"
  shows "headed_incidence (record_structure r ps xs) r = set (zip ps xs)"
  using assms
  by (auto simp: record_structure_def headed_incidence_def
    dest: set_zip_leftD intro: rev_image_eqI)

lemma record_structure_head_outside:
  assumes "a \<notin> insert r (set ps)"
  shows "headed_incidence (record_structure r ps xs) a = {}"
  using assms by (auto simp: record_structure_def headed_incidence_def dest: set_zip_leftD)

lemma record_object_field:
  assumes root: "r \<notin> set ps" and distinct: "distinct ps"
    and member: "(p,x) \<in> set (zip ps xs)"
  shows "field_endpoint (record_structure r ps xs) r p x"
proof -
  have fibre: "{y. (p,y) \<in> set (zip ps xs)} = {x}"
    by (rule single_valued_fibre[OF single_valued_zip[OF distinct] member])
  have head: "headed_incidence (record_structure r ps xs) r = set (zip ps xs)"
    by (rule record_object_root_head[OF root])
  have "{y. (p,y) \<in> headed_incidence (record_structure r ps xs) r} = {x}"
    using head fibre by simp
  then show ?thesis by (simp add: field_endpoint_def)
qed

lemma record_object_port_head:
  assumes "p \<noteq> r"
  shows "headed_incidence (record_structure r ps xs) p =
    (\<lambda>q. (p,q)) ` {q. (p,q) \<in> set (zip ps (tl ps))}"
  using assms
  by (auto simp: record_structure_def headed_incidence_def intro: rev_image_eqI)

lemma record_successor_fibre:
  assumes dist: "distinct ps" and index: "i < length ps"
  shows "{q. (ps ! i,q) \<in> set (zip ps (tl ps))} =
    (if Suc i < length ps then {ps ! Suc i} else {})"
proof -
  have nth: "(tl ps) ! i = ps ! Suc i" using index by (cases ps) auto
  have member: "\<And>q. (ps ! i,q) \<in> set (zip ps (tl ps)) \<longleftrightarrow>
    Suc i < length ps \<and> q = ps ! Suc i"
  proof -
    fix q
    show "(ps ! i,q) \<in> set (zip ps (tl ps)) \<longleftrightarrow>
      Suc i < length ps \<and> q = ps ! Suc i"
    proof
      assume "(ps ! i,q) \<in> set (zip ps (tl ps))"
      then obtain j where j: "ps ! j = ps ! i" "(tl ps) ! j = q"
        "j < length ps" "j < length (tl ps)"
        by (auto simp: in_set_zip)
      have ji: "j = i" using nth_eq_iff_index_eq[OF dist j(3) index] j(1) by simp
      show "Suc i < length ps \<and> q = ps ! Suc i"
        using j(2,4) ji nth by (cases ps) auto
    next
      assume rhs: "Suc i < length ps \<and> q = ps ! Suc i"
      have small: "i < length (tl ps)" using rhs by (cases ps) auto
      show "(ps ! i,q) \<in> set (zip ps (tl ps))"
        using index small rhs nth by (auto simp: in_set_zip)
    qed
  qed
  show ?thesis using member by auto
qed

lemma record_object_recovers:
  assumes len: "length ps = length xs" and dist: "distinct ps" and root: "r \<notin> set ps"
  shows "record_at (record_object r ps xs) r ps xs"
proof -
  let ?S = "record_structure r ps xs"
  have fields: "\<forall>i<length ps. field_endpoint ?S r (ps ! i) (xs ! i)"
  proof (intro allI impI)
    fix i assume i: "i < length ps"
    have pair: "(ps ! i,xs ! i) \<in> set (zip ps xs)"
      using i len by (auto simp: in_set_zip)
    show "field_endpoint ?S r (ps ! i) (xs ! i)"
      by (rule record_object_field[OF root dist pair])
  qed
  have heads: "\<forall>i<length ps. headed_incidence ?S (ps ! i) =
    (if Suc i < length ps then {(ps ! i,ps ! Suc i)} else {})"
  proof (intro allI impI)
    fix i assume i: "i < length ps"
    have pr: "ps ! i \<noteq> r" using i root by auto
    show "headed_incidence ?S (ps ! i) =
      (if Suc i < length ps then {(ps ! i,ps ! Suc i)} else {})"
      using record_object_port_head[OF pr, of ps xs]
        record_successor_fibre[OF dist i]
      by (auto split: if_splits)
  qed
  have raw: "raw_record_at ?S r ps xs"
  proof (cases "ps = []")
    case True
    then show ?thesis using len record_object_root_head[OF root, of xs]
      by (simp add: raw_record_at_def)
  next
    case False
    have path: "record_path ?S r (hd ps) ps xs"
      by (rule record_path_from_equations[OF False len root fields heads])
    show ?thesis using path record_object_root_head[OF root, of xs]
      by (simp add: raw_record_at_def)
  qed
  show ?thesis
    using record_object_formed[of r ps xs] raw
    by (simp add: record_at_def record_object_def record_structure_def)
qed

lemma record_representation_total:
  assumes root_formed: "octets_formed r" and endpoints: "\<forall>x\<in>set xs. octets_formed x"
  shows "\<exists>ps R. exact_formed R \<and> record_at R r ps xs \<and>
    rra_carrier (object_structure R) = insert r (set ps \<union> set xs)"
proof -
  let ?ps = "fresh_addresses (insert r (set xs)) (length xs)"
  let ?R = "record_object r ?ps xs :: exact_artifact"
  have disjoint: "distinct ?ps \<and> set ?ps \<inter> insert r (set xs) = {}"
    by (rule fresh_addresses_disjoint) simp
  have cite: "record_at ?R r ?ps xs"
    by (rule record_object_recovers) (use disjoint in auto)
  have oformed: "object_formed ?R" by (rule record_object_formed)
  have exact: "exact_formed ?R"
    using oformed root_formed endpoints fresh_addresses_formed[of "insert r (set xs)" "length xs"]
    by (auto simp: exact_formed_def record_object_def record_structure_def)
  show ?thesis
    by (rule exI[of _ ?ps], rule exI[of _ ?R])
       (use cite exact in \<open>simp add: record_object_def record_structure_def\<close>)
qed

text \<open>
  Field incidence determines the complete socket set. Successor incidence orders
  that set; the first socket is recovered from the complete path. There is no
  stored header, position number, or terminal marker. Empty and singleton
  records need no order incidence. Distinctness of sockets follows from finite
  deterministic reading; endpoint repetition and sharing remain visible.
\<close>

section \<open>Families preserve their complete socket graph\<close>

definition family_at ::
  "('a,'v) structured_object \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bool" where
  "family_at obj r M \<longleftrightarrow>
    object_formed obj \<and> r \<in> rra_carrier (object_structure obj) \<and>
    headed_incidence (object_structure obj) r = M \<and> single_valued M \<and>
    r \<notin> rel_dom M \<and>
    (\<forall>p\<in>rel_dom M. headed_incidence (object_structure obj) p = {}) \<and>
    restrict_basis (insert r (rel_dom M)) (object_data obj) = empty_basis"

lemma family_at_unique:
  assumes "family_at obj r M" "family_at obj r N"
  shows "M = N"
  using assms by (simp add: family_at_def)

lemma family_interior_in_carrier:
  assumes "family_at R r M"
  shows "insert r (rel_dom M) \<subseteq> rra_carrier (object_structure R)"
  using assms
  by (auto simp: family_at_def object_formed_def rra_formed_def rel_dom_def headed_incidence_def)

lemma family_socket_targets:
  assumes "family_at obj r M" "p \<in> rel_dom M"
  shows "\<exists>!x. (p,x) \<in> M"
  using assms by (auto simp: family_at_def single_valued_def rel_dom_def)

lemma family_socket_graph_finite:
  assumes "family_at obj r M"
  shows "finite M"
proof -
  have sub: "M \<subseteq> rra_carrier (object_structure obj) \<times> rra_carrier (object_structure obj)"
    using assms by (auto simp: family_at_def headed_incidence_def object_formed_def rra_formed_def)
  have fin: "finite (rra_carrier (object_structure obj))"
    using assms by (simp add: family_at_def object_formed_def rra_formed_def)
  show ?thesis by (rule finite_subset[OF sub]) (use fin in simp)
qed

lemma family_at_push:
  assumes source: "family_at obj r M"
    and injective: "inj_on f (rra_carrier (object_structure obj))"
  shows "family_at (push_object f obj) (f r) ((\<lambda>(p,x). (f p,f x)) ` M)"
proof -
  let ?U = "rra_carrier (object_structure obj)"
  let ?I = "insert r (rel_dom M)"
  let ?N = "(\<lambda>(p,x). (f p,f x)) ` M"
  have oformed: "object_formed obj" and root: "r \<in> ?U"
    and head: "headed_incidence (object_structure obj) r = M"
    and sv: "single_valued M" and separate: "r \<notin> rel_dom M"
    and ports: "\<forall>p\<in>rel_dom M. headed_incidence (object_structure obj) p = {}"
    and data: "restrict_basis ?I (object_data obj) = empty_basis"
    using source by (auto simp: family_at_def)
  have sformed: "rra_formed (object_structure obj)" and dformed: "basis_formed ?U (object_data obj)"
    using oformed by (auto simp: object_formed_def)
  have fin: "finite ?U" using sformed by (simp add: rra_formed_def)
  have local: "M \<subseteq> ?U \<times> ?U"
    using sformed head by (auto simp: rra_formed_def headed_incidence_def)
  have subset: "?I \<subseteq> ?U" using local root by (auto simp: rel_dom_def)
  have domain_inj: "inj_on f (rel_dom M)" by (rule inj_on_subset[OF injective]) (use subset in auto)
  have nsv: "single_valued ?N" by (rule single_valued_pair_image[OF sv domain_inj])
  have apart: "f r \<notin> rel_dom ?N"
  proof
    assume "f r \<in> rel_dom ?N"
    then obtain p where member: "p \<in> rel_dom M" and eq: "f r = f p"
      by (auto simp: pair_image_domain)
    have pu: "p \<in> ?U" using subset member by blast
    have "r = p" by (rule inj_onD[OF injective eq root pu])
    then show False using member separate by simp
  qed
  have target: "object_formed (push_object f obj)"
    using object_push_isomorphism[OF oformed injective] by (auto simp: object_isomorphism_def)
  have pushed_head: "headed_incidence (object_structure (push_object f obj)) (f r) = ?N"
    using headed_incidence_push[OF sformed injective root] head by (simp add: push_object_def)
  have pushed_ports: "\<forall>p\<in>rel_dom ?N. headed_incidence (object_structure (push_object f obj)) p = {}"
  proof (intro ballI)
    fix p assume "p \<in> rel_dom ?N"
    then obtain a where member: "a \<in> rel_dom M" and eq: "p = f a"
      by (auto simp: pair_image_domain)
    have au: "a \<in> ?U" using subset member by blast
    have empty: "headed_incidence (object_structure obj) a = {}" using ports member by blast
    show "headed_incidence (object_structure (push_object f obj)) p = {}"
      using headed_incidence_push[OF sformed injective au] empty eq by (simp add: push_object_def)
  qed
  have pushed_data: "restrict_basis (insert (f r) (rel_dom ?N)) (object_data (push_object f obj)) = empty_basis"
    using empty_restriction_push_iff[OF fin dformed injective subset] data
    by (simp add: push_object_def pair_image_domain)
  show ?thesis using target root pushed_head nsv apart pushed_ports pushed_data
    by (simp add: family_at_def push_object_def)
qed

definition family_object :: "'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a,'v) structured_object" where
  "family_object r M =
    \<lparr>object_structure =
      \<lparr>rra_carrier = insert r (rel_dom M \<union> rel_ran M),
       rra_incidence = (\<lambda>(p,x). (r,p,x)) ` M\<rparr>,
     object_data = empty_basis\<rparr>"

lemma family_object_formed:
  assumes "finite M"
  shows "object_formed (family_object r M)"
  using assms finite_rel_dom[OF assms] finite_rel_ran[OF assms]
  by (auto simp: family_object_def object_formed_def rra_formed_def rel_dom_def rel_ran_def)

lemma family_object_head:
  "headed_incidence (object_structure (family_object r M)) r = M"
  by (auto simp: family_object_def headed_incidence_def intro: rev_image_eqI)

lemma family_object_other_head:
  assumes "p \<noteq> r"
  shows "headed_incidence (object_structure (family_object r M)) p = {}"
  using assms by (auto simp: family_object_def headed_incidence_def)

lemma family_object_recovers:
  assumes finite: "finite M" and functional: "single_valued M" and separate: "r \<notin> rel_dom M"
  shows "family_at (family_object r M) r M"
proof -
  have formed: "object_formed (family_object r M)"
    by (rule family_object_formed[OF finite])
  have heads: "\<forall>p\<in>rel_dom M. headed_incidence (object_structure (family_object r M)) p = {}"
  proof (intro ballI)
    fix p assume "p \<in> rel_dom M"
    then have different: "p \<noteq> r" using separate by blast
    show "headed_incidence (object_structure (family_object r M)) p = {}"
      by (rule family_object_other_head[OF different])
  qed
  show ?thesis
    using formed functional separate heads family_object_head[of r M]
    by (simp add: family_at_def family_object_def)
qed

lemma a_family_retains_repeated_endpoints:
  "\<exists>R :: exact_artifact. \<exists>r M.
    exact_formed R \<and> family_at R r M \<and> card (rel_dom M) = 2 \<and> card (rel_ran M) = 1"
proof -
  let ?M = "{([0],[2]),([1],[2])} :: (local_address \<times> local_address) set"
  let ?R = "family_object [] ?M :: exact_artifact"
  have fam: "family_at ?R [] ?M"
    by (rule family_object_recovers)
       (auto simp: single_valued_def rel_dom_def)
  have ef: "exact_formed ?R"
  proof -
    have formed: "object_formed ?R" by (rule family_object_formed) simp
    show ?thesis using formed
      by (simp add: exact_formed_def family_object_def rel_dom_image rel_ran_image octets_formed_def)
  qed
  have sizes: "card (rel_dom ?M) = 2" "card (rel_ran ?M) = 1"
    by (simp_all add: rel_dom_image rel_ran_image)
  show ?thesis
    by (rule exI[of _ ?R], rule exI[of _ "[]"], rule exI[of _ ?M])
       (use fam ef sizes in blast)
qed

text \<open>
  A family exposes the complete relation from socket occurrences to endpoints.
  Two sockets may reach the same endpoint. No enumeration order is stored or
  inferred. Reading only the endpoint set would discard multiplicity and is not
  the family projection.
\<close>

section \<open>Families of exact cited targets\<close>

definition anchor_family_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   (local_address \<times> exact_target) set \<Rightarrow> bool" where
  "anchor_family_at E u root K \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R M g. artifact_at E u R \<and> family_at R root M \<and>
      (\<forall>s a. (s,a) \<in> M \<longrightarrow> anchored_at E u a (g s)) \<and>
      K = graph_map (rel_dom M) g)"

lemma anchor_family_unique:
  assumes first: "anchor_family_at E u root K" and second: "anchor_family_at E u root L"
  shows "K = L"
proof -
  obtain R M g where a: "environment_formed E" "artifact_at E u R" "family_at R root M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> anchored_at E u a (g s)"
    "K = graph_map (rel_dom M) g"
    using first unfolding anchor_family_at_def by blast
  obtain S N h where b: "artifact_at E u S" "family_at S root N"
    "\<forall>s a. (s,a) \<in> N \<longrightarrow> anchored_at E u a (h s)"
    "L = graph_map (rel_dom N) h"
    using second unfolding anchor_family_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have sockets: "M = N" using family_at_unique[OF a(3)] b(2) same by blast
  have pointwise: "\<And>s. s \<in> rel_dom M \<Longrightarrow> g s = h s"
  proof -
    fix s assume "s \<in> rel_dom M"
    then obtain d where edge: "(s,d) \<in> M" by (auto simp: rel_dom_def)
    have left: "anchored_at E u d (g s)" using a(4) edge by blast
    have right: "anchored_at E u d (h s)" using b(3) edge sockets by blast
    show "g s = h s" by (rule anchored_at_unique[OF a(1) left right])
  qed
  show ?thesis using pointwise sockets a(5) b(4) by (auto simp: graph_map_def)
qed

lemma anchor_family_complete_domain:
  assumes source: "anchor_family_at E u root K"
    and art: "artifact_at E u R" and fam: "family_at R root M"
  shows "rel_dom K = rel_dom M"
proof -
  obtain S N g where a: "environment_formed E" "artifact_at E u S" "family_at S root N"
    "K = graph_map (rel_dom N) g"
    using source unfolding anchor_family_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1) art a(2)])
  have sockets: "M = N" using family_at_unique[OF fam] a(3) same by blast
  show ?thesis using a(4) sockets by (simp add: graph_map_dom)
qed

lemma anchor_family_finite:
  assumes "anchor_family_at E u root K"
  shows "finite K"
proof -
  obtain R M g where a: "artifact_at E u R" "family_at R root M" "K = graph_map (rel_dom M) g"
    using assms unfolding anchor_family_at_def by blast
  have finite: "finite (rel_dom M)"
    by (rule finite_rel_dom[OF family_socket_graph_finite[OF a(2)]])
  show ?thesis using graph_map_exact[OF finite, of g] a(3) by (simp add: exact_map_def)
qed

lemma anchor_family_single_valued:
  assumes "anchor_family_at E u root K"
  shows "single_valued K"
  using assms graph_map_single_valued unfolding anchor_family_at_def by blast

lemma anchor_family_targets_formed:
  assumes source: "anchor_family_at E u root K" and member: "(s,t) \<in> K"
  shows "target_formed t"
proof -
  obtain R M g where a: "artifact_at E u R" "family_at R root M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> anchored_at E u a (g s)"
    "K = graph_map (rel_dom M) g"
    using source unfolding anchor_family_at_def by blast
  obtain d where edge: "(s,d) \<in> M" and target: "t = g s"
    using member a(4) by (auto simp: graph_map_def rel_dom_def)
  have anchor: "anchored_at E u d t" using a(3) edge target by blast
  show ?thesis by (rule anchored_at_target_formed[OF anchor])
qed

lemma anchor_family_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "anchor_family_at E u root K = anchor_family_at F u root K"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have targets: "\<forall>a t. anchored_at E u a t = anchored_at F u a t"
    using anchored_at_environment_locality[OF agree closed member] by blast
  show ?thesis by (simp only: anchor_family_at_def ef ff arts targets)
qed

definition target_selection_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> exact_target set \<Rightarrow> bool" where
  "target_selection_at E u root T \<longleftrightarrow>
    (\<exists>K. anchor_family_at E u root K \<and> inj_on snd K \<and> T = rel_ran K)"

lemma target_selection_unique:
  assumes first: "target_selection_at E u root S" and second: "target_selection_at E u root T"
  shows "S = T"
proof -
  obtain K where a: "anchor_family_at E u root K" "S = rel_ran K"
    using first unfolding target_selection_at_def by blast
  obtain L where b: "anchor_family_at E u root L" "T = rel_ran L"
    using second unfolding target_selection_at_def by blast
  have "K = L" by (rule anchor_family_unique[OF a(1) b(1)])
  then show ?thesis using a(2) b(2) by simp
qed

lemma target_selection_formed:
  assumes "target_selection_at E u root T"
  shows "finite T \<and> (\<forall>t\<in>T. target_formed t)"
proof -
  obtain K where family: "anchor_family_at E u root K" and targets: "T = rel_ran K"
    using assms unfolding target_selection_at_def by blast
  have finite: "finite T" using finite_rel_ran[OF anchor_family_finite[OF family]] targets by simp
  have formed: "\<forall>t\<in>T. target_formed t"
    using anchor_family_targets_formed[OF family] targets unfolding rel_ran_def by blast
  show ?thesis using finite formed by blast
qed

lemma target_selection_locality:
  assumes "environment_formed E" "environment_formed F" "environment_agrees_on E F U"
    "environment_edge_closed E U" "u \<in> U"
  shows "target_selection_at E u root T = target_selection_at F u root T"
  unfolding target_selection_at_def
  by (simp only: anchor_family_locality[OF assms])

section \<open>Readdressing citation structure while preserving opaque operands\<close>

fun map_citation_positions :: "(local_address \<Rightarrow> local_address) \<Rightarrow> citation \<Rightarrow> citation" where
  "map_citation_positions f (Local a) = Local (f a)"
| "map_citation_positions f Local_Whole = Local_Whole"
| "map_citation_positions f (External k a) = External (f k) a"
| "map_citation_positions f (External_Whole k) = External_Whole (f k)"

lemma citation_at_push:
  assumes cite: "citation_at R r c I"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
  shows "citation_at (push_object f R) (f r) (map_citation_positions f c) (f ` I)"
proof -
  let ?U = "rra_carrier (object_structure R)"
  let ?S = "object_structure R"
  have formed: "exact_formed R" and source: "object_formed R" and sf: "rra_formed ?S"
    and member: "r \<in> ?U" and empty: "restrict_basis {r} (object_data R) = empty_basis"
    and raw: "raw_citation_at R r c I"
    using cite by (auto simp: citation_at_def exact_formed_def object_formed_def)
  have injective: "inj_on f ?U" using addressing by (simp add: finite_addressing_def)
  have head: "headed_incidence (object_structure (push_object f R)) (f r) =
    (\<lambda>(p,x). (f p,f x)) ` headed_incidence ?S r"
    using headed_incidence_push[OF sf injective member] by (simp add: push_object_def)
  have result: "raw_citation_at (push_object f R) (f r) (map_citation_positions f c) (f ` I)"
  proof (cases rule: raw_citation_at.cases[OF raw, case_names local local_whole external_whole external])
    case (local a)
    have "raw_citation_at (push_object f R) (f r) (Local (f a)) {f r}"
      by (rule raw_citation_at.local) (simp add: head local)
    then show ?thesis using local by simp
  next
    case local_whole
    have "raw_citation_at (push_object f R) (f r) Local_Whole {f r}"
      by (rule raw_citation_at.local_whole) (simp add: head local_whole)
    then show ?thesis using local_whole by simp
  next
    case (external_whole k)
    have km: "k \<in> ?U" using citation_slots_in_carrier[OF cite] external_whole by simp
    have apart: "f r \<noteq> f k"
      using inj_on_eq_iff[OF injective member km] external_whole by simp
    have "raw_citation_at (push_object f R) (f r) (External_Whole (f k)) {f r}"
      by (rule raw_citation_at.external_whole[OF apart]) (simp add: head external_whole)
    then show ?thesis using external_whole by simp
  next
    case (external k d a)
    have km: "k \<in> ?U" using citation_slots_in_carrier[OF cite] external by simp
    have dm: "d \<in> ?U" using citation_interior_in_carrier[OF cite] external by simp
    have apart: "distinct [f r,f k,f d]"
      using external inj_on_eq_iff[OF injective member km]
        inj_on_eq_iff[OF injective member dm] inj_on_eq_iff[OF injective km dm] by simp
    have leaf: "headed_incidence (object_structure (push_object f R)) (f d) = {}"
      using headed_incidence_push[OF sf injective dm] external
      by (simp add: push_object_def)
    have payload: "payload_at (push_object f R) (f d) a"
      using payload_at_push[OF source injective dm] external by simp
    have "raw_citation_at (push_object f R) (f r) (External (f k) a) {f r,f d}"
      by (rule raw_citation_at.external[OF apart _ leaf payload]) (simp add: head external)
    then show ?thesis using external by simp
  qed
  have target: "exact_formed (push_object f R)" by (rule exact_push_formed[OF formed addressing])
  have mapped_member: "f r \<in> rra_carrier (object_structure (push_object f R))"
    using member by (simp add: push_object_def)
  have fin: "finite ?U" and df: "basis_formed ?U (object_data R)"
    using source by (auto simp: object_formed_def rra_formed_def)
  have no_data: "restrict_basis {f r} (object_data (push_object f R)) = empty_basis"
    using empty_restriction_push_iff[OF fin df injective, of "{r}"] member empty
    by (simp add: push_object_def)
  show ?thesis using target mapped_member no_data result by (simp add: citation_at_def)
qed

lemma citation_slots_push:
  "citation_slots (map_citation_positions f c) = f ` citation_slots c"
  by (cases c) simp_all

definition external_slot_values ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> exact_artifact set" where
  "external_slot_values E u k = {R. \<exists>v. binds_slot E u k v \<and> artifact_at E v R}"

lemma external_interpretation_by_slot:
  "interpret_citation E u (External k a) t \<longleftrightarrow>
    (\<exists>R\<in>external_slot_values E u k. anchor_formed (R,a) \<and> t = Occurrence_Anchor (R,a))"
  "interpret_citation E u (External_Whole k) t \<longleftrightarrow>
    (\<exists>R\<in>external_slot_values E u k. exact_formed R \<and> t = Whole_Artifact R)"
  by (auto simp: external_slot_values_def)

lemma external_citation_slot_transport:
  assumes external: "citation_slots c \<noteq> {}"
    and agree: "\<forall>k\<in>citation_slots c. external_slot_values E u k = external_slot_values F w (f k)"
  shows "interpret_citation E u c t = interpret_citation F w (map_citation_positions f c) t"
  using assms by (cases c)
    (simp_all add: external_interpretation_by_slot del: interpret_citation.simps)

lemma anchored_at_with_citation:
  assumes formed: "environment_formed E" and art: "artifact_at E u R"
    and cite: "citation_at R r c I"
  shows "anchored_at E u r t \<longleftrightarrow> interpret_citation E u c t"
proof
  assume "anchored_at E u r t"
  then obtain S d J where other: "artifact_at E u S" "citation_at S r d J" "interpret_citation E u d t"
    by (auto simp: anchored_at_def)
  have same: "R = S" by (rule environment_artifact_unique[OF formed art other(1)])
  have code: "c = d" using citation_at_unique(1)[OF cite] other(2) same by blast
  show "interpret_citation E u c t" using code other(3) by simp
next
  assume "interpret_citation E u c t"
  then show "anchored_at E u r t" by (rule anchored_atI[OF art cite])
qed

theorem external_citation_readdressing:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and source: "artifact_at E u R" and target: "artifact_at F w (push_object f R)"
    and cite: "citation_at R r c I"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and external: "citation_slots c \<noteq> {}"
    and agree: "\<forall>k\<in>citation_slots c. external_slot_values E u k = external_slot_values F w (f k)"
  shows "anchored_at E u r t \<longleftrightarrow> anchored_at F w (f r) t"
proof -
  have copied: "citation_at (push_object f R) (f r) (map_citation_positions f c) (f ` I)"
    by (rule citation_at_push[OF cite addressing])
  show ?thesis
    using external_citation_slot_transport[OF external agree, of t]
    by (simp only: anchored_at_with_citation[OF ef source cite]
        anchored_at_with_citation[OF ff target copied])
qed

lemma one_binding_slot_value [simp]:
  "external_slot_values (one_binding_environment R k S) False k = {S}"
  by (auto simp: external_slot_values_def one_binding_environment_def artifact_at_def binds_slot_def)

theorem one_binding_slot_readdressing:
  assumes cite: "citation_at R r c I" and slot: "citation_slots c = {k}"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and remote: "exact_formed T"
  shows "environment_closed (one_binding_environment (push_object f R) (f k) T)
      {False} {(False,f k)}"
    and "anchored_at (one_binding_environment R k T) False r t \<longleftrightarrow>
      anchored_at (one_binding_environment (push_object f R) (f k) T) False (f r) t"
proof -
  have rf: "exact_formed R" using cite by (simp add: citation_at_def)
  have sf: "exact_formed (push_object f R)" by (rule exact_push_formed[OF rf addressing])
  have km: "k \<in> rra_carrier (object_structure R)"
    using citation_slots_in_carrier[OF cite] slot by simp
  have mapped: "f k \<in> rra_carrier (object_structure (push_object f R))"
    using km by (simp add: push_object_def)
  have ec: "environment_closed (one_binding_environment R k T) {False} {(False,k)}"
    by (rule one_binding_environment_closed[OF rf remote km])
  show fc: "environment_closed (one_binding_environment (push_object f R) (f k) T)
      {False} {(False,f k)}"
    by (rule one_binding_environment_closed[OF sf remote mapped])
  have ef: "environment_formed (one_binding_environment R k T)"
    using ec by (simp add: environment_closed_def)
  have ff: "environment_formed (one_binding_environment (push_object f R) (f k) T)"
    using fc by (simp add: environment_closed_def)
  have source: "artifact_at (one_binding_environment R k T) False R"
    and target: "artifact_at (one_binding_environment (push_object f R) (f k) T) False (push_object f R)"
    by (auto simp: one_binding_environment_def artifact_at_def)
  show "anchored_at (one_binding_environment R k T) False r t \<longleftrightarrow>
      anchored_at (one_binding_environment (push_object f R) (f k) T) False (f r) t"
    by (rule external_citation_readdressing[OF ef ff source target cite addressing])
       (use slot in auto)
qed

text \<open>
  Slot correspondence compares the exact artifacts already supplied by the two
  finite environments. It supplies no truth interpretation. Remote addresses
  are opaque operands and remain fixed. A local citation instead changes its
  containing exact artifact under readdressing; it must be transported as an
  exact anchor and cannot be claimed literally unchanged.
\<close>

end
