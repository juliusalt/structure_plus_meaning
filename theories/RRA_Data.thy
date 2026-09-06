theory RRA_Data
  imports RRA_Core
begin

type_synonym octets = "nat list"

definition octets_formed :: "octets \<Rightarrow> bool" where
  "octets_formed xs \<longleftrightarrow> (\<forall>x \<in> set xs. x < 256)"


section \<open>Opaque attachments with explicit transport\<close>

record ('a,'v) opaque_basis =
  bag_count :: "('a \<times> 'v) \<Rightarrow> nat"
  functional_bindings :: "('a \<times> 'v) set"

definition bag_support :: "('a,'v) opaque_basis \<Rightarrow> ('a \<times> 'v) set" where
  "bag_support D = {av. bag_count D av \<noteq> 0}"

definition basis_values :: "('a,'v) opaque_basis \<Rightarrow> 'v set" where
  "basis_values D = snd ` (bag_support D \<union> functional_bindings D)"

definition basis_formed :: "'a set \<Rightarrow> ('a,'v) opaque_basis \<Rightarrow> bool" where
  "basis_formed U D \<longleftrightarrow>
     finite (bag_support D) \<and> finite (functional_bindings D) \<and>
     single_valued (functional_bindings D) \<and>
     bag_support D \<subseteq> U \<times> UNIV \<and>
     functional_bindings D \<subseteq> U \<times> UNIV"

definition empty_basis :: "('a,'v) opaque_basis" where
  "empty_basis = \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {}\<rparr>"

lemma empty_basis_formed [simp]: "basis_formed U empty_basis"
  by (simp add: basis_formed_def empty_basis_def bag_support_def single_valued_def)

lemma empty_basis_values [simp]: "basis_values empty_basis = {}"
  by (simp add: basis_values_def empty_basis_def bag_support_def)

lemma basis_identity:
  fixes D E :: "('a,'v) opaque_basis"
  shows "D = E \<longleftrightarrow>
    bag_count D = bag_count E \<and> functional_bindings D = functional_bindings E"
  by (cases D; cases E) auto

lemma bag_attachment_in_carrier:
  assumes "basis_formed U D" "bag_count D (a,v) \<noteq> 0"
  shows "a \<in> U"
  using assms by (auto simp: basis_formed_def bag_support_def)

lemma functional_attachment_in_carrier:
  assumes "basis_formed U D" "(a,v) \<in> functional_bindings D"
  shows "a \<in> U"
  using assms by (auto simp: basis_formed_def)

lemma finite_basis_values:
  assumes "basis_formed U D"
  shows "finite (basis_values D)"
  using assms by (auto simp: basis_formed_def basis_values_def)

lemma basis_formed_mono:
  assumes "basis_formed U D" "U \<subseteq> V"
  shows "basis_formed V D"
  using assms unfolding basis_formed_def by blast

section \<open>Restriction at the sole attachment atom\<close>

definition restrict_basis ::
  "'a set \<Rightarrow> ('a,'v) opaque_basis \<Rightarrow> ('a,'v) opaque_basis" where
  "restrict_basis A D =
    \<lparr>bag_count = (\<lambda>av. if fst av \<in> A then bag_count D av else 0),
     functional_bindings = {av \<in> functional_bindings D. fst av \<in> A}\<rparr>"

lemma restrict_empty_basis [simp]:
  "restrict_basis A empty_basis = empty_basis"
  by (auto simp: restrict_basis_def empty_basis_def basis_identity fun_eq_iff)

lemma functional_bindings_restrict [simp]:
  "functional_bindings (restrict_basis A D) = {av \<in> functional_bindings D. fst av \<in> A}"
  by (simp add: restrict_basis_def)

lemma bag_support_restrict:
  "bag_support (restrict_basis A D) = {av \<in> bag_support D. fst av \<in> A}"
  by (auto simp: bag_support_def restrict_basis_def)

lemma restrict_basis_formed:
  assumes "basis_formed U D"
  shows "basis_formed (U \<inter> A) (restrict_basis A D)"
  using assms
  by (auto simp: basis_formed_def bag_support_restrict single_valued_def)

lemma basis_values_restrict:
  "basis_values (restrict_basis A D) \<subseteq> basis_values D"
  by (auto simp: basis_values_def bag_support_def restrict_basis_def)

lemma restriction_at_atom:
  "bag_count (restrict_basis A D) (a,v) =
     (if a \<in> A then bag_count D (a,v) else 0)"
  "(a,v) \<in> functional_bindings (restrict_basis A D) \<longleftrightarrow>
     a \<in> A \<and> (a,v) \<in> functional_bindings D"
  by (auto simp: restrict_basis_def)

lemma restriction_composes:
  "restrict_basis A (restrict_basis B D) = restrict_basis (A \<inter> B) D"
  by (auto simp: basis_identity restrict_basis_def fun_eq_iff)

section \<open>Finite gluing\<close>

definition pushed_count ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a \<times> 'v) \<Rightarrow> nat) \<Rightarrow>
   ('b \<times> 'v) \<Rightarrow> nat" where
  "pushed_count U f b = (\<lambda>(y,v). \<Sum>a\<in>U. if f a = y then b (a,v) else 0)"

lemma pushed_count_apply:
  "pushed_count U f b (y,v) = (\<Sum>a\<in>U. if f a = y then b (a,v) else 0)"
  by (simp add: pushed_count_def)

definition push_basis ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a,'v) opaque_basis \<Rightarrow> ('b,'v) opaque_basis" where
  "push_basis U f D =
    \<lparr>bag_count = pushed_count U f (bag_count D),
     functional_bindings = (\<lambda>(a,v). (f a,v)) ` functional_bindings D\<rparr>"

definition basis_compatible :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'v) opaque_basis \<Rightarrow> bool" where
  "basis_compatible f D \<longleftrightarrow>
    (\<forall>a v b w. (a,v) \<in> functional_bindings D \<longrightarrow>
       (b,w) \<in> functional_bindings D \<longrightarrow> f a = f b \<longrightarrow> v = w)"

definition compatible_bindings :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'v) list \<Rightarrow> bool" where
  "compatible_bindings f xs =
    list_all (\<lambda>av. list_all
      (\<lambda>bw. f (fst av) = f (fst bw) \<longrightarrow> snd av = snd bw) xs) xs"

lemma compatible_bindings_correct:
  "compatible_bindings f xs \<longleftrightarrow>
    (\<forall>av\<in>set xs. \<forall>bw\<in>set xs. f (fst av) = f (fst bw) \<longrightarrow> snd av = snd bw)"
  by (simp add: compatible_bindings_def list_all_iff)

lemma basis_compatibility_finite_check:
  assumes "set entries = functional_bindings D"
  shows "compatible_bindings f entries \<longleftrightarrow> basis_compatible f D"
  using assms by (auto simp: compatible_bindings_correct basis_compatible_def)

lemma pushed_count_origin:
  assumes "pushed_count U f b (y,v) \<noteq> 0"
  shows "\<exists>a \<in> U. f a = y \<and> b (a,v) \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>a \<in> U. f a = y \<and> b (a,v) \<noteq> 0)"
  then have zero: "\<And>a. a \<in> U \<Longrightarrow> (if f a = y then b (a,v) else 0) = 0"
    by auto
  have "pushed_count U f b (y,v) = 0"
    unfolding pushed_count_def by (simp add: sum.neutral zero)
  with assms show False by simp
qed

lemma pushed_bag_support:
  "bag_support (push_basis U f D) \<subseteq>
    (\<lambda>(a,v). (f a,v)) ` bag_support D"
proof
  fix av
  assume "av \<in> bag_support (push_basis U f D)"
  obtain y v where av: "av = (y,v)" by (cases av)
  then have "pushed_count U f (bag_count D) (y,v) \<noteq> 0"
    using \<open>av \<in> bag_support (push_basis U f D)\<close>
    by (simp add: bag_support_def push_basis_def)
  from pushed_count_origin[OF this] show
    "av \<in> (\<lambda>(a,v). (f a,v)) ` bag_support D"
    by (auto simp: av bag_support_def)
qed

lemma pushed_functional_single_valued:
  "single_valued (functional_bindings (push_basis U f D)) \<longleftrightarrow>
   basis_compatible f D"
  by (force simp: single_valued_def basis_compatible_def push_basis_def)

lemma pushed_basis_values:
  "basis_values (push_basis U f D) \<subseteq> basis_values D"
  using pushed_bag_support[of U f D]
  by (force simp: basis_values_def push_basis_def)

lemma push_basis_formed_iff:
  assumes "basis_formed U D"
  shows "basis_formed (f ` U) (push_basis U f D) \<longleftrightarrow> basis_compatible f D"
proof -
  have fin: "finite (bag_support (push_basis U f D))"
    using finite_subset[OF pushed_bag_support[of U f D]] assms
    by (auto simp: basis_formed_def)
  have loc: "bag_support (push_basis U f D) \<subseteq> (f ` U) \<times> UNIV"
    using pushed_bag_support[of U f D] assms
    by (force simp: basis_formed_def)
  show ?thesis
    using assms fin loc pushed_functional_single_valued[of U f D]
    by (auto simp: basis_formed_def push_basis_def)
qed

lemma injective_gluing_compatible:
  assumes formed: "basis_formed U D" and injective: "inj_on f U"
  shows "basis_compatible f D"
  unfolding basis_compatible_def
proof (intro allI impI)
  fix a v b w
  assume av: "(a,v) \<in> functional_bindings D"
    and bw: "(b,w) \<in> functional_bindings D" and same: "f a = f b"
  have au: "a \<in> U" by (rule functional_attachment_in_carrier[OF formed av])
  have bu: "b \<in> U" by (rule functional_attachment_in_carrier[OF formed bw])
  have ab: "a = b" by (rule inj_onD[OF injective same au bu])
  have sv: "single_valued (functional_bindings D)" using formed by (simp add: basis_formed_def)
  show "v = w" using sv av bw ab unfolding single_valued_def by blast
qed

lemma empty_push [simp]: "push_basis U f empty_basis = empty_basis"
  by (simp add: basis_identity push_basis_def empty_basis_def pushed_count_def fun_eq_iff)

lemma empty_compatible [simp]: "basis_compatible f empty_basis"
  by (simp add: basis_compatible_def empty_basis_def)

lemma count_outside_carrier:
  assumes "basis_formed U D" "a \<notin> U"
  shows "bag_count D (a,v) = 0"
  using assms by (auto simp: basis_formed_def bag_support_def)

lemma push_identity:
  fixes D :: "('a,'v) opaque_basis" and U :: "'a set"
  assumes "finite U" "basis_formed U D"
  shows "push_basis U id D = D"
proof (rule opaque_basis.equality)
  show "bag_count (push_basis U id D) = bag_count D"
  proof (rule ext)
    fix av :: "'a \<times> 'v"
    obtain a v where av: "av = (a,v)" by (cases av)
    show "bag_count (push_basis U id D) av = bag_count D av"
      using assms count_outside_carrier[of U D a v]
      by (simp add: av push_basis_def pushed_count_def)
  qed
  show "functional_bindings (push_basis U id D) = functional_bindings D"
    by (auto simp: push_basis_def)
  show "opaque_basis.more (push_basis U id D) = opaque_basis.more D" by simp
qed

lemma pushed_count_injective:
  assumes fin: "finite U" and injective: "inj_on f U" and member: "x \<in> U"
  shows "pushed_count U f b (f x,v) = b (x,v)"
proof -
  have eq: "\<And>a. a \<in> U \<Longrightarrow> (f a = f x \<longleftrightarrow> a = x)"
    using injective member unfolding inj_on_def by blast
  show ?thesis by (simp add: pushed_count_def eq fin member)
qed

lemma functional_at_injective:
  assumes formed: "basis_formed U D" and injective: "inj_on f U" and member: "x \<in> U"
  shows "(f x,v) \<in> functional_bindings (push_basis U f D) \<longleftrightarrow>
    (x,v) \<in> functional_bindings D"
proof
  assume "(f x,v) \<in> functional_bindings (push_basis U f D)"
  then obtain y where yv: "(y,v) \<in> functional_bindings D" and same: "f y = f x"
    by (auto simp: push_basis_def)
  have yu: "y \<in> U" by (rule functional_attachment_in_carrier[OF formed yv])
  have "y = x" by (rule inj_onD[OF injective same yu member])
  with yv show "(x,v) \<in> functional_bindings D" by simp
next
  assume "(x,v) \<in> functional_bindings D"
  then show "(f x,v) \<in> functional_bindings (push_basis U f D)"
    by (auto simp: push_basis_def intro: rev_image_eqI)
qed

lemma empty_restriction_iff:
  "restrict_basis A D = empty_basis \<longleftrightarrow>
    (\<forall>a\<in>A. (\<forall>v. bag_count D (a,v) = 0) \<and>
      (\<forall>v. (a,v) \<notin> functional_bindings D))"
  by (auto simp: basis_identity restrict_basis_def empty_basis_def fun_eq_iff)

lemma empty_restriction_mono:
  assumes "restrict_basis A D = empty_basis" "B \<subseteq> A"
  shows "restrict_basis B D = empty_basis"
  using assms by (auto simp: empty_restriction_iff; blast)

lemma empty_restriction_union:
  "restrict_basis (A \<union> B) D = empty_basis \<longleftrightarrow>
    restrict_basis A D = empty_basis \<and> restrict_basis B D = empty_basis"
  by (auto simp: empty_restriction_iff)

lemma empty_restriction_outside:
  assumes "basis_formed U D" "A \<inter> U = {}"
  shows "restrict_basis A D = empty_basis"
  using assms by (auto simp: empty_restriction_iff basis_formed_def bag_support_def)

lemma empty_restriction_push_iff:
  assumes fin: "finite U" and formed: "basis_formed U D"
    and injective: "inj_on f U" and subset: "A \<subseteq> U"
  shows "restrict_basis (f ` A) (push_basis U f D) = empty_basis \<longleftrightarrow>
    restrict_basis A D = empty_basis"
proof -
  have counts: "\<And>a v. a \<in> A \<Longrightarrow>
    bag_count (push_basis U f D) (f a,v) = bag_count D (a,v)"
  proof -
    fix a v assume "a \<in> A"
    then have member: "a \<in> U" using subset by blast
    show "bag_count (push_basis U f D) (f a,v) = bag_count D (a,v)"
      by (simp add: push_basis_def pushed_count_injective[OF fin injective member])
  qed
  have bindings: "\<And>a v. a \<in> A \<Longrightarrow>
    ((f a,v) \<in> functional_bindings (push_basis U f D)) = ((a,v) \<in> functional_bindings D)"
  proof -
    fix a v assume "a \<in> A"
    then have member: "a \<in> U" using subset by blast
    show "((f a,v) \<in> functional_bindings (push_basis U f D)) = ((a,v) \<in> functional_bindings D)"
      by (rule functional_at_injective[OF formed injective member])
  qed
  show ?thesis using counts bindings by (auto simp: empty_restriction_iff)
qed

lemma pushed_count_composes:
  fixes b :: "('a \<times> 'v) \<Rightarrow> nat" and f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
  assumes fin: "finite U"
  shows "pushed_count (f ` U) g (pushed_count U f b) = pushed_count U (g \<circ> f) b"
proof (rule ext)
  fix zv :: "'c \<times> 'v"
  obtain z v where zv: "zv = (z,v)" by (cases zv)
  have inner: "(if g y = z then pushed_count U f b (y,v) else 0) =
      (\<Sum>x\<in>{x \<in> U. f x = y}. if g (f x) = z then b (x,v) else 0)" for y
    by (cases "g y = z")
       (auto simp: pushed_count_def sum.inter_filter[OF fin] intro!: sum.cong)
  have "pushed_count (f ` U) g (pushed_count U f b) (z,v) =
      (\<Sum>y\<in>f ` U. if g y = z then pushed_count U f b (y,v) else 0)"
    by (rule pushed_count_apply)
  also have "\<dots> =
      (\<Sum>y\<in>f ` U. \<Sum>x\<in>{x \<in> U. f x = y}. if g (f x) = z then b (x,v) else 0)"
    by (simp only: inner)
  also have "\<dots> = (\<Sum>x\<in>U. if g (f x) = z then b (x,v) else 0)"
    by (rule sum.group[OF fin finite_imageI[OF fin] order_refl])
  also have "\<dots> = pushed_count U (g \<circ> f) b (z,v)"
    by (simp add: pushed_count_def)
  finally show "pushed_count (f ` U) g (pushed_count U f b) zv =
    pushed_count U (g \<circ> f) b zv" by (simp add: zv)
qed

lemma push_basis_composes:
  assumes "finite U"
  shows "push_basis (f ` U) g (push_basis U f D) = push_basis U (g \<circ> f) D"
  by (auto simp: basis_identity push_basis_def pushed_count_composes[OF assms]
    image_image intro: rev_image_eqI)

lemma pushed_count_cong:
  assumes "\<forall>a \<in> U. f a = g a"
  shows "pushed_count U f b = pushed_count U g b"
  using assms by (auto simp: pushed_count_def fun_eq_iff intro!: sum.cong)

lemma push_basis_cong:
  fixes D :: "('a,'v) opaque_basis" and f g :: "'a \<Rightarrow> 'b"
  assumes formed: "basis_formed U D" and agree: "\<forall>a \<in> U. f a = g a"
  shows "push_basis U f D = push_basis U g D"
proof (rule opaque_basis.equality)
  show "bag_count (push_basis U f D) = bag_count (push_basis U g D)"
    by (simp add: push_basis_def pushed_count_cong[OF agree])
  have images: "(\<lambda>(a,v). (f a,v)) ` functional_bindings D =
                (\<lambda>(a,v). (g a,v)) ` functional_bindings D"
  proof (rule image_cong[OF refl])
    fix av :: "'a \<times> 'v"
    assume av: "av \<in> functional_bindings D"
    obtain a v where pair: "av = (a,v)" by (cases av)
    have "a \<in> U" using functional_attachment_in_carrier[OF formed] av pair by blast
    then show "(case av of (a,v) \<Rightarrow> (f a,v)) = (case av of (a,v) \<Rightarrow> (g a,v))"
      using agree pair by simp
  qed
  show "functional_bindings (push_basis U f D) = functional_bindings (push_basis U g D)"
    by (simp add: push_basis_def images)
  show "opaque_basis.more (push_basis U f D) = opaque_basis.more (push_basis U g D)"
    by simp
qed

lemma push_basis_left_inverse:
  assumes fin: "finite U" and formed: "basis_formed U D"
    and inverse: "\<forall>a \<in> U. g (f a) = a"
  shows "push_basis (f ` U) g (push_basis U f D) = D"
proof -
  have same: "push_basis U (g \<circ> f) D = push_basis U id D"
    by (rule push_basis_cong[OF formed]) (use inverse in simp)
  show ?thesis
    using push_basis_composes[OF fin, where f=f and g=g and D=D]
      same push_identity[OF fin formed] by simp
qed

lemma basis_push_injective:
  assumes fin: "finite U" and df: "basis_formed U D" and ef: "basis_formed U E"
    and injective: "inj_on f U"
  shows "push_basis U f D = push_basis U f E \<longleftrightarrow> D = E"
proof
  assume eq: "push_basis U f D = push_basis U f E"
  have inverse: "\<forall>a \<in> U. inv_into U f (f a) = a"
    using injective by simp
  have d: "push_basis (f ` U) (inv_into U f) (push_basis U f D) = D"
    by (rule push_basis_left_inverse[where f=f and g="inv_into U f", OF fin df inverse])
  have e: "push_basis (f ` U) (inv_into U f) (push_basis U f E) = E"
    by (rule push_basis_left_inverse[where f=f and g="inv_into U f", OF fin ef inverse])
  have "D = push_basis (f ` U) (inv_into U f) (push_basis U f D)"
    by (rule d[symmetric])
  also have "\<dots> = push_basis (f ` U) (inv_into U f) (push_basis U f E)"
    by (rule arg_cong[OF eq])
  also have "\<dots> = E" by (rule e)
  finally show "D = E" .
next
  assume "D = E"
  then show "push_basis U f D = push_basis U f E" by simp
qed

text \<open>
  Compatibility is a finite pairwise comparison on a formed basis. The output
  is determined even when compatibility fails; only a compatible output forms.
  No value is interpreted as a number, program, address, or proposition here.
\<close>

section \<open>A transport counterexample to multiplicity-one reduction\<close>

definition two_functional_bindings :: "'v \<Rightarrow> (bool,'v) opaque_basis" where
  "two_functional_bindings v =
    \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = {(False,v), (True,v)}\<rparr>"

definition functional_as_units :: "('a,'v) opaque_basis \<Rightarrow> ('a,'v) opaque_basis" where
  "functional_as_units D =
    \<lparr>bag_count = (\<lambda>av. if av \<in> functional_bindings D then 1 else 0),
     functional_bindings = {}\<rparr>"

lemma support_functional_units [simp]:
  "bag_support (functional_as_units D) = functional_bindings D"
  by (auto simp: bag_support_def functional_as_units_def)

lemma functional_gluing_sources_formed:
  "basis_formed {False,True} (two_functional_bindings v)"
  "basis_formed {False,True} (functional_as_units (two_functional_bindings v))"
  by (auto simp: basis_formed_def two_functional_bindings_def functional_as_units_def
    bag_support_def single_valued_def)

lemma equal_functional_gluing_is_compatible:
  "basis_compatible (\<lambda>_. ()) (two_functional_bindings v)"
  by (auto simp: basis_compatible_def two_functional_bindings_def)

lemma functional_units_do_not_commute:
  "bag_count (push_basis {False,True} (\<lambda>_. ())
     (functional_as_units (two_functional_bindings v))) ((),v) = 2"
  "bag_count (functional_as_units
     (push_basis {False,True} (\<lambda>_. ()) (two_functional_bindings v))) ((),v) = 1"
  by (simp_all add: push_basis_def pushed_count_def functional_as_units_def
    two_functional_bindings_def)

lemma functional_units_unequal_push:
  "push_basis {False,True} (\<lambda>_. ()) (functional_as_units (two_functional_bindings v))
   \<noteq> functional_as_units (push_basis {False,True} (\<lambda>_. ()) (two_functional_bindings v))"
proof
  assume eq: "push_basis {False,True} (\<lambda>_. ()) (functional_as_units (two_functional_bindings v)) =
    functional_as_units (push_basis {False,True} (\<lambda>_. ()) (two_functional_bindings v))"
  have "bag_count (push_basis {False,True} (\<lambda>_. ())
     (functional_as_units (two_functional_bindings v))) ((),v) =
    bag_count (functional_as_units
     (push_basis {False,True} (\<lambda>_. ()) (two_functional_bindings v))) ((),v)"
    using eq by simp
  then have "(2::nat) = 1" by (simp only: functional_units_do_not_commute)
  then show False by simp
qed

section \<open>Structures carrying the opaque basis\<close>

record ('a,'v) structured_object =
  object_structure :: "'a rra_structure"
  object_data :: "('a,'v) opaque_basis"

lemma object_identity:
  fixes obj other :: "('a,'v) structured_object"
  shows "obj = other \<longleftrightarrow> object_structure obj = object_structure other \<and>
    object_data obj = object_data other"
  by (cases obj; cases other) auto

definition object_formed :: "('a,'v) structured_object \<Rightarrow> bool" where
  "object_formed obj \<longleftrightarrow>
    rra_formed (object_structure obj) \<and>
    basis_formed (rra_carrier (object_structure obj)) (object_data obj)"

definition restrict_object ::
  "('a,'v) structured_object \<Rightarrow> 'a set \<Rightarrow> ('a,'v) structured_object" where
  "restrict_object obj A =
    \<lparr>object_structure = restrict_structure (object_structure obj) A,
     object_data = restrict_basis (rra_carrier (object_structure obj) \<inter> A) (object_data obj)\<rparr>"

lemma restrict_object_formed:
  assumes formed: "object_formed obj"
  shows "object_formed (restrict_object obj A)"
proof -
  have sformed: "rra_formed (restrict_structure (object_structure obj) A)"
    using formed restrict_structure_formed[of "object_structure obj" A]
    by (simp add: object_formed_def)
  have source: "basis_formed (rra_carrier (object_structure obj)) (object_data obj)"
    using formed by (simp add: object_formed_def)
  have data: "basis_formed (rra_carrier (object_structure obj) \<inter> A)
    (restrict_basis (rra_carrier (object_structure obj) \<inter> A) (object_data obj))"
    using restrict_basis_formed[OF source, where A="rra_carrier (object_structure obj) \<inter> A"]
    by simp
  show ?thesis using sformed data
    by (simp add: object_formed_def restrict_object_def restrict_structure_def)
qed

definition push_object ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'v) structured_object \<Rightarrow> ('b,'v) structured_object" where
  "push_object f obj =
    \<lparr>object_structure = push_structure f (object_structure obj),
     object_data = push_basis (rra_carrier (object_structure obj)) f (object_data obj)\<rparr>"

lemma push_object_formed_iff:
  assumes formed: "object_formed obj"
  shows "object_formed (push_object f obj) \<longleftrightarrow> basis_compatible f (object_data obj)"
proof -
  have sformed: "rra_formed (push_structure f (object_structure obj))"
    using formed push_structure_formed[of "object_structure obj" f]
    by (simp add: object_formed_def)
  have source: "basis_formed (rra_carrier (object_structure obj)) (object_data obj)"
    using formed by (simp add: object_formed_def)
  show ?thesis
    using sformed push_basis_formed_iff[OF source, where f=f]
    by (simp add: object_formed_def push_object_def push_structure_def)
qed

definition object_isomorphism ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'v) structured_object \<Rightarrow> ('b,'v) structured_object \<Rightarrow> bool" where
  "object_isomorphism f obj obj' \<longleftrightarrow>
    object_formed obj \<and> object_formed obj' \<and>
    rra_isomorphism f (object_structure obj) (object_structure obj') \<and>
    object_data obj' = push_basis (rra_carrier (object_structure obj)) f (object_data obj)"

lemma object_push_isomorphism:
  assumes formed: "object_formed obj" and injective: "inj_on f (rra_carrier (object_structure obj))"
  shows "object_isomorphism f obj (push_object f obj)"
proof -
  have compatible: "basis_compatible f (object_data obj)"
    by (rule injective_gluing_compatible[OF _ injective])
       (use formed in \<open>simp add: object_formed_def\<close>)
  have target: "object_formed (push_object f obj)"
    using push_object_formed_iff[OF formed, where f=f] compatible by simp
  have source: "rra_formed (object_structure obj)" using formed by (simp add: object_formed_def)
  show ?thesis
    using formed target push_structure_iso[OF source injective]
    by (simp add: object_isomorphism_def push_object_def)
qed

lemma push_object_composes:
  assumes formed: "object_formed obj"
  shows "push_object g (push_object f obj) = push_object (g \<circ> f) obj"
proof -
  have fin: "finite (rra_carrier (object_structure obj))"
    using formed by (simp add: object_formed_def rra_formed_def)
  show ?thesis
    using push_basis_composes[OF fin, where f=f and g=g and D="object_data obj"]
    by (simp add: push_object_def push_structure_composes)
qed

lemma push_object_left_inverse:
  assumes formed: "object_formed obj"
    and inverse: "\<And>a. a \<in> rra_carrier (object_structure obj) \<Longrightarrow> g (f a) = a"
  shows "push_object g (push_object f obj) = obj"
proof -
  have sf: "rra_formed (object_structure obj)"
    and bf: "basis_formed (rra_carrier (object_structure obj)) (object_data obj)"
    using formed by (auto simp: object_formed_def)
  have fin: "finite (rra_carrier (object_structure obj))"
    using sf by (simp add: rra_formed_def)
  have bs: "push_basis (f ` rra_carrier (object_structure obj)) g
      (push_basis (rra_carrier (object_structure obj)) f (object_data obj)) = object_data obj"
    by (rule push_basis_left_inverse[OF fin bf]) (use inverse in auto)
  have ss: "push_structure g (push_structure f (object_structure obj)) = object_structure obj"
    by (rule push_structure_left_inverse[where f=f and g=g, OF sf inverse])
  show ?thesis using bs ss
    by (simp add: push_object_def object_identity)
qed

lemma push_object_identity:
  assumes "object_formed obj"
  shows "push_object id obj = obj"
proof -
  have fin: "finite (rra_carrier (object_structure obj))"
    and bf: "basis_formed (rra_carrier (object_structure obj)) (object_data obj)"
    using assms by (auto simp: object_formed_def rra_formed_def)
  show ?thesis
    using push_identity[OF fin bf]
    by (simp add: push_object_def object_identity)
qed

lemma object_isomorphism_as_copy:
  "object_isomorphism f obj other \<longleftrightarrow>
    object_formed obj \<and> inj_on f (rra_carrier (object_structure obj)) \<and> other = push_object f obj"
proof
  assume "object_isomorphism f obj other"
  then show "object_formed obj \<and> inj_on f (rra_carrier (object_structure obj)) \<and> other = push_object f obj"
    by (auto simp: object_isomorphism_def rra_isomorphism_def bij_betw_def push_object_def object_identity)
next
  assume copy: "object_formed obj \<and> inj_on f (rra_carrier (object_structure obj)) \<and> other = push_object f obj"
  have "object_isomorphism f obj (push_object f obj)"
    by (rule object_push_isomorphism) (use copy in auto)
  then show "object_isomorphism f obj other" using copy by simp
qed

lemma object_isomorphism_inverse:
  assumes iso: "object_isomorphism f obj other"
  shows "object_isomorphism (inv_into (rra_carrier (object_structure obj)) f) other obj"
proof -
  let ?U = "rra_carrier (object_structure obj)"
  let ?V = "rra_carrier (object_structure other)"
  let ?g = "inv_into ?U f"
  have source: "object_formed obj" and target: "object_formed other"
    and bij: "bij_betw f ?U ?V"
    using iso by (auto simp: object_isomorphism_def rra_isomorphism_def)
  have copy: "other = push_object f obj"
    using iso by (simp add: object_isomorphism_as_copy)
  have gi: "inj_on ?g ?V"
    using bij_betw_inv_into[OF bij] by (simp add: bij_betw_def)
  have inverse: "\<And>a. a \<in> ?U \<Longrightarrow> ?g (f a) = a"
    by (rule bij_betw_inv_into_left[OF bij])
  have recovered: "push_object ?g other = obj"
    unfolding copy by (rule push_object_left_inverse[where f=f and g="?g", OF source inverse])
  show ?thesis
    using object_push_isomorphism[OF target gi] recovered by simp
qed

lemma object_isomorphism_composes:
  assumes first: "object_isomorphism f obj other" and second: "object_isomorphism g other target"
  shows "object_isomorphism (g \<circ> f) obj target"
proof -
  have source: "object_formed obj" and fc: "other = push_object f obj"
    using first by (auto simp: object_isomorphism_as_copy)
  have gc: "target = push_object g other"
    using second by (simp add: object_isomorphism_as_copy)
  have fi: "rra_isomorphism f (object_structure obj) (object_structure other)"
    and gi: "rra_isomorphism g (object_structure other) (object_structure target)"
    using first second by (auto simp: object_isomorphism_def)
  have inj: "inj_on (g \<circ> f) (rra_carrier (object_structure obj))"
    using rra_isomorphism_composes[OF fi gi] by (simp add: rra_isomorphism_def bij_betw_def)
  have tc: "target = push_object (g \<circ> f) obj"
    using fc gc push_object_composes[OF source, where f=f and g=g] by simp
  show ?thesis using source inj tc by (simp add: object_isomorphism_as_copy)
qed

section \<open>Objects with an explicit external boundary\<close>

record ('k,'a,'v) bounded_object =
  bounded_content :: "('a,'v) structured_object"
  object_boundary :: "('k \<times> 'a) set"

definition bounded_object_formed :: "('k,'a,'v) bounded_object \<Rightarrow> bool" where
  "bounded_object_formed V \<longleftrightarrow>
    object_formed (bounded_content V) \<and>
    finite (object_boundary V) \<and> single_valued (object_boundary V) \<and>
    rel_ran (object_boundary V) \<subseteq> rra_carrier (object_structure (bounded_content V))"

definition bounded_object_isomorphism ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a,'v) bounded_object \<Rightarrow> ('k,'b,'v) bounded_object \<Rightarrow> bool" where
  "bounded_object_isomorphism f V W \<longleftrightarrow>
    bounded_object_formed V \<and> object_isomorphism f (bounded_content V) (bounded_content W) \<and>
    object_boundary W = (\<lambda>(k,a). (k,f a)) ` object_boundary V"

definition bounded_objects_isomorphic ::
  "('k,'a,'v) bounded_object \<Rightarrow> ('k,'b,'v) bounded_object \<Rightarrow> bool" where
  "bounded_objects_isomorphic V W \<longleftrightarrow> (\<exists>f. bounded_object_isomorphism f V W)"

lemma bounded_object_isomorphism_keys:
  assumes "bounded_object_isomorphism f V W"
  shows "rel_dom (object_boundary V) = rel_dom (object_boundary W)"
  using assms
  by (auto simp: bounded_object_isomorphism_def rel_dom_def intro: rev_image_eqI)

lemma bounded_object_isomorphism_target:
  assumes iso: "bounded_object_isomorphism f V W"
  shows "bounded_object_formed W"
proof -
  have vf: "bounded_object_formed V" and oi: "object_isomorphism f (bounded_content V) (bounded_content W)"
    and boundary: "object_boundary W = (\<lambda>(k,a). (k,f a)) ` object_boundary V"
    using iso by (auto simp: bounded_object_isomorphism_def)
  have wf: "object_formed (bounded_content W)" using oi by (simp add: object_isomorphism_def)
  have carrier: "rra_carrier (object_structure (bounded_content W)) =
    f ` rra_carrier (object_structure (bounded_content V))"
    using oi by (simp add: object_isomorphism_as_copy push_object_def)
  show ?thesis using vf wf boundary carrier
    by (auto simp: bounded_object_formed_def single_valued_def rel_ran_def intro: rev_image_eqI; blast)
qed

definition rename_bounded_object ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('k,'a,'v) bounded_object \<Rightarrow> ('k,'b,'v) bounded_object" where
  "rename_bounded_object f V =
    \<lparr>bounded_content = push_object f (bounded_content V),
     object_boundary = (\<lambda>(k,a). (k,f a)) ` object_boundary V\<rparr>"

lemma rename_bounded_object_isomorphism:
  assumes formed: "bounded_object_formed V"
    and injective: "inj_on f (rra_carrier (object_structure (bounded_content V)))"
  shows "bounded_object_isomorphism f V (rename_bounded_object f V)"
proof -
  have source: "object_formed (bounded_content V)"
    using formed by (simp add: bounded_object_formed_def)
  show ?thesis
    using formed object_push_isomorphism[OF source injective]
    by (simp add: bounded_object_isomorphism_def rename_bounded_object_def)
qed

lemma bounded_object_isomorphism_refl:
  assumes "bounded_object_formed V"
  shows "bounded_object_isomorphism id V V"
proof -
  have source: "object_formed (bounded_content V)"
    using assms by (simp add: bounded_object_formed_def)
  have oi: "object_isomorphism id (bounded_content V) (bounded_content V)"
    using object_push_isomorphism[OF source, of id] push_object_identity[OF source] by simp
  show ?thesis using assms oi
    by (auto simp: bounded_object_isomorphism_def)
qed

lemma bounded_object_isomorphism_composes:
  assumes first: "bounded_object_isomorphism f V W" and second: "bounded_object_isomorphism g W Z"
  shows "bounded_object_isomorphism (g \<circ> f) V Z"
proof -
  have fi: "object_isomorphism f (bounded_content V) (bounded_content W)"
    and gi: "object_isomorphism g (bounded_content W) (bounded_content Z)"
    using first second by (auto simp: bounded_object_isomorphism_def)
  have oi: "object_isomorphism (g \<circ> f) (bounded_content V) (bounded_content Z)"
    by (rule object_isomorphism_composes[OF fi gi])
  show ?thesis using first second oi
    by (auto simp: bounded_object_isomorphism_def image_image intro: rev_image_eqI)
qed

lemma bounded_object_isomorphism_inverse:
  assumes iso: "bounded_object_isomorphism f V W"
  shows "bounded_object_isomorphism
    (inv_into (rra_carrier (object_structure (bounded_content V))) f) W V"
proof -
  let ?U = "rra_carrier (object_structure (bounded_content V))"
  let ?g = "inv_into ?U f"
  have vf: "bounded_object_formed V"
    and oi: "object_isomorphism f (bounded_content V) (bounded_content W)"
    and boundary: "object_boundary W = (\<lambda>(k,a). (k,f a)) ` object_boundary V"
    using iso by (auto simp: bounded_object_isomorphism_def)
  have wf: "bounded_object_formed W" by (rule bounded_object_isomorphism_target[OF iso])
  have inverse: "object_isomorphism ?g (bounded_content W) (bounded_content V)"
    by (rule object_isomorphism_inverse[OF oi])
  have fi: "inj_on f ?U" using oi by (simp add: object_isomorphism_as_copy)
  have loc: "\<And>k a. (k,a) \<in> object_boundary V \<Longrightarrow> a \<in> ?U"
    using vf by (auto simp: bounded_object_formed_def rel_ran_def)
  have fixed: "(\<lambda>(k,a). (k,?g (f a))) ` object_boundary V = object_boundary V"
  proof -
    have "(\<lambda>(k,a). (k,?g (f a))) ` object_boundary V = id ` object_boundary V"
      by (rule image_cong[OF refl])
         (use inv_into_f_f[OF fi] loc in \<open>auto\<close>)
    then show ?thesis by simp
  qed
  have recovered: "object_boundary V = (\<lambda>(k,a). (k,?g a)) ` object_boundary W"
  proof -
    have "(\<lambda>(k,a). (k,?g a)) ` object_boundary W =
      (\<lambda>(k,a). (k,?g (f a))) ` object_boundary V"
      by (simp add: boundary image_image split_def)
    then show ?thesis using fixed by simp
  qed
  show ?thesis using wf inverse recovered by (simp add: bounded_object_isomorphism_def)
qed

lemma bounded_copies_agree:
  assumes left: "bounded_object_isomorphism f V W" and right: "bounded_object_isomorphism g V Z"
  shows "bounded_objects_isomorphic W Z"
proof -
  have inverse: "bounded_object_isomorphism
    (inv_into (rra_carrier (object_structure (bounded_content V))) f) W V"
    by (rule bounded_object_isomorphism_inverse[OF left])
  have composed: "bounded_object_isomorphism
    (g \<circ> inv_into (rra_carrier (object_structure (bounded_content V))) f) W Z"
    by (rule bounded_object_isomorphism_composes[OF inverse right])
  show ?thesis using composed unfolding bounded_objects_isomorphic_def by blast
qed

text \<open>
  Boundary keys are supplied by the enclosing use. They are neither data
  attached to the reached atoms nor an additional property of those atoms.
  The isomorphism preserves primitive incidence coordinates, opaque values,
  multiplicities, and the complete boundary graph.
\<close>

end
