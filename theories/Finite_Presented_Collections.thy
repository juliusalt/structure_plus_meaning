theory Finite_Presented_Collections
  imports Ordered_Finite_Terms Factor_Presentation_Classes
begin

section \<open>Executable terms carry the generic pair, sequence and collection classes\<close>

definition finite_presents :: "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a \<Rightarrow> factor_term \<Rightarrow> bool" where
  "finite_presents f a t \<longleftrightarrow> t=decode_finite_term (f a)"

theorem finite_presents_class:
  assumes "inj_on f {a. D a}"
  shows "presentation_class (\<lambda>a t. D a \<and> finite_presents f a t) D
    (\<lambda>t. \<exists>a. D a \<and> t=decode_finite_term (f a))"
proof -
  have "inj_on (decode_finite_term \<circ> f) {a. D a}"
    using assms by (auto simp: inj_on_def)
  then show ?thesis
    using injective_presentation_class[of "decode_finite_term \<circ> f" D]
    by (simp add: finite_presents_def comp_def)
qed

definition finite_pair_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('b \<Rightarrow> finite_factor_term) \<Rightarrow> 'a\<times>'b \<Rightarrow> finite_factor_term" where
  "finite_pair_presentation f g z=Finite_Pair (f (fst z)) (g (snd z))"

lemma finite_pair_presentation_at [simp]:
  "finite_pair_presentation f g (a,b)=Finite_Pair (f a) (g b)"
  by (simp add: finite_pair_presentation_def)

lemma finite_pair_presentation_injective [intro]:
  assumes "inj f" "inj g"
  shows "inj (finite_pair_presentation f g)"
  by (rule injI) (use assms in \<open>auto simp: finite_pair_presentation_def prod_eq_iff inj_eq\<close>)

theorem finite_pair_presentation_admitted:
  "factor_pair_presents (finite_presents f) (finite_presents g) z
    (decode_finite_term (finite_pair_presentation f g z))"
  by (cases z) (simp add: finite_presents_def)

lemma finite_payload_injective [intro]: "inj Finite_Payload"
  by (rule injI) simp

fun finite_data_list :: "finite_factor_term list \<Rightarrow> finite_factor_term" where
  "finite_data_list []=Finite_Payload []"
| "finite_data_list (t#ts)=Finite_Pair t (finite_data_list ts)"

lemma decode_finite_data_list [simp]:
  "decode_finite_term (finite_data_list ts)=data_list_term (map decode_finite_term ts)"
  by (induction ts) simp_all

lemma finite_data_list_injective: "finite_data_list xs=finite_data_list ys \<longleftrightarrow> xs=ys"
  by (induction xs arbitrary: ys) (case_tac ys; auto)+

lemma finite_data_list_formed: "finite_term_formed (finite_data_list ts) \<longleftrightarrow> list_all finite_term_formed ts"
  by (induction ts) (simp_all add: octets_formed_def)

lemma map_members_injective:
  assumes members: "\<And>x y. x\<in>set xs \<Longrightarrow> f x=f y \<Longrightarrow> x=y" and same: "map f xs=map f ys"
  shows "xs=ys"
  using same members
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  obtain z zs where ys: "ys=z#zs" and head: "f x=f z" and tail: "map f xs=map f zs"
    using Cons.prems(1) by (auto simp: map_eq_Cons_conv)
  have "x=z" by (rule Cons.prems(2)) (use head in auto)
  moreover have "xs=zs" by (rule Cons.IH[OF tail]) (use Cons.prems(2) in auto)
  ultimately show ?case by (simp add: ys)
qed simp

definition finite_sequence_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a list \<Rightarrow> finite_factor_term" where
  "finite_sequence_presentation f xs=finite_data_list (map f xs)"

lemma finite_sequence_presentation_simps [simp]:
  "finite_sequence_presentation f []=Finite_Payload []"
  "finite_sequence_presentation f (x#xs)=Finite_Pair (f x) (finite_sequence_presentation f xs)"
  by (simp_all add: finite_sequence_presentation_def)

lemma finite_sequence_presentation_member_injective:
  assumes members: "\<And>x y. x\<in>set xs \<Longrightarrow> f x=f y \<Longrightarrow> x=y"
    and same: "finite_sequence_presentation f xs=finite_sequence_presentation f ys"
  shows "xs=ys"
proof (rule map_members_injective[OF members])
  show "map f xs=map f ys"
    using same by (simp add: finite_sequence_presentation_def finite_data_list_injective)
qed

lemma finite_sequence_presentation_injective [intro]:
  assumes "inj f"
  shows "inj (finite_sequence_presentation f)"
  by (rule injI) (use assms in \<open>simp add: finite_sequence_presentation_def finite_data_list_injective inj_map_eq_map\<close>)

theorem finite_sequence_presentation_admitted:
  "data_sequence_presents (finite_presents f) xs (decode_finite_term (finite_sequence_presentation f xs))"
  unfolding data_sequence_presents_def finite_sequence_presentation_def
  by (rule exI[of _ "map (decode_finite_term \<circ> f) xs"]) (simp add: finite_presents_def list_all2_conv_all_nth)

section \<open>A finite collection is presented by every distinct enumeration\<close>

theorem finite_collection_enumeration_admitted:
  assumes "distinct xs" "set xs=A"
  shows "data_collection_presents (finite_presents f) A (data_list_term (map (decode_finite_term \<circ> f) xs))"
  unfolding data_collection_presents_def
  by (rule exI[of _ xs], rule exI[of _ "map (decode_finite_term \<circ> f) xs"])
    (use assms in \<open>simp add: finite_presents_def list_all2_conv_all_nth\<close>)

definition ordered_finite_terms :: "finite_factor_term fset \<Rightarrow> finite_factor_term list" where
  "ordered_finite_terms A=map unordered_factor_term (sorted_list_of_fset (fimage Ordered_Factor_Term A))"

lemma ordered_finite_terms_set: "set (ordered_finite_terms A)=fset A"
proof -
  have "set (sorted_list_of_fset (fimage Ordered_Factor_Term A))=Ordered_Factor_Term ` fset A"
    by simp
  then show ?thesis
    by (auto simp: ordered_finite_terms_def image_iff)
qed

lemma ordered_finite_terms_distinct: "distinct (ordered_finite_terms A)"
proof -
  have "inj_on unordered_factor_term (set (sorted_list_of_fset (fimage Ordered_Factor_Term A)))"
    by (auto simp: inj_on_def)
  then show ?thesis
    by (simp add: ordered_finite_terms_def distinct_map)
qed

definition finite_collection_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a fset \<Rightarrow> finite_factor_term" where
  "finite_collection_presentation f A=finite_data_list (ordered_finite_terms (fimage f A))"

theorem finite_collection_presentation_admitted:
  assumes injective: "inj_on f (fset A)"
  shows "data_collection_presents (finite_presents f) (fset A)
    (decode_finite_term (finite_collection_presentation f A))"
proof -
  let ?ts="ordered_finite_terms (fimage f A)"
  let ?xs="map (the_inv_into (fset A) f) ?ts"
  have terms: "set ?ts=f ` fset A" by (simp add: ordered_finite_terms_set fimage.rep_eq)
  have recovered: "\<And>t. t\<in>set ?ts \<Longrightarrow> f (the_inv_into (fset A) f t)=t"
    using terms f_the_inv_into_f[OF injective] by auto
  have inverse_inj: "inj_on (the_inv_into (fset A) f) (set ?ts)"
    using terms inj_on_the_inv_into[OF injective] by simp
  have distinct: "distinct ?xs"
    using ordered_finite_terms_distinct inverse_inj by (simp add: distinct_map)
  have enumerated: "set ?xs=fset A"
    by (simp only: set_map terms the_inv_into_onto[OF injective])
  have mapped: "map (decode_finite_term \<circ> f) ?xs=map decode_finite_term ?ts"
    using recovered by (simp add: map_eq_conv)
  have "data_collection_presents (finite_presents f) (fset A) (data_list_term (map decode_finite_term ?ts))"
    using finite_collection_enumeration_admitted[OF distinct enumerated, of f] by (simp only: mapped)
  then show ?thesis by (simp add: finite_collection_presentation_def)
qed

lemma fimage_injective_on_left:
  assumes members: "\<And>x y. x |\<in>| A \<Longrightarrow> g x=g y \<longleftrightarrow> x=y"
  shows "fimage g A=fimage g B \<longleftrightarrow> A=B"
proof
  assume same: "fimage g A=fimage g B"
  show "A=B"
  proof (rule fset_eqI, rule iffI)
    fix x assume x: "x |\<in>| A"
    have "g x |\<in>| fimage g B" using same x by (metis fimageI)
    then obtain y where y: "y |\<in>| B" "g x=g y" by (auto simp: fimage.rep_eq)
    then show "x |\<in>| B" using members[OF x] by simp
  next
    fix y assume y: "y |\<in>| B"
    have "g y |\<in>| fimage g A" using same y by (metis fimageI)
    then obtain x where x: "x |\<in>| A" "g x=g y" by (auto simp: fimage.rep_eq)
    then show "y |\<in>| A" using members[OF x(1)] by simp
  qed
qed simp

theorem finite_collection_presentation_exact_on:
  assumes members: "\<And>x y. x |\<in>| A \<Longrightarrow> f x=f y \<longleftrightarrow> x=y"
  shows "finite_collection_presentation f A=finite_collection_presentation f B \<longleftrightarrow> A=B"
proof
  assume same: "finite_collection_presentation f A=finite_collection_presentation f B"
  have terms: "ordered_finite_terms (fimage f A)=ordered_finite_terms (fimage f B)"
    using same by (simp add: finite_collection_presentation_def finite_data_list_injective)
  have "fimage f A=fimage f B"
    using arg_cong[OF terms, of set] by (simp only: ordered_finite_terms_set fset_inject)
  then show "A=B" by (simp only: fimage_injective_on_left[OF members])
qed simp

corollary finite_collection_presentation_injective [intro]:
  assumes "inj f"
  shows "inj (finite_collection_presentation f)"
proof (rule injI)
  fix A B
  assume same: "finite_collection_presentation f A=finite_collection_presentation f B"
  have members: "\<And>x y. x |\<in>| A \<Longrightarrow> f x=f y \<longleftrightarrow> x=y" using assms by (simp add: inj_eq)
  show "A=B" using same by (simp only: finite_collection_presentation_exact_on[OF members])
qed

section \<open>An optional value is the sequence of its present elements\<close>

definition finite_option_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a option \<Rightarrow> finite_factor_term" where
  "finite_option_presentation f x=finite_sequence_presentation f (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"

lemma finite_option_presentation_simps [simp]:
  "finite_option_presentation f None=Finite_Payload []"
  "finite_option_presentation f (Some a)=Finite_Pair (f a) (Finite_Payload [])"
  by (simp_all add: finite_option_presentation_def)

lemma finite_option_presentation_injective [intro]:
  assumes "inj f"
  shows "inj (finite_option_presentation f)"
proof (rule injI)
  fix x y assume "finite_option_presentation f x=finite_option_presentation f y"
  then show "x=y" using assms by (cases x; cases y) (auto dest: injD)
qed

theorem finite_option_presentation_admitted:
  "data_sequence_presents (finite_presents f) (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])
    (decode_finite_term (finite_option_presentation f x))"
  unfolding finite_option_presentation_def by (rule finite_sequence_presentation_admitted)

text \<open>
  Each executable presentation decodes into the generic pair, sequence or
  collection class of the presented components, and it is injective whenever
  its component presentations are. A finite collection admits every distinct
  enumeration of its members; the executable presentation chooses the
  enumeration ordered by the complete term key, so equal presentations identify
  equal collections. Factor_Encoding_Order_Audit shows that this chosen order
  stays observable to native programs over the presented term: identification
  of collections is not a claim of semantic invariance under enumeration. An
  optional value is presented as the sequence of its present elements.
\<close>

end
