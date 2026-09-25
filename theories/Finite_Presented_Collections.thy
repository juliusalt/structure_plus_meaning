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

lemma decode_finite_sequence_presentation:
  "decode_finite_term (finite_sequence_presentation f xs)=data_list_term (map (decode_finite_term \<circ> f) xs)"
  by (simp add: finite_sequence_presentation_def)

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

section \<open>A partial presentation presents its domain exactly\<close>

text \<open>
  A presentation in context is partial: a value outside its premise has no presentation, and a report
  carrying one is not a presentation of it. A partial presentation presents a domain exactly when every
  value of the domain has a presentation and distinct values have distinct presentations. The generic
  presentations compose as the total ones do: a pair presents the product of its parts' domains, a
  sequence the lists over its element's domain, an optional value the options over it and a collection
  the finite sets inside it; a total presentation is partial nowhere.
\<close>

definition finite_presented_on :: "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "finite_presented_on f A \<longleftrightarrow> (\<forall>x\<in>A. f x\<noteq>None) \<and> inj_on f A"

lemma finite_presented_onI:
  assumes some: "\<And>x. x\<in>A \<Longrightarrow> f x\<noteq>None"
    and exact: "\<And>x y t. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> f x=Some t \<Longrightarrow> f y=Some t \<Longrightarrow> x=y"
  shows "finite_presented_on f A"
  unfolding finite_presented_on_def
proof (intro conjI ballI inj_onI)
  fix x assume "x\<in>A" then show "f x\<noteq>None" by (rule some)
next
  fix x y assume x: "x\<in>A" and y: "y\<in>A" and same: "f x=f y"
  obtain t where t: "f x=Some t" using some[OF x] by blast
  show "x=y" by (rule exact[OF x y t]) (use same t in simp)
qed

lemma finite_presented_on_some:
  assumes "finite_presented_on f A" "x\<in>A"
  obtains t where "f x=Some t"
  using assms by (auto simp: finite_presented_on_def)

lemma finite_presented_on_eq:
  assumes presented: "finite_presented_on f A" and x: "x\<in>A" and y: "y\<in>A" and same: "f x=f y"
  shows "x=y"
proof -
  have "inj_on f A" using presented by (simp add: finite_presented_on_def)
  then show ?thesis by (rule inj_onD[OF _ same x y])
qed

lemma finite_presented_on_mono:
  assumes presented: "finite_presented_on f A" and inside: "B\<subseteq>A"
  shows "finite_presented_on f B"
proof -
  have injective: "inj_on f A" and some: "\<forall>x\<in>A. f x\<noteq>None"
    using presented by (simp_all add: finite_presented_on_def)
  have "inj_on f B" by (rule inj_on_subset[OF injective inside])
  then show ?thesis using some inside by (auto simp: finite_presented_on_def)
qed

lemma finite_presented_total [intro]:
  assumes injective: "inj g"
  shows "finite_presented_on (Some \<circ> g) A"
proof (rule finite_presented_onI)
  fix x show "(Some \<circ> g) x\<noteq>None" by simp
next
  fix x y t assume "(Some \<circ> g) x=Some t" "(Some \<circ> g) y=Some t"
  then have "g x=g y" by simp
  then show "x=y" by (rule injD[OF injective])
qed

lemma finite_presented_on_comp:
  assumes presented: "finite_presented_on f A" and injective: "inj_on h B" and inside: "h ` B\<subseteq>A"
  shows "finite_presented_on (f \<circ> h) B"
proof (rule finite_presented_onI)
  fix x assume "x\<in>B"
  then have "h x\<in>A" using inside by blast
  then show "(f \<circ> h) x\<noteq>None" using presented by (auto simp: finite_presented_on_def)
next
  fix x y t assume x: "x\<in>B" and y: "y\<in>B" and fx: "(f \<circ> h) x=Some t" and fy: "(f \<circ> h) y=Some t"
  have "h x=h y"
    by (rule finite_presented_on_eq[OF presented]) (use x y fx fy inside in \<open>auto simp: image_subset_iff\<close>)
  then show "x=y" by (rule inj_onD[OF injective _ x y])
qed

definition finite_partial_pair ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> ('b \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a\<times>'b \<Rightarrow>
      finite_factor_term option" where
  "finite_partial_pair f g z=(case f (fst z) of None \<Rightarrow> None | Some x \<Rightarrow> map_option (Finite_Pair x) (g (snd z)))"

lemma finite_partial_pair_presented [intro]:
  assumes first: "finite_presented_on f A" and second: "finite_presented_on g B"
  shows "finite_presented_on (finite_partial_pair f g) (A\<times>B)"
proof (rule finite_presented_onI)
  fix z assume "z\<in>A\<times>B"
  then obtain a b where z: "z=(a,b)" "a\<in>A" "b\<in>B" by blast
  obtain x where x: "f a=Some x" by (rule finite_presented_on_some[OF first z(2)])
  obtain y where y: "g b=Some y" by (rule finite_presented_on_some[OF second z(3)])
  show "finite_partial_pair f g z\<noteq>None" by (simp add: finite_partial_pair_def z(1) x y)
next
  fix z w t assume z: "z\<in>A\<times>B" and w: "w\<in>A\<times>B"
    and fz: "finite_partial_pair f g z=Some t" and fw: "finite_partial_pair f g w=Some t"
  obtain a b where Z: "z=(a,b)" "a\<in>A" "b\<in>B" using z by blast
  obtain a' b' where W: "w=(a',b')" "a'\<in>A" "b'\<in>B" using w by blast
  obtain x y where x: "f a=Some x" and y: "g b=Some y" and t: "t=Finite_Pair x y"
    using fz by (auto simp: finite_partial_pair_def Z(1) split: option.splits)
  obtain x' y' where x': "f a'=Some x'" and y': "g b'=Some y'" and t': "t=Finite_Pair x' y'"
    using fw by (auto simp: finite_partial_pair_def W(1) split: option.splits)
  have "a=a'" by (rule finite_presented_on_eq[OF first Z(2) W(2)]) (use x x' t t' in simp)
  moreover have "b=b'" by (rule finite_presented_on_eq[OF second Z(3) W(3)]) (use y y' t t' in simp)
  ultimately show "z=w" by (simp add: Z(1) W(1))
qed

definition finite_partial_sequence ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a list \<Rightarrow> finite_factor_term option" where
  "finite_partial_sequence f xs=map_option finite_data_list (those (map f xs))"

lemma those_map_present:
  assumes "\<And>x. x\<in>set xs \<Longrightarrow> f x\<noteq>None"
  shows "those (map f xs)=Some (map (the \<circ> f) xs)"
  using assms by (induction xs) (auto split: option.splits)

lemma finite_partial_sequence_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_sequence f) (lists A)"
proof (rule finite_presented_onI)
  fix xs assume "xs\<in>lists A"
  then have "\<And>x. x\<in>set xs \<Longrightarrow> f x\<noteq>None" using presented by (auto simp: finite_presented_on_def)
  then show "finite_partial_sequence f xs\<noteq>None" by (simp add: finite_partial_sequence_def those_map_present)
next
  fix xs ys t assume xs: "xs\<in>lists A" and ys: "ys\<in>lists A"
    and first: "finite_partial_sequence f xs=Some t" and second: "finite_partial_sequence f ys=Some t"
  have some: "\<And>x. x\<in>set xs \<union> set ys \<Longrightarrow> f x\<noteq>None"
    using presented xs ys by (auto simp: finite_presented_on_def)
  have sx: "those (map f xs)=Some (map (the \<circ> f) xs)" by (rule those_map_present) (use some in blast)
  have sy: "those (map f ys)=Some (map (the \<circ> f) ys)" by (rule those_map_present) (use some in blast)
  have "finite_data_list (map (the \<circ> f) xs)=finite_data_list (map (the \<circ> f) ys)"
    using first second by (simp add: finite_partial_sequence_def sx sy)
  then have maps: "map (the \<circ> f) xs=map (the \<circ> f) ys" by (simp add: finite_data_list_injective)
  have "inj_on (the \<circ> f) (set xs \<union> set ys)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>set xs \<union> set ys" and y: "y\<in>set xs \<union> set ys" and same: "(the \<circ> f) x=(the \<circ> f) y"
    have fxy: "f x=f y" using same some[OF x] some[OF y] by (cases "f x"; cases "f y") auto
    show "x=y" by (rule finite_presented_on_eq[OF presented _ _ fxy]) (use x y xs ys in auto)
  qed
  then show "xs=ys" using maps by (simp add: inj_on_map_eq_map)
qed

definition finite_partial_option ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a option \<Rightarrow> finite_factor_term option" where
  "finite_partial_option f x=finite_partial_sequence f (case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"

lemma finite_partial_option_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_option f) {x. set_option x\<subseteq>A}"
proof -
  have eq: "finite_partial_option f=finite_partial_sequence f \<circ> (\<lambda>x. case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a])"
    by (simp add: fun_eq_iff finite_partial_option_def)
  show ?thesis unfolding eq
    by (rule finite_presented_on_comp[OF finite_partial_sequence_presented[OF presented]])
      (auto simp: inj_on_def split: option.splits)
qed

definition finite_partial_collection ::
    "('a \<Rightarrow> finite_factor_term option) \<Rightarrow> 'a fset \<Rightarrow> finite_factor_term option" where
  "finite_partial_collection f X=(if fBall X (\<lambda>x. f x\<noteq>None)
    then Some (finite_collection_presentation (the \<circ> f) X) else None)"

lemma finite_presented_on_the:
  assumes presented: "finite_presented_on f A"
  shows "inj_on (the \<circ> f) A"
proof (rule inj_onI)
  fix x y assume x: "x\<in>A" and y: "y\<in>A" and same: "(the \<circ> f) x=(the \<circ> f) y"
  have "f x\<noteq>None" "f y\<noteq>None" using presented x y by (auto simp: finite_presented_on_def)
  then have "f x=f y" using same by (cases "f x"; cases "f y") auto
  then show "x=y" by (rule finite_presented_on_eq[OF presented x y])
qed

lemma finite_partial_collection_presented [intro]:
  assumes presented: "finite_presented_on f A"
  shows "finite_presented_on (finite_partial_collection f) {X. fset X\<subseteq>A}"
proof (rule finite_presented_onI)
  fix X assume X: "X\<in>{X. fset X\<subseteq>A}"
  have some: "\<forall>x\<in>A. f x\<noteq>None" using presented by (simp add: finite_presented_on_def)
  have inside: "fset X\<subseteq>A" using X by simp
  have "fBall X (\<lambda>x. f x\<noteq>None)"
  proof (rule fBallI)
    fix x assume "x\<in>fset X"
    then have "x\<in>A" using inside by (rule rev_subsetD)
    then show "f x\<noteq>None" by (rule bspec[OF some])
  qed
  then show "finite_partial_collection f X\<noteq>None" by (simp add: finite_partial_collection_def)
next
  fix X Y t assume X: "X\<in>{X. fset X\<subseteq>A}" and Y: "Y\<in>{X. fset X\<subseteq>A}"
    and first: "finite_partial_collection f X=Some t" and second: "finite_partial_collection f Y=Some t"
  have tX: "finite_collection_presentation (the \<circ> f) X=t"
    using first by (simp add: finite_partial_collection_def split: if_splits)
  have tY: "finite_collection_presentation (the \<circ> f) Y=t"
    using second by (simp add: finite_partial_collection_def split: if_splits)
  have "finite_data_list (ordered_finite_terms (fimage (the \<circ> f) X))=
      finite_data_list (ordered_finite_terms (fimage (the \<circ> f) Y))"
    using tX tY by (simp only: finite_collection_presentation_def)
  then have terms: "ordered_finite_terms (fimage (the \<circ> f) X)=ordered_finite_terms (fimage (the \<circ> f) Y)"
    by (simp only: finite_data_list_injective)
  have images: "(the \<circ> f) ` fset X=(the \<circ> f) ` fset Y"
    using arg_cong[OF terms, of set] by (simp add: ordered_finite_terms_set fimage.rep_eq)
  have "fset X=fset Y"
    by (rule inj_on_image_eq_iff[THEN iffD1, OF finite_presented_on_the[OF presented] _ _ images]) (use X Y in simp_all)
  then show "X=Y" by (simp add: fset_inject)
qed

end
