theory Bootstrap_Relations
  imports Main
begin

section \<open>Finite extensional relations\<close>

text \<open>
  These definitions are mathematical conveniences only.  They introduce no
  stored map object and no procedural reading.  Whenever a relation is used as
  a map, its exact graph is the fact being supplied.
\<close>

definition rel_dom :: "('a \<times> 'b) set \<Rightarrow> 'a set" where
  "rel_dom R = {x. \<exists>y. (x,y) \<in> R}"

definition rel_ran :: "('a \<times> 'b) set \<Rightarrow> 'b set" where
  "rel_ran R = {y. \<exists>x. (x,y) \<in> R}"

lemma rel_dom_empty [simp]: "rel_dom {} = {}"
  by (simp add: rel_dom_def)

lemma rel_ran_empty [simp]: "rel_ran {} = {}"
  by (simp add: rel_ran_def)

lemma rel_dom_union: "rel_dom (R \<union> S) = rel_dom R \<union> rel_dom S"
  by (auto simp: rel_dom_def)

lemma rel_ran_union: "rel_ran (R \<union> S) = rel_ran R \<union> rel_ran S"
  by (auto simp: rel_ran_def)

lemma rel_domI [intro]:
  "(x,y) \<in> R \<Longrightarrow> x \<in> rel_dom R"
  unfolding rel_dom_def by blast

lemma rel_ranI [intro]:
  "(x,y) \<in> R \<Longrightarrow> y \<in> rel_ran R"
  unfolding rel_ran_def by blast

lemma rel_dom_image:
  "rel_dom R = fst ` R"
  by (auto simp: rel_dom_def intro: rev_image_eqI)

lemma rel_ran_image:
  "rel_ran R = snd ` R"
  by (auto simp: rel_ran_def intro: rev_image_eqI)

lemma finite_rel_dom:
  assumes "finite R"
  shows "finite (rel_dom R)"
  using assms by (simp add: rel_dom_image)

lemma finite_rel_ran:
  assumes "finite R"
  shows "finite (rel_ran R)"
  using assms by (simp add: rel_ran_image)

lemma rel_dom_eq_empty [simp]:
  "rel_dom R = {} \<longleftrightarrow> R = {}"
  by (auto simp: rel_dom_def)

definition single_valued :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "single_valued R \<longleftrightarrow> (\<forall>x y z. (x,y) \<in> R \<longrightarrow> (x,z) \<in> R \<longrightarrow> y = z)"

lemma single_valued_outputs:
  assumes "single_valued R" "(x,y) \<in> R" "(x,z) \<in> R"
  shows "y = z"
  using assms by (auto simp: single_valued_def)

definition map_relation_values ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('k \<times> 'a) set \<Rightarrow> ('k \<times> 'b) set" where
  "map_relation_values f R = (\<lambda>(k,v). (k,f v)) ` R"

lemma map_relation_values_member [simp]:
  "(k,w) \<in> map_relation_values f R \<longleftrightarrow> (\<exists>v. (k,v) \<in> R \<and> w=f v)"
  by (auto simp: map_relation_values_def)

lemma map_relation_values_domain [simp]:
  "rel_dom (map_relation_values f R) = rel_dom R"
  by (auto simp: rel_dom_def)

lemma map_relation_values_keys [simp]:
  "fst ` map_relation_values f R = fst ` R"
  by (simp only: rel_dom_image[symmetric] map_relation_values_domain)

lemma map_relation_values_finite [simp]:
  "finite R \<Longrightarrow> finite (map_relation_values f R)"
  by (simp add: map_relation_values_def)

lemma map_relation_values_functional:
  assumes "inj f"
  shows "single_valued (map_relation_values f R) \<longleftrightarrow> single_valued R"
  using assms by (auto simp: single_valued_def inj_def; blast)

lemma map_relation_values_injective:
  assumes "inj f"
  shows "map_relation_values f R = map_relation_values f S \<longleftrightarrow> R = S"
proof -
  have injective: "inj (\<lambda>(k,v). (k,f v))"
    using assms by (auto simp: inj_def)
  show ?thesis
    using inj_image_eq_iff[OF injective, of R S]
    by (simp add: map_relation_values_def)
qed

lemma map_relation_values_inverse:
  assumes "\<And>k v. (k,v) \<in> R \<Longrightarrow> g (f v) = v"
  shows "map_relation_values g (map_relation_values f R) = R"
  using assms by (auto; metis)

lemma map_relation_values_join:
  "map_relation_values f (R O S) = R O map_relation_values f S"
  by (auto simp: relcomp_unfold; blast)

lemma complete_socket_reading_origin:
  assumes sv: "single_valued Q" and domain: "rel_dom Q = rel_dom M"
    and complete: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> Q \<and> reads a x)"
    and member: "(s,x) \<in> Q"
  shows "\<exists>a. (s,a) \<in> M \<and> reads a x"
proof -
  have key: "s \<in> rel_dom M" using rel_domI[OF member] domain by simp
  obtain a where field: "(s,a) \<in> M" using key by (auto simp: rel_dom_def)
  obtain y where recovered: "(s,y) \<in> Q" "reads a y" using complete field by blast
  have same: "x=y" by (rule single_valued_outputs[OF sv member recovered(1)])
  show ?thesis using field recovered(2) same by blast
qed

lemma complete_socket_reading_unique:
  assumes qsv: "single_valued Q" and qdom: "rel_dom Q = rel_dom M"
    and qread: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> Q \<and> reads a x)"
    and wsv: "single_valued W" and wdom: "rel_dom W = rel_dom M"
    and wread: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> W \<and> reads a x)"
    and unique: "\<And>a x y. reads a x \<Longrightarrow> reads a y \<Longrightarrow> x = y"
  shows "Q = W"
proof -
  have compare: "\<And>A B. single_valued A \<Longrightarrow> rel_dom A = rel_dom M \<Longrightarrow>
    (\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> A \<and> reads a x)) \<Longrightarrow>
    (\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> B \<and> reads a x)) \<Longrightarrow> A \<subseteq> B"
  proof -
    fix A B assume sv: "single_valued A" and domain: "rel_dom A = rel_dom M"
      and left: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> A \<and> reads a x)"
      and right: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>x. (s,x) \<in> B \<and> reads a x)"
    show "A \<subseteq> B"
    proof
      fix entry assume member: "entry \<in> A"
      obtain s x where shape: "entry = (s,x)" by (cases entry) auto
      have entry: "(s,x) \<in> A" using member shape by simp
      have key: "s \<in> rel_dom M" using rel_domI[OF entry] domain by simp
      obtain a where field: "(s,a) \<in> M" using key by (auto simp: rel_dom_def)
      obtain y where first: "(s,y) \<in> A" "reads a y" using left field by blast
      obtain z where second: "(s,z) \<in> B" "reads a z" using right field by blast
      have xy: "x = y" by (rule single_valued_outputs[OF sv entry first(1)])
      have yz: "y = z" by (rule unique[OF first(2) second(2)])
      show "entry \<in> B" using shape xy yz second(1) by simp
    qed
  qed
  show ?thesis using compare[OF qsv qdom qread wread] compare[OF wsv wdom wread qread] by blast
qed

definition total_on :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "total_on A R \<longleftrightarrow> rel_dom R = A"

definition graph_map :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) set" where
  "graph_map A f = {(x,f x) |x. x \<in> A}"

definition rel_value :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "rel_value R x = (THE y. (x,y) \<in> R)"

definition exact_map :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "exact_map A B R \<longleftrightarrow>
     finite A \<and> finite B \<and> finite R \<and>
     single_valued R \<and> rel_dom R = A \<and> rel_ran R = B"

lemma single_valued_union_iff:
  assumes "single_valued R" "single_valued S"
  shows "single_valued (R \<union> S) \<longleftrightarrow>
    (\<forall>x y z. (x,y) \<in> R \<longrightarrow> (x,z) \<in> S \<longrightarrow> y = z)"
  using assms by (auto simp: single_valued_def; blast)

lemma single_valued_fibre:
  assumes "single_valued R" "(x,y) \<in> R"
  shows "{z. (x,z) \<in> R} = {y}"
  using assms by (auto simp: single_valued_def)

lemma single_valued_zip:
  assumes "distinct xs"
  shows "single_valued (set (zip xs ys))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by (simp add: single_valued_def)
next
  case (Cons x xs)
  then show ?case
    by (cases ys) (auto simp: single_valued_def dest: set_zip_leftD)
qed

lemma graph_map_member:
  "(x,y) \<in> graph_map A f \<longleftrightarrow> x \<in> A \<and> y=f x"
  by (auto simp: graph_map_def)

lemma graph_map_finite:
  assumes "finite A"
  shows "finite (graph_map A f)"
proof -
  have "graph_map A f = (\<lambda>x. (x,f x)) ` A" by (auto simp: graph_map_def)
  then show ?thesis using assms by simp
qed

lemma graph_map_single_valued:
  "single_valued (graph_map A f)"
  by (auto simp: single_valued_def graph_map_def)

lemma graph_map_empty [simp]: "graph_map {} f = {}"
  by (simp add: graph_map_def)

lemma graph_map_insert [simp]:
  "graph_map (insert x A) f = insert (x,f x) (graph_map A f)"
  by (auto simp: graph_map_def)

lemma graph_map_dom:
  "rel_dom (graph_map A f) = A"
  by (auto simp: rel_dom_def graph_map_def)

lemma graph_map_ran:
  "rel_ran (graph_map A f) = f ` A"
  by (auto simp: rel_ran_def graph_map_def)

lemma rel_value_graph_map:
  assumes "x \<in> A"
  shows "rel_value (graph_map A f) x = f x"
  using assms by (simp add: rel_value_def graph_map_def)

lemma rel_value_eq:
  assumes "single_valued R" "(x,y) \<in> R"
  shows "rel_value R x = y"
  unfolding rel_value_def
  by (rule the_equality) (use assms in \<open>auto simp: single_valued_def\<close>)

lemma relation_join_functional:
  assumes "single_valued R" "single_valued S"
  shows "single_valued (R O S)"
  using assms by (auto simp: single_valued_def; blast)

lemma relation_join_domain:
  assumes "rel_ran R \<subseteq> rel_dom S"
  shows "rel_dom (R O S) = rel_dom R"
  using assms by (auto simp: rel_dom_def rel_ran_def; blast)

lemma relation_join_value:
  assumes rsv: "single_valued R" and ssv: "single_valued S"
    and covered: "rel_ran R \<subseteq> rel_dom S" and link: "(s,m) \<in> R"
  shows "(m,rel_value (R O S) s) \<in> S"
proof -
  have key: "m \<in> rel_dom S" using covered rel_ranI[OF link] by blast
  obtain q where row: "(m,q) \<in> S" using key by (auto simp: rel_dom_def)
  have joined: "(s,q) \<in> R O S" using link row by blast
  have sv: "single_valued (R O S)" by (rule relation_join_functional[OF rsv ssv])
  show ?thesis using row rel_value_eq[OF sv joined] by simp
qed

lemma relation_join_recovers:
  fixes Q :: "('s \<times> 'q) set" and J :: "('n \<times> 'q) set" and R :: "('s \<times> 'n) set"
  assumes qsv: "single_valued Q" and jsv: "single_valued J"
    and domain: "rel_dom Q = rel_dom R"
    and children: "\<And>s m. (s,m) \<in> R \<Longrightarrow> (m,rel_value Q s) \<in> J"
  shows "Q = R O J"
proof (rule set_eqI)
  fix x :: "'s \<times> 'q"
  obtain s q where shape: "x=(s,q)" by (cases x) auto
  show "x \<in> Q \<longleftrightarrow> x \<in> R O J"
  proof
    assume member: "x \<in> Q"
    have row: "(s,q) \<in> Q" using member shape by simp
    have key: "s \<in> rel_dom R" using rel_domI[OF row] domain by simp
    obtain m where link: "(s,m) \<in> R" using key by (auto simp: rel_dom_def)
    have rv: "rel_value Q s=q" by (rule rel_value_eq[OF qsv row])
    show "x \<in> R O J" using link children[OF link] shape rv by blast
  next
    assume member: "x \<in> R O J"
    obtain m where link: "(s,m) \<in> R" and child: "(m,q) \<in> J"
      using member shape by auto
    have key: "s \<in> rel_dom Q" using rel_domI[OF link] domain by simp
    obtain v where row: "(s,v) \<in> Q" using key by (auto simp: rel_dom_def)
    have rv: "rel_value Q s=v" by (rule rel_value_eq[OF qsv row])
    have same: "q=rel_value Q s"
      by (rule single_valued_outputs[OF jsv child children[OF link]])
    show "x \<in> Q" using row same rv shape by simp
  qed
qed

lemma single_valued_graph:
  assumes "single_valued R"
  shows "R = graph_map (rel_dom R) (rel_value R)"
  using rel_value_eq[OF assms]
  by (auto simp: graph_map_def rel_dom_def)

lemma finite_single_valued:
  fixes R :: "('a \<times> 'b) set"
  assumes "finite (rel_dom R)" "single_valued R"
  shows "finite R"
proof -
  have graph: "R = (\<lambda>x. (x,rel_value R x)) ` rel_dom R"
    using single_valued_graph[OF assms(2)] by (auto simp: graph_map_def)
  show ?thesis by (subst graph) (rule finite_imageI[OF assms(1)])
qed

lemma exact_map_value:
  assumes "exact_map A B R" "x \<in> A"
  shows "(x, rel_value R x) \<in> R"
proof -
  from assms have "x \<in> rel_dom R"
    by (simp add: exact_map_def)
  then obtain y where xy: "(x,y) \<in> R"
    by (auto simp: rel_dom_def)
  from assms have sv: "single_valued R"
    by (simp add: exact_map_def)
  have "(THE z. (x,z) \<in> R) = y"
    by (rule the_equality) (use xy sv in \<open>auto simp: single_valued_def\<close>)
  with xy show ?thesis
    by (simp add: rel_value_def)
qed

lemma exact_map_value_in_ran:
  assumes "exact_map A B R" "x \<in> A"
  shows "rel_value R x \<in> B"
  using exact_map_value[OF assms] assms
  by (auto simp: exact_map_def rel_ran_def)

lemma exact_map_surjective:
  assumes "exact_map A B R" "y \<in> B"
  shows "\<exists>x \<in> A. (x,y) \<in> R"
  using assms unfolding exact_map_def rel_dom_def rel_ran_def by blast

lemma exact_map_value_image:
  assumes "exact_map A B R"
  shows "rel_value R ` A = B"
proof
  show "rel_value R ` A \<subseteq> B"
    using exact_map_value_in_ran[OF assms] by blast
  show "B \<subseteq> rel_value R ` A"
  proof
    fix y assume "y \<in> B"
    then obtain x where "x \<in> A" "(x,y) \<in> R"
      using exact_map_surjective[OF assms] by blast
    moreover have "single_valued R"
      using assms by (simp add: exact_map_def)
    ultimately show "y \<in> rel_value R ` A"
      using rel_value_eq[of R x y] by blast
  qed
qed

lemma graph_map_exact:
  assumes "finite A"
  shows "exact_map A (f ` A) (graph_map A f)"
proof -
  have "graph_map A f = (\<lambda>x. (x,f x)) ` A"
    by (auto simp: graph_map_def)
  with assms have "finite (graph_map A f)" by simp
  with assms show ?thesis
    by (simp add: exact_map_def graph_map_single_valued graph_map_dom graph_map_ran)
qed

definition relation_image ::
  "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('b \<times> 'b) set" where
  "relation_image f R =
     {(rel_value f x, rel_value f y) |x y. (x,y) \<in> R}"

definition ternary_image ::
  "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'a \<times> 'a) set \<Rightarrow> ('b \<times> 'b \<times> 'b) set" where
  "ternary_image f R =
     {(rel_value f r, rel_value f p, rel_value f x) |r p x.
        (r,p,x) \<in> R}"

lemma pair_image_cong:
  assumes "R \<subseteq> U \<times> U" "\<And>a. a \<in> U \<Longrightarrow> f a = g a"
  shows "(\<lambda>(a,b). (f a,f b)) ` R = (\<lambda>(a,b). (g a,g b)) ` R"
  by (rule image_cong[OF refl]) (use assms in auto)

lemma pair_image_domain:
  "rel_dom ((\<lambda>(a,b). (f a,g b)) ` R) = f ` rel_dom R"
  by (auto simp: rel_dom_def intro: rev_image_eqI)

lemma pair_image_range:
  "rel_ran ((\<lambda>(a,b). (f a,g b)) ` R) = g ` rel_ran R"
  by (auto simp: rel_ran_def intro: rev_image_eqI)

lemma single_valued_pair_image:
  assumes "single_valued R" "inj_on f (rel_dom R)"
  shows "single_valued ((\<lambda>(a,b). (f a,g b)) ` R)"
  using assms by (auto simp: single_valued_def inj_on_def rel_dom_def; blast)

lemma key_image_member:
  "(y,v) \<in> map_prod f id ` R \<longleftrightarrow> (\<exists>x. (x,v) \<in> R \<and> y=f x)"
  by (auto simp: map_prod_def)

lemma pair_image_snd_injective:
  fixes R :: "('a \<times> 'b) set" and f :: "'a \<Rightarrow> 'c" and g :: "'b \<Rightarrow> 'd"
  assumes source: "inj_on snd R" and target: "inj_on g (rel_ran R)"
  shows "inj_on snd ((\<lambda>(a,b). (f a,g b)) ` R)"
proof (rule inj_onI)
  fix x y :: "'c \<times> 'd"
  assume xm: "x \<in> (\<lambda>(a,b). (f a,g b)) ` R"
    and ym: "y \<in> (\<lambda>(a,b). (f a,g b)) ` R" and eq: "snd x = snd y"
  obtain a b where ab: "(a,b) \<in> R" and xp: "x = (f a,g b)" using xm by auto
  obtain c d where cd: "(c,d) \<in> R" and yp: "y = (f c,g d)" using ym by auto
  have br: "b \<in> rel_ran R" and dr: "d \<in> rel_ran R" using ab cd by (auto simp: rel_ran_def)
  have images: "g b = g d" using eq xp yp by simp
  have same: "b = d" by (rule inj_onD[OF target images br dr])
  have pairs: "(a,b) = (c,d)" by (rule inj_onD[OF source _ ab cd]) (use same in simp)
  show "x = y" using pairs xp yp by simp
qed

section \<open>Two projections of one identified socket graph\<close>

definition socket_sum :: "('s \<times> 'a) set \<Rightarrow> ('s \<times> 'b) set \<Rightarrow> ('s \<times> ('a + 'b)) set" where
  "socket_sum Q W = (\<lambda>(s,x). (s,Inl x)) ` Q \<union> (\<lambda>(s,x). (s,Inr x)) ` W"

lemma socket_sum_members [simp]:
  fixes Q :: "('s \<times> 'a) set" and W :: "('s \<times> 'b) set"
  shows "(s,Inl x) \<in> socket_sum Q W \<longleftrightarrow> (s,x) \<in> Q"
    "(s,Inr y) \<in> socket_sum Q W \<longleftrightarrow> (s,y) \<in> W"
  by (auto simp: socket_sum_def)

lemma socket_sum_domain [simp]:
  "rel_dom (socket_sum Q W) = rel_dom Q \<union> rel_dom W"
  by (auto simp: socket_sum_def rel_dom_def)

lemma socket_sum_range:
  "rel_ran (socket_sum Q C) = Inl ` rel_ran Q \<union> Inr ` rel_ran C"
  by (auto simp: socket_sum_def rel_ran_def intro: rev_image_eqI)

lemma socket_sum_finite [simp]:
  fixes Q :: "('s \<times> 'a) set" and W :: "('s \<times> 'b) set"
  shows "finite (socket_sum Q W) \<longleftrightarrow> finite Q \<and> finite W"
proof -
  have left: "inj_on (\<lambda>(s,x). (s,Inl x :: 'a + 'b)) Q"
    and right: "inj_on (\<lambda>(s,x). (s,Inr x :: 'a + 'b)) W"
    by (auto simp: inj_on_def)
  show ?thesis
    by (simp only: socket_sum_def finite_Un finite_image_iff[OF left] finite_image_iff[OF right])
qed

lemma socket_sum_single_valued:
  fixes Q :: "('s \<times> 'a) set" and W :: "('s \<times> 'b) set"
  shows "single_valued (socket_sum Q W) \<longleftrightarrow>
    single_valued Q \<and> single_valued W \<and> rel_dom Q \<inter> rel_dom W = {}"
proof
  assume sv: "single_valued (socket_sum Q W)"
  have left: "single_valued Q"
  proof (unfold single_valued_def, intro allI impI)
    fix s x y assume first: "(s,x) \<in> Q" and second: "(s,y) \<in> Q"
    have a: "(s,Inl x) \<in> socket_sum Q W" and b: "(s,Inl y) \<in> socket_sum Q W"
      using first second by simp_all
    have "Inl x = (Inl y :: 'a + 'b)" by (rule single_valued_outputs[OF sv a b])
    then show "x=y" by simp
  qed
  have right: "single_valued W"
  proof (unfold single_valued_def, intro allI impI)
    fix s x y assume first: "(s,x) \<in> W" and second: "(s,y) \<in> W"
    have a: "(s,Inr x) \<in> socket_sum Q W" and b: "(s,Inr y) \<in> socket_sum Q W"
      using first second by simp_all
    have "Inr x = (Inr y :: 'a + 'b)" by (rule single_valued_outputs[OF sv a b])
    then show "x=y" by simp
  qed
  have separate: "rel_dom Q \<inter> rel_dom W = {}"
  proof (rule equals0I)
    fix s assume member: "s \<in> rel_dom Q \<inter> rel_dom W"
    obtain x y where first: "(s,x) \<in> Q" and second: "(s,y) \<in> W"
      using member by (auto simp: rel_dom_def)
    have a: "(s,Inl x) \<in> socket_sum Q W" and b: "(s,Inr y) \<in> socket_sum Q W"
      using first second by simp_all
    have "Inl x = (Inr y :: 'a + 'b)" by (rule single_valued_outputs[OF sv a b])
    then show False by simp
  qed
  show "single_valued Q \<and> single_valued W \<and> rel_dom Q \<inter> rel_dom W = {}"
    using left right separate by blast
next
  assume props: "single_valued Q \<and> single_valued W \<and> rel_dom Q \<inter> rel_dom W = {}"
  show "single_valued (socket_sum Q W)"
  proof (unfold single_valued_def, intro allI impI)
    fix s x y assume first: "(s,x) \<in> socket_sum Q W" and second: "(s,y) \<in> socket_sum Q W"
    show "x=y" using first second props
      by (cases x; cases y; auto simp: single_valued_def rel_dom_def; blast)
  qed
qed

lemma socket_sum_unique:
  fixes Q Q' :: "('s \<times> 'a) set" and W W' :: "('s \<times> 'b) set"
  shows "socket_sum Q W = socket_sum Q' W' \<longleftrightarrow> Q=Q' \<and> W=W'"
proof
  assume eq: "socket_sum Q W = socket_sum Q' W'"
  have left: "\<And>s x. (s,x) \<in> Q \<longleftrightarrow> (s,x) \<in> Q'"
  proof -
    fix s x
    have "(s,Inl x) \<in> socket_sum Q W \<longleftrightarrow> (s,Inl x) \<in> socket_sum Q' W'"
      by (simp only: eq)
    then show "(s,x) \<in> Q \<longleftrightarrow> (s,x) \<in> Q'" by simp
  qed
  have right: "\<And>s x. (s,x) \<in> W \<longleftrightarrow> (s,x) \<in> W'"
  proof -
    fix s x
    have "(s,Inr x) \<in> socket_sum Q W \<longleftrightarrow> (s,Inr x) \<in> socket_sum Q' W'"
      by (simp only: eq)
    then show "(s,x) \<in> W \<longleftrightarrow> (s,x) \<in> W'" by simp
  qed
  show "Q=Q' \<and> W=W'" using left right by auto
next
  assume "Q=Q' \<and> W=W'"
  then show "socket_sum Q W = socket_sum Q' W'" by simp
qed

section \<open>Finite ancestry\<close>

text \<open>Only direct edges are stored.  Transitive ancestry is always derived.\<close>

definition strict_ancestor :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "strict_ancestor E x y \<longleftrightarrow> (x,y) \<in> E\<^sup>+"

definition acyclic_edges :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "acyclic_edges E \<longleftrightarrow> (\<forall>x. (x,x) \<notin> E\<^sup>+)"

lemma strict_ancestor_irrefl:
  assumes "acyclic_edges E"
  shows "\<not> strict_ancestor E x x"
  using assms by (simp add: acyclic_edges_def strict_ancestor_def)

lemma strict_ancestor_trans:
  assumes "strict_ancestor E x y" "strict_ancestor E y z"
  shows "strict_ancestor E x z"
  using assms unfolding strict_ancestor_def by (meson trancl_trans)


lemma relation_range_union:
  "(\<Union>(s,t)\<in>M. F t) = (\<Union>t\<in>rel_ran M. F t)"
  by (auto simp: rel_ran_def)

section \<open>Finite functional families admit distinct socket enumerations\<close>

lemma zip_domain:
  assumes "length xs = length ys"
  shows "rel_dom (set (zip xs ys)) = set xs"
  using assms by (induction xs arbitrary: ys) (case_tac ys; auto simp: rel_dom_def)+

lemma zip_range:
  assumes "length xs = length ys"
  shows "rel_ran (set (zip xs ys)) = set ys"
  using assms by (induction xs arbitrary: ys) (case_tac ys; auto simp: rel_ran_def)+

lemma set_zip_map_both:
  "set (zip (map f xs) (map g ys)) = (\<lambda>(a,b). (f a,g b)) ` set (zip xs ys)"
proof (induction xs arbitrary: ys)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case by (cases ys) (simp_all add: Cons.IH)
qed

lemma finite_functional_list:
  fixes M :: "('s \<times> 'a) set"
  assumes fin: "finite M" and sv: "single_valued M"
  shows "\<exists>ss xs. length ss = length xs \<and> distinct ss \<and> set (zip ss xs) = M"
proof -
  obtain es :: "('s \<times> 'a) list" where enumeration: "set es = M" and separate: "distinct es"
    using finite_distinct_list[OF fin] by metis
  have injective: "inj_on fst M"
  proof (rule inj_onI)
    fix x y assume first: "x \<in> M" and second: "y \<in> M" and same: "fst x = fst y"
    have left: "(fst x,snd x) \<in> M" using first by simp
    have right: "(fst x,snd y) \<in> M" using second same by simp
    have outputs: "snd x = snd y" by (rule single_valued_outputs[OF sv left right])
    show "x=y" using same outputs by (cases x; cases y) simp
  qed
  have distinct: "distinct (map fst es)" using separate injective enumeration by (simp add: distinct_map)
  show ?thesis by (rule exI[of _ "map fst es"], rule exI[of _ "map snd es"])
    (use distinct enumeration in \<open>simp add: zip_map_fst_snd\<close>)
qed

lemma distinct_list_rekey:
  assumes len: "length xs = length ys" and separate: "distinct xs" "distinct ys"
  shows "\<exists>h. inj_on h (set xs) \<and> map h xs = ys"
proof -
  let ?Q = "set (zip xs ys)"
  let ?h = "rel_value ?Q"
  have sv: "single_valued ?Q" by (rule single_valued_zip[OF separate(1)])
  have entries: "\<forall>i<length xs. ?h (xs!i) = ys!i"
  proof (intro allI impI)
    fix i assume index: "i < length xs"
    have pair: "(xs!i,ys!i) \<in> ?Q"
      by (simp only: in_set_zip; rule exI[of _ i]) (use index len in auto)
    show "?h (xs!i) = ys!i" by (rule rel_value_eq[OF sv pair])
  qed
  have mapped: "map ?h xs = ys" by (rule nth_equalityI) (use len entries in auto)
  have distinct_image: "distinct (map ?h xs)" using separate(2) mapped by simp
  have injective: "inj_on ?h (set xs)" using distinct_image by (simp only: distinct_map)
  show ?thesis by (rule exI[of _ ?h]) (use mapped injective in blast)
qed

end
