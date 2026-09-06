theory Factor_Finite_Terms
  imports Factor_Material_Observation
begin

section \<open>Finite extensional fields as ordinary terms\<close>

definition finite_set_term ::
  "('a::linorder \<Rightarrow> factor_term) \<Rightarrow> 'a set \<Rightarrow> factor_term" where
  "finite_set_term f A = enumeration_term (map f (sorted_list_of_set A))"

lemma finite_set_term_formed:
  assumes "finite A"
  shows "term_formed (finite_set_term f A) \<longleftrightarrow> (\<forall>a\<in>A. term_formed (f a))"
  using assms by (simp add: finite_set_term_def enumeration_term_formed)

lemma finite_set_term_exact:
  assumes finite: "finite A" "finite B" and inj: "inj f"
  shows "finite_set_term f A = finite_set_term f B \<longleftrightarrow> A = B"
proof
  assume eq: "finite_set_term f A = finite_set_term f B"
  have lists: "map f (sorted_list_of_set A) = map f (sorted_list_of_set B)"
    using eq by (simp add: finite_set_term_def enumeration_term_injective)
  have images: "f ` A = f ` B"
    using arg_cong[OF lists, where f=set] finite by simp
  show "A = B" using images inj_image_eq_iff[OF inj] by blast
next
  assume "A = B" then show "finite_set_term f A = finite_set_term f B" by simp
qed

definition finite_table_rows ::
  "('k::linorder \<Rightarrow> factor_term) \<Rightarrow> ('v \<Rightarrow> factor_term) \<Rightarrow>
    ('k \<times> 'v) set \<Rightarrow> factor_term list" where
  "finite_table_rows K V R =
    map (\<lambda>k. Pair_Term (K k) (V (rel_value R k))) (sorted_list_of_set (rel_dom R))"

definition finite_table_term ::
  "('k::linorder \<Rightarrow> factor_term) \<Rightarrow> ('v \<Rightarrow> factor_term) \<Rightarrow>
    ('k \<times> 'v) set \<Rightarrow> factor_term" where
  "finite_table_term K V R = enumeration_term (finite_table_rows K V R)"

lemma finite_table_rows_complete:
  assumes fin: "finite R" and sv: "single_valued R"
  shows "set (finite_table_rows K V R) = (\<lambda>(k,v). Pair_Term (K k) (V v)) ` R"
proof -
  have finite: "finite (rel_dom R)" by (rule finite_rel_dom[OF fin])
  show ?thesis
  proof
    show "set (finite_table_rows K V R) \<subseteq> (\<lambda>(k,v). Pair_Term (K k) (V v)) ` R"
    proof
      fix t assume member: "t \<in> set (finite_table_rows K V R)"
      obtain k where key: "k \<in> rel_dom R"
        and encoded: "t = Pair_Term (K k) (V (rel_value R k))"
        using member finite by (auto simp: finite_table_rows_def)
      obtain v where entry: "(k,v) \<in> R" using key by (auto simp: rel_dom_def)
      have rv: "rel_value R k = v" by (rule rel_value_eq[OF sv entry])
      show "t \<in> (\<lambda>(k,v). Pair_Term (K k) (V v)) ` R"
        by (rule rev_image_eqI[OF entry]) (use encoded rv in simp)
    qed
    show "(\<lambda>(k,v). Pair_Term (K k) (V v)) ` R \<subseteq> set (finite_table_rows K V R)"
    proof
      fix t assume member: "t \<in> (\<lambda>(k,v). Pair_Term (K k) (V v)) ` R"
      obtain k v where entry: "(k,v) \<in> R" and encoded: "t = Pair_Term (K k) (V v)"
        using member by auto
      have key: "k \<in> rel_dom R" using entry by auto
      have rv: "rel_value R k = v" by (rule rel_value_eq[OF sv entry])
      have "Pair_Term (K k) (V (rel_value R k)) \<in> set (finite_table_rows K V R)"
        using key finite by (auto simp: finite_table_rows_def)
      then show "t \<in> set (finite_table_rows K V R)" using encoded rv by simp
    qed
  qed
qed

lemma finite_table_term_formed:
  assumes "finite R" "single_valued R"
  shows "term_formed (finite_table_term K V R) \<longleftrightarrow>
    (\<forall>k v. (k,v) \<in> R \<longrightarrow> term_formed (K k) \<and> term_formed (V v))"
  using finite_table_rows_complete[OF assms, of K V]
  by (auto simp: finite_table_term_def enumeration_term_formed)

lemma finite_table_term_same_rows:
  assumes rf: "finite R" and rsv: "single_valued R"
    and sf: "finite S" and ssv: "single_valued S"
    and same: "finite_table_term K V R = finite_table_term K V S"
  shows "(\<lambda>(k,v). Pair_Term (K k) (V v)) ` R =
    (\<lambda>(k,v). Pair_Term (K k) (V v)) ` S"
proof -
  have rows: "finite_table_rows K V R = finite_table_rows K V S"
    using same by (simp add: finite_table_term_def enumeration_term_injective)
  show ?thesis
    using arg_cong[OF rows, where f=set]
      finite_table_rows_complete[OF rf rsv, of K V]
      finite_table_rows_complete[OF sf ssv, of K V] by simp
qed

lemma finite_table_term_exact:
  fixes K :: "'k::linorder \<Rightarrow> factor_term" and V :: "'v \<Rightarrow> factor_term"
  assumes rf: "finite R" and rsv: "single_valued R"
    and sf: "finite S" and ssv: "single_valued S"
    and keys: "inj K" and vals: "inj_on V (rel_ran R \<union> rel_ran S)"
  shows "finite_table_term K V R = finite_table_term K V S \<longleftrightarrow> R = S"
proof
  assume eq: "finite_table_term K V R = finite_table_term K V S"
  let ?row = "\<lambda>(k,v). Pair_Term (K k) (V v)"
  have rowinj: "inj_on ?row (R \<union> S)"
  proof (rule inj_onI)
    fix x y assume xm: "x \<in> R \<union> S" and ym: "y \<in> R \<union> S"
      and equal: "?row x = ?row y"
    obtain k v where xp: "x = (k,v)" by (cases x) auto
    obtain l w where yp: "y = (l,w)" by (cases y) auto
    have ke: "K k = K l" and ve: "V v = V w" using equal xp yp by simp_all
    have kl: "k=l" by (rule injD[OF keys ke])
    have vr: "v \<in> rel_ran R \<union> rel_ran S"
      and wr: "w \<in> rel_ran R \<union> rel_ran S"
      using xm ym xp yp by (auto simp: rel_ran_def)
    have vw: "v=w" by (rule inj_onD[OF vals ve vr wr])
    show "x=y" using xp yp kl vw by simp
  qed
  show "R = S"
    using finite_table_term_same_rows[OF rf rsv sf ssv eq]
      inj_on_Un_image_eq_iff[OF rowinj] by blast
next
  assume "R = S"
  then show "finite_table_term K V R = finite_table_term K V S" by simp
qed

section \<open>Structural natural indices and exact source lists\<close>

fun natural_term :: "nat \<Rightarrow> factor_term" where
  "natural_term 0 = enumeration_term []"
| "natural_term (Suc n) = Pair_Term (Payload_Term []) (natural_term n)"

lemma natural_term_formed [simp]: "term_formed (natural_term n)"
  by (induction n) (auto simp: octets_formed_def)

lemma natural_term_not_payload [simp]: "natural_term n \<noteq> Payload_Term b"
  by (cases n) auto

lemma natural_term_exact [simp]:
  "natural_term n = natural_term m \<longleftrightarrow> n=m"
  by (induction n arbitrary: m) (case_tac m; auto)+

definition artifact_list_term :: "exact_artifact list \<Rightarrow> factor_term" where
  "artifact_list_term xs = enumeration_term (map (Target_Term \<circ> Whole_Artifact) xs)"

lemma artifact_list_term_formed:
  "term_formed (artifact_list_term xs) \<longleftrightarrow> (\<forall>R\<in>set xs. exact_formed R)"
  by (simp add: artifact_list_term_def enumeration_term_formed)

lemma artifact_list_term_exact:
  "artifact_list_term xs = artifact_list_term ys \<longleftrightarrow> xs=ys"
  unfolding artifact_list_term_def
  by (induction xs arbitrary: ys) (case_tac ys; auto simp: enumeration_term_injective)+

text \<open>
  Sorting chooses one ordered term for each finite set or functional table.
  Factor patterns can observe that order. Exact recovery of the represented
  relation does not establish semantic invariance under another enumeration.
  These serialization results therefore do not justify an unordered permission
  boundary. Actual input lists intentionally keep their order and repetitions.
\<close>

end
