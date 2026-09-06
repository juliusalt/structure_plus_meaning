theory Factor_Finite_Presentations
  imports Factor_Finite_Terms
begin

section \<open>Every complete presentation of a finite collection\<close>

definition finite_collection_presents ::
  "('a \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "finite_collection_presents read A t \<longleftrightarrow>
    (\<exists>xs ts. distinct xs \<and> set xs=A \<and> list_all2 read xs ts \<and> t=enumeration_term ts)"

lemma finite_collection_presents_map:
  assumes "distinct xs" "set xs=A" "\<And>x. x\<in>A \<Longrightarrow> read x (f x)"
  shows "finite_collection_presents read A (enumeration_term (map f xs))"
  unfolding finite_collection_presents_def
  by (rule exI[of _ xs], rule exI[of _ "map f xs"])
     (use assms in \<open>simp add: list_all2_map2 list_all2_same\<close>)

lemma finite_collection_presents_finite:
  assumes "finite_collection_presents read A t"
  shows "finite A"
  using assms by (auto simp: finite_collection_presents_def)

lemma finite_collection_presents_formed:
  assumes present: "finite_collection_presents read A t"
    and each: "\<And>a u. a\<in>A \<Longrightarrow> read a u \<Longrightarrow> term_formed u"
  shows "term_formed t"
proof -
  obtain xs ts where entries: "set xs=A" "list_all2 read xs ts" "t=enumeration_term ts"
    using present by (auto simp: finite_collection_presents_def)
  have formed: "\<forall>u\<in>set ts. term_formed u"
  proof (intro ballI)
    fix u assume "u\<in>set ts"
    then obtain i where index: "i<length ts" "u=ts!i" by (auto simp: in_set_conv_nth)
    have bound: "i<length xs" using entries(2) index(1) list_all2_lengthD by metis
    have inside: "xs!i\<in>A" using nth_mem[OF bound] entries(1) by simp
    have read: "read (xs!i) (ts!i)" by (rule list_all2_nthD[OF entries(2) bound])
    show "term_formed u" using each[OF inside read] index(2) by simp
  qed
  show ?thesis using formed entries(3) by (simp add: enumeration_term_formed)
qed

lemma finite_collection_presents_unique:
  assumes first: "finite_collection_presents read A t"
    and second: "finite_collection_presents read B t"
    and unique: "\<And>a b u. a\<in>A \<Longrightarrow> b\<in>B \<Longrightarrow>
      read a u \<Longrightarrow> read b u \<Longrightarrow> a=b"
  shows "A=B"
proof -
  obtain xs ts where left: "set xs=A" "list_all2 read xs ts" "t=enumeration_term ts"
    using first by (auto simp: finite_collection_presents_def)
  obtain ys us where right: "set ys=B" "list_all2 read ys us" "t=enumeration_term us"
    using second by (auto simp: finite_collection_presents_def)
  have same: "ts=us" using left(3) right(3) by (simp add: enumeration_term_injective)
  have other: "list_all2 read ys ts" using right(2) same by simp
  have lengths: "length xs=length ys" using left(2) other list_all2_lengthD by metis
  have equal: "xs=ys"
  proof (rule nth_equalityI[OF lengths])
    fix i assume index: "i<length xs"
    have bound: "i<length ys" using index lengths by simp
    have a: "xs!i\<in>A" using nth_mem[OF index] left(1) by simp
    have b: "ys!i\<in>B" using nth_mem[OF bound] right(1) by simp
    show "xs!i=ys!i"
      by (rule unique[OF a b list_all2_nthD[OF left(2) index]
          list_all2_nthD[OF other bound]])
  qed
  show ?thesis using left(1) right(1) equal by simp
qed

definition finite_set_presents ::
  "('a \<Rightarrow> factor_term) \<Rightarrow> 'a set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "finite_set_presents f A t \<longleftrightarrow> finite_collection_presents (\<lambda>a u. u=f a) A t"

lemma finite_set_presents_iff:
  "finite_set_presents f A t \<longleftrightarrow>
    (\<exists>xs. distinct xs \<and> set xs=A \<and> t=enumeration_term (map f xs))"
proof -
  have related: "list_all2 (\<lambda>a u. u=f a) xs ts \<longleftrightarrow> ts=map f xs" for xs ts
    by (induction xs arbitrary: ts) (auto simp: list_all2_Cons1)
  show ?thesis by (simp add: finite_set_presents_def finite_collection_presents_def related)
qed

lemma finite_set_term_presents:
  assumes "finite A"
  shows "finite_set_presents f A (finite_set_term f A)"
  unfolding finite_set_presents_iff finite_set_term_def
  by (rule exI[of _ "sorted_list_of_set A"]) (use assms in simp)

lemma finite_set_presents_unique:
  assumes "finite_set_presents f A t" "finite_set_presents f B t" "inj f"
  shows "A=B"
  by (rule finite_collection_presents_unique[OF assms(1,2)[unfolded finite_set_presents_def]])
     (use assms(3) in \<open>auto dest: injD\<close>)

lemma finite_set_presents_formed:
  assumes "finite_set_presents f A t" "\<And>a. a\<in>A \<Longrightarrow> term_formed (f a)"
  shows "term_formed t"
  by (rule finite_collection_presents_formed[OF assms(1)[unfolded finite_set_presents_def]])
     (use assms(2) in auto)

section \<open>Complete tables with recursively presented values\<close>

definition table_entry_presents ::
  "('k \<Rightarrow> factor_term) \<Rightarrow> ('v \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
    ('k \<times> 'v) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "table_entry_presents K read z t \<longleftrightarrow>
    (\<exists>u. read (snd z) u \<and> t=Pair_Term (K (fst z)) u)"

definition finite_table_presents ::
  "('k \<Rightarrow> factor_term) \<Rightarrow> ('v \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
    ('k \<times> 'v) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "finite_table_presents K read R t \<longleftrightarrow>
    single_valued R \<and> finite_collection_presents (table_entry_presents K read) R t"

lemma finite_table_term_presents:
  assumes fin: "finite R" and sv: "single_valued R"
    and each: "\<And>v. v\<in>rel_ran R \<Longrightarrow> read v (V v)"
  shows "finite_table_presents K read R (finite_table_term K V R)"
proof -
  let ?ks = "sorted_list_of_set (rel_dom R)"
  let ?entry = "\<lambda>k. (k,rel_value R k)"
  let ?row = "\<lambda>z. Pair_Term (K (fst z)) (V (snd z))"
  have kfin: "finite (rel_dom R)" by (rule finite_rel_dom[OF fin])
  have complete: "set (map ?entry ?ks)=R"
  proof
    show "set (map ?entry ?ks)\<subseteq>R"
    proof
      fix z assume "z\<in>set (map ?entry ?ks)"
      then obtain k v where key: "(k,v)\<in>R" "z=(k,rel_value R k)"
        using kfin by (auto simp: rel_dom_def)
      show "z\<in>R" using key rel_value_eq[OF sv key(1)] by simp
    qed
    show "R\<subseteq>set (map ?entry ?ks)"
    proof
      fix z assume "z\<in>R"
      then obtain k v where key: "(k,v)\<in>R" "z=(k,v)" by (cases z) auto
      have inside: "k\<in>set ?ks" using key(1) kfin by auto
      show "z\<in>set (map ?entry ?ks)"
        using imageI[OF inside, of ?entry] key(2) rel_value_eq[OF sv key(1)] by simp
    qed
  qed
  have distinct: "distinct (map ?entry ?ks)"
    by (auto simp: distinct_map inj_on_def)
  have reads: "\<And>z. z\<in>R \<Longrightarrow> table_entry_presents K read z (?row z)"
    using each by (auto simp: table_entry_presents_def rel_ran_def; blast)
  have presented: "finite_collection_presents (table_entry_presents K read) R
    (enumeration_term (map ?row (map ?entry ?ks)))"
    by (rule finite_collection_presents_map[where f="?row", OF distinct complete])
       (rule reads; assumption)
  show ?thesis using sv presented
    by (simp add: finite_table_presents_def finite_table_term_def finite_table_rows_def comp_def)
qed

lemma finite_table_presents_formed:
  assumes present: "finite_table_presents K read R t"
    and each: "\<And>k v u. (k,v)\<in>R \<Longrightarrow> read v u \<Longrightarrow>
      term_formed (K k) \<and> term_formed u"
  shows "term_formed t"
proof -
  have collection: "finite_collection_presents (table_entry_presents K read) R t"
    using present by (simp add: finite_table_presents_def)
  show ?thesis
    by (rule finite_collection_presents_formed[OF collection])
       (use each in \<open>auto simp: table_entry_presents_def\<close>)
qed

lemma finite_table_presents_unique:
  assumes first: "finite_table_presents K read R t"
    and second: "finite_table_presents K read S t" and keys: "inj K"
    and vals: "\<And>v w u. v\<in>rel_ran R \<Longrightarrow> w\<in>rel_ran S \<Longrightarrow>
      read v u \<Longrightarrow> read w u \<Longrightarrow> v=w"
  shows "R=S"
proof -
  have left: "finite_collection_presents (table_entry_presents K read) R t"
    and right: "finite_collection_presents (table_entry_presents K read) S t"
    using first second by (simp_all add: finite_table_presents_def)
  show ?thesis
  proof (rule finite_collection_presents_unique[OF left right])
    fix a b u assume a: "a\<in>R" and b: "b\<in>S"
      and ar: "table_entry_presents K read a u"
      and br: "table_entry_presents K read b u"
    have fst: "fst a=fst b" and same: "\<exists>x. read (snd a) x \<and> read (snd b) x"
      using ar br keys by (auto simp: table_entry_presents_def dest: injD)
    have av: "snd a\<in>rel_ran R" using a by (cases a) (auto simp: rel_ran_def)
    have bv: "snd b\<in>rel_ran S" using b by (cases b) (auto simp: rel_ran_def)
    have snd: "snd a=snd b" using vals[OF av bv] same by blast
    show "a=b" using fst snd by (rule prod_eqI)
  qed
qed

text \<open>
  Enumeration order is a presentation witness. Every source entry occurs once;
  table functionality excludes duplicate keys. Values may themselves have
  several presentations. Unique recovery is separate from any claim that a
  semantic definition gives all presentations the same answer.
\<close>

end
