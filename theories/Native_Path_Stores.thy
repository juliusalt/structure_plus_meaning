theory Native_Path_Stores
  imports Native_Collection_Programs Binary_Path_Stores Finite_Presented_Collections
begin

section \<open>A path and a path store are structure\<close>

text \<open>
  A key that a native definition searches by is structure, not an octet: a binary path is a list of bits,
  and a bit is a shape, the empty payload for one direction and a pair of empty payloads for the other.
  A path store is the existing binary store presented as structure: the empty store is the empty payload,
  and a node is its optional value beside the pair of its two children, an absent value being the empty
  payload and a present one a pair of the empty payload and the value. Nothing here is an octet but the
  empty payload, so a native program searching a path store reads no octet as structure; two paths are
  told apart by their shapes alone.
\<close>

definition bit_term :: "bool \<Rightarrow> factor_term" where
  "bit_term b=(if b then Pair_Term (Payload_Term []) (Payload_Term []) else Payload_Term [])"

definition path_term :: "bool list \<Rightarrow> factor_term" where
  "path_term bs=data_list_term (map bit_term bs)"

lemma bit_term_injective: "bit_term b=bit_term c \<longleftrightarrow> b=c"
  by (cases b; cases c) (simp_all add: bit_term_def)

lemma bit_term_shapes:
  "bit_term b=Payload_Term v \<longleftrightarrow> \<not>b \<and> v=[]"
  "bit_term b=Pair_Term x y \<longleftrightarrow> b \<and> x=Payload_Term [] \<and> y=Payload_Term []"
  "bit_term b\<noteq>Target_Term t"
  "Payload_Term v=bit_term b \<longleftrightarrow> \<not>b \<and> v=[]"
  "Pair_Term x y=bit_term b \<longleftrightarrow> b \<and> x=Payload_Term [] \<and> y=Payload_Term []"
  "Target_Term t\<noteq>bit_term b"
  by (cases b; auto simp: bit_term_def)+

lemma path_term_simps [simp]:
  "path_term []=Payload_Term []"
  "path_term (b#bs)=Pair_Term (bit_term b) (path_term bs)"
  by (simp_all add: path_term_def)

lemma path_term_shapes:
  "path_term bs=Payload_Term v \<longleftrightarrow> bs=[] \<and> v=[]"
  "path_term bs=Pair_Term x y \<longleftrightarrow> (\<exists>c cs. bs=c#cs \<and> x=bit_term c \<and> y=path_term cs)"
  "path_term bs\<noteq>Target_Term t"
  "Payload_Term v=path_term bs \<longleftrightarrow> bs=[] \<and> v=[]"
  "Pair_Term x y=path_term bs \<longleftrightarrow> (\<exists>c cs. bs=c#cs \<and> x=bit_term c \<and> y=path_term cs)"
  "Target_Term t\<noteq>path_term bs"
  by (cases bs; auto)+

lemma path_term_injective: "path_term bs=path_term cs \<longleftrightarrow> bs=cs"
proof (induction bs arbitrary: cs)
  case Nil
  then show ?case by (cases cs) simp_all
next
  case (Cons b bs)
  then show ?case by (cases cs) (simp_all add: bit_term_injective)
qed

lemma bit_term_formed [simp]: "term_formed (bit_term b)"
  by (cases b) (simp_all add: bit_term_def octets_formed_def)

lemma path_term_formed [simp]: "term_formed (path_term bs)"
  by (induction bs) (simp_all add: octets_formed_def)

definition store_option_term :: "('v \<Rightarrow> factor_term) \<Rightarrow> 'v option \<Rightarrow> factor_term" where
  "store_option_term val v=(case v of None \<Rightarrow> Payload_Term [] | Some x \<Rightarrow> Pair_Term (Payload_Term []) (val x))"

fun store_term :: "('v \<Rightarrow> factor_term) \<Rightarrow> 'v binary_path_store \<Rightarrow> factor_term" where
  "store_term val Empty_Store=Payload_Term []"
| "store_term val (Store_Node v l r)=Pair_Term (store_option_term val v) (Pair_Term (store_term val l) (store_term val r))"

lemma store_option_term_found:
  "store_option_term val v=Pair_Term (Payload_Term []) w \<longleftrightarrow> (\<exists>x. v=Some x \<and> w=val x)"
  "Pair_Term (Payload_Term []) w=store_option_term val v \<longleftrightarrow> (\<exists>x. v=Some x \<and> w=val x)"
  by (cases v; auto simp: store_option_term_def)+

lemma store_term_shapes:
  "store_term val T=Payload_Term u \<longleftrightarrow> T=Empty_Store \<and> u=[]"
  "store_term val T=Pair_Term a b \<longleftrightarrow>
    (\<exists>v l r. T=Store_Node v l r \<and> a=store_option_term val v \<and> b=Pair_Term (store_term val l) (store_term val r))"
  "Payload_Term u=store_term val T \<longleftrightarrow> T=Empty_Store \<and> u=[]"
  "Pair_Term a b=store_term val T \<longleftrightarrow>
    (\<exists>v l r. T=Store_Node v l r \<and> a=store_option_term val v \<and> b=Pair_Term (store_term val l) (store_term val r))"
  by (cases T; auto)+

lemma store_option_term_formed:
  assumes valued: "\<And>x. term_formed (val x)"
  shows "term_formed (store_option_term val v)"
  using valued by (cases v) (simp_all add: store_option_term_def octets_formed_def)

lemma store_term_formed:
  assumes valued: "\<And>x. term_formed (val x)"
  shows "term_formed (store_term val T)"
  by (induction T) (simp_all add: store_option_term_formed[OF valued] octets_formed_def)

section \<open>The value a path store holds at a path, checked in a context\<close>

text \<open>
  The search descends the store along the path: at the empty path a node holding a value is found and the
  value is checked in the context; a bit of the one shape descends into the left child, of the other into
  the right one. The empty store holds nothing, so no rule reads it. Each call reads one node, and a search
  makes as many calls as its path has bits.
\<close>

definition native_store_found_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_store_found_rule ch=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)) (native_var 2))))
    [([0],(ch,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"

definition native_store_left_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_store_left_rule k=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
      (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))
    [([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"

definition native_store_right_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_store_right_rule k=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])) (native_var 1))
      (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))
    [([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4))))]"

definition native_store_search_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_store_search_rules k ch=[([0],native_store_found_rule ch),([1],native_store_left_rule k),
    ([2],native_store_right_rule k)]"

locale native_store_search_program = native_rule_family P k "native_store_search_rules k ch"
  for P :: "'u native_system" and k ch :: "'u definition_site"
begin

sublocale law: native_rule_law P k "native_store_search_rules k ch"
  by (rule native_rule_lawI[OF native_rule_family_axioms])
    (simp add: native_store_search_rules_def native_store_found_rule_def native_store_left_rule_def
      native_store_right_rule_def; blast)

text \<open>
  The search is read for every key, not only for a path: a key the rules do not descend by, a target or a
  payload other than the empty one, has no search that holds. A key that holds is therefore a path, and the
  value found is the value the store holds at it. What the search's rules say is stated once, at a rule of
  the family and any support relation (@{text unfold_rule}); the family's law reads a clause or a call as
  such a rule, and the induction over the key and over the path stays the search's own.
\<close>

lemma unfold_rule:
  assumes rule: "(c,finite_native_rule p ps)\<in>set (native_store_search_rules k ch)"
    and support: "\<forall>(s,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>Y"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (Pair_Term key (store_term val T))"
  shows "(\<exists>v l r. key=Payload_Term [] \<and> T=Store_Node (Some v) l r \<and> (ch,Pair_Term x (val v))\<in>Y) \<or>
    (\<exists>key' v l r. key=Pair_Term (bit_term False) key' \<and> T=Store_Node v l r \<and>
      (k,Pair_Term x (Pair_Term key' (store_term val l)))\<in>Y) \<or>
    (\<exists>key' v l r. key=Pair_Term (bit_term True) key' \<and> T=Store_Node v l r \<and>
      (k,Pair_Term x (Pair_Term key' (store_term val r)))\<in>Y)"
proof -
  have "finite_native_rule p ps=native_store_found_rule ch \<or> finite_native_rule p ps=native_store_left_rule k \<or>
      finite_native_rule p ps=native_store_right_rule k"
    using rule by (auto simp: native_store_search_rules_def)
  then show ?thesis
  proof (elim disjE)
    assume "finite_native_rule p ps=native_store_found_rule ch"
    note F=this[unfolded native_store_found_rule_def finite_native_rule_eq_iff]
    have premise: "(ch,Pair_Term (f [0]) (f [1]))\<in>Y" using support by (simp add: F)
    show ?thesis using shape premise
      by (auto simp: F store_term_shapes store_option_term_found)
  next
    assume "finite_native_rule p ps=native_store_left_rule k"
    note F=this[unfolded native_store_left_rule_def finite_native_rule_eq_iff]
    have premise: "(k,Pair_Term (f [0]) (Pair_Term (f [1]) (f [3])))\<in>Y" using support by (simp add: F)
    show ?thesis using shape premise
      by (auto simp: F bit_term_def store_term_shapes)
  next
    assume "finite_native_rule p ps=native_store_right_rule k"
    note F=this[unfolded native_store_right_rule_def finite_native_rule_eq_iff]
    have premise: "(k,Pair_Term (f [0]) (Pair_Term (f [1]) (f [4])))\<in>Y" using support by (simp add: F)
    show ?thesis using shape premise
      by (auto simp: F bit_term_def store_term_shapes)
  qed
qed

lemma sound:
  assumes holds: "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  shows "\<exists>bs v. key=path_term bs \<and> store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P"
  using holds
proof (induction key arbitrary: T)
  case (Target_Term t)
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (Pair_Term (Target_Term t) (store_term val T))"
    and support: "\<forall>(s,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    by (rule law.holds_rule[OF Target_Term.prems]) blast
  show ?case using unfold_rule[OF rule support shape] by auto
next
  case (Payload_Term w)
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (Pair_Term (Payload_Term w) (store_term val T))"
    and support: "\<forall>(s,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    by (rule law.holds_rule[OF Payload_Term.prems]) blast
  obtain v l r where w: "w=[]" and T: "T=Store_Node (Some v) l r"
    and found: "(ch,Pair_Term x (val v))\<in>positive_meaning P"
    using unfold_rule[OF rule support shape] by auto
  show ?case
  proof (intro exI conjI)
    show "Payload_Term w=path_term []" using w by simp
    show "store_lookup T []=Some v" using T by simp
    show "(ch,Pair_Term x (val v))\<in>positive_meaning P" by (rule found)
  qed
next
  case (Pair_Term a b)
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (Pair_Term (Pair_Term a b) (store_term val T))"
    and support: "\<forall>(s,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    by (rule law.holds_rule[OF Pair_Term.prems]) blast
  have "(\<exists>key' v l r. Pair_Term a b=Pair_Term (bit_term False) key' \<and> T=Store_Node v l r \<and>
        (k,Pair_Term x (Pair_Term key' (store_term val l)))\<in>positive_meaning P) \<or>
      (\<exists>key' v l r. Pair_Term a b=Pair_Term (bit_term True) key' \<and> T=Store_Node v l r \<and>
        (k,Pair_Term x (Pair_Term key' (store_term val r)))\<in>positive_meaning P)"
    using unfold_rule[OF rule support shape] by auto
  then show ?case
  proof (elim disjE exE conjE)
    fix key' v l r
    assume ab: "Pair_Term a b=Pair_Term (bit_term False) key'" and T: "T=Store_Node v l r"
      and inner: "(k,Pair_Term x (Pair_Term key' (store_term val l)))\<in>positive_meaning P"
    obtain bs w where b: "b=path_term bs" and lookup: "store_lookup l bs=Some w"
      and found: "(ch,Pair_Term x (val w))\<in>positive_meaning P"
      using Pair_Term.IH(2)[of l] inner ab by auto
    show ?case
    proof (intro exI conjI)
      show "Pair_Term a b=path_term (False#bs)" using ab b by simp
      show "store_lookup T (False#bs)=Some w" using T lookup by simp
      show "(ch,Pair_Term x (val w))\<in>positive_meaning P" by (rule found)
    qed
  next
    fix key' v l r
    assume ab: "Pair_Term a b=Pair_Term (bit_term True) key'" and T: "T=Store_Node v l r"
      and inner: "(k,Pair_Term x (Pair_Term key' (store_term val r)))\<in>positive_meaning P"
    obtain bs w where b: "b=path_term bs" and lookup: "store_lookup r bs=Some w"
      and found: "(ch,Pair_Term x (val w))\<in>positive_meaning P"
      using Pair_Term.IH(2)[of r] inner ab by auto
    show ?case
    proof (intro exI conjI)
      show "Pair_Term a b=path_term (True#bs)" using ab b by simp
      show "store_lookup T (True#bs)=Some w" using T lookup by simp
      show "(ch,Pair_Term x (val w))\<in>positive_meaning P" by (rule found)
    qed
  qed
qed

theorem exact:
  assumes valued: "\<And>y. term_formed (val y)"
  shows "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P)"
proof
  assume holds: "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  have xf: "term_formed x" using holds_formed[OF holds] by simp
  show "term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P)"
    using xf sound[OF holds] by blast
next
  assume "term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P)"
  then obtain bs where xf: "term_formed x" and key: "key=path_term bs"
    and found: "\<exists>v. store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P" by blast
  show "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
    unfolding key using found
  proof (induction bs arbitrary: T)
    case Nil
    obtain v where lookup: "store_lookup T []=Some v" and checked: "(ch,Pair_Term x (val v))\<in>positive_meaning P"
      using Nil.prems by blast
    obtain l r where T: "T=Store_Node (Some v) l r"
      using lookup by (cases T) auto
    have lf: "term_formed (store_term val l)" and rf: "term_formed (store_term val r)"
      by (simp_all add: store_term_formed[OF valued])
    have vf: "term_formed (val v)" by (rule valued)
    have "(k,evaluate_pattern (native_values [x,val v,Pair_Term (store_term val l) (store_term val r)])
        (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)) (native_var 2))))))
        \<in>positive_meaning P"
      by (rule law.step_at[where c="[0]" and ps="[([0],(ch,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
        (use checked xf vf lf rf in \<open>simp_all add: insert_Diff_if native_store_search_rules_def
          native_store_found_rule_def\<close>)
    then show ?case by (simp add: T store_option_term_def octets_formed_def)
  next
    case (Cons b bs)
    obtain v where lookup: "store_lookup T (b#bs)=Some v" and checked: "(ch,Pair_Term x (val v))\<in>positive_meaning P"
      using Cons.prems by blast
    obtain w l r where T: "T=Store_Node w l r"
      using lookup by (cases T; cases b) (simp_all add: store_left.simps store_right.simps)
    have wf: "term_formed (store_option_term val w)" by (rule store_option_term_formed[OF valued])
    have lf: "term_formed (store_term val l)" and rf: "term_formed (store_term val r)"
      by (simp_all add: store_term_formed[OF valued])
    have pf: "term_formed (path_term bs)" by simp
    show ?case
    proof (cases b)
      case False
      have inner: "(k,Pair_Term x (Pair_Term (path_term bs) (store_term val l)))\<in>positive_meaning P"
        using Cons.IH[of l] lookup checked T False by auto
      have "(k,evaluate_pattern (native_values [x,path_term bs,store_option_term val w,store_term val l,store_term val r])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
            (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
            (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))))
          \<in>positive_meaning P"
        by (rule law.step_at[where c="[1]" and
            ps="[([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"])
          (use inner xf wf lf rf pf in \<open>simp_all add: insert_Diff_if native_store_search_rules_def
            native_store_left_rule_def\<close>)
      then show ?thesis using T False by (simp add: bit_term_def)
    next
      case True
      have inner: "(k,Pair_Term x (Pair_Term (path_term bs) (store_term val r)))\<in>positive_meaning P"
        using Cons.IH[of r] lookup checked T True by auto
      have "(k,evaluate_pattern (native_values [x,path_term bs,store_option_term val w,store_term val l,store_term val r])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
            (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload [])) (native_var 1))
            (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))))
          \<in>positive_meaning P"
        by (rule law.step_at[where c="[2]" and
            ps="[([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4))))]"])
          (use inner xf wf lf rf pf in \<open>simp_all add: insert_Diff_if native_store_search_rules_def
            native_store_right_rule_def octets_formed_def\<close>)
      then show ?thesis using T True by (simp add: bit_term_def)
    qed
  qed
qed

end

section \<open>A path store holds nothing at a path, in a context\<close>

text \<open>
  The other half of the search, and a notion of its own. The search finds the value a store holds at a
  path; absence says that the store holds none there. Neither is the negation of the other: absence
  descends the store along the path by the bits' shapes, as the search does, and stops where the search
  cannot go on — at the empty store, which holds nothing at any path, and at a node whose optional value
  is absent, which is a shape and not an octet. A store that holds an empty value at a path holds a value
  there, so absence does not hold of it (\<open>absent_not_at_value\<close>): an empty result and a failed one stay
  apart. A key that is no path has neither a search nor an absence, and the two never hold of one key and
  store (\<open>store_search_absent_exclusive\<close>), which is exclusion and not complementation.
\<close>

abbreviation store_descend :: "bool \<Rightarrow> 'v binary_path_store \<Rightarrow> 'v binary_path_store" where
  "store_descend b T \<equiv> (case T of Empty_Store \<Rightarrow> Empty_Store | Store_Node v l r \<Rightarrow> if b then r else l)"

lemma store_lookup_descend: "store_lookup T (b#bs)=store_lookup (store_descend b T) bs"
  by (cases T; cases b) simp_all

lemma store_option_term_absent:
  "store_option_term val v=Payload_Term [] \<longleftrightarrow> v=None"
  by (cases v) (simp_all add: store_option_term_def)

lemma store_option_term_absent_rev:
  "Payload_Term []=store_option_term val v \<longleftrightarrow> v=None"
  by (cases v) (simp_all add: store_option_term_def)

definition native_absent_empty_rule ::
    "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_empty_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
      (Finite_Pattern_Payload []))) []"

definition native_absent_none_rule ::
    "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_none_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
      (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))) []"

declare native_absent_empty_rule_def [code_unfold] native_absent_none_rule_def [code_unfold]

definition native_absent_left_leaf_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_left_leaf_rule a=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)) (Finite_Pattern_Payload [])))
    [([0],(a,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))]"

definition native_absent_left_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_left_rule a=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
      (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))
    [([0],(a,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"

definition native_absent_right_leaf_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_right_leaf_rule a=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
        (native_var 1)) (Finite_Pattern_Payload [])))
    [([0],(a,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))]"

definition native_absent_right_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_absent_right_rule a=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
        (native_var 1))
      (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))
    [([0],(a,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4))))]"

definition native_store_absent_rules :: "'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_store_absent_rules a=[([0],native_absent_empty_rule),([1],native_absent_none_rule),
    ([2],native_absent_left_leaf_rule a),([3],native_absent_left_rule a),
    ([4],native_absent_right_leaf_rule a),([5],native_absent_right_rule a)]"

locale native_store_absent_program = native_rule_family P a "native_store_absent_rules a"
  for P :: "'u native_system" and a :: "'u definition_site"
begin

sublocale law: native_rule_law P a "native_store_absent_rules a"
proof (rule native_rule_lawI)
  show "native_rule_family P a (native_store_absent_rules a)" by unfold_locales
next
  fix c F assume "(c,F)\<in>set (native_store_absent_rules a)"
  then show "\<exists>p ps. F=finite_native_rule p ps"
    by (auto simp: native_store_absent_rules_def native_absent_empty_rule_def native_absent_none_rule_def
      native_absent_left_leaf_rule_def native_absent_left_rule_def native_absent_right_leaf_rule_def
      native_absent_right_rule_def)
qed

text \<open>
  Absence is read for every key, as the search is: a key the rules do not descend by has no absence,
  and a key that holds is a path at which the store holds nothing.
\<close>

lemma unfold:
  assumes holds: "(a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  shows "(key=Payload_Term [] \<and> store_lookup T []=None) \<or>
    (\<exists>b key'. key=Pair_Term (bit_term b) key' \<and>
      (a,Pair_Term x (Pair_Term key' (store_term val (store_descend b T))))\<in>positive_meaning P)"
proof -
  obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (native_store_absent_rules a)"
    and concl: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (Pair_Term key (store_term val T))"
    and prem: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    by (rule law.holds_rule[OF holds]) blast
  have cases: "finite_native_rule p ps=native_absent_empty_rule \<or>
      finite_native_rule p ps=native_absent_none_rule \<or>
      finite_native_rule p ps=native_absent_left_leaf_rule a \<or>
      finite_native_rule p ps=native_absent_left_rule a \<or>
      finite_native_rule p ps=native_absent_right_leaf_rule a \<or>
      finite_native_rule p ps=native_absent_right_rule a"
    using rule by (auto simp: native_store_absent_rules_def)
  then show ?thesis
  proof (elim disjE)
    assume F: "finite_native_rule p ps=native_absent_empty_rule"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
        (Finite_Pattern_Payload []))"
      by (simp add: native_absent_empty_rule_def finite_native_rule_eq_iff)
    have eqs: "f [0]=x \<and> Payload_Term []=key \<and> Payload_Term []=store_term val T"
      using concl by (simp add: p) blast
    have key: "key=Payload_Term []" using eqs by (rule sym[OF conjunct1[OF conjunct2]])
    have store: "store_term val T=Payload_Term []" using eqs by (rule sym[OF conjunct2[OF conjunct2]])
    have "T=Empty_Store" using store by (simp add: store_term_shapes)
    then show ?thesis using key by simp
  next
    assume F: "finite_native_rule p ps=native_absent_none_rule"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))"
      by (simp add: native_absent_none_rule_def finite_native_rule_eq_iff)
    have eqs: "f [0]=x \<and> Payload_Term []=key \<and> Pair_Term (Payload_Term []) (f [1])=store_term val T"
      using concl by (simp add: p; blast)
    have key: "key=Payload_Term []" using eqs by (rule sym[OF conjunct1[OF conjunct2]])
    have store: "store_term val T=Pair_Term (Payload_Term []) (f [1])"
      using eqs by (rule sym[OF conjunct2[OF conjunct2]])
    obtain v l r where T: "T=Store_Node v l r" and option: "Payload_Term []=store_option_term val v"
      using store by (auto simp: store_term_shapes)
    have "v=None" using option by (simp add: store_option_term_absent_rev)
    then show ?thesis using key T by simp
  next
    assume F: "finite_native_rule p ps=native_absent_left_leaf_rule a"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)) (Finite_Pattern_Payload []))"
      and ps: "set ps={([0],(a,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))}"
      by (simp_all add: native_absent_left_leaf_rule_def finite_native_rule_eq_iff)
    have x: "x=f [0]" and key: "key=Pair_Term (Payload_Term []) (f [1])"
      and store: "store_term val T=Payload_Term []"
      using concl by (simp_all add: p eq_commute[of "Payload_Term []"])
    have T: "T=Empty_Store" using store by (simp add: store_term_shapes)
    have "(a,Pair_Term (f [0]) (Pair_Term (f [1]) (Payload_Term [])))\<in>positive_meaning P"
      using prem by (simp add: ps)
    then have "(a,Pair_Term x (Pair_Term (f [1]) (store_term val (store_descend False T))))\<in>positive_meaning P"
      using x T by simp
    then show ?thesis using key by (auto simp: bit_term_def)
  next
    assume F: "finite_native_rule p ps=native_absent_left_rule a"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
          (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4))))"
      and ps: "set ps={([0],(a,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 3))))}"
      by (simp_all add: native_absent_left_rule_def finite_native_rule_eq_iff)
    have x: "x=f [0]" and key: "key=Pair_Term (Payload_Term []) (f [1])"
      and store: "store_term val T=Pair_Term (f [2]) (Pair_Term (f [3]) (f [4]))"
      using concl by (simp_all add: p eq_commute[of "Payload_Term []"])
    obtain v l r where T: "T=Store_Node v l r"
      and children: "Pair_Term (f [3]) (f [4])=Pair_Term (store_term val l) (store_term val r)"
      using store by (auto simp: store_term_shapes)
    have left: "f [3]=store_term val l" using children by simp
    have "(a,Pair_Term (f [0]) (Pair_Term (f [1]) (f [3])))\<in>positive_meaning P"
      using prem by (simp add: ps)
    then have "(a,Pair_Term x (Pair_Term (f [1]) (store_term val (store_descend False T))))\<in>positive_meaning P"
      using x T left by simp
    then show ?thesis using key by (auto simp: bit_term_def)
  next
    assume F: "finite_native_rule p ps=native_absent_right_leaf_rule a"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
            (native_var 1)) (Finite_Pattern_Payload []))"
      and ps: "set ps={([0],(a,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))}"
      by (simp_all add: native_absent_right_leaf_rule_def finite_native_rule_eq_iff)
    have x: "x=f [0]"
      and key: "key=Pair_Term (Pair_Term (Payload_Term []) (Payload_Term [])) (f [1])"
      and store: "store_term val T=Payload_Term []"
      using concl by (simp_all add: p eq_commute[of "Payload_Term []"])
    have T: "T=Empty_Store" using store by (simp add: store_term_shapes)
    have "(a,Pair_Term (f [0]) (Pair_Term (f [1]) (Payload_Term [])))\<in>positive_meaning P"
      using prem by (simp add: ps)
    then have "(a,Pair_Term x (Pair_Term (f [1]) (store_term val (store_descend True T))))\<in>positive_meaning P"
      using x T by simp
    then show ?thesis using key by (auto simp: bit_term_def)
  next
    assume F: "finite_native_rule p ps=native_absent_right_rule a"
    then have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
            (native_var 1))
          (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4))))"
      and ps: "set ps={([0],(a,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 4))))}"
      by (simp_all add: native_absent_right_rule_def finite_native_rule_eq_iff)
    have x: "x=f [0]"
      and key: "key=Pair_Term (Pair_Term (Payload_Term []) (Payload_Term [])) (f [1])"
      and store: "store_term val T=Pair_Term (f [2]) (Pair_Term (f [3]) (f [4]))"
      using concl by (simp_all add: p eq_commute[of "Payload_Term []"])
    obtain v l r where T: "T=Store_Node v l r"
      and children: "Pair_Term (f [3]) (f [4])=Pair_Term (store_term val l) (store_term val r)"
      using store by (auto simp: store_term_shapes)
    have right: "f [4]=store_term val r" using children by simp
    have "(a,Pair_Term (f [0]) (Pair_Term (f [1]) (f [4])))\<in>positive_meaning P"
      using prem by (simp add: ps)
    then have "(a,Pair_Term x (Pair_Term (f [1]) (store_term val (store_descend True T))))\<in>positive_meaning P"
      using x T right by simp
    then show ?thesis using key by (auto simp: bit_term_def)
  qed
qed

lemma sound:
  assumes holds: "(a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  shows "\<exists>bs. key=path_term bs \<and> store_lookup T bs=None"
  using holds
proof (induction key arbitrary: T)
  case (Target_Term t)
  show ?case using unfold[OF Target_Term.prems] by auto
next
  case (Payload_Term w)
  have "Payload_Term w=Payload_Term [] \<and> store_lookup T []=None"
    using unfold[OF Payload_Term.prems] by auto
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Pair_Term u w)
  obtain b where key: "Pair_Term u w=Pair_Term (bit_term b) w"
    and inner: "(a,Pair_Term x (Pair_Term w (store_term val (store_descend b T))))\<in>positive_meaning P"
    using unfold[OF Pair_Term.prems] by auto
  obtain bs where w: "w=path_term bs" and lookup: "store_lookup (store_descend b T) bs=None"
    using Pair_Term.IH(2)[of "store_descend b T"] inner by blast
  show ?case
  proof (intro exI conjI)
    show "Pair_Term u w=path_term (b#bs)" using key w by simp
    show "store_lookup T (b#bs)=None" using lookup by (simp only: store_lookup_descend)
  qed
qed

theorem exact:
  assumes valued: "\<And>y. term_formed (val y)"
  shows "(a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<exists>bs. key=path_term bs \<and> store_lookup T bs=None)"
proof
  assume holds: "(a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  show "term_formed x \<and> (\<exists>bs. key=path_term bs \<and> store_lookup T bs=None)"
    using holds_formed[OF holds] sound[OF holds] by simp
next
  assume "term_formed x \<and> (\<exists>bs. key=path_term bs \<and> store_lookup T bs=None)"
  then obtain bs where xf: "term_formed x" and key: "key=path_term bs"
    and lookup: "store_lookup T bs=None" by blast
  have "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val T)))\<in>positive_meaning P"
    using lookup
  proof (induction bs arbitrary: T)
    case Nil
    show ?case
    proof (cases T)
      case Empty_Store
      have "(a,evaluate_pattern (native_values [x]) (decode_finite_pattern
          (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
            (Finite_Pattern_Payload [])))))\<in>positive_meaning P"
        by (rule law.step_at[where c="[0]" and ps="[]"])
          (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_empty_rule_def xf)
      then show ?thesis by (simp add: Empty_Store)
    next
      case (Store_Node v l r)
      have none: "v=None" using Nil.prems by (simp add: Store_Node)
      have lf: "term_formed (store_term val l)" by (rule store_term_formed) (rule valued)
      have rf: "term_formed (store_term val r)" by (rule store_term_formed) (rule valued)
      have formed: "term_formed (Pair_Term (store_term val l) (store_term val r))" using lf rf by simp
      have "(a,evaluate_pattern (native_values [x,Pair_Term (store_term val l) (store_term val r)])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
            (Finite_Pattern_Payload []) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
              (native_var 1))))))\<in>positive_meaning P"
        by (rule law.step_at[where c="[1]" and ps="[]"])
          (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_none_rule_def xf formed lf rf)
      then show ?thesis by (simp add: Store_Node none store_option_term_def)
    qed
  next
    case (Cons b bs)
    have inner: "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val (store_descend b T))))\<in>positive_meaning P"
      by (rule Cons.IH[of "store_descend b T"]) (use Cons.prems in \<open>simp only: store_lookup_descend\<close>)
    show ?case
    proof (cases T)
      case Empty_Store
      have premise: "(a,Pair_Term x (Pair_Term (path_term bs) (Payload_Term [])))\<in>positive_meaning P"
        using inner by (simp add: Empty_Store)
      show ?thesis
      proof (cases b)
        case False
        have "(a,evaluate_pattern (native_values [x,path_term bs]) (decode_finite_pattern
            (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
              (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
              (Finite_Pattern_Payload [])))))\<in>positive_meaning P"
          by (rule law.step_at[where c="[2]" and ps="[([0],(a,Finite_Pattern_Pair (native_var 0)
              (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))]"])
            (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_left_leaf_rule_def xf premise)
        then show ?thesis by (simp add: Empty_Store False bit_term_def)
      next
        case True
        have "(a,evaluate_pattern (native_values [x,path_term bs]) (decode_finite_pattern
            (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
              (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
                (native_var 1)) (Finite_Pattern_Payload [])))))\<in>positive_meaning P"
          by (rule law.step_at[where c="[4]" and ps="[([0],(a,Finite_Pattern_Pair (native_var 0)
              (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Payload []))))]"])
            (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_right_leaf_rule_def xf premise)
        then show ?thesis by (simp add: Empty_Store True bit_term_def)
      qed
    next
      case (Store_Node v l r)
      have formed: "term_formed (store_option_term val v)" "term_formed (store_term val l)"
        "term_formed (store_term val r)"
        by (simp_all add: store_option_term_formed[OF valued] store_term_formed[OF valued])
      show ?thesis
      proof (cases b)
        case False
        have premise: "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val l)))\<in>positive_meaning P"
          using inner by (simp add: Store_Node False)
        have "(a,evaluate_pattern (native_values [x,path_term bs,store_option_term val v,
            store_term val l,store_term val r]) (decode_finite_pattern
            (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
              (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))
              (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3)
                (native_var 4)))))))\<in>positive_meaning P"
          by (rule law.step_at[where c="[3]" and ps="[([0],(a,Finite_Pattern_Pair (native_var 0)
              (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"])
            (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_left_rule_def xf formed premise)
        then show ?thesis by (simp add: Store_Node False bit_term_def)
      next
        case True
        have premise: "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val r)))\<in>positive_meaning P"
          using inner by (simp add: Store_Node True)
        have "(a,evaluate_pattern (native_values [x,path_term bs,store_option_term val v,
            store_term val l,store_term val r]) (decode_finite_pattern
            (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair
              (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
                (native_var 1))
              (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3)
                (native_var 4)))))))\<in>positive_meaning P"
          by (rule law.step_at[where c="[5]" and ps="[([0],(a,Finite_Pattern_Pair (native_var 0)
              (Finite_Pattern_Pair (native_var 1) (native_var 4))))]"])
            (simp_all add: insert_Diff_if native_store_absent_rules_def native_absent_right_rule_def xf formed premise)
        then show ?thesis by (simp add: Store_Node True bit_term_def)
      qed
    qed
  qed
  then show "(a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P" using key by simp
qed

text \<open>
  The contract at a path key, the form its consumers read, and the two statements that keep absence
  apart from the search: a store that holds a value at a key has no absence there, whatever that value
  is, and a key that is no path has none either.
\<close>

theorem exact_at_path:
  assumes valued: "\<And>y. term_formed (val y)"
  shows "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val T)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> store_lookup T bs=None"
  using exact[where val=val and key="path_term bs",OF valued] by (simp add: path_term_injective)

theorem absent_not_at_value:
  assumes held: "store_lookup T bs=Some v"
  shows "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val T)))\<notin>positive_meaning P"
proof
  assume "(a,Pair_Term x (Pair_Term (path_term bs) (store_term val T)))\<in>positive_meaning P"
  then obtain cs where key: "path_term bs=path_term cs" and lookup: "store_lookup T cs=None"
    using sound by blast
  show False using held lookup key by (simp add: path_term_injective)
qed

theorem absent_refuses_unpresented:
  assumes "\<nexists>bs. key=path_term bs"
  shows "(a,Pair_Term x (Pair_Term key (store_term val T)))\<notin>positive_meaning P"
  using assms sound by blast

end

text \<open>
  The search and absence never hold of one key and store: the search's key is a path at which the store
  holds a value, absence's a path at which it holds none, and a path is determined by its term. That is
  exclusion; neither program is the negation of the other, and a key that is no path has neither.
\<close>

theorem store_search_absent_exclusive:
  assumes search: "native_store_search_program P k ch" and absent: "native_store_absent_program P a"
  shows "\<not>((k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P \<and>
    (a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P)"
proof
  assume both: "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P \<and>
    (a,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  obtain bs v where found: "key=path_term bs" "store_lookup T bs=Some v"
    using native_store_search_program.sound[OF search] both by blast
  obtain cs where none: "key=path_term cs" "store_lookup T cs=None"
    using native_store_absent_program.sound[OF absent] both by blast
  show False using found none by (simp add: path_term_injective)
qed

section \<open>A path store is built from its rows\<close>

text \<open>
  The store of a list of rows holds, at each row's path, a value of a row at that path: it is the existing
  store updated once per row. Whatever the rows, a value found is a row's value; where the rows are
  single-valued, as rows repeated with one value are, looking a path up returns exactly the value its rows hold.
\<close>

definition path_store :: "(bool list\<times>'v) list \<Rightarrow> 'v binary_path_store" where
  "path_store rows=fold (\<lambda>(k,v) T. store_update T k (Some v)) rows Empty_Store"

lemma path_store_fold_found:
  assumes "store_lookup (fold (\<lambda>(k,v) T. store_update T k (Some v)) rows T) q=Some v"
  shows "(q,v)\<in>set rows \<or> store_lookup T q=Some v"
  using assms
proof (induction rows arbitrary: T)
  case Nil
  then show ?case by simp
next
  case (Cons r rows)
  obtain k w where r: "r=(k,w)" by (cases r)
  have "(q,v)\<in>set rows \<or> store_lookup (store_update T k (Some w)) q=Some v"
    using Cons.IH[of "store_update T k (Some w)"] Cons.prems by (simp add: r)
  then show ?case by (auto simp: r split: if_splits)
qed

lemma path_store_found:
  assumes "store_lookup (path_store rows) q=Some v"
  shows "(q,v)\<in>set rows"
  using path_store_fold_found[OF assms[unfolded path_store_def]] by simp

lemma path_store_fold_lookup:
  assumes sv: "single_valued (set rows)"
  shows "store_lookup (fold (\<lambda>(k,v) T. store_update T k (Some v)) rows T) q=Some v \<longleftrightarrow>
    (q,v)\<in>set rows \<or> (q\<notin>fst ` set rows \<and> store_lookup T q=Some v)"
  using sv
proof (induction rows arbitrary: T)
  case Nil
  then show ?case by simp
next
  case (Cons r rows)
  obtain k w where r: "r=(k,w)" by (cases r)
  have rest: "single_valued (set rows)" using Cons.prems by (auto simp: single_valued_def)
  have head: "\<And>u. (k,u)\<in>set rows \<Longrightarrow> u=w" using Cons.prems r by (auto simp: single_valued_def)
  have "store_lookup (fold (\<lambda>(k,v) T. store_update T k (Some v)) (r#rows) T) q=Some v \<longleftrightarrow>
      (q,v)\<in>set rows \<or> (q\<notin>fst ` set rows \<and> store_lookup (store_update T k (Some w)) q=Some v)"
    using Cons.IH[OF rest] by (simp add: r)
  also have "\<dots> \<longleftrightarrow> (q,v)\<in>set (r#rows) \<or> (q\<notin>fst ` set (r#rows) \<and> store_lookup T q=Some v)"
  proof (cases "q=k")
    case True
    show ?thesis
    proof
      assume "(q,v)\<in>set rows \<or> (q\<notin>fst ` set rows \<and> store_lookup (store_update T k (Some w)) q=Some v)"
      then show "(q,v)\<in>set (r#rows) \<or> (q\<notin>fst ` set (r#rows) \<and> store_lookup T q=Some v)"
        using True by (auto simp: r)
    next
      assume "(q,v)\<in>set (r#rows) \<or> (q\<notin>fst ` set (r#rows) \<and> store_lookup T q=Some v)"
      then have "(q,v)\<in>set rows \<or> (q=k \<and> v=w)" using True by (auto simp: r)
      then show "(q,v)\<in>set rows \<or> (q\<notin>fst ` set rows \<and> store_lookup (store_update T k (Some w)) q=Some v)"
      proof
        assume qv: "q=k \<and> v=w"
        show ?thesis
        proof (cases "q\<in>fst ` set rows")
          case True
          then obtain u where "(k,u)\<in>set rows" using qv by force
          then show ?thesis using head qv by auto
        next
          case False
          then show ?thesis using qv by simp
        qed
      qed simp
    qed
  next
    case False
    then show ?thesis by (auto simp: r)
  qed
  finally show ?case .
qed

theorem path_store_lookup:
  assumes sv: "single_valued (set rows)"
  shows "store_lookup (path_store rows) q=Some v \<longleftrightarrow> (q,v)\<in>set rows"
  using path_store_fold_lookup[OF sv, of Empty_Store q v] by (simp add: path_store_def)

text \<open>
  A key is present in a store built from rows exactly when it is a key of those rows, whatever the rows
  are: presence needs no single-valuedness, only the lookup of the replacements the build makes.
\<close>

lemma path_store_fold_present:
  "store_lookup (fold (\<lambda>(k,v) T. store_update T k (Some v)) rows T) q\<noteq>None \<longleftrightarrow>
    q\<in>fst ` set rows \<or> store_lookup T q\<noteq>None"
  by (induction rows arbitrary: T) (auto simp: store_lookup_update split: if_splits)

lemma path_store_present: "store_lookup (path_store rows) q\<noteq>None \<longleftrightarrow> q\<in>fst ` set rows"
  using path_store_fold_present[of rows Empty_Store q] by (simp add: path_store_def)

section \<open>Executable paths and stores\<close>

definition finite_bit :: "bool \<Rightarrow> finite_factor_term" where
  "finite_bit b=(if b then Finite_Pair (Finite_Payload []) (Finite_Payload []) else Finite_Payload [])"

definition finite_path :: "bool list \<Rightarrow> finite_factor_term" where
  "finite_path bs=finite_data_list (map finite_bit bs)"

lemma decode_finite_bit [simp]: "decode_finite_term (finite_bit b)=bit_term b"
  by (cases b) (simp_all add: finite_bit_def bit_term_def)

lemma decode_finite_path [simp]: "decode_finite_term (finite_path bs)=path_term bs"
  by (induction bs) (simp_all add: finite_path_def)

lemma finite_path_injective: "inj finite_path"
proof (rule injI)
  fix bs cs assume "finite_path bs=finite_path cs"
  then have "decode_finite_term (finite_path bs)=decode_finite_term (finite_path cs)" by simp
  then show "bs=cs" by (simp add: path_term_injective)
qed

definition finite_store_option :: "('v \<Rightarrow> finite_factor_term) \<Rightarrow> 'v option \<Rightarrow> finite_factor_term" where
  "finite_store_option val v=(case v of None \<Rightarrow> Finite_Payload [] | Some x \<Rightarrow> Finite_Pair (Finite_Payload []) (val x))"

fun finite_store :: "('v \<Rightarrow> finite_factor_term) \<Rightarrow> 'v binary_path_store \<Rightarrow> finite_factor_term" where
  "finite_store val Empty_Store=Finite_Payload []"
| "finite_store val (Store_Node v l r)=Finite_Pair (finite_store_option val v)
    (Finite_Pair (finite_store val l) (finite_store val r))"

lemma decode_finite_store:
  "decode_finite_term (finite_store val T)=store_term (decode_finite_term \<circ> val) T"
  by (induction T) (simp_all add: finite_store_option_def store_option_term_def split: option.splits)

text \<open>
  A path presented by its executable term is read back bit by bit: a pair of leaves is the one direction and
  every other bit the other, so reading a presented path returns it.
\<close>

fun finite_path_bits :: "finite_factor_term \<Rightarrow> bool list" where
  "finite_path_bits (Finite_Pair b rest)=(b\<noteq>Finite_Payload [])#finite_path_bits rest"
| "finite_path_bits (Finite_Payload v)=[]"
| "finite_path_bits (Finite_Target t)=[]"

lemma finite_path_bits_path [simp]: "finite_path_bits (finite_path bs)=bs"
  by (induction bs) (simp_all add: finite_path_def finite_bit_def)

text \<open>
  The store of the rows is a notion of its rows, not of the order in which the rows were inserted, only
  where the rows are single-valued: that is the premise under which the lookup contract above holds, and
  every use of a path store states it.
\<close>

section \<open>The presentations of the path store\<close>

text \<open>
  A path and a store are presented by their executable terms; each presentation is injective whenever
  the presentation of the values it holds is, and formed whenever those are.
\<close>

lemma finite_store_option_injective [intro]:
  assumes injective: "inj f"
  shows "inj (finite_store_option f)"
proof (rule injI)
  fix x y assume "finite_store_option f x=finite_store_option f y"
  then show "x=y" using injective by (cases x; cases y) (auto simp: finite_store_option_def dest: injD)
qed

lemma finite_store_injective [intro]:
  assumes injective: "inj f"
  shows "inj (finite_store f)"
proof (rule injI)
  fix S T show "finite_store f S=finite_store f T \<Longrightarrow> S=T"
  proof (induction S arbitrary: T)
    case Empty_Store
    then show ?case by (cases T) simp_all
  next
    case (Store_Node v l r)
    from Store_Node.prems obtain v' l' r' where T: "T=Store_Node v' l' r'"
      and head: "finite_store_option f v=finite_store_option f v'"
      and left: "finite_store f l=finite_store f l'" and right: "finite_store f r=finite_store f r'"
      by (cases T) simp_all
    have "v=v'" by (rule injD[OF finite_store_option_injective[OF injective] head])
    moreover have "l=l'" by (rule Store_Node.IH(1)[OF left])
    moreover have "r=r'" by (rule Store_Node.IH(2)[OF right])
    ultimately show ?case by (simp add: T)
  qed
qed

lemma finite_path_formed [simp]: "finite_term_formed (finite_path bs)"
  by (induction bs) (simp_all add: finite_path_def finite_bit_def octets_formed_def)

lemma finite_store_option_formed:
  assumes "\<And>x. finite_term_formed (f x)"
  shows "finite_term_formed (finite_store_option f v)"
  using assms by (cases v) (simp_all add: finite_store_option_def octets_formed_def)

lemma finite_store_formed:
  assumes "\<And>x. finite_term_formed (f x)"
  shows "finite_term_formed (finite_store f T)"
  by (induction T) (simp_all add: octets_formed_def finite_store_option_formed[OF assms])

text \<open>
  Two stores with equal presentations hold, at every path where the one holds a value, a value of the
  other with the same presentation: this is what the presentation of a store identifies when the
  presentation of its values is injective only on the values it holds.
\<close>

lemma finite_store_lookup_agree:
  assumes "finite_store f S=finite_store f T" "store_lookup S q=Some v"
  shows "\<exists>w. store_lookup T q=Some w \<and> f w=f v"
  using assms
proof (induction q arbitrary: S T)
  case Nil
  from Nil.prems(2) obtain l r where S: "S=Store_Node (Some v) l r" by (cases S) simp_all
  from Nil.prems(1) S obtain v1 l' r' where T: "T=Store_Node v1 l' r'"
    and H: "finite_store_option f (Some v)=finite_store_option f v1"
    by (cases T) simp_all
  show ?case using H T by (cases v1) (simp_all add: finite_store_option_def)
next
  case (Cons b bs)
  from Cons.prems(2) obtain v0 l r where S: "S=Store_Node v0 l r" by (cases S; cases b) simp_all
  from Cons.prems(1) S obtain v1 l' r' where T: "T=Store_Node v1 l' r'"
    and L: "finite_store f l=finite_store f l'" and R: "finite_store f r=finite_store f r'"
    by (cases T) simp_all
  show ?case
  proof (cases b)
    case True
    have "store_lookup r bs=Some v" using Cons.prems(2) S True by simp
    from Cons.IH[OF R this] show ?thesis using T True by simp
  next
    case False
    have "store_lookup l bs=Some v" using Cons.prems(2) S False by simp
    from Cons.IH[OF L this] show ?thesis using T False by simp
  qed
qed

section \<open>A path store is canonical, so its lookups determine it\<close>

lemma path_store_canonical: "store_canonical (path_store rows)"
  unfolding path_store_def by (rule path_store_fold_canonical) simp

text \<open>
  The store of a single-valued listing is a function of the rows it holds: two such listings of one set
  of rows, in whatever order and with whatever repetitions, build the same store.
\<close>

theorem path_store_rows:
  assumes sv: "single_valued (set rows)" and sv': "single_valued (set rows')" and same: "set rows=set rows'"
  shows "path_store rows=path_store rows'"
proof (rule store_canonical_lookup_eq[OF path_store_canonical path_store_canonical])
  fix q
  have some: "store_lookup (path_store rows) q=Some v \<longleftrightarrow> store_lookup (path_store rows') q=Some v" for v
    using path_store_lookup[OF sv] path_store_lookup[OF sv'] same by simp
  show "store_lookup (path_store rows) q=store_lookup (path_store rows') q"
  proof (cases "store_lookup (path_store rows) q")
    case None
    then show ?thesis using some by (cases "store_lookup (path_store rows') q") auto
  next
    case (Some v)
    then show ?thesis using some[of v] by simp
  qed
qed

section \<open>A store's presentation reads only the values it holds\<close>

lemma store_term_cong:
  assumes same: "\<And>bs v. store_lookup T bs=Some v \<Longrightarrow> f v=g v"
  shows "store_term f T=store_term g T"
  using same
proof (induction T)
  case Empty_Store
  then show ?case by simp
next
  case (Store_Node v l r)
  have held: "store_option_term f v=store_option_term g v"
  proof (cases v)
    case None
    then show ?thesis by (simp add: store_option_term_def)
  next
    case (Some x)
    have "store_lookup (Store_Node v l r) []=Some x" using Some by simp
    then have "f x=g x" by (rule Store_Node.prems)
    then show ?thesis using Some by (simp add: store_option_term_def)
  qed
  have left: "store_term f l=store_term g l"
  proof (rule Store_Node.IH(1))
    fix bs x assume "store_lookup l bs=Some x"
    then have "store_lookup (Store_Node v l r) (False#bs)=Some x" by simp
    then show "f x=g x" by (rule Store_Node.prems)
  qed
  have right: "store_term f r=store_term g r"
  proof (rule Store_Node.IH(2))
    fix bs x assume "store_lookup r bs=Some x"
    then have "store_lookup (Store_Node v l r) (True#bs)=Some x" by simp
    then show "f x=g x" by (rule Store_Node.prems)
  qed
  show ?case by (simp only: store_term.simps held left right)
qed

section \<open>A row is its path with its value, and a table is the store of its rows\<close>

text \<open>
  A row of a table is presented as the pair of its path and its value, and a table, given as a listing
  of its rows, as the store of that listing. The readiness line and the development's rows are instances,
  each with the presentation of its own values.
\<close>

definition finite_store_row ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> bool list\<times>'v \<Rightarrow> finite_factor_term" where
  "finite_store_row val=finite_pair_presentation finite_path val"

definition finite_listing_store ::
    "('v \<Rightarrow> finite_factor_term) \<Rightarrow> (bool list\<times>'v) list \<Rightarrow> finite_factor_term" where
  "finite_listing_store val rows=finite_store val (path_store rows)"

text \<open>
  A row presenter is injective on the rows whose values its value presentation is injective on, so a row
  whose values are presented injectively only where they occur is still presented injectively.
\<close>

lemma finite_store_row_injective_on:
  assumes injective: "inj_on val A"
  shows "inj_on (finite_store_row val) {r. snd r\<in>A}"
proof (rule inj_onI)
  fix r s assume r: "r\<in>{r. snd r\<in>A}" and s: "s\<in>{r. snd r\<in>A}"
    and same: "finite_store_row val r=finite_store_row val s"
  have paths: "finite_path (fst r)=finite_path (fst s)" and presented: "val (snd r)=val (snd s)"
    using same by (simp_all add: finite_store_row_def finite_pair_presentation_def)
  have "fst r=fst s" by (rule injD[OF finite_path_injective paths])
  moreover have "snd r=snd s" by (rule inj_onD[OF injective presented]) (use r s in simp_all)
  ultimately show "r=s" by (rule prod_eqI)
qed

lemma finite_store_row_injective [intro]:
  assumes "inj val"
  shows "inj (finite_store_row val)"
  using finite_store_row_injective_on[OF assms] by simp

lemma finite_store_row_formed:
  assumes "finite_term_formed (val v)"
  shows "finite_term_formed (finite_store_row val (l,v))"
  using assms by (simp add: finite_store_row_def)

lemma finite_listing_store_formed:
  assumes "\<And>v. finite_term_formed (val v)"
  shows "finite_term_formed (finite_listing_store val rows)"
  unfolding finite_listing_store_def by (rule finite_store_formed[OF assms])

lemma decode_finite_store_row:
  "decode_finite_term (finite_store_row val (l,v))=Pair_Term (path_term l) (decode_finite_term (val v))"
  by (simp add: finite_store_row_def)

lemma decode_finite_listing_store:
  "decode_finite_term (finite_listing_store val rows)=store_term (decode_finite_term \<circ> val) (path_store rows)"
  by (simp add: finite_listing_store_def decode_finite_store)

text \<open>
  A table presents the rows it holds and nothing of the order they were listed in: over single-valued
  listings, whose values are presented injectively on the values they hold, equal presentations hold
  the same rows, and listings of the same rows have equal presentations.
\<close>

theorem finite_listing_store_identifies:
  assumes presented: "inj_on val (snd ` set rows \<union> snd ` set rows')"
    and sv: "single_valued (set rows)" and sv': "single_valued (set rows')"
    and same: "finite_listing_store val rows=finite_listing_store val rows'"
  shows "set rows=set rows'"
proof -
  have into: "(q,v)\<in>set ys" if xv: "(q,v)\<in>set xs"
      and eq: "finite_listing_store val xs=finite_listing_store val ys"
      and svx: "single_valued (set xs)" and inj: "inj_on val (snd ` set xs \<union> snd ` set ys)" for xs ys q v
  proof -
    have "store_lookup (path_store xs) q=Some v" using path_store_lookup[OF svx] xv by simp
    from finite_store_lookup_agree[OF eq[unfolded finite_listing_store_def] this]
    obtain w where w: "store_lookup (path_store ys) q=Some w" "val w=val v" by blast
    have wy: "(q,w)\<in>set ys" by (rule path_store_found[OF w(1)])
    have wA: "w\<in>snd ` set xs \<union> snd ` set ys" using wy by force
    have vA: "v\<in>snd ` set xs \<union> snd ` set ys" using xv by force
    have "w=v" by (rule inj_onD[OF inj w(2) wA vA])
    with wy show ?thesis by simp
  qed
  have presented': "inj_on val (snd ` set rows' \<union> snd ` set rows)" using presented by (simp add: Un_commute)
  show ?thesis
  proof (rule set_eqI)
    fix x
    show "x\<in>set rows \<longleftrightarrow> x\<in>set rows'"
      using into[OF _ same sv presented, where q="fst x" and v="snd x"]
        into[OF _ same[symmetric] sv' presented', where q="fst x" and v="snd x"] by (metis prod.collapse)
  qed
qed

section \<open>A list of paths\<close>

text \<open>
  A list of paths is the data list of the paths: one notion, which the keys a row cites, the families a
  request's body holds and every list of keys a native definition reads present alike.
\<close>

definition keys_term :: "bool list list \<Rightarrow> factor_term" where
  "keys_term ks=data_list_term (map path_term ks)"

lemma keys_term_formed [simp]: "term_formed (keys_term ks)"
  by (simp add: keys_term_def data_list_term_formed)

lemma keys_term_pair [simp]:
  "keys_term ks=Pair_Term a b \<longleftrightarrow> (\<exists>k ks'. ks=k#ks' \<and> a=path_term k \<and> b=keys_term ks')"
  "Pair_Term a b=keys_term ks \<longleftrightarrow> (\<exists>k ks'. ks=k#ks' \<and> a=path_term k \<and> b=keys_term ks')"
  by (cases ks; auto simp: keys_term_def)+

lemma keys_term_Cons: "keys_term (k#ks)=Pair_Term (path_term k) (keys_term ks)"
  by (simp add: keys_term_def)

lemma keys_term_eq_iff: "keys_term ks=keys_term ks' \<longleftrightarrow> ks=ks'"
proof (induction ks arbitrary: ks')
  case Nil
  show ?case by (cases ks') (simp_all add: keys_term_def)
next
  case (Cons k ks)
  show ?case by (cases ks') (simp_all add: keys_term_def path_term_injective Cons.IH[unfolded keys_term_def])
qed

lemma keys_term_inj: "inj keys_term"
  by (rule injI) (simp only: keys_term_eq_iff)

text \<open>
  A store presented through a value map reads only the values it holds, so the search's contract needs
  those values formed and no other: the contract above, through any formed map agreeing with the
  presentation where the store holds a value (@{thm store_term_cong}).
\<close>

context native_store_search_program
begin

theorem exact_held:
  assumes held: "\<And>bs y. store_lookup S bs=Some y \<Longrightarrow> term_formed (val y)"
  shows "(k,Pair_Term x (Pair_Term key (store_term val S)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup S bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P)"
proof -
  define f where "f=(\<lambda>y. if term_formed (val y) then val y else Payload_Term [])"
  have ff: "term_formed (f y)" for y by (simp add: f_def octets_formed_def)
  have agree: "f y=val y" if "store_lookup S bs=Some y" for bs y using held[OF that] by (simp add: f_def)
  have same: "store_term val S=store_term f S" by (rule store_term_cong) (erule agree[symmetric])
  have "(k,Pair_Term x (Pair_Term key (store_term val S)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup S bs=Some v \<and> (ch,Pair_Term x (f v))\<in>positive_meaning P)"
    unfolding same by (rule exact) (rule ff)
  also have "\<dots> \<longleftrightarrow>
    term_formed x \<and> (\<exists>bs v. key=path_term bs \<and> store_lookup S bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P)"
    using agree by fastforce
  finally show ?thesis .
qed

text \<open>
  At a key where the store holds a value, the search holds exactly when the check holds of that value.
\<close>

theorem held_at:
  assumes held: "\<And>bs y. store_lookup S bs=Some y \<Longrightarrow> term_formed (val y)"
    and stored: "store_lookup S bs=Some v"
  shows "(k,Pair_Term x (Pair_Term (path_term bs) (store_term val S)))\<in>positive_meaning P \<longleftrightarrow>
    (ch,Pair_Term x (val v))\<in>positive_meaning P"
  using stored by (auto simp: exact_held[OF held] path_term_injective dest: positive_meaning_term_formed)

end

theorem finite_listing_store_exact:
  assumes presented: "inj_on val (snd ` set rows \<union> snd ` set rows')"
    and sv: "single_valued (set rows)" and sv': "single_valued (set rows')"
  shows "finite_listing_store val rows=finite_listing_store val rows' \<longleftrightarrow> set rows=set rows'"
  using finite_listing_store_identifies[OF presented sv sv'] path_store_rows[OF sv sv']
  by (auto simp: finite_listing_store_def)

section \<open>A table of rows is the store of any listing of them\<close>

text \<open>
  A row presented as a term is the pair of its path and its value, read back by its path's own reader. A
  finite set of presented rows is presented as the path store of the rows read from it; over rows whose
  paths are distinct, that store is the store of every listing of those rows
  (@{thm [source] path_store_rows}), so its word is a function of the rows and of no listing, and equal
  words identify the rows (@{thm [source] finite_listing_store_identifies}).
\<close>

definition finite_row_read :: "finite_factor_term \<Rightarrow> bool list\<times>finite_factor_term" where
  "finite_row_read t=(case t of Finite_Pair l v \<Rightarrow> (finite_path_bits l,v) | _ \<Rightarrow> ([],t))"

lemma finite_row_read_row [simp]: "finite_row_read (finite_store_row val (l,v))=(l,val v)"
  by (simp add: finite_row_read_def finite_store_row_def finite_pair_presentation_def)

definition finite_rows_table :: "finite_factor_term fset \<Rightarrow> finite_factor_term" where
  "finite_rows_table T=finite_listing_store id (map finite_row_read (ordered_finite_terms T))"

theorem finite_rows_table_listing:
  assumes rows: "set rows=finite_row_read ` fset T" and sv: "single_valued (set rows)"
  shows "finite_rows_table T=finite_listing_store id rows"
  unfolding finite_rows_table_def finite_listing_store_def
  by (rule arg_cong[where f="finite_store id"], rule path_store_rows)
    (use rows sv in \<open>simp_all add: ordered_finite_terms_set\<close>)

theorem finite_rows_table_identifies:
  assumes shape: "\<And>t. t\<in>fset T \<union> fset T' \<Longrightarrow> \<exists>l v. t=Finite_Pair (finite_path l) v"
    and sv: "single_valued (finite_row_read ` fset T)" and sv': "single_valued (finite_row_read ` fset T')"
    and same: "finite_rows_table T=finite_rows_table T'"
  shows "T=T'"
proof -
  have "set (map finite_row_read (ordered_finite_terms T))=set (map finite_row_read (ordered_finite_terms T'))"
    by (rule finite_listing_store_identifies[OF _ _ _ same[unfolded finite_rows_table_def]])
      (use sv sv' in \<open>simp_all add: ordered_finite_terms_set\<close>)
  then have images: "finite_row_read ` fset T=finite_row_read ` fset T'" by (simp add: ordered_finite_terms_set)
  have "inj_on finite_row_read (fset T \<union> fset T')"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>fset T \<union> fset T'" and y: "y\<in>fset T \<union> fset T'"
      and read: "finite_row_read x=finite_row_read y"
    obtain l v where "x=Finite_Pair (finite_path l) v" using shape[OF x] by blast
    moreover obtain l' v' where "y=Finite_Pair (finite_path l') v'" using shape[OF y] by blast
    ultimately show "x=y" using read by (simp add: finite_row_read_def)
  qed
  then have "fset T=fset T'"
    by (rule inj_on_image_eq_iff[THEN iffD1, OF _ _ _ images]) auto
  then show ?thesis by (simp add: fset_inject)
qed

end
