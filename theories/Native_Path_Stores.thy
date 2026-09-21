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

text \<open>
  The search is read for every key, not only for a path: a key the rules do not descend by, a target or a
  payload other than the empty one, has no search that holds. A key that holds is therefore a path, and the
  value found is the value the store holds at it.
\<close>

lemma unfold:
  assumes clause: "((k,c),S)\<in>system_clauses P"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>Y"
    and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term x (Pair_Term key (store_term val T))"
  shows "(\<exists>v l r. key=Payload_Term [] \<and> T=Store_Node (Some v) l r \<and> (ch,Pair_Term x (val v))\<in>Y) \<or>
    (\<exists>key' v l r. key=Pair_Term (bit_term False) key' \<and> T=Store_Node v l r \<and>
      (k,Pair_Term x (Pair_Term key' (store_term val l)))\<in>Y) \<or>
    (\<exists>key' v l r. key=Pair_Term (bit_term True) key' \<and> T=Store_Node v l r \<and>
      (k,Pair_Term x (Pair_Term key' (store_term val r)))\<in>Y)"
proof -
  obtain F where rule: "(c,F)\<in>set (native_store_search_rules k ch)" and S: "S=decode_finite_schema F"
    using clause family by blast
  have cases: "F=native_store_found_rule ch \<or> F=native_store_left_rule k \<or> F=native_store_right_rule k"
    using rule by (auto simp: native_store_search_rules_def)
  then show ?thesis
  proof (elim disjE)
    assume F: "F=native_store_found_rule ch"
    have premise: "(ch,Pair_Term (f [0]) (f [1]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_store_found_rule_def]] by simp
    show ?thesis using shape premise
      by (auto simp: S F native_store_found_rule_def store_term_shapes store_option_term_found)
  next
    assume F: "F=native_store_left_rule k"
    have premise: "(k,Pair_Term (f [0]) (Pair_Term (f [1]) (f [3])))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_store_left_rule_def]] by simp
    show ?thesis using shape premise
      by (auto simp: S F native_store_left_rule_def bit_term_def store_term_shapes)
  next
    assume F: "F=native_store_right_rule k"
    have premise: "(k,Pair_Term (f [0]) (Pair_Term (f [1]) (f [4])))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_store_right_rule_def]] by simp
    show ?thesis using shape premise
      by (auto simp: S F native_store_right_rule_def bit_term_def store_term_shapes)
  qed
qed

lemma sound:
  assumes holds: "(k,Pair_Term x (Pair_Term key (store_term val T)))\<in>positive_meaning P"
  shows "\<exists>bs v. key=path_term bs \<and> store_lookup T bs=Some v \<and> (ch,Pair_Term x (val v))\<in>positive_meaning P"
  using holds
proof (induction key arbitrary: T)
  case (Target_Term t)
  obtain c F f where rule: "(c,F)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term (Target_Term t) (store_term val T))"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P"
    by (rule holds_cases[OF Target_Term.prems]) blast
  show ?case using unfold[OF rule_clause[OF rule] support shape] by auto
next
  case (Payload_Term w)
  obtain c F f where rule: "(c,F)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term (Payload_Term w) (store_term val T))"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P"
    by (rule holds_cases[OF Payload_Term.prems]) blast
  obtain v l r where w: "w=[]" and T: "T=Store_Node (Some v) l r"
    and found: "(ch,Pair_Term x (val v))\<in>positive_meaning P"
    using unfold[OF rule_clause[OF rule] support shape] by auto
  show ?case
  proof (intro exI conjI)
    show "Payload_Term w=path_term []" using w by simp
    show "store_lookup T []=Some v" using T by simp
    show "(ch,Pair_Term x (val v))\<in>positive_meaning P" by (rule found)
  qed
next
  case (Pair_Term a b)
  obtain c F f where rule: "(c,F)\<in>set (native_store_search_rules k ch)"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term (Pair_Term a b) (store_term val T))"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P"
    by (rule holds_cases[OF Pair_Term.prems]) blast
  have "(\<exists>key' v l r. Pair_Term a b=Pair_Term (bit_term False) key' \<and> T=Store_Node v l r \<and>
        (k,Pair_Term x (Pair_Term key' (store_term val l)))\<in>positive_meaning P) \<or>
      (\<exists>key' v l r. Pair_Term a b=Pair_Term (bit_term True) key' \<and> T=Store_Node v l r \<and>
        (k,Pair_Term x (Pair_Term key' (store_term val r)))\<in>positive_meaning P)"
    using unfold[OF rule_clause[OF rule] support shape] by auto
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
      by (rule native_step[where c="[0]" and ps="[([0],(ch,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
        (use checked xf vf lf rf in \<open>simp_all add: native_store_search_rules_def native_store_found_rule_def\<close>)
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
        by (rule native_step[where c="[1]" and
            ps="[([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"])
          (use inner xf wf lf rf pf in \<open>simp_all add: native_store_search_rules_def native_store_left_rule_def\<close>)
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
        by (rule native_step[where c="[2]" and
            ps="[([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4))))]"])
          (use inner xf wf lf rf pf in \<open>simp_all add: native_store_search_rules_def native_store_right_rule_def
            octets_formed_def\<close>)
      then show ?thesis using T True by (simp add: bit_term_def)
    qed
  qed
qed

end

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

section \<open>A canonical store is determined by its lookups\<close>

lemma store_canonical_none:
  assumes "store_canonical T" "\<And>q. store_lookup T q=None"
  shows "T=Empty_Store"
  using assms
proof (induction T)
  case Empty_Store
  then show ?case by simp
next
  case (Store_Node v l r)
  have v: "v=None" using Store_Node.prems(2)[of "[]"] by simp
  have l: "l=Empty_Store"
  proof (rule Store_Node.IH(1))
    show "store_canonical l" using Store_Node.prems(1) by simp
    show "store_lookup l q=None" for q using Store_Node.prems(2)[of "False#q"] by simp
  qed
  have r: "r=Empty_Store"
  proof (rule Store_Node.IH(2))
    show "store_canonical r" using Store_Node.prems(1) by simp
    show "store_lookup r q=None" for q using Store_Node.prems(2)[of "True#q"] by simp
  qed
  show ?case using Store_Node.prems(1) v l r by simp
qed

theorem store_canonical_lookup_eq:
  assumes "store_canonical S" "store_canonical T" "\<And>q. store_lookup S q=store_lookup T q"
  shows "S=T"
  using assms
proof (induction S arbitrary: T)
  case Empty_Store
  have "store_lookup T q=None" for q using Empty_Store.prems(3)[of q] by simp
  from store_canonical_none[OF Empty_Store.prems(2) this] show ?case by simp
next
  case (Store_Node v l r)
  note prems=Store_Node.prems and IH=Store_Node.IH
  show ?case
  proof (cases T)
    case Empty_Store
    have "store_lookup (Store_Node v l r) q=None" for q using prems(3)[of q] Empty_Store by simp
    from store_canonical_none[OF prems(1) this] show ?thesis by simp
  next
    case (Store_Node v' l' r')
    have v: "v=v'" using prems(3)[of "[]"] Store_Node by simp
    have l: "l=l'"
    proof (rule IH(1))
      show "store_canonical l" using prems(1) by simp
      show "store_canonical l'" using prems(2) Store_Node by simp
      show "store_lookup l q=store_lookup l' q" for q using prems(3)[of "False#q"] Store_Node by simp
    qed
    have r: "r=r'"
    proof (rule IH(2))
      show "store_canonical r" using prems(1) by simp
      show "store_canonical r'" using prems(2) Store_Node by simp
      show "store_lookup r q=store_lookup r' q" for q using prems(3)[of "True#q"] Store_Node by simp
    qed
    show ?thesis using Store_Node v l r by simp
  qed
qed

lemma path_store_fold_canonical:
  "store_canonical T \<Longrightarrow> store_canonical (fold (\<lambda>(k,v) T. store_update T k (Some v)) rows T)"
  by (induction rows arbitrary: T) (auto simp: split_beta intro: store_update_canonical)

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

lemma finite_store_row_injective [intro]:
  assumes "inj val"
  shows "inj (finite_store_row val)"
  unfolding finite_store_row_def by (intro finite_pair_presentation_injective finite_path_injective assms)

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

theorem finite_listing_store_exact:
  assumes presented: "inj_on val (snd ` set rows \<union> snd ` set rows')"
    and sv: "single_valued (set rows)" and sv': "single_valued (set rows')"
  shows "finite_listing_store val rows=finite_listing_store val rows' \<longleftrightarrow> set rows=set rows'"
  using finite_listing_store_identifies[OF presented sv sv'] path_store_rows[OF sv sv']
  by (auto simp: finite_listing_store_def)

end
