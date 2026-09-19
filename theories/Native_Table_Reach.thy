theory Native_Table_Reach
  imports Native_Path_Stores
begin

section \<open>Reach over a table of rows is a native definition\<close>

text \<open>
  A row holds a key, whether the key is a root, and the keys of its predecessors. A key is reached when
  its row is a root or one of its predecessors is reached; that is a least closure, which positive
  meaning is. Whether a key is reached reads the table of rows, which the key is judged with. The status
  of a row is structure, not a name: a root's status is a leaf and every other row's a pair of leaves.
  The program is closed: two collection notions at its own sites (some element of a list, the value a
  path store holds at a path) and three rules of its own; a key is a path and the table is the path store
  of the rows, so a row is found by descending the store along its key. The program compares keys only
  for equality, through variables that occur twice, and states no octet but the empty payload.
\<close>

abbreviation reach_reached :: "local_address option definition_site" where
  "reach_reached \<equiv> (Some [],[1])"

abbreviation reach_search :: "local_address option definition_site" where
  "reach_search \<equiv> (Some [],[2])"

abbreviation reach_holds :: "local_address option definition_site" where
  "reach_holds \<equiv> (Some [],[3])"

abbreviation reach_some :: "local_address option definition_site" where
  "reach_some \<equiv> (Some [],[4])"

definition reach_reached_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "reach_reached_rule=finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 1))
    [([0],(reach_search,Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Pair (native_var 1) (native_var 0))))]"

definition reach_root_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "reach_root_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))) []"

definition reach_step_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "reach_step_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(reach_some,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition reach_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "reach_definitions=[(reach_reached,[([0],reach_reached_rule)]),
    (reach_search,native_store_search_rules reach_search reach_holds),
    (reach_holds,[([0],reach_root_rule),([1],reach_step_rule)]),
    (reach_some,native_some_rules reach_some reach_reached)]"

definition finite_native_reach :: "local_address option finite_native_system" where
  "finite_native_reach=finite_rule_program reach_definitions"

definition native_reach_system :: "local_address option native_system" where
  "native_reach_system=decode_finite_system finite_native_reach"

lemma finite_native_reach_formed: "finite_system_formed finite_native_reach"
  by code_simp

lemma native_reach_formed: "schema_system_formed native_reach_system"
  using finite_native_reach_formed by (simp only: native_reach_system_def finite_system_formed_correct)

lemma native_reach_family:
  assumes member: "(d,rs)\<in>set reach_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family native_reach_system d rs"
proof (rule native_rule_family.intro)
  show "schema_system_formed native_reach_system" by (rule native_reach_formed)
  have distinct: "distinct (map fst reach_definitions)" by (simp add: reach_definitions_def)
  show "((d,c),S)\<in>system_clauses native_reach_system \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F)" for c S
  proof -
    have "((d,c),S)\<in>system_clauses native_reach_system \<longleftrightarrow>
        (\<exists>rs'. (d,rs')\<in>set reach_definitions \<and> (\<exists>F. (c,F)\<in>set rs' \<and> S=decode_finite_schema F))"
      unfolding native_reach_system_def finite_native_reach_def by (rule finite_rule_program_clause)
    then show ?thesis using eq_key_imp_eq_value[OF distinct member] member by blast
  qed
  have site: "d\<in>fst ` set reach_definitions" using member by (rule rev_image_eqI) simp
  show "schema_call_formed native_reach_system d t \<longleftrightarrow> term_formed t" for t
    unfolding native_reach_system_def finite_native_reach_def
    by (rule finite_rule_program_call[OF native_reach_formed[unfolded native_reach_system_def
      finite_native_reach_def] site])
  show "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}" by (rule plain)
qed

lemma native_reach_definitions:
  "system_definitions native_reach_system=fst ` set reach_definitions"
  by (simp add: native_reach_system_def finite_native_reach_def finite_rule_program_definitions)

interpretation reach_reached_family: native_rule_family native_reach_system reach_reached
    "[([0],reach_reached_rule)]"
  by (rule native_reach_family) (simp_all add: reach_definitions_def reach_reached_rule_def)

interpretation reach_searches: native_store_search_program native_reach_system reach_search reach_holds
  unfolding native_store_search_program_def by (rule native_reach_family)
    (simp_all add: reach_definitions_def native_store_search_rules_def native_store_found_rule_def
      native_store_left_rule_def native_store_right_rule_def)

interpretation reach_holds_family: native_rule_family native_reach_system reach_holds
    "[([0],reach_root_rule),([1],reach_step_rule)]"
  by (rule native_reach_family) (simp_all add: reach_definitions_def reach_root_rule_def reach_step_rule_def)

interpretation reach_somes: native_some_program native_reach_system reach_some reach_reached
  unfolding native_some_program_def by (rule native_reach_family)
    (simp_all add: reach_definitions_def native_some_rules_def native_some_first_def native_some_rest_def)

section \<open>The subject: rows and their reach\<close>

type_synonym reach_table = "(bool list\<times>bool\<times>bool list list) list"

definition reach_status :: "bool \<Rightarrow> factor_term" where
  "reach_status root=(if root then Payload_Term [] else Pair_Term (Payload_Term []) (Payload_Term []))"

lemma reach_status_root: "reach_status r=Payload_Term [] \<longleftrightarrow> r"
  by (cases r) (simp_all add: reach_status_def)

lemma reach_status_formed [simp]: "term_formed (reach_status r)"
  by (cases r) (simp_all add: reach_status_def octets_formed_def)

definition reach_value :: "bool \<Rightarrow> bool list list \<Rightarrow> factor_term" where
  "reach_value r ps=Pair_Term (reach_status r) (data_list_term (map path_term ps))"

definition reach_row_value :: "bool\<times>bool list list \<Rightarrow> factor_term" where
  "reach_row_value v=reach_value (fst v) (snd v)"

lemma reach_row_value_formed [simp]: "term_formed (reach_row_value v)"
  by (simp add: reach_row_value_def reach_value_def data_list_term_formed)

definition reach_table_term :: "reach_table \<Rightarrow> factor_term" where
  "reach_table_term T=store_term reach_row_value (path_store T)"

lemma reach_table_term_formed [simp]: "term_formed (reach_table_term T)"
  by (simp add: reach_table_term_def store_term_formed)

definition reach_table_formed :: "reach_table \<Rightarrow> bool" where
  "reach_table_formed T \<longleftrightarrow> single_valued (set T)"

inductive_set table_reached :: "reach_table \<Rightarrow> bool list set" for T where
  root: "(k,True,ps)\<in>set T \<Longrightarrow> k\<in>table_reached T"
| step: "(k,r,ps)\<in>set T \<Longrightarrow> p\<in>set ps \<Longrightarrow> p\<in>table_reached T \<Longrightarrow> k\<in>table_reached T"

lemma reach_table_lookup:
  assumes formed: "reach_table_formed T" and row: "(k,r,ps)\<in>set T"
  shows "store_lookup (path_store T) k=Some (r,ps)"
  using path_store_lookup[of T k "(r,ps)"] formed row by (simp add: reach_table_formed_def)

section \<open>Native reach is the least closure\<close>

definition reach_key :: "reach_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "reach_key T z \<longleftrightarrow> (\<exists>bs. z=path_term bs \<and> bs\<in>table_reached T)"

lemma reach_key_path [simp]: "reach_key T (path_term bs) \<longleftrightarrow> bs\<in>table_reached T"
  by (auto simp: reach_key_def path_term_injective)

definition reach_holds_at :: "reach_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "reach_holds_at T v \<longleftrightarrow> (\<exists>w. v=Pair_Term (Payload_Term []) w) \<or>
    (\<exists>s w. v=Pair_Term s w \<and> (\<forall>ps. w=data_list_term ps \<longrightarrow> (\<exists>p\<in>set ps. reach_key T p)))"

definition reach_invariant :: "local_address option definition_site \<Rightarrow> factor_term \<Rightarrow> bool" where
  "reach_invariant d t \<longleftrightarrow>
    (d=reach_reached \<longrightarrow> (\<forall>T k. t=Pair_Term (reach_table_term T) k \<longrightarrow> reach_key T k)) \<and>
    (d=reach_search \<longrightarrow> (\<forall>T k S. t=Pair_Term (reach_table_term T) (Pair_Term k (store_term reach_row_value S)) \<longrightarrow>
      (\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> reach_holds_at T (reach_row_value v)))) \<and>
    (d=reach_holds \<longrightarrow> (\<forall>T v. t=Pair_Term (reach_table_term T) v \<longrightarrow> reach_holds_at T v)) \<and>
    (d=reach_some \<longrightarrow> (\<forall>T ps. t=Pair_Term (reach_table_term T) (data_list_term ps) \<longrightarrow>
      (\<exists>p\<in>set ps. reach_key T p)))"

lemma reach_invariant_sites:
  "reach_invariant reach_reached t \<longleftrightarrow> (\<forall>T k. t=Pair_Term (reach_table_term T) k \<longrightarrow> reach_key T k)"
  "reach_invariant reach_search t \<longleftrightarrow>
    (\<forall>T k S. t=Pair_Term (reach_table_term T) (Pair_Term k (store_term reach_row_value S)) \<longrightarrow>
      (\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> reach_holds_at T (reach_row_value v)))"
  "reach_invariant reach_holds t \<longleftrightarrow> (\<forall>T v. t=Pair_Term (reach_table_term T) v \<longrightarrow> reach_holds_at T v)"
  "reach_invariant reach_some t \<longleftrightarrow>
    (\<forall>T ps. t=Pair_Term (reach_table_term T) (data_list_term ps) \<longrightarrow> (\<exists>p\<in>set ps. reach_key T p))"
  by (simp_all add: reach_invariant_def)

lemma reach_invariant_reached_at:
  assumes "reach_invariant reach_reached (Pair_Term (reach_table_term T) k)"
  shows "reach_key T k"
proof -
  have "\<forall>T' k'. Pair_Term (reach_table_term T) k=Pair_Term (reach_table_term T') k' \<longrightarrow> reach_key T' k'"
    using assms by (simp only: reach_invariant_sites)
  from this[rule_format, of T k] show ?thesis by simp
qed

lemma reach_invariant_search_at:
  assumes "reach_invariant reach_search (Pair_Term (reach_table_term T) (Pair_Term k (store_term reach_row_value S)))"
  shows "\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> reach_holds_at T (reach_row_value v)"
proof -
  have "\<forall>T' k' S'. Pair_Term (reach_table_term T) (Pair_Term k (store_term reach_row_value S))=
      Pair_Term (reach_table_term T') (Pair_Term k' (store_term reach_row_value S')) \<longrightarrow>
      (\<exists>bs v. k'=path_term bs \<and> store_lookup S' bs=Some v \<and> reach_holds_at T' (reach_row_value v))"
    using assms by (simp only: reach_invariant_sites)
  from this[rule_format, of T k S] show ?thesis by simp
qed

lemma reach_invariant_holds_at:
  assumes "reach_invariant reach_holds (Pair_Term (reach_table_term T) v)"
  shows "reach_holds_at T v"
proof -
  have "\<forall>T' v'. Pair_Term (reach_table_term T) v=Pair_Term (reach_table_term T') v' \<longrightarrow> reach_holds_at T' v'"
    using assms by (simp only: reach_invariant_sites)
  from this[rule_format, of T v] show ?thesis by simp
qed

lemma reach_invariant_some_at:
  assumes "reach_invariant reach_some (Pair_Term (reach_table_term T) (data_list_term ps))"
  shows "\<exists>p\<in>set ps. reach_key T p"
proof -
  have "\<forall>T' ps'. Pair_Term (reach_table_term T) (data_list_term ps)=
      Pair_Term (reach_table_term T') (data_list_term ps') \<longrightarrow> (\<exists>p\<in>set ps'. reach_key T' p)"
    using assms by (simp only: reach_invariant_sites)
  from this[rule_format, of T ps] show ?thesis by simp
qed

lemma reach_holds_reached:
  assumes row: "(k,v)\<in>set T" and holds: "reach_holds_at T (reach_row_value v)"
  shows "k\<in>table_reached T"
proof -
  obtain r ps where v: "v=(r,ps)" by (cases v)
  have presented: "reach_row_value v=Pair_Term (reach_status r) (data_list_term (map path_term ps))"
    by (simp add: v reach_row_value_def reach_value_def)
  show ?thesis using holds unfolding reach_holds_at_def
  proof (elim disjE exE conjE)
    fix w assume "reach_row_value v=Pair_Term (Payload_Term []) w"
    then have "reach_status r=Payload_Term []" by (simp add: presented)
    then have "r" by (simp add: reach_status_root)
    then have "(k,True,ps)\<in>set T" using row by (simp add: v)
    then show ?thesis by (rule table_reached.root)
  next
    fix s w assume shape: "reach_row_value v=Pair_Term s w"
      and some: "\<forall>ps'. w=data_list_term ps' \<longrightarrow> (\<exists>p\<in>set ps'. reach_key T p)"
    have "w=data_list_term (map path_term ps)" using shape by (simp add: presented)
    then obtain z where z: "z\<in>set (map path_term ps)" and reached: "reach_key T z" using some by blast
    obtain p where p: "p\<in>set ps" and zp: "z=path_term p" using z by auto
    have reached': "p\<in>table_reached T" using reached zp by simp
    have row': "(k,r,ps)\<in>set T" using row by (simp add: v)
    show ?thesis by (rule table_reached.step[OF row' p reached'])
  qed
qed

theorem reach_invariant_holds:
  assumes holds: "(d,t)\<in>positive_meaning native_reach_system"
  shows "reach_invariant d t"
proof (rule positive_valuation_induct[OF holds, where property=reach_invariant])
  fix d c S f
  assume clause: "((d,c),S)\<in>system_clauses native_reach_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and call: "schema_call_formed native_reach_system d (evaluate_pattern f (schema_conclusion S))"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning native_reach_system \<and> reach_invariant e (evaluate_pattern f p)"
  define Y where "Y={q. q\<in>positive_meaning native_reach_system \<and> reach_invariant (fst q) (snd q)}"
  have into: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>Y"
    using support by (auto simp: Y_def)
  have Y_invariant: "reach_invariant e u" if "(e,u)\<in>Y" for e u
    using that by (simp add: Y_def)
  show "reach_invariant d (evaluate_pattern f (schema_conclusion S))"
    unfolding reach_invariant_def
  proof (intro conjI impI allI)
    fix T k
    assume site: "d=reach_reached"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (reach_table_term T) k"
    have rule: "S=decode_finite_schema reach_reached_rule"
      using clause site reach_reached_family.family by auto
    have fields: "f [0]=reach_table_term T \<and> f [1]=k"
      using shape by (simp add: rule reach_reached_rule_def)
    have given: "(reach_search,Pair_Term (f [0]) (Pair_Term (f [1]) (f [0])))\<in>Y"
      using native_rule_support[OF into[unfolded rule reach_reached_rule_def]] by simp
    have search: "(reach_search,Pair_Term (reach_table_term T)
        (Pair_Term k (store_term reach_row_value (path_store T))))\<in>Y"
      using given fields by (simp add: reach_table_term_def)
    obtain bs v where key: "k=path_term bs" and lookup: "store_lookup (path_store T) bs=Some v"
      and found: "reach_holds_at T (reach_row_value v)"
      using reach_invariant_search_at[OF Y_invariant[OF search]] by blast
    have "bs\<in>table_reached T" by (rule reach_holds_reached[OF path_store_found[OF lookup] found])
    then show "reach_key T k" using key by simp
  next
    fix T k S'
    assume site: "d=reach_search"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (reach_table_term T)
        (Pair_Term k (store_term reach_row_value S'))"
    have clause': "((reach_search,c),S)\<in>system_clauses native_reach_system"
      using clause site by simp
    have cases: "(\<exists>v l r. k=Payload_Term [] \<and> S'=Store_Node (Some v) l r \<and>
          (reach_holds,Pair_Term (reach_table_term T) (reach_row_value v))\<in>Y) \<or>
        (\<exists>k' v l r. k=Pair_Term (bit_term False) k' \<and> S'=Store_Node v l r \<and>
          (reach_search,Pair_Term (reach_table_term T) (Pair_Term k' (store_term reach_row_value l)))\<in>Y) \<or>
        (\<exists>k' v l r. k=Pair_Term (bit_term True) k' \<and> S'=Store_Node v l r \<and>
          (reach_search,Pair_Term (reach_table_term T) (Pair_Term k' (store_term reach_row_value r)))\<in>Y)"
      by (rule reach_searches.unfold[OF clause' into shape])
    show "\<exists>bs v. k=path_term bs \<and> store_lookup S' bs=Some v \<and> reach_holds_at T (reach_row_value v)"
      using cases
    proof (elim disjE exE conjE)
      fix v l r
      assume k: "k=Payload_Term []" and S': "S'=Store_Node (Some v) l r"
        and holds_v: "(reach_holds,Pair_Term (reach_table_term T) (reach_row_value v))\<in>Y"
      have "reach_holds_at T (reach_row_value v)"
        by (rule reach_invariant_holds_at[OF Y_invariant[OF holds_v]])
      then show ?thesis using k S' by (intro exI[of _ "[]"] exI[of _ v]) simp
    next
      fix k' v l r
      assume k: "k=Pair_Term (bit_term False) k'" and S': "S'=Store_Node v l r"
        and inner: "(reach_search,Pair_Term (reach_table_term T) (Pair_Term k' (store_term reach_row_value l)))\<in>Y"
      obtain bs w where k': "k'=path_term bs" and lookup: "store_lookup l bs=Some w"
        and found: "reach_holds_at T (reach_row_value w)"
        using reach_invariant_search_at[OF Y_invariant[OF inner]] by blast
      show ?thesis using k k' S' lookup found by (intro exI[of _ "False#bs"] exI[of _ w]) simp
    next
      fix k' v l r
      assume k: "k=Pair_Term (bit_term True) k'" and S': "S'=Store_Node v l r"
        and inner: "(reach_search,Pair_Term (reach_table_term T) (Pair_Term k' (store_term reach_row_value r)))\<in>Y"
      obtain bs w where k': "k'=path_term bs" and lookup: "store_lookup r bs=Some w"
        and found: "reach_holds_at T (reach_row_value w)"
        using reach_invariant_search_at[OF Y_invariant[OF inner]] by blast
      show ?thesis using k k' S' lookup found by (intro exI[of _ "True#bs"] exI[of _ w]) simp
    qed
  next
    fix T v
    assume site: "d=reach_holds"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (reach_table_term T) v"
    have rules: "S=decode_finite_schema reach_root_rule \<or> S=decode_finite_schema reach_step_rule"
      using clause site reach_holds_family.family by auto
    then show "reach_holds_at T v"
    proof
      assume rule: "S=decode_finite_schema reach_root_rule"
      have "v=Pair_Term (Payload_Term []) (f [1])"
        using shape by (simp add: rule reach_root_rule_def)
      then show ?thesis unfolding reach_holds_at_def by blast
    next
      assume rule: "S=decode_finite_schema reach_step_rule"
      have fields: "f [0]=reach_table_term T" "v=Pair_Term (f [1]) (f [2])"
        using shape by (simp_all add: rule reach_step_rule_def)
      have given: "(reach_some,Pair_Term (f [0]) (f [2]))\<in>Y"
        using native_rule_support[OF into[unfolded rule reach_step_rule_def]] by simp
      have some: "\<forall>ps. f [2]=data_list_term ps \<longrightarrow> (\<exists>p\<in>set ps. reach_key T p)"
      proof (intro allI impI)
        fix ps assume valued: "f [2]=data_list_term ps"
        have "(reach_some,Pair_Term (reach_table_term T) (data_list_term ps))\<in>Y"
          using given fields(1) valued by simp
        then show "\<exists>p\<in>set ps. reach_key T p" by (rule reach_invariant_some_at[OF Y_invariant])
      qed
      show ?thesis unfolding reach_holds_at_def using fields(2) some by blast
    qed
  next
    fix T ps
    assume site: "d=reach_some"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (reach_table_term T) (data_list_term ps)"
    have clause': "((reach_some,c),S)\<in>system_clauses native_reach_system"
      using clause site by simp
    obtain h ps' where ps: "ps=h#ps'"
      and choice: "(reach_reached,Pair_Term (reach_table_term T) h)\<in>Y \<or>
        (reach_some,Pair_Term (reach_table_term T) (data_list_term ps'))\<in>Y"
      using reach_somes.unfold[OF clause' into shape] by blast
    show "\<exists>p\<in>set ps. reach_key T p"
      using choice
    proof
      assume "(reach_reached,Pair_Term (reach_table_term T) h)\<in>Y"
      then have "reach_key T h" by (rule reach_invariant_reached_at[OF Y_invariant])
      then show ?thesis using ps by auto
    next
      assume "(reach_some,Pair_Term (reach_table_term T) (data_list_term ps'))\<in>Y"
      then have "\<exists>p\<in>set ps'. reach_key T p" by (rule reach_invariant_some_at[OF Y_invariant])
      then show ?thesis using ps by auto
    qed
  qed
qed

theorem native_reached_sound:
  assumes "(reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning native_reach_system"
  shows "bs\<in>table_reached T"
  using reach_invariant_reached_at[OF reach_invariant_holds[OF assms]] by simp

lemma native_reached_search:
  assumes formed: "reach_table_formed T" and row: "(k,r,ps)\<in>set T"
    and holds_row: "(reach_holds,Pair_Term (reach_table_term T) (reach_row_value (r,ps)))\<in>positive_meaning native_reach_system"
  shows "(reach_reached,Pair_Term (reach_table_term T) (path_term k))\<in>positive_meaning native_reach_system"
proof -
  let ?c="reach_table_term T"
  have cf: "term_formed ?c" by simp
  have lookup: "store_lookup (path_store T) k=Some (r,ps)" by (rule reach_table_lookup[OF formed row])
  have search: "(reach_search,Pair_Term ?c (Pair_Term (path_term k)
      (store_term reach_row_value (path_store T))))\<in>positive_meaning native_reach_system"
    using cf holds_row lookup
    by (auto simp: reach_searches.exact[OF reach_row_value_formed] path_term_injective)
  have "(reach_reached,evaluate_pattern (native_values [?c,path_term k])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1))))\<in>positive_meaning native_reach_system"
    by (rule reach_reached_family.native_step[where c="[0]" and
        ps="[([0],(reach_search,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 0))))]"])
      (use search cf in \<open>simp_all add: reach_reached_rule_def reach_table_term_def\<close>)
  then show ?thesis by simp
qed

theorem native_reached_complete:
  assumes formed: "reach_table_formed T" and reached: "bs\<in>table_reached T"
  shows "(reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning native_reach_system"
  using reached
proof (induction rule: table_reached.induct)
  case (root k ps)
  let ?c="reach_table_term T"
  have cf: "term_formed ?c" by simp
  have "(reach_holds,evaluate_pattern (native_values [?c,data_list_term (map path_term ps)])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))))\<in>positive_meaning native_reach_system"
    by (rule reach_holds_family.native_step[where c="[0]" and ps="[]"])
      (use cf in \<open>simp_all add: reach_root_rule_def data_list_term_formed\<close>)
  then have "(reach_holds,Pair_Term ?c (reach_row_value (True,ps)))\<in>positive_meaning native_reach_system"
    by (simp add: reach_row_value_def reach_value_def reach_status_def)
  then show ?case by (rule native_reached_search[OF formed root.hyps])
next
  case (step k r ps p)
  let ?c="reach_table_term T"
  have cf: "term_formed ?c" by simp
  have some: "(reach_some,Pair_Term ?c (data_list_term (map path_term ps)))\<in>positive_meaning native_reach_system"
    using cf step.IH step.hyps(2) by (auto simp: reach_somes.exact)
  have "(reach_holds,evaluate_pattern (native_values [?c,reach_status r,data_list_term (map path_term ps)])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (native_var 1) (native_var 2)))))\<in>positive_meaning native_reach_system"
    by (rule reach_holds_family.native_step[where c="[1]" and
        ps="[([0],(reach_some,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
      (use some cf in \<open>simp_all add: reach_step_rule_def data_list_term_formed\<close>)
  then have "(reach_holds,Pair_Term ?c (reach_row_value (r,ps)))\<in>positive_meaning native_reach_system"
    by (simp add: reach_row_value_def reach_value_def)
  then show ?case by (rule native_reached_search[OF formed step.hyps(1)])
qed

theorem native_reached_exact:
  assumes formed: "reach_table_formed T"
  shows "(reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning native_reach_system \<longleftrightarrow>
    bs\<in>table_reached T"
  using native_reached_sound native_reached_complete[OF formed] by blast

section \<open>Rows and tables are presented by their finite terms\<close>

definition finite_reach_status :: "bool \<Rightarrow> finite_factor_term" where
  "finite_reach_status r=(if r then Finite_Payload [] else Finite_Pair (Finite_Payload []) (Finite_Payload []))"

lemma decode_finite_reach_status [simp]: "decode_finite_term (finite_reach_status r)=reach_status r"
  by (simp add: finite_reach_status_def reach_status_def)

definition finite_reach_value :: "bool \<Rightarrow> bool list list \<Rightarrow> finite_factor_term" where
  "finite_reach_value r ps=Finite_Pair (finite_reach_status r) (finite_data_list (map finite_path ps))"

lemma decode_finite_reach_value [simp]: "decode_finite_term (finite_reach_value r ps)=reach_value r ps"
  by (simp add: finite_reach_value_def reach_value_def comp_def)

definition finite_reach_row_value :: "bool\<times>bool list list \<Rightarrow> finite_factor_term" where
  "finite_reach_row_value v=finite_reach_value (fst v) (snd v)"

lemma decode_finite_reach_row_value: "decode_finite_term \<circ> finite_reach_row_value=reach_row_value"
  by (rule ext) (simp add: finite_reach_row_value_def reach_row_value_def)

definition finite_reach_table :: "reach_table \<Rightarrow> finite_factor_term" where
  "finite_reach_table T=finite_store finite_reach_row_value (path_store T)"

lemma decode_finite_reach_table: "decode_finite_term (finite_reach_table T)=reach_table_term T"
  by (simp add: finite_reach_table_def reach_table_term_def decode_finite_store decode_finite_reach_row_value)

end
