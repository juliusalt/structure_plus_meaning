theory Native_Table_Reach
  imports Native_Path_Store_Indexes
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
  "reach_reached_rule=native_context_call_rule reach_search"

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
  unfolding native_reach_system_def finite_native_reach_def
  by (rule finite_rule_program_family[OF native_reach_formed[unfolded native_reach_system_def
    finite_native_reach_def] _ member plain]) (simp add: reach_definitions_def)

lemma native_reach_definitions:
  "system_definitions native_reach_system=fst ` set reach_definitions"
  by (simp add: native_reach_system_def finite_native_reach_def finite_rule_program_definitions)

interpretation reach_reached_family: native_context_call_program native_reach_system reach_reached reach_search
  unfolding native_context_call_program_def by (rule native_reach_family)
    (simp_all add: reach_definitions_def reach_reached_rule_def native_context_call_rule_def)

interpretation reach_searches: native_store_search_program native_reach_system reach_search reach_holds
  unfolding native_store_search_program_def by (rule native_reach_family)
    (simp_all add: reach_definitions_def native_store_search_rules_def native_store_found_rule_def
      native_store_left_rule_def native_store_right_rule_def)

interpretation reach_holds_family: native_rule_law native_reach_system reach_holds
    "[([0],reach_root_rule),([1],reach_step_rule)]"
  by (rule native_rule_lawI, rule native_reach_family)
    (auto simp: reach_definitions_def reach_root_rule_def reach_step_rule_def)

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
  using carrier_index.query_search[OF Native_Path_Store_Indexes.path_store_carrier_index,
      where c=T and q=k and v="(r,ps)"]
    formed row by (simp add: reach_table_formed_def)

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
      using clause site reach_reached_family.family by (auto simp: reach_reached_rule_def)
    have fields: "f [0]=reach_table_term T \<and> f [1]=k"
      using shape by (simp add: rule reach_reached_rule_def native_context_call_rule_def)
    have given: "(reach_search,Pair_Term (f [0]) (Pair_Term (f [1]) (f [0])))\<in>Y"
      by (rule reach_reached_family.rearranged.law.supported_clause[OF clause[unfolded site] into])
        (auto simp: finite_native_rule_eq_iff native_context_call_rule_def)
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
    obtain p ps where rule: "(c,finite_native_rule p ps)\<in>set [([0],reach_root_rule),([1],reach_step_rule)]"
      and concl: "schema_conclusion S=decode_finite_pattern p"
      and sup: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>Y"
      by (rule reach_holds_family.supported_clause[OF clause[unfolded site] into]) (rule that; assumption)
    from rule consider
      (root) "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1))"
      | (step) "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))"
        "set ps={([0],(reach_some,Finite_Pattern_Pair (native_var 0) (native_var 2)))}"
      by (auto simp: reach_root_rule_def reach_step_rule_def finite_native_rule_eq_iff)
    then show "reach_holds_at T v"
    proof cases
      case root
      have "v=Pair_Term (Payload_Term []) (f [1])"
        using shape by (simp add: concl root)
      then show ?thesis unfolding reach_holds_at_def by blast
    next
      case step
      have fields: "f [0]=reach_table_term T" "v=Pair_Term (f [1]) (f [2])"
        using shape by (simp_all add: concl step(1))
      have given: "(reach_some,Pair_Term (f [0]) (f [2]))\<in>Y"
        using sup step(2) by auto
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
  have search: "(reach_search,Pair_Term ?c (Pair_Term (path_term k)
      (store_term reach_row_value (path_store T))))\<in>positive_meaning native_reach_system"
    using native_carrier_index.site_query[OF reach_searches.index[OF reach_row_value_formed],
        where c=T and q=k and x="?c"] formed row cf holds_row
    by (auto simp: reach_table_formed_def)
  show ?thesis unfolding reach_reached_family.exact using search by (simp add: reach_table_term_def)
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
    by (rule reach_holds_family.step_at[where c="[0]" and ps="[]"])
      (use cf in \<open>simp_all add: reach_root_rule_def data_list_term_formed insert_Diff_if\<close>)
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
    by (rule reach_holds_family.step_at[where c="[1]" and
        ps="[([0],(reach_some,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
      (use some cf in \<open>simp_all add: reach_step_rule_def data_list_term_formed insert_Diff_if\<close>)
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

section \<open>Reach under seeding, restriction and removal\<close>

text \<open>
  Three changes of a table keep what it reaches, and the reach of an edited table is recomputed from
  them. A row's edges run from each of its predecessors to its key; a root is a row whose status is a
  root. Seeding makes rows roots without predecessors, restriction keeps the rows at a set of keys, and
  removal takes edges away. The statements hold over any table, formed or not, and name no state: seeding
  with keys the table already reaches leaves its reach unchanged; restriction to keys closed under the
  predecessors of their rows keeps the reach at those keys; and a set of keys that holds the target of
  every removed edge and is closed under the table's successors leaves every other reached key reached.
\<close>

definition reach_keys :: "reach_table \<Rightarrow> bool list set" where
  "reach_keys T=fst ` set T"

definition reach_roots :: "reach_table \<Rightarrow> bool list set" where
  "reach_roots T={k. \<exists>ps. (k,True,ps)\<in>set T}"

definition reach_edges :: "reach_table \<Rightarrow> (bool list\<times>bool list) set" where
  "reach_edges T={(p,k). \<exists>r ps. (k,r,ps)\<in>set T \<and> p\<in>set ps}"

definition reach_seed_row :: "bool list set \<Rightarrow> bool list\<times>bool\<times>bool list list \<Rightarrow> bool list\<times>bool\<times>bool list list" where
  "reach_seed_row K w=(if fst w\<in>K then (fst w,True,[]) else w)"

definition reach_seeded :: "bool list set \<Rightarrow> reach_table \<Rightarrow> reach_table" where
  "reach_seeded K T=map (reach_seed_row K) T"

definition reach_restricted :: "bool list set \<Rightarrow> reach_table \<Rightarrow> reach_table" where
  "reach_restricted K T=filter (\<lambda>w. fst w\<in>K) T"

lemma reach_edges_member: "(p,k)\<in>reach_edges T \<longleftrightarrow> (\<exists>r ps. (k,r,ps)\<in>set T \<and> p\<in>set ps)"
  by (simp add: reach_edges_def)

lemma table_reached_keys:
  assumes "k\<in>table_reached T"
  shows "k\<in>reach_keys T"
  using assms
proof (induction rule: table_reached.induct)
  case (root k ps)
  show ?case unfolding reach_keys_def by (rule rev_image_eqI[OF root.hyps]) simp
next
  case (step k r ps p)
  show ?case unfolding reach_keys_def by (rule rev_image_eqI[OF step.hyps(1)]) simp
qed

text \<open>
  A reached key of one table is reached in another when every row that can reach sends its key to a row
  of the other that is a root wherever it is one and has the images of its predecessors among its own:
  reach transported along a map of keys. Inclusion of rows is its identity instance.
\<close>

lemma table_reached_simulation:
  assumes rows: "\<And>k r ps. (k,r,ps)\<in>set T \<Longrightarrow> r \<or> ps\<noteq>[] \<Longrightarrow>
      \<exists>r' ps'. (g k,r',ps')\<in>set T' \<and> (r\<longrightarrow>r') \<and> g ` set ps\<subseteq>set ps'"
    and reached: "k\<in>table_reached T"
  shows "g k\<in>table_reached T'"
  using reached
proof induction
  case (root k ps)
  have "\<exists>r' ps'. (g k,r',ps')\<in>set T' \<and> (True\<longrightarrow>r') \<and> g ` set ps\<subseteq>set ps'"
    by (rule rows[OF root]) simp
  then obtain r' ps' where row: "(g k,r',ps')\<in>set T'" and r': "r'" by blast
  from row r' have "(g k,True,ps')\<in>set T'" by simp
  then show ?case by (rule table_reached.root)
next
  case (step k r ps p)
  have "\<exists>r' ps'. (g k,r',ps')\<in>set T' \<and> (r\<longrightarrow>r') \<and> g ` set ps\<subseteq>set ps'"
    by (rule rows[OF step.hyps(1)]) (use step.hyps(2) in auto)
  then obtain r' ps' where row: "(g k,r',ps')\<in>set T'" and sub: "g ` set ps\<subseteq>set ps'" by blast
  have "g p\<in>set ps'" using sub step.hyps(2) by blast
  then show ?case by (rule table_reached.step[OF row _ step.IH])
qed

lemma table_reached_mono:
  assumes rows: "set T\<subseteq>set U"
  shows "table_reached T\<subseteq>table_reached U"
proof
  fix k assume reached: "k\<in>table_reached T"
  have "id k\<in>table_reached U"
    by (rule table_reached_simulation[OF _ reached]) (use rows in auto)
  then show "k\<in>table_reached U" by simp
qed

lemma reach_seeded_member:
  "(k,v)\<in>set (reach_seeded K T) \<longleftrightarrow> (\<exists>r ps. (k,r,ps)\<in>set T \<and> v=(if k\<in>K then (True,[]) else (r,ps)))"
proof
  assume "(k,v)\<in>set (reach_seeded K T)"
  then obtain w where w: "w\<in>set T" and eq: "(k,v)=reach_seed_row K w"
    unfolding reach_seeded_def set_map image_iff by blast
  obtain k' r ps where ww: "w=(k',r,ps)" by (cases w)
  have "k'=k \<and> v=(if k\<in>K then (True,[]) else (r,ps))"
    using eq by (auto simp: ww reach_seed_row_def split: if_splits)
  then show "\<exists>r ps. (k,r,ps)\<in>set T \<and> v=(if k\<in>K then (True,[]) else (r,ps))"
    using w by (auto simp: ww)
next
  assume "\<exists>r ps. (k,r,ps)\<in>set T \<and> v=(if k\<in>K then (True,[]) else (r,ps))"
  then obtain r ps where row: "(k,r,ps)\<in>set T" and v: "v=(if k\<in>K then (True,[]) else (r,ps))" by blast
  have seeded: "reach_seed_row K (k,r,ps)=(k,v)" by (simp add: reach_seed_row_def v)
  show "(k,v)\<in>set (reach_seeded K T)"
    unfolding reach_seeded_def set_map by (rule image_eqI[where f="reach_seed_row K", OF seeded[symmetric] row])
qed

lemma reach_seeded_formed:
  assumes formed: "reach_table_formed T"
  shows "reach_table_formed (reach_seeded K T)"
  unfolding reach_table_formed_def single_valued_def
proof (intro allI impI)
  fix x y z assume first: "(x,y)\<in>set (reach_seeded K T)" and second: "(x,z)\<in>set (reach_seeded K T)"
  obtain r ps where a: "(x,r,ps)\<in>set T" and y: "y=(if x\<in>K then (True,[]) else (r,ps))"
    using first[unfolded reach_seeded_member] by blast
  obtain r' ps' where b: "(x,r',ps')\<in>set T" and z: "z=(if x\<in>K then (True,[]) else (r',ps'))"
    using second[unfolded reach_seeded_member] by blast
  have "(r,ps)=(r',ps')" using formed a b unfolding reach_table_formed_def single_valued_def by blast
  then show "y=z" using y z by simp
qed

lemma reach_restricted_formed:
  assumes formed: "reach_table_formed T"
  shows "reach_table_formed (reach_restricted K T)"
  unfolding reach_table_formed_def single_valued_def
proof (intro allI impI)
  fix x y z assume "(x,y)\<in>set (reach_restricted K T)" and "(x,z)\<in>set (reach_restricted K T)"
  then have a: "(x,y)\<in>set T" and b: "(x,z)\<in>set T" by (simp_all add: reach_restricted_def)
  show "y=z" using formed a b unfolding reach_table_formed_def single_valued_def by blast
qed

text \<open>
  Seeding with keys of its own reach leaves a table's reach unchanged: a seeded key was reached, and a
  derivation in the table reaches a seeded key at once and every other key through its unchanged row.
\<close>

theorem table_reached_seeded:
  assumes seeds: "K\<subseteq>table_reached T"
  shows "table_reached (reach_seeded K T)=table_reached T"
proof (intro set_eqI iffI)
  fix k assume "k\<in>table_reached (reach_seeded K T)"
  then show "k\<in>table_reached T"
  proof (induction rule: table_reached.induct)
    case (root k ps)
    obtain r ps0 where row: "(k,r,ps0)\<in>set T" and v: "(True,ps)=(if k\<in>K then (True,[]) else (r,ps0))"
      using root.hyps[unfolded reach_seeded_member] by blast
    show ?case
    proof (cases "k\<in>K")
      case True
      then show ?thesis using seeds by blast
    next
      case False
      then have "(k,True,ps)\<in>set T" using row v by simp
      then show ?thesis by (rule table_reached.root)
    qed
  next
    case (step k r ps p)
    obtain r0 ps0 where row: "(k,r0,ps0)\<in>set T" and v: "(r,ps)=(if k\<in>K then (True,[]) else (r0,ps0))"
      using step.hyps(1)[unfolded reach_seeded_member] by blast
    show ?case
    proof (cases "k\<in>K")
      case True
      then show ?thesis using seeds by blast
    next
      case False
      then have "(k,r,ps)\<in>set T" using row v by simp
      then show ?thesis by (rule table_reached.step[OF _ step.hyps(2) step.IH])
    qed
  qed
next
  fix k assume "k\<in>table_reached T"
  then show "k\<in>table_reached (reach_seeded K T)"
  proof (induction rule: table_reached.induct)
    case (root k ps)
    have "(k,(if k\<in>K then (True,[]) else (True,ps)))\<in>set (reach_seeded K T)"
      unfolding reach_seeded_member using root.hyps by blast
    then have "(k,True,if k\<in>K then [] else ps)\<in>set (reach_seeded K T)" by (cases "k\<in>K") simp_all
    then show ?case by (rule table_reached.root)
  next
    case (step k r ps p)
    have row: "(k,(if k\<in>K then (True,[]) else (r,ps)))\<in>set (reach_seeded K T)"
      unfolding reach_seeded_member using step.hyps(1) by blast
    show ?case
    proof (cases "k\<in>K")
      case True
      then have "(k,True,[])\<in>set (reach_seeded K T)" using row by simp
      then show ?thesis by (rule table_reached.root)
    next
      case False
      then have "(k,r,ps)\<in>set (reach_seeded K T)" using row by simp
      then show ?thesis by (rule table_reached.step[OF _ step.hyps(2) step.IH])
    qed
  qed
qed

text \<open>
  Restricted to a set of keys closed under the predecessors of their rows, a table reaches the same keys
  of the set: every derivation of such a key stays inside the set.
\<close>

theorem table_reached_restricted:
  assumes closed: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> k\<in>K \<Longrightarrow> p\<in>K" and key: "k\<in>K"
  shows "k\<in>table_reached (reach_restricted K T) \<longleftrightarrow> k\<in>table_reached T"
proof
  assume "k\<in>table_reached (reach_restricted K T)"
  then show "k\<in>table_reached T"
    using table_reached_mono[of "reach_restricted K T" T] by (auto simp: reach_restricted_def)
next
  have "k\<in>K \<longrightarrow> k\<in>table_reached (reach_restricted K T)" if "k\<in>table_reached T" for k
    using that
  proof (induction rule: table_reached.induct)
    case (root k ps)
    show ?case
    proof
      assume "k\<in>K"
      then have "(k,True,ps)\<in>set (reach_restricted K T)" using root.hyps by (simp add: reach_restricted_def)
      then show "k\<in>table_reached (reach_restricted K T)" by (rule table_reached.root)
    qed
  next
    case (step k r ps p)
    show ?case
    proof
      assume inside: "k\<in>K"
      have "(p,k)\<in>reach_edges T" unfolding reach_edges_member using step.hyps(1,2) by blast
      then have "p\<in>K" using closed inside by blast
      then have reached: "p\<in>table_reached (reach_restricted K T)" using step.IH by blast
      have "(k,r,ps)\<in>set (reach_restricted K T)" using step.hyps(1) inside by (simp add: reach_restricted_def)
      then show "k\<in>table_reached (reach_restricted K T)" by (rule table_reached.step[OF _ step.hyps(2) reached])
    qed
  qed
  then show "k\<in>table_reached T \<Longrightarrow> k\<in>table_reached (reach_restricted K T)" using key by blast
qed

text \<open>
  The removal lemma. Let \<open>T'\<close> keep every root of \<open>T\<close>, and let \<open>O\<close> hold the target of every edge of \<open>T\<close>
  that \<open>T'\<close> lacks and be closed under the successors of \<open>T\<close>. A derivation in \<open>T\<close> of a key outside
  \<open>O\<close> uses no edge whose source lies in \<open>O\<close>, since closure would carry its end into \<open>O\<close>; so it uses no
  removed edge, and is a derivation in \<open>T'\<close>. The set is named \<open>L\<close> below, \<open>O\<close> being relational
  composition in HOL.
\<close>

theorem table_reached_removal:
  assumes roots: "reach_roots T\<subseteq>reach_roots T'"
    and targets: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> (p,k)\<notin>reach_edges T' \<Longrightarrow> k\<in>L"
    and closed: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> p\<in>L \<Longrightarrow> k\<in>L"
    and reached: "k\<in>table_reached T" and outside: "k\<notin>L"
  shows "k\<in>table_reached T'"
proof -
  have "k\<notin>L \<longrightarrow> k\<in>table_reached T'" using reached
  proof (induction rule: table_reached.induct)
    case (root k ps)
    have "k\<in>reach_roots T" using root.hyps by (auto simp: reach_roots_def)
    then obtain ps' where "(k,True,ps')\<in>set T'" using roots by (auto simp: reach_roots_def)
    then have "k\<in>table_reached T'" by (rule table_reached.root)
    then show ?case by blast
  next
    case (step k r ps p)
    show ?case
    proof
      assume kO: "k\<notin>L"
      have edge: "(p,k)\<in>reach_edges T" unfolding reach_edges_member using step.hyps(1,2) by blast
      have pO: "p\<notin>L" using closed[OF edge] kO by blast
      have reached': "p\<in>table_reached T'" using step.IH pO by blast
      have "(p,k)\<in>reach_edges T'" using targets[OF edge] kO by blast
      then obtain r' ps' where row: "(k,r',ps')\<in>set T'" and p: "p\<in>set ps'"
        unfolding reach_edges_member by blast
      show "k\<in>table_reached T'" by (rule table_reached.step[OF row p reached'])
    qed
  qed
  then show ?thesis using outside by blast
qed

corollary table_reached_removal_keys:
  assumes roots: "reach_roots T\<subseteq>reach_roots T'"
    and targets: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> (p,k)\<notin>reach_edges T' \<Longrightarrow> k\<in>L"
    and closed: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> p\<in>L \<Longrightarrow> k\<in>L"
    and all: "reach_keys T\<subseteq>table_reached T"
  shows "reach_keys T-L\<subseteq>table_reached T'"
proof
  fix k assume k: "k\<in>reach_keys T-L"
  have reached: "k\<in>table_reached T" using k all by blast
  have outside: "k\<notin>L" using k by blast
  show "k\<in>table_reached T'"
    by (rule table_reached_removal[OF roots _ _ reached outside]) (fact targets, fact closed)
qed

text \<open>
  Its consequence: \<open>T'\<close> with every key of \<open>T\<close> outside \<open>O\<close> made a root without predecessors has the
  reach of \<open>T'\<close>, since those keys are of its own reach.
\<close>

corollary table_reached_removal_seeded:
  assumes roots: "reach_roots T\<subseteq>reach_roots T'"
    and targets: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> (p,k)\<notin>reach_edges T' \<Longrightarrow> k\<in>L"
    and closed: "\<And>p k. (p,k)\<in>reach_edges T \<Longrightarrow> p\<in>L \<Longrightarrow> k\<in>L"
    and all: "reach_keys T\<subseteq>table_reached T"
  shows "table_reached (reach_seeded (reach_keys T-L) T')=table_reached T'"
  by (rule table_reached_seeded[OF table_reached_removal_keys[OF roots targets closed all]])

end
