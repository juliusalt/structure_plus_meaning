theory Development_Native_Readiness
  imports Native_Path_Stores
begin

section \<open>Readiness is a native definition\<close>

text \<open>
  The owner's direction of 2026-09-19 makes native definitions normative: a notion of the development is a
  Factor program over native structure, its meaning is its positive meaning, and Isabelle verifies its
  contract. Readiness is defined so. A problem is presented by its row: its key, its status and the list of
  its decompositions, a decomposition being the list of its premise keys. The status is structure of the
  row, not a name: an answered problem's status is a leaf and an open problem's a pair of leaves. Whether a
  problem is ready reads its own row and the table of the rows its settledness reads, which the row is judged
  with; the program compares problems only for equality, through variables that occur twice.

  The program is closed: it is composed of the native collection notions (every and some element of a list,
  the value a path store holds at a path) at its own sites, and of three rules of its own. A key is a path,
  a list of bits each of which is a shape, and the table of rows is the path store of the rows, so a row is
  found by descending the store along its key rather than by walking the table. Settlement is a least
  closure, which positive meaning is: a problem is settled when its row in the table is answered and one of
  its decompositions has every premise settled. A row is ready when it is open and every premise of every
  one of its decompositions is settled. Every rule's conclusion binds every variable
  its premises use, so a call determines the calls it premises, and the program is evaluated by demand.
\<close>

abbreviation readiness_settled :: "local_address option definition_site" where
  "readiness_settled \<equiv> (Some [],[1])"

abbreviation readiness_settled_search :: "local_address option definition_site" where
  "readiness_settled_search \<equiv> (Some [],[2])"

abbreviation readiness_answered :: "local_address option definition_site" where
  "readiness_answered \<equiv> (Some [],[3])"

abbreviation readiness_some :: "local_address option definition_site" where
  "readiness_some \<equiv> (Some [],[4])"

abbreviation readiness_all :: "local_address option definition_site" where
  "readiness_all \<equiv> (Some [],[5])"

abbreviation readiness_every :: "local_address option definition_site" where
  "readiness_every \<equiv> (Some [],[6])"

abbreviation readiness_ready :: "local_address option definition_site" where
  "readiness_ready \<equiv> (Some [],[7])"

text \<open>
  A key is settled when the table holds, for it, an answered row some decomposition of which has all its
  premises settled. A row, judged together with the table of the rows its readiness reads, is ready when its
  status is open and every one of its decompositions has all its premises settled in that table; the
  subject of the question that asks it is not read.
\<close>

definition readiness_settled_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "readiness_settled_rule=finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 1))
    [([0],(readiness_settled_search,Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Pair (native_var 1) (native_var 0))))]"

definition readiness_answered_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "readiness_answered_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))
    [([0],(readiness_some,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"

definition readiness_ready_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "readiness_ready_rule=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (Finite_Pattern_Pair (native_var 2)
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))
        (native_var 3)))))
    [([0],(readiness_every,Finite_Pattern_Pair (native_var 1) (native_var 3)))]"

definition readiness_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "readiness_definitions=[(readiness_settled,[([0],readiness_settled_rule)]),
    (readiness_settled_search,native_store_search_rules readiness_settled_search readiness_answered),
    (readiness_answered,[([0],readiness_answered_rule)]),
    (readiness_some,native_some_rules readiness_some readiness_all),
    (readiness_all,native_every_rules readiness_all readiness_settled),
    (readiness_every,native_every_rules readiness_every readiness_all),
    (readiness_ready,[([0],readiness_ready_rule)])]"

definition finite_native_readiness :: "local_address option finite_native_system" where
  "finite_native_readiness=finite_rule_program readiness_definitions"

definition native_readiness_system :: "local_address option native_system" where
  "native_readiness_system=decode_finite_system finite_native_readiness"

lemma finite_native_readiness_formed: "finite_system_formed finite_native_readiness"
  by code_simp

lemma native_readiness_formed: "schema_system_formed native_readiness_system"
  using finite_native_readiness_formed by (simp only: native_readiness_system_def finite_system_formed_correct)

lemma native_readiness_family:
  assumes member: "(d,rs)\<in>set readiness_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family native_readiness_system d rs"
proof (rule native_rule_family.intro)
  show "schema_system_formed native_readiness_system" by (rule native_readiness_formed)
  have distinct: "distinct (map fst readiness_definitions)" by (simp add: readiness_definitions_def)
  show "((d,c),S)\<in>system_clauses native_readiness_system \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F)" for c S
  proof -
    have "((d,c),S)\<in>system_clauses native_readiness_system \<longleftrightarrow>
        (\<exists>rs'. (d,rs')\<in>set readiness_definitions \<and> (\<exists>F. (c,F)\<in>set rs' \<and> S=decode_finite_schema F))"
      unfolding native_readiness_system_def finite_native_readiness_def by (rule finite_rule_program_clause)
    then show ?thesis using eq_key_imp_eq_value[OF distinct member] member by blast
  qed
  have site: "d\<in>fst ` set readiness_definitions" using member by (rule rev_image_eqI) simp
  show "schema_call_formed native_readiness_system d t \<longleftrightarrow> term_formed t" for t
    unfolding native_readiness_system_def finite_native_readiness_def
    by (rule finite_rule_program_call[OF native_readiness_formed[unfolded native_readiness_system_def
      finite_native_readiness_def] site])
  show "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}" by (rule plain)
qed

lemma native_readiness_definitions:
  "system_definitions native_readiness_system=fst ` set readiness_definitions"
  by (simp add: native_readiness_system_def finite_native_readiness_def finite_rule_program_definitions)

interpretation readiness_settled_family: native_rule_family native_readiness_system readiness_settled
    "[([0],readiness_settled_rule)]"
  by (rule native_readiness_family) (simp_all add: readiness_definitions_def readiness_settled_rule_def)

interpretation readiness_settled_searches: native_store_search_program native_readiness_system
    readiness_settled_search readiness_answered
  unfolding native_store_search_program_def by (rule native_readiness_family)
    (simp_all add: readiness_definitions_def native_store_search_rules_def native_store_found_rule_def
      native_store_left_rule_def native_store_right_rule_def)

interpretation readiness_answered_family: native_rule_family native_readiness_system readiness_answered
    "[([0],readiness_answered_rule)]"
  by (rule native_readiness_family) (simp_all add: readiness_definitions_def readiness_answered_rule_def)

interpretation readiness_somes: native_some_program native_readiness_system readiness_some readiness_all
  unfolding native_some_program_def by (rule native_readiness_family)
    (simp_all add: readiness_definitions_def native_some_rules_def native_some_first_def native_some_rest_def)

interpretation readiness_alls: native_every_program native_readiness_system readiness_all readiness_settled
  unfolding native_every_program_def by (rule native_readiness_family)
    (simp_all add: readiness_definitions_def native_every_rules_def native_every_nil_def native_every_step_def)

interpretation readiness_everys: native_every_program native_readiness_system readiness_every readiness_all
  unfolding native_every_program_def by (rule native_readiness_family)
    (simp_all add: readiness_definitions_def native_every_rules_def native_every_nil_def native_every_step_def)

interpretation readiness_ready_family: native_rule_family native_readiness_system readiness_ready
    "[([0],readiness_ready_rule)]"
  by (rule native_readiness_family) (simp_all add: readiness_definitions_def readiness_ready_rule_def)

section \<open>The subject: rows of problems and their settlement\<close>

text \<open>
  A row holds a problem's key, whether it is answered, and the list of its decompositions, each the list of
  its premise keys. A key is a path, so a table of rows is a list of paths with their values, and the table is
  presented as the path store of its rows. A key is settled in a table of rows when an answered row of the
  table holds it and one of its decompositions has every premise settled; this least closure is stated here
  once, and native settlement computes exactly it on every single-valued table.
\<close>

type_synonym readiness_table = "(bool list\<times>bool\<times>bool list list list) list"

definition readiness_status :: "bool \<Rightarrow> factor_term" where
  "readiness_status answered=(if answered then Payload_Term [] else Pair_Term (Payload_Term []) (Payload_Term []))"

lemma readiness_status_answered: "readiness_status a=Payload_Term [] \<longleftrightarrow> a"
  by (cases a) (simp_all add: readiness_status_def)

lemma readiness_status_open: "readiness_status a=Pair_Term (Payload_Term []) (Payload_Term []) \<longleftrightarrow> \<not>a"
  by (cases a) (simp_all add: readiness_status_def)

lemma readiness_status_formed [simp]: "term_formed (readiness_status a)"
  by (cases a) (simp_all add: readiness_status_def octets_formed_def)

definition readiness_decompositions :: "bool list list list \<Rightarrow> factor_term" where
  "readiness_decompositions hs=data_list_term (map (\<lambda>h. data_list_term (map path_term h)) hs)"

lemma readiness_decompositions_formed [simp]: "term_formed (readiness_decompositions hs)"
  by (simp add: readiness_decompositions_def data_list_term_formed)

definition readiness_value :: "bool \<Rightarrow> bool list list list \<Rightarrow> factor_term" where
  "readiness_value a hs=Pair_Term (readiness_status a) (readiness_decompositions hs)"

lemma readiness_value_formed [simp]: "term_formed (readiness_value a hs)"
  by (simp add: readiness_value_def)

definition readiness_row_value :: "bool\<times>bool list list list \<Rightarrow> factor_term" where
  "readiness_row_value r=readiness_value (fst r) (snd r)"

lemma readiness_row_value_formed [simp]: "term_formed (readiness_row_value r)"
  by (simp add: readiness_row_value_def)

definition readiness_table_term :: "readiness_table \<Rightarrow> factor_term" where
  "readiness_table_term T=store_term readiness_row_value (path_store T)"

definition readiness_table_formed :: "readiness_table \<Rightarrow> bool" where
  "readiness_table_formed T \<longleftrightarrow> single_valued (set T)"

inductive_set table_settled :: "readiness_table \<Rightarrow> bool list set" for T where
  settle: "(k,True,hs)\<in>set T \<Longrightarrow> h\<in>set hs \<Longrightarrow> \<forall>x\<in>set h. x\<in>table_settled T \<Longrightarrow> k\<in>table_settled T"

lemma readiness_table_term_formed [simp]: "term_formed (readiness_table_term T)"
  by (simp add: readiness_table_term_def store_term_formed)

lemma readiness_table_found:
  assumes "store_lookup (path_store T) k=Some v"
  shows "(k,v)\<in>set T"
  by (rule path_store_found[OF assms])

lemma readiness_table_lookup:
  assumes formed: "readiness_table_formed T" and row: "(k,a,hs)\<in>set T"
  shows "store_lookup (path_store T) k=Some (a,hs)"
  using path_store_lookup[of T k "(a,hs)"] formed row by (simp add: readiness_table_formed_def)

section \<open>Native settlement is the least closure\<close>

definition readiness_settled_key :: "readiness_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "readiness_settled_key T z \<longleftrightarrow> (\<exists>bs. z=path_term bs \<and> bs\<in>table_settled T)"

lemma readiness_settled_key_path [simp]: "readiness_settled_key T (path_term bs) \<longleftrightarrow> bs\<in>table_settled T"
  by (auto simp: readiness_settled_key_def path_term_injective)

definition readiness_answered_at :: "readiness_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "readiness_answered_at T v \<longleftrightarrow> (\<exists>w. v=Pair_Term (Payload_Term []) w \<and>
    (\<forall>vs. w=data_list_term vs \<longrightarrow>
      (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z))))"

definition readiness_invariant :: "local_address option definition_site \<Rightarrow> factor_term \<Rightarrow> bool" where
  "readiness_invariant d t \<longleftrightarrow>
    (d=readiness_settled \<longrightarrow> (\<forall>T k. t=Pair_Term (readiness_table_term T) k \<longrightarrow> readiness_settled_key T k)) \<and>
    (d=readiness_settled_search \<longrightarrow> (\<forall>T k S. t=Pair_Term (readiness_table_term T)
        (Pair_Term k (store_term readiness_row_value S)) \<longrightarrow>
      (\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> readiness_answered_at T (readiness_row_value v)))) \<and>
    (d=readiness_answered \<longrightarrow> (\<forall>T v. t=Pair_Term (readiness_table_term T) v \<longrightarrow> readiness_answered_at T v)) \<and>
    (d=readiness_some \<longrightarrow> (\<forall>T vs. t=Pair_Term (readiness_table_term T) (data_list_term vs) \<longrightarrow>
      (\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)))) \<and>
    (d=readiness_all \<longrightarrow> (\<forall>T zs. t=Pair_Term (readiness_table_term T) (data_list_term zs) \<longrightarrow>
      (\<forall>z\<in>set zs. readiness_settled_key T z)))"

lemma readiness_invariant_sites:
  "readiness_invariant readiness_settled t \<longleftrightarrow>
    (\<forall>T k. t=Pair_Term (readiness_table_term T) k \<longrightarrow> readiness_settled_key T k)"
  "readiness_invariant readiness_settled_search t \<longleftrightarrow>
    (\<forall>T k S. t=Pair_Term (readiness_table_term T) (Pair_Term k (store_term readiness_row_value S)) \<longrightarrow>
      (\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> readiness_answered_at T (readiness_row_value v)))"
  "readiness_invariant readiness_answered t \<longleftrightarrow>
    (\<forall>T v. t=Pair_Term (readiness_table_term T) v \<longrightarrow> readiness_answered_at T v)"
  "readiness_invariant readiness_some t \<longleftrightarrow>
    (\<forall>T vs. t=Pair_Term (readiness_table_term T) (data_list_term vs) \<longrightarrow>
      (\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)))"
  "readiness_invariant readiness_all t \<longleftrightarrow>
    (\<forall>T zs. t=Pair_Term (readiness_table_term T) (data_list_term zs) \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z))"
  by (simp_all add: readiness_invariant_def)

lemma readiness_invariant_settled_at:
  assumes "readiness_invariant readiness_settled (Pair_Term (readiness_table_term T) k)"
  shows "readiness_settled_key T k"
proof -
  have "\<forall>T' k'. Pair_Term (readiness_table_term T) k=Pair_Term (readiness_table_term T') k' \<longrightarrow>
      readiness_settled_key T' k'"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T k] show ?thesis by simp
qed

lemma readiness_invariant_search_at:
  assumes "readiness_invariant readiness_settled_search
    (Pair_Term (readiness_table_term T) (Pair_Term k (store_term readiness_row_value S)))"
  shows "\<exists>bs v. k=path_term bs \<and> store_lookup S bs=Some v \<and> readiness_answered_at T (readiness_row_value v)"
proof -
  have "\<forall>T' k' S'. Pair_Term (readiness_table_term T) (Pair_Term k (store_term readiness_row_value S))=
      Pair_Term (readiness_table_term T') (Pair_Term k' (store_term readiness_row_value S')) \<longrightarrow>
      (\<exists>bs v. k'=path_term bs \<and> store_lookup S' bs=Some v \<and> readiness_answered_at T' (readiness_row_value v))"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T k S] show ?thesis by simp
qed

lemma readiness_invariant_answered_at:
  assumes "readiness_invariant readiness_answered (Pair_Term (readiness_table_term T) v)"
  shows "readiness_answered_at T v"
proof -
  have "\<forall>T' v'. Pair_Term (readiness_table_term T) v=Pair_Term (readiness_table_term T') v' \<longrightarrow>
      readiness_answered_at T' v'"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T v] show ?thesis by simp
qed

lemma readiness_invariant_some_at:
  assumes "readiness_invariant readiness_some (Pair_Term (readiness_table_term T) (data_list_term vs))"
  shows "\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
proof -
  have "\<forall>T' vs'. Pair_Term (readiness_table_term T) (data_list_term vs)=
      Pair_Term (readiness_table_term T') (data_list_term vs') \<longrightarrow>
      (\<exists>v\<in>set vs'. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T' z))"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T vs] show ?thesis by simp
qed

lemma readiness_invariant_all_at:
  assumes "readiness_invariant readiness_all (Pair_Term (readiness_table_term T) (data_list_term zs))"
  shows "\<forall>z\<in>set zs. readiness_settled_key T z"
proof -
  have "\<forall>T' zs'. Pair_Term (readiness_table_term T) (data_list_term zs)=
      Pair_Term (readiness_table_term T') (data_list_term zs') \<longrightarrow> (\<forall>z\<in>set zs'. readiness_settled_key T' z)"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T zs] show ?thesis by simp
qed

lemma readiness_answered_settled:
  assumes row: "(k,v)\<in>set T" and answered: "readiness_answered_at T (readiness_row_value v)"
  shows "k\<in>table_settled T"
proof -
  obtain a hs where v: "v=(a,hs)" by (cases v)
  obtain w where vw: "readiness_row_value v=Pair_Term (Payload_Term []) w"
    and some: "\<forall>vs. w=data_list_term vs \<longrightarrow>
      (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z))"
    using answered by (auto simp: readiness_answered_at_def)
  have same: "Pair_Term (readiness_status a) (readiness_decompositions hs)=Pair_Term (Payload_Term []) w"
    using vw by (simp add: v readiness_row_value_def readiness_value_def)
  have status: "readiness_status a=Payload_Term []"
    and ww: "w=data_list_term (map (\<lambda>h. data_list_term (map path_term h)) hs)"
    using same by (simp_all add: readiness_decompositions_def)
  have entry: "(k,True,hs)\<in>set T" using row status by (simp add: v readiness_status_answered)
  obtain u where u: "u\<in>set (map (\<lambda>h. data_list_term (map path_term h)) hs)"
    and settled_u: "\<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
    using some ww by blast
  obtain h where h: "h\<in>set hs" and uh: "u=data_list_term (map path_term h)" using u by auto
  have "\<forall>z\<in>set (map path_term h). readiness_settled_key T z" using settled_u[rule_format, OF uh] by blast
  then have "\<forall>x\<in>set h. x\<in>table_settled T" by simp
  then show ?thesis by (rule table_settled.settle[OF entry h])
qed

theorem readiness_invariant_holds:
  assumes holds: "(d,t)\<in>positive_meaning native_readiness_system"
  shows "readiness_invariant d t"
proof (rule positive_valuation_induct[OF holds, where property=readiness_invariant])
  fix d c S f
  assume clause: "((d,c),S)\<in>system_clauses native_readiness_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and call: "schema_call_formed native_readiness_system d (evaluate_pattern f (schema_conclusion S))"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning native_readiness_system \<and> readiness_invariant e (evaluate_pattern f p)"
  define Y where "Y={q. q\<in>positive_meaning native_readiness_system \<and> readiness_invariant (fst q) (snd q)}"
  have into: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>Y"
    using support by (auto simp: Y_def)
  have Y_invariant: "readiness_invariant e u" if "(e,u)\<in>Y" for e u
    using that by (simp add: Y_def)
  show "readiness_invariant d (evaluate_pattern f (schema_conclusion S))"
    unfolding readiness_invariant_def
  proof (intro conjI impI allI)
    fix T k
    assume site: "d=readiness_settled"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T) k"
    have rule: "S=decode_finite_schema readiness_settled_rule"
      using clause site readiness_settled_family.family by auto
    have fields: "f [0]=readiness_table_term T \<and> f [1]=k"
      using shape by (simp add: rule readiness_settled_rule_def)
    have given: "(readiness_settled_search,Pair_Term (f [0]) (Pair_Term (f [1]) (f [0])))\<in>Y"
      using native_rule_support[OF into[unfolded rule readiness_settled_rule_def]] by simp
    have search: "(readiness_settled_search,Pair_Term (readiness_table_term T)
        (Pair_Term k (store_term readiness_row_value (path_store T))))\<in>Y"
      using given fields by (simp add: readiness_table_term_def)
    obtain bs v where key: "k=path_term bs" and lookup: "store_lookup (path_store T) bs=Some v"
      and found: "readiness_answered_at T (readiness_row_value v)"
      using readiness_invariant_search_at[OF Y_invariant[OF search]] by blast
    have "bs\<in>table_settled T" by (rule readiness_answered_settled[OF readiness_table_found[OF lookup] found])
    then show "readiness_settled_key T k" using key by simp
  next
    fix T k S'
    assume site: "d=readiness_settled_search"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T)
        (Pair_Term k (store_term readiness_row_value S'))"
    have clause': "((readiness_settled_search,c),S)\<in>system_clauses native_readiness_system"
      using clause site by simp
    have cases: "(\<exists>v l r. k=Payload_Term [] \<and> S'=Store_Node (Some v) l r \<and>
          (readiness_answered,Pair_Term (readiness_table_term T) (readiness_row_value v))\<in>Y) \<or>
        (\<exists>k' v l r. k=Pair_Term (bit_term False) k' \<and> S'=Store_Node v l r \<and>
          (readiness_settled_search,Pair_Term (readiness_table_term T)
            (Pair_Term k' (store_term readiness_row_value l)))\<in>Y) \<or>
        (\<exists>k' v l r. k=Pair_Term (bit_term True) k' \<and> S'=Store_Node v l r \<and>
          (readiness_settled_search,Pair_Term (readiness_table_term T)
            (Pair_Term k' (store_term readiness_row_value r)))\<in>Y)"
      by (rule readiness_settled_searches.unfold[OF clause' into shape])
    show "\<exists>bs v. k=path_term bs \<and> store_lookup S' bs=Some v \<and> readiness_answered_at T (readiness_row_value v)"
      using cases
    proof (elim disjE exE conjE)
      fix v l r
      assume k: "k=Payload_Term []" and S': "S'=Store_Node (Some v) l r"
        and answered: "(readiness_answered,Pair_Term (readiness_table_term T) (readiness_row_value v))\<in>Y"
      have "readiness_answered_at T (readiness_row_value v)"
        by (rule readiness_invariant_answered_at[OF Y_invariant[OF answered]])
      then show ?thesis using k S' by (intro exI[of _ "[]"] exI[of _ v]) simp
    next
      fix k' v l r
      assume k: "k=Pair_Term (bit_term False) k'" and S': "S'=Store_Node v l r"
        and inner: "(readiness_settled_search,Pair_Term (readiness_table_term T)
          (Pair_Term k' (store_term readiness_row_value l)))\<in>Y"
      obtain bs w where k': "k'=path_term bs" and lookup: "store_lookup l bs=Some w"
        and found: "readiness_answered_at T (readiness_row_value w)"
        using readiness_invariant_search_at[OF Y_invariant[OF inner]] by blast
      show ?thesis using k k' S' lookup found by (intro exI[of _ "False#bs"] exI[of _ w]) simp
    next
      fix k' v l r
      assume k: "k=Pair_Term (bit_term True) k'" and S': "S'=Store_Node v l r"
        and inner: "(readiness_settled_search,Pair_Term (readiness_table_term T)
          (Pair_Term k' (store_term readiness_row_value r)))\<in>Y"
      obtain bs w where k': "k'=path_term bs" and lookup: "store_lookup r bs=Some w"
        and found: "readiness_answered_at T (readiness_row_value w)"
        using readiness_invariant_search_at[OF Y_invariant[OF inner]] by blast
      show ?thesis using k k' S' lookup found by (intro exI[of _ "True#bs"] exI[of _ w]) simp
    qed
  next
    fix T v
    assume site: "d=readiness_answered"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T) v"
    have rule: "S=decode_finite_schema readiness_answered_rule"
      using clause site readiness_answered_family.family by auto
    have fields: "f [0]=readiness_table_term T" "v=Pair_Term (Payload_Term []) (f [1])"
      using shape by (simp_all add: rule readiness_answered_rule_def)
    have given: "(readiness_some,Pair_Term (f [0]) (f [1]))\<in>Y"
      using native_rule_support[OF into[unfolded rule readiness_answered_rule_def]] by simp
    have some: "\<forall>vs. f [1]=data_list_term vs \<longrightarrow>
        (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z))"
    proof (intro allI impI)
      fix vs assume valued: "f [1]=data_list_term vs"
      have "(readiness_some,Pair_Term (readiness_table_term T) (data_list_term vs))\<in>Y"
        using given fields(1) valued by simp
      then show "\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
        by (rule readiness_invariant_some_at[OF Y_invariant])
    qed
    show "readiness_answered_at T v" unfolding readiness_answered_at_def using fields(2) some by blast
  next
    fix T vs
    assume site: "d=readiness_some"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T) (data_list_term vs)"
    have clause': "((readiness_some,c),S)\<in>system_clauses native_readiness_system"
      using clause site by simp
    obtain h vs' where vs: "vs=h#vs'"
      and choice: "(readiness_all,Pair_Term (readiness_table_term T) h)\<in>Y \<or>
        (readiness_some,Pair_Term (readiness_table_term T) (data_list_term vs'))\<in>Y"
      using readiness_somes.unfold[OF clause' into shape] by blast
    show "\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
      using choice
    proof
      assume all: "(readiness_all,Pair_Term (readiness_table_term T) h)\<in>Y"
      have "\<forall>zs. h=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
      proof (intro allI impI)
        fix zs assume valued: "h=data_list_term zs"
        show "\<forall>z\<in>set zs. readiness_settled_key T z"
          by (rule readiness_invariant_all_at[OF Y_invariant[OF all[unfolded valued]]])
      qed
      then show ?thesis using vs by auto
    next
      assume rest: "(readiness_some,Pair_Term (readiness_table_term T) (data_list_term vs'))\<in>Y"
      have "\<exists>v\<in>set vs'. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. readiness_settled_key T z)"
        by (rule readiness_invariant_some_at[OF Y_invariant[OF rest]])
      then show ?thesis using vs by auto
    qed
  next
    fix T zs
    assume site: "d=readiness_all"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T) (data_list_term zs)"
    have clause': "((readiness_all,c),S)\<in>system_clauses native_readiness_system"
      using clause site by simp
    have cases: "zs=[] \<or> (\<exists>z zs'. zs=z#zs' \<and> (readiness_settled,Pair_Term (readiness_table_term T) z)\<in>Y \<and>
        (readiness_all,Pair_Term (readiness_table_term T) (data_list_term zs'))\<in>Y)"
      by (rule readiness_alls.unfold[OF clause' into shape])
    show "\<forall>z\<in>set zs. readiness_settled_key T z"
      using cases
    proof
      assume "zs=[]"
      then show ?thesis by simp
    next
      assume "\<exists>z zs'. zs=z#zs' \<and> (readiness_settled,Pair_Term (readiness_table_term T) z)\<in>Y \<and>
        (readiness_all,Pair_Term (readiness_table_term T) (data_list_term zs'))\<in>Y"
      then obtain z zs' where zs: "zs=z#zs'"
        and head: "(readiness_settled,Pair_Term (readiness_table_term T) z)\<in>Y"
        and tail: "(readiness_all,Pair_Term (readiness_table_term T) (data_list_term zs'))\<in>Y"
        by blast
      have "readiness_settled_key T z" by (rule readiness_invariant_settled_at[OF Y_invariant[OF head]])
      moreover have "\<forall>z\<in>set zs'. readiness_settled_key T z"
        by (rule readiness_invariant_all_at[OF Y_invariant[OF tail]])
      ultimately show ?thesis using zs by simp
    qed
  qed
qed

theorem native_settled_sound:
  assumes "(readiness_settled,Pair_Term (readiness_table_term T) (path_term bs))\<in>positive_meaning native_readiness_system"
  shows "bs\<in>table_settled T"
  using readiness_invariant_settled_at[OF readiness_invariant_holds[OF assms]] by simp

theorem native_settled_complete:
  assumes formed: "readiness_table_formed T" and settled: "bs\<in>table_settled T"
  shows "(readiness_settled,Pair_Term (readiness_table_term T) (path_term bs))\<in>positive_meaning native_readiness_system"
  using settled
proof (induction rule: table_settled.induct)
  case (settle k hs h)
  let ?c="readiness_table_term T"
  have cf: "term_formed ?c" by simp
  have given: "\<forall>x\<in>set h. (readiness_settled,Pair_Term ?c (path_term x))\<in>positive_meaning native_readiness_system"
    using settle.IH by blast
  have all: "(readiness_all,Pair_Term ?c (data_list_term (map path_term h)))\<in>positive_meaning native_readiness_system"
    using cf given by (simp add: readiness_alls.exact)
  have some: "(readiness_some,Pair_Term ?c (readiness_decompositions hs))\<in>positive_meaning native_readiness_system"
    using cf all settle.hyps(2) by (auto simp: readiness_somes.exact readiness_decompositions_def data_list_term_formed)
  have "(readiness_answered,evaluate_pattern (native_values [?c,readiness_decompositions hs])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_answered_family.native_step[where c="[0]" and
        ps="[([0],(readiness_some,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
      (use some cf in \<open>simp_all add: readiness_answered_rule_def\<close>)
  then have answered: "(readiness_answered,Pair_Term ?c (readiness_row_value (True,hs)))
      \<in>positive_meaning native_readiness_system"
    by (simp add: readiness_row_value_def readiness_value_def readiness_status_def)
  have lookup: "store_lookup (path_store T) k=Some (True,hs)"
    by (rule readiness_table_lookup[OF formed settle.hyps(1)])
  have search: "(readiness_settled_search,Pair_Term ?c (Pair_Term (path_term k)
      (store_term readiness_row_value (path_store T))))\<in>positive_meaning native_readiness_system"
    using cf answered lookup
    by (auto simp: readiness_settled_searches.exact[OF readiness_row_value_formed] path_term_injective)
  have "(readiness_settled,evaluate_pattern (native_values [?c,path_term k])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_settled_family.native_step[where c="[0]" and
        ps="[([0],(readiness_settled_search,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 0))))]"])
      (use search cf in \<open>simp_all add: readiness_settled_rule_def readiness_table_term_def\<close>)
  then show ?case by simp
qed

theorem native_settled_exact:
  assumes formed: "readiness_table_formed T"
  shows "(readiness_settled,Pair_Term (readiness_table_term T) (path_term bs))\<in>positive_meaning native_readiness_system \<longleftrightarrow>
    bs\<in>table_settled T"
  using native_settled_sound native_settled_complete[OF formed] by blast

section \<open>Native readiness\<close>

lemma native_every_settled:
  assumes formed: "readiness_table_formed T"
  shows "(readiness_every,Pair_Term (readiness_table_term T) (readiness_decompositions hs))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)"
proof -
  have cf: "term_formed (readiness_table_term T)" by simp
  have each: "(readiness_all,Pair_Term (readiness_table_term T) (data_list_term (map path_term h)))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> (\<forall>x\<in>set h. x\<in>table_settled T)" for h
    using readiness_alls.exact cf native_settled_exact[OF formed] by simp
  show ?thesis using readiness_everys.exact cf each by (simp add: readiness_decompositions_def)
qed

theorem native_ready_exact:
  assumes xf: "term_formed x" and formed: "readiness_table_formed T" and kf: "term_formed k"
  shows "(readiness_ready,Pair_Term x (Pair_Term (readiness_table_term T) (Pair_Term k (readiness_value a hs))))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> \<not>a \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)"
proof
  assume holds: "(readiness_ready,Pair_Term x (Pair_Term (readiness_table_term T) (Pair_Term k (readiness_value a hs))))
    \<in>positive_meaning native_readiness_system"
  obtain c F f where rule: "(c,F)\<in>set [([0::nat],readiness_ready_rule)]"
    and assignment: "\<forall>a\<in>schema_variables (decode_finite_schema F). term_formed (f a)"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term x (Pair_Term (readiness_table_term T) (Pair_Term k (readiness_value a hs)))"
    and support: "\<forall>s e q. (s,e,q)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (e,evaluate_pattern f q)\<in>positive_meaning native_readiness_system"
    by (rule readiness_ready_family.holds_cases[OF holds])
  have F: "F=readiness_ready_rule" using rule by simp
  have fields: "f [1]=readiness_table_term T" "readiness_status a=Pair_Term (Payload_Term []) (Payload_Term [])"
      "f [3]=readiness_decompositions hs"
    using shape by (auto simp: F readiness_ready_rule_def readiness_value_def)
  have opened: "\<not>a" using fields(2) by (simp add: readiness_status_open)
  have given: "(readiness_every,Pair_Term (f [1]) (f [3]))\<in>positive_meaning native_readiness_system"
    using native_rule_support[OF support[unfolded F readiness_ready_rule_def]] by simp
  have "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T"
    using given fields(1,3) native_every_settled[OF formed] by simp
  then show "\<not>a \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)" using opened by blast
next
  assume "\<not>a \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)"
  then have opened: "\<not>a" and settled: "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T" by blast+
  let ?c="readiness_table_term T"
  have cf: "term_formed ?c" by simp
  have every: "(readiness_every,Pair_Term ?c (readiness_decompositions hs))\<in>positive_meaning native_readiness_system"
    using native_every_settled[OF formed] settled by simp
  have "(readiness_ready,evaluate_pattern (native_values [x,?c,k,readiness_decompositions hs])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
        (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload [])
          (Finite_Pattern_Payload [])) (native_var 3)))))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_ready_family.native_step[where c="[0]" and
        ps="[([0],(readiness_every,Finite_Pattern_Pair (native_var 1) (native_var 3)))]"])
      (use every xf cf kf in \<open>simp_all add: readiness_ready_rule_def\<close>)
  then show "(readiness_ready,Pair_Term x (Pair_Term ?c (Pair_Term k (readiness_value a hs))))
      \<in>positive_meaning native_readiness_system"
    using opened by (simp add: readiness_value_def readiness_status_def)
qed

section \<open>Rows and tables are presented by their finite terms\<close>

text \<open>
  A row's executable term presents the row: its key is the path of its bits, its status the leaf or the pair
  of leaves, a decomposition the data list of its premise paths. A table's executable term is the executable
  store of its rows, which presents the path store of the rows.
\<close>

definition finite_readiness_status :: "bool \<Rightarrow> finite_factor_term" where
  "finite_readiness_status a=(if a then Finite_Payload [] else Finite_Pair (Finite_Payload []) (Finite_Payload []))"

lemma decode_finite_readiness_status [simp]:
  "decode_finite_term (finite_readiness_status a)=readiness_status a"
  by (cases a) (simp_all add: finite_readiness_status_def readiness_status_def)

definition finite_readiness_value :: "bool \<Rightarrow> bool list list list \<Rightarrow> finite_factor_term" where
  "finite_readiness_value a hs=Finite_Pair (finite_readiness_status a)
    (finite_data_list (map (\<lambda>h. finite_data_list (map finite_path h)) hs))"

lemma decode_finite_readiness_value [simp]:
  "decode_finite_term (finite_readiness_value a hs)=readiness_value a hs"
  by (simp add: finite_readiness_value_def readiness_value_def readiness_decompositions_def comp_def)

definition finite_readiness_row_value :: "bool\<times>bool list list list \<Rightarrow> finite_factor_term" where
  "finite_readiness_row_value r=finite_readiness_value (fst r) (snd r)"

lemma decode_finite_readiness_row_value: "decode_finite_term \<circ> finite_readiness_row_value=readiness_row_value"
  by (rule ext) (simp add: finite_readiness_row_value_def readiness_row_value_def)

definition finite_readiness_row :: "bool list \<Rightarrow> bool \<Rightarrow> bool list list list \<Rightarrow> finite_factor_term" where
  "finite_readiness_row k a hs=finite_store_row finite_readiness_row_value (k,(a,hs))"

lemma decode_finite_readiness_row:
  "decode_finite_term (finite_readiness_row k a hs)=Pair_Term (path_term k) (readiness_value a hs)"
  by (simp add: finite_readiness_row_def finite_store_row_def finite_readiness_row_value_def)

definition finite_readiness_table :: "readiness_table \<Rightarrow> finite_factor_term" where
  "finite_readiness_table T=finite_listing_store finite_readiness_row_value T"

lemma decode_finite_readiness_table:
  "decode_finite_term (finite_readiness_table T)=readiness_table_term T"
  by (simp add: finite_readiness_table_def finite_listing_store_def readiness_table_term_def decode_finite_store
    decode_finite_readiness_row_value)

section \<open>Native readiness is a condition of its own\<close>

text \<open>
  A native question judges a candidate by a condition, a native program installed at one of its
  entries. Native readiness is such a program: installed beside the guard source, whose single
  definition it neither calls nor is called by, its condition holds of a subject and a candidate
  exactly when native readiness holds of their pair.
\<close>

definition native_readiness_condition :: "native_development_condition option" where
  "native_readiness_condition=finite_standalone_condition finite_native_readiness readiness_ready"

lemma native_readiness_ready_member: "readiness_ready\<in>system_definitions native_readiness_system"
  by (simp add: native_readiness_definitions readiness_definitions_def)

lemma native_readiness_separate: "(None,[Suc 0])\<notin>system_definitions native_readiness_system"
  by (simp add: native_readiness_definitions readiness_definitions_def)

theorem native_readiness_condition_total: "\<exists>C. native_readiness_condition=Some C"
  using finite_standalone_condition_total[OF native_readiness_formed[unfolded native_readiness_system_def]
    native_readiness_separate[unfolded native_readiness_system_def]
    native_readiness_ready_member[unfolded native_readiness_system_def]]
  by (simp add: native_readiness_condition_def)

theorem native_readiness_condition_exact:
  assumes condition: "native_readiness_condition=Some C"
  shows "development_condition_holds C x y \<longleftrightarrow>
    (readiness_ready,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning native_readiness_system"
  using finite_standalone_condition_exact[OF native_readiness_formed[unfolded native_readiness_system_def]
    native_readiness_separate[unfolded native_readiness_system_def]
    native_readiness_ready_member[unfolded native_readiness_system_def]
    condition[unfolded native_readiness_condition_def]]
  by (simp only: native_readiness_system_def)

text \<open>
  The program's own clauses state the empty payload, which ends every list, is the status of an answered row,
  is one bit's shape and the empty store, and no other octet: a key is a path of shapes, and problems are
  compared only for equality. Its contracts state its meaning on every single-valued table: settlement is the
  closure \<open>table_settled\<close>, and a row is ready exactly when it is open and every premise of every one of its
  decompositions is settled in the table it is judged with. Nothing here decides a problem by reading its key
  or the subject beside it.
\<close>

end
