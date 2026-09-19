theory Development_Native_Readiness
  imports Native_Collection_Programs Finite_Presented_Collections
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
  the value a keyed table holds) at its own sites, and of three rules of its own. Settlement is a least
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
    (readiness_settled_search,native_keyed_search_rules readiness_settled_search readiness_answered),
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

interpretation readiness_settled_searches: native_keyed_search_program native_readiness_system
    readiness_settled_search readiness_answered
  unfolding native_keyed_search_program_def by (rule native_readiness_family)
    (simp_all add: readiness_definitions_def native_keyed_search_rules_def native_found_rule_def native_skip_rule_def)

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
  its premise keys. A key is settled in a table of rows when an answered row of the table holds it and one
  of its decompositions has every premise settled; this least closure is stated here once, and native
  settlement computes exactly it on every table whose keys are formed terms.
\<close>

type_synonym readiness_table = "(factor_term\<times>bool\<times>factor_term list list) list"

definition readiness_status :: "bool \<Rightarrow> factor_term" where
  "readiness_status answered=(if answered then Payload_Term [] else Pair_Term (Payload_Term []) (Payload_Term []))"

lemma readiness_status_answered: "readiness_status a=Payload_Term [] \<longleftrightarrow> a"
  by (cases a) (simp_all add: readiness_status_def)

lemma readiness_status_open: "readiness_status a=Pair_Term (Payload_Term []) (Payload_Term []) \<longleftrightarrow> \<not>a"
  by (cases a) (simp_all add: readiness_status_def)

lemma readiness_status_formed [simp]: "term_formed (readiness_status a)"
  by (cases a) (simp_all add: readiness_status_def octets_formed_def)

definition readiness_value :: "bool \<Rightarrow> factor_term list list \<Rightarrow> factor_term" where
  "readiness_value a hs=Pair_Term (readiness_status a) (data_list_term (map data_list_term hs))"

lemma readiness_value_formed:
  "term_formed (readiness_value a hs) \<longleftrightarrow> (\<forall>h\<in>set hs. \<forall>x\<in>set h. term_formed x)"
  by (simp add: readiness_value_def data_list_term_formed)

definition readiness_rows :: "readiness_table \<Rightarrow> (factor_term\<times>factor_term) list" where
  "readiness_rows T=map (\<lambda>(k,a,hs). (k,readiness_value a hs)) T"

definition readiness_table_term :: "readiness_table \<Rightarrow> factor_term" where
  "readiness_table_term T=data_list_term (map (case_prod Pair_Term) (readiness_rows T))"

definition readiness_table_formed :: "readiness_table \<Rightarrow> bool" where
  "readiness_table_formed T \<longleftrightarrow>
    (\<forall>e\<in>set T. term_formed (fst e) \<and> (\<forall>h\<in>set (snd (snd e)). \<forall>x\<in>set h. term_formed x))"

inductive_set table_settled :: "readiness_table \<Rightarrow> factor_term set" for T where
  settle: "(k,True,hs)\<in>set T \<Longrightarrow> h\<in>set hs \<Longrightarrow> \<forall>x\<in>set h. x\<in>table_settled T \<Longrightarrow> k\<in>table_settled T"

lemma readiness_rows_member:
  "(k,v)\<in>set (readiness_rows T) \<longleftrightarrow> (\<exists>a hs. (k,a,hs)\<in>set T \<and> v=readiness_value a hs)"
proof
  assume "(k,v)\<in>set (readiness_rows T)"
  then show "\<exists>a hs. (k,a,hs)\<in>set T \<and> v=readiness_value a hs" by (auto simp: readiness_rows_def)
next
  assume "\<exists>a hs. (k,a,hs)\<in>set T \<and> v=readiness_value a hs"
  then obtain a hs where entry: "(k,a,hs)\<in>set T" and valued: "v=readiness_value a hs" by blast
  show "(k,v)\<in>set (readiness_rows T)" unfolding readiness_rows_def set_map
    by (rule rev_image_eqI[OF entry]) (simp add: valued)
qed

lemma readiness_rows_formed:
  assumes "readiness_table_formed T"
  shows "\<forall>(a,v)\<in>set (readiness_rows T). term_formed a \<and> term_formed v"
  using assms by (force simp: readiness_table_formed_def readiness_rows_def readiness_value_formed)

lemma readiness_table_term_formed:
  assumes formed: "readiness_table_formed T"
  shows "term_formed (readiness_table_term T)"
  using readiness_rows_formed[OF formed] by (simp add: readiness_table_term_def data_rows_formed)

section \<open>Native settlement is the least closure\<close>

definition readiness_answered_at :: "readiness_table \<Rightarrow> factor_term \<Rightarrow> bool" where
  "readiness_answered_at T v \<longleftrightarrow> (\<exists>w. v=Pair_Term (Payload_Term []) w \<and>
    (\<forall>vs. w=data_list_term vs \<longrightarrow> (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T))))"

definition readiness_invariant :: "local_address option definition_site \<Rightarrow> factor_term \<Rightarrow> bool" where
  "readiness_invariant d t \<longleftrightarrow>
    (d=readiness_settled \<longrightarrow> (\<forall>T k. t=Pair_Term (readiness_table_term T) k \<longrightarrow> k\<in>table_settled T)) \<and>
    (d=readiness_settled_search \<longrightarrow> (\<forall>T k R. t=Pair_Term (readiness_table_term T)
        (Pair_Term k (data_list_term (map (case_prod Pair_Term) R))) \<longrightarrow>
      (\<exists>v. (k,v)\<in>set R \<and> readiness_answered_at T v))) \<and>
    (d=readiness_answered \<longrightarrow> (\<forall>T v. t=Pair_Term (readiness_table_term T) v \<longrightarrow> readiness_answered_at T v)) \<and>
    (d=readiness_some \<longrightarrow> (\<forall>T vs. t=Pair_Term (readiness_table_term T) (data_list_term vs) \<longrightarrow>
      (\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)))) \<and>
    (d=readiness_all \<longrightarrow> (\<forall>T zs. t=Pair_Term (readiness_table_term T) (data_list_term zs) \<longrightarrow>
      (\<forall>z\<in>set zs. z\<in>table_settled T)))"

lemma readiness_invariant_sites:
  "readiness_invariant readiness_settled t \<longleftrightarrow>
    (\<forall>T k. t=Pair_Term (readiness_table_term T) k \<longrightarrow> k\<in>table_settled T)"
  "readiness_invariant readiness_settled_search t \<longleftrightarrow>
    (\<forall>T k R. t=Pair_Term (readiness_table_term T) (Pair_Term k (data_list_term (map (case_prod Pair_Term) R))) \<longrightarrow>
      (\<exists>v. (k,v)\<in>set R \<and> readiness_answered_at T v))"
  "readiness_invariant readiness_answered t \<longleftrightarrow>
    (\<forall>T v. t=Pair_Term (readiness_table_term T) v \<longrightarrow> readiness_answered_at T v)"
  "readiness_invariant readiness_some t \<longleftrightarrow>
    (\<forall>T vs. t=Pair_Term (readiness_table_term T) (data_list_term vs) \<longrightarrow>
      (\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)))"
  "readiness_invariant readiness_all t \<longleftrightarrow>
    (\<forall>T zs. t=Pair_Term (readiness_table_term T) (data_list_term zs) \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T))"
  by (simp_all add: readiness_invariant_def)

lemma readiness_invariant_settled_at:
  assumes "readiness_invariant readiness_settled (Pair_Term (readiness_table_term T) k)"
  shows "k\<in>table_settled T"
proof -
  have "\<forall>T' k'. Pair_Term (readiness_table_term T) k=Pair_Term (readiness_table_term T') k' \<longrightarrow>
      k'\<in>table_settled T'"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T k] show ?thesis by simp
qed

lemma readiness_invariant_search_at:
  assumes "readiness_invariant readiness_settled_search
    (Pair_Term (readiness_table_term T) (Pair_Term k (data_list_term (map (case_prod Pair_Term) R))))"
  shows "\<exists>v. (k,v)\<in>set R \<and> readiness_answered_at T v"
proof -
  have "\<forall>T' k' R'. Pair_Term (readiness_table_term T) (Pair_Term k (data_list_term (map (case_prod Pair_Term) R)))=
      Pair_Term (readiness_table_term T') (Pair_Term k' (data_list_term (map (case_prod Pair_Term) R'))) \<longrightarrow>
      (\<exists>v. (k',v)\<in>set R' \<and> readiness_answered_at T' v)"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T k R] show ?thesis by simp
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
  shows "\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
proof -
  have "\<forall>T' vs'. Pair_Term (readiness_table_term T) (data_list_term vs)=
      Pair_Term (readiness_table_term T') (data_list_term vs') \<longrightarrow>
      (\<exists>v\<in>set vs'. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T'))"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T vs] show ?thesis by simp
qed

lemma readiness_invariant_all_at:
  assumes "readiness_invariant readiness_all (Pair_Term (readiness_table_term T) (data_list_term zs))"
  shows "\<forall>z\<in>set zs. z\<in>table_settled T"
proof -
  have "\<forall>T' zs'. Pair_Term (readiness_table_term T) (data_list_term zs)=
      Pair_Term (readiness_table_term T') (data_list_term zs') \<longrightarrow> (\<forall>z\<in>set zs'. z\<in>table_settled T')"
    using assms by (simp only: readiness_invariant_sites)
  from this[rule_format, of T zs] show ?thesis by simp
qed

lemma readiness_answered_settled:
  assumes row: "(k,v)\<in>set (readiness_rows T)" and answered: "readiness_answered_at T v"
  shows "k\<in>table_settled T"
proof -
  obtain a hs where entry: "(k,a,hs)\<in>set T" and valued: "v=readiness_value a hs"
    using row by (auto simp: readiness_rows_member)
  obtain w where vw: "v=Pair_Term (Payload_Term []) w"
    and some: "\<forall>vs. w=data_list_term vs \<longrightarrow> (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T))"
    using answered by (auto simp: readiness_answered_at_def)
  have same: "Pair_Term (readiness_status a) (data_list_term (map data_list_term hs))=Pair_Term (Payload_Term []) w"
    using vw valued by (simp add: readiness_value_def)
  have status: "readiness_status a=Payload_Term []" and ww: "w=data_list_term (map data_list_term hs)"
    using same by simp_all
  have entry': "(k,True,hs)\<in>set T" using entry status by (simp add: readiness_status_answered)
  obtain u where u: "u\<in>set (map data_list_term hs)"
    and settled_u: "\<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
    using some ww by blast
  obtain h where h: "h\<in>set hs" and uh: "u=data_list_term h" using u by auto
  have "\<forall>x\<in>set h. x\<in>table_settled T" using settled_u uh by blast
  then show ?thesis by (rule table_settled.settle[OF entry' h])
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
        (Pair_Term k (data_list_term (map (case_prod Pair_Term) (readiness_rows T)))))\<in>Y"
      using given fields by (simp add: readiness_table_term_def)
    obtain v where row: "(k,v)\<in>set (readiness_rows T)" and found: "readiness_answered_at T v"
      using readiness_invariant_search_at[OF Y_invariant[OF search]] by blast
    show "k\<in>table_settled T" by (rule readiness_answered_settled[OF row found])
  next
    fix T k R
    assume site: "d=readiness_settled_search"
      and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term (readiness_table_term T)
        (Pair_Term k (data_list_term (map (case_prod Pair_Term) R)))"
    have clause': "((readiness_settled_search,c),S)\<in>system_clauses native_readiness_system"
      using clause site by simp
    obtain a v R' where R: "R=(a,v)#R'"
      and choice: "(a=k \<and> (readiness_answered,Pair_Term (readiness_table_term T) v)\<in>Y) \<or>
        (readiness_settled_search,Pair_Term (readiness_table_term T)
          (Pair_Term k (data_list_term (map (case_prod Pair_Term) R'))))\<in>Y"
      using readiness_settled_searches.unfold[OF clause' into shape] by blast
    show "\<exists>v. (k,v)\<in>set R \<and> readiness_answered_at T v"
      using choice
    proof
      assume found: "a=k \<and> (readiness_answered,Pair_Term (readiness_table_term T) v)\<in>Y"
      have "readiness_answered_at T v"
        by (rule readiness_invariant_answered_at[OF Y_invariant[OF found[THEN conjunct2]]])
      then show ?thesis using R found by auto
    next
      assume rest: "(readiness_settled_search,Pair_Term (readiness_table_term T)
        (Pair_Term k (data_list_term (map (case_prod Pair_Term) R'))))\<in>Y"
      obtain w where "(k,w)\<in>set R'" "readiness_answered_at T w"
        using readiness_invariant_search_at[OF Y_invariant[OF rest]] by blast
      then show ?thesis using R by auto
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
        (\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T))"
    proof (intro allI impI)
      fix vs assume valued: "f [1]=data_list_term vs"
      have "(readiness_some,Pair_Term (readiness_table_term T) (data_list_term vs))\<in>Y"
        using given fields(1) valued by simp
      then show "\<exists>u\<in>set vs. \<forall>zs. u=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
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
    show "\<exists>v\<in>set vs. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
      using choice
    proof
      assume all: "(readiness_all,Pair_Term (readiness_table_term T) h)\<in>Y"
      have "\<forall>zs. h=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
      proof (intro allI impI)
        fix zs assume valued: "h=data_list_term zs"
        show "\<forall>z\<in>set zs. z\<in>table_settled T"
          by (rule readiness_invariant_all_at[OF Y_invariant[OF all[unfolded valued]]])
      qed
      then show ?thesis using vs by auto
    next
      assume rest: "(readiness_some,Pair_Term (readiness_table_term T) (data_list_term vs'))\<in>Y"
      have "\<exists>v\<in>set vs'. \<forall>zs. v=data_list_term zs \<longrightarrow> (\<forall>z\<in>set zs. z\<in>table_settled T)"
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
    show "\<forall>z\<in>set zs. z\<in>table_settled T"
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
      have "z\<in>table_settled T" by (rule readiness_invariant_settled_at[OF Y_invariant[OF head]])
      moreover have "\<forall>z\<in>set zs'. z\<in>table_settled T" by (rule readiness_invariant_all_at[OF Y_invariant[OF tail]])
      ultimately show ?thesis using zs by simp
    qed
  qed
qed

theorem native_settled_sound:
  assumes "(readiness_settled,Pair_Term (readiness_table_term T) k)\<in>positive_meaning native_readiness_system"
  shows "k\<in>table_settled T"
  by (rule readiness_invariant_settled_at[OF readiness_invariant_holds[OF assms]])

theorem native_settled_complete:
  assumes formed: "readiness_table_formed T" and settled: "k\<in>table_settled T"
  shows "(readiness_settled,Pair_Term (readiness_table_term T) k)\<in>positive_meaning native_readiness_system"
  using settled
proof (induction rule: table_settled.induct)
  case (settle k hs h)
  let ?c="readiness_table_term T"
  have cf: "term_formed ?c" by (rule readiness_table_term_formed[OF formed])
  have given: "\<forall>x\<in>set h. (readiness_settled,Pair_Term ?c x)\<in>positive_meaning native_readiness_system"
    using settle.IH by blast
  have all: "(readiness_all,Pair_Term ?c (data_list_term h))\<in>positive_meaning native_readiness_system"
    using cf given by (simp add: readiness_alls.exact)
  have hs_formed: "\<forall>g\<in>set (map data_list_term hs). term_formed g"
    using formed settle.hyps(1) by (force simp: readiness_table_formed_def data_list_term_formed)
  have some: "(readiness_some,Pair_Term ?c (data_list_term (map data_list_term hs)))\<in>positive_meaning native_readiness_system"
    using cf hs_formed all settle.hyps(2) by (auto simp: readiness_somes.exact)
  have hf: "term_formed (data_list_term (map data_list_term hs))"
    using hs_formed by (simp add: data_list_term_formed)
  have "(readiness_answered,evaluate_pattern (native_values [?c,data_list_term (map data_list_term hs)])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (native_var 1)))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_answered_family.native_step[where c="[0]" and
        ps="[([0],(readiness_some,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
      (use some cf hf in \<open>simp_all add: readiness_answered_rule_def\<close>)
  then have answered: "(readiness_answered,Pair_Term ?c (readiness_value True hs))\<in>positive_meaning native_readiness_system"
    by (simp add: readiness_value_def readiness_status_def)
  have rows_formed: "\<forall>(a,v)\<in>set (readiness_rows T). term_formed a \<and> term_formed v"
    by (rule readiness_rows_formed[OF formed])
  have kf: "term_formed k" using formed settle.hyps(1) by (force simp: readiness_table_formed_def)
  have row: "(k,readiness_value True hs)\<in>set (readiness_rows T)"
    using settle.hyps(1) by (force simp: readiness_rows_def)
  have search: "(readiness_settled_search,Pair_Term ?c (Pair_Term k
      (data_list_term (map (case_prod Pair_Term) (readiness_rows T)))))\<in>positive_meaning native_readiness_system"
    using cf kf rows_formed answered row by (auto simp: readiness_settled_searches.exact)
  have "(readiness_settled,evaluate_pattern (native_values [?c,k])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_settled_family.native_step[where c="[0]" and
        ps="[([0],(readiness_settled_search,Finite_Pattern_Pair (native_var 0)
          (Finite_Pattern_Pair (native_var 1) (native_var 0))))]"])
      (use search cf kf in \<open>simp_all add: readiness_settled_rule_def readiness_table_term_def\<close>)
  then show ?case by simp
qed

theorem native_settled_exact:
  assumes formed: "readiness_table_formed T"
  shows "(readiness_settled,Pair_Term (readiness_table_term T) k)\<in>positive_meaning native_readiness_system \<longleftrightarrow>
    k\<in>table_settled T"
  using native_settled_sound native_settled_complete[OF formed] by blast

section \<open>Native readiness\<close>

lemma native_every_settled:
  assumes formed: "readiness_table_formed T" and decompositions: "\<forall>h\<in>set hs. \<forall>x\<in>set h. term_formed x"
  shows "(readiness_every,Pair_Term (readiness_table_term T) (data_list_term (map data_list_term hs)))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)"
proof -
  have cf: "term_formed (readiness_table_term T)" by (rule readiness_table_term_formed[OF formed])
  have each: "(readiness_all,Pair_Term (readiness_table_term T) (data_list_term h))\<in>positive_meaning native_readiness_system
      \<longleftrightarrow> (\<forall>x\<in>set h. x\<in>table_settled T)" for h
    using readiness_alls.exact cf native_settled_exact[OF formed] by simp
  show ?thesis using readiness_everys.exact cf each by simp
qed

theorem native_ready_exact:
  assumes xf: "term_formed x" and formed: "readiness_table_formed T" and kf: "term_formed k"
    and hs_formed: "\<forall>h\<in>set hs. \<forall>x\<in>set h. term_formed x"
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
      "f [3]=data_list_term (map data_list_term hs)"
    using shape by (auto simp: F readiness_ready_rule_def readiness_value_def)
  have opened: "\<not>a" using fields(2) by (simp add: readiness_status_open)
  have given: "(readiness_every,Pair_Term (f [1]) (f [3]))\<in>positive_meaning native_readiness_system"
    using native_rule_support[OF support[unfolded F readiness_ready_rule_def]] by simp
  have "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T"
    using given fields(1,3) native_every_settled[OF formed hs_formed] by simp
  then show "\<not>a \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)" using opened by blast
next
  assume "\<not>a \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T)"
  then have opened: "\<not>a" and settled: "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T" by blast+
  let ?c="readiness_table_term T"
  have cf: "term_formed ?c" by (rule readiness_table_term_formed[OF formed])
  have every: "(readiness_every,Pair_Term ?c (data_list_term (map data_list_term hs)))\<in>positive_meaning native_readiness_system"
    using native_every_settled[OF formed hs_formed] settled by simp
  have hf: "term_formed (data_list_term (map data_list_term hs))"
    using hs_formed by (simp add: data_list_term_formed)
  have "(readiness_ready,evaluate_pattern (native_values [x,?c,k,data_list_term (map data_list_term hs)])
      (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
        (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Payload [])
          (Finite_Pattern_Payload [])) (native_var 3)))))))\<in>positive_meaning native_readiness_system"
    by (rule readiness_ready_family.native_step[where c="[0]" and
        ps="[([0],(readiness_every,Finite_Pattern_Pair (native_var 1) (native_var 3)))]"])
      (use every xf cf kf hf in \<open>simp_all add: readiness_ready_rule_def\<close>)
  then show "(readiness_ready,Pair_Term x (Pair_Term ?c (Pair_Term k (readiness_value a hs))))
      \<in>positive_meaning native_readiness_system"
    using opened by (simp add: readiness_value_def readiness_status_def)
qed

section \<open>Rows and tables are presented by their finite terms\<close>

text \<open>
  A row given by executable terms, its key and the lists of premise keys of its decompositions, presents
  the row of its decoded terms, and a table of such rows presents the table of its decoded rows: the
  status is the leaf or the pair of leaves, a decomposition the data list of its premise keys.
\<close>

definition finite_readiness_status :: "bool \<Rightarrow> finite_factor_term" where
  "finite_readiness_status a=(if a then Finite_Payload [] else Finite_Pair (Finite_Payload []) (Finite_Payload []))"

lemma decode_finite_readiness_status [simp]:
  "decode_finite_term (finite_readiness_status a)=readiness_status a"
  by (cases a) (simp_all add: finite_readiness_status_def readiness_status_def)

definition finite_readiness_row :: "finite_factor_term \<Rightarrow> bool \<Rightarrow> finite_factor_term list list \<Rightarrow> finite_factor_term" where
  "finite_readiness_row k a hs=Finite_Pair k (Finite_Pair (finite_readiness_status a)
    (finite_data_list (map finite_data_list hs)))"

lemma decode_finite_readiness_row:
  "decode_finite_term (finite_readiness_row k a hs)=
    Pair_Term (decode_finite_term k) (readiness_value a (map (map decode_finite_term) hs))"
  by (simp add: finite_readiness_row_def readiness_value_def comp_def)

definition finite_readiness_table :: "(finite_factor_term\<times>bool\<times>finite_factor_term list list) list \<Rightarrow>
    finite_factor_term" where
  "finite_readiness_table T=finite_data_list (map (\<lambda>(k,a,hs). finite_readiness_row k a hs) T)"

definition decode_readiness_table :: "(finite_factor_term\<times>bool\<times>finite_factor_term list list) list \<Rightarrow>
    readiness_table" where
  "decode_readiness_table T=map (\<lambda>(k,a,hs). (decode_finite_term k,a,map (map decode_finite_term) hs)) T"

lemma decode_finite_readiness_table:
  "decode_finite_term (finite_readiness_table T)=readiness_table_term (decode_readiness_table T)"
  by (induction T) (auto simp: finite_readiness_table_def decode_readiness_table_def readiness_table_term_def
    readiness_rows_def decode_finite_readiness_row)

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
  The program's own clauses state the empty payload, which ends every list and is the status of an answered
  row, and no other octet: problems are compared only for equality. Its contracts state its meaning on every
  table whose keys are formed terms: settlement is the closure \<open>table_settled\<close>, and a row is ready exactly
  when it is open and every premise of every one of its decompositions is settled in the table it is judged
  with. Nothing here decides a problem by reading its key or the subject beside it.
\<close>

end
