theory Development_Request_Citations
imports Development_Request_Scope Development_Verdict_Difference Development_Verdict_Unreached
begin

section \<open>Three fields of request construction that search\<close>

text \<open>
  Request construction checks a support family \<open>ks\<close> and a context family \<open>es\<close> against the presented request
  state. Three of its fields search a store the state's rows present, and each reads a consumed search and
  rebuilds none. \<open>declarations cited\<close> reads the declaration store (theory \<open>Development_Verdict_Mentions\<close>) at
  every key of \<open>ks\<close> and asks that the row key it holds be a key of \<open>es\<close>: the key-level predicate "a key is
  cited" is membership in the list \<open>es\<close> the body holds (@{locale list_cited_program}).
  \<open>context sound\<close> reads the search of the state's rows by row key (@{const family_row_term}, theory
  \<open>Development_Verdict_Difference\<close>) at every key of \<open>es\<close> and asks that the row found there have the subject's
  key among its subjects or declare a key of \<open>ks\<close>. \<open>support sound\<close> reads the reach table over the state's
  constant keys (@{const state_reach_table}, theory \<open>Development_Verdict_Unreached\<close>) at every key of \<open>ks\<close> and
  asks that the subject's key be among its predecessors: the table is the index of the mention relation by
  the constant mentioned.

  Each field is an \<open>every\<close> over one family of the body, whose element call is passed, by one rearranging
  rule, to the store's own search with the call's context. No field reads a kind, a row's identity or a
  store's absence, and no field has a subject of its own beyond the key it is given. Every family of the
  body is read as the list the body holds (@{const keys_term}); no store is built from it.
\<close>

subsection \<open>A keyed search called at an element beside its context\<close>

text \<open>
  An element of a traversal is called beside the traversal's context, a pair; the store's search takes the
  first part of that pair as its context, the element as its key and the second part as its store. One
  rearranging rule passes the call; its contract is the rearranging rule's (@{locale native_rearranging_program}).
\<close>

definition keyed_search_call_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "keyed_search_call_rule k=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))
    [([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 2) (native_var 1))))]"

locale keyed_search_call_program = native_rule_family P s "[([0],keyed_search_call_rule k)]"
  for P :: "'u native_system" and s k :: "'u definition_site"

sublocale keyed_search_call_program \<subseteq> rearranged: native_rearranging_program P s
  "Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)" k
  "Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 2) (native_var 1))"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def
  using native_rule_family_axioms[unfolded keyed_search_call_rule_def] by auto

context keyed_search_call_program
begin

theorem exact:
  "(s,Pair_Term (Pair_Term a b) c)\<in>positive_meaning P \<longleftrightarrow> (k,Pair_Term a (Pair_Term c b))\<in>positive_meaning P"
  using rearranged.at[of "native_values [a,b,c]"] by simp

end

subsection \<open>The rows of a keyed presentation\<close>

text \<open>
  The two keyed readings of a presentation's rows stand with the entity-key condition in
  \<open>Development_State_Rows\<close> (@{thm [source] keyed_rows_exist}, @{thm [source] keyed_rows_all}); the fields
  below consume them.
\<close>

lemma row_declared_key:
  "q\<in>set (row_declared (entity_row key C e)) \<longleftrightarrow> (\<exists>d. q=key d \<and> isabelle_declared_constant e=Some d)"
  by (auto simp: entity_declared_def split: option.splits)

lemma declared_inside:
  assumes present: "state_presents key S R" and e: "e\<in>set (snd (snd S))"
    and declared: "isabelle_declared_constant e=Some d"
  shows "d<length (fst (snd S))"
proof -
  have "d\<in>set (entity_declared e)" by (simp add: entity_declared_def declared)
  then show ?thesis by (rule state_presents_declared_inside[OF present e])
qed

subsection \<open>The support of a request, read through the mentions of its scope\<close>

text \<open>
  The support is the mentions of the scope and every support constant is a position of the state; both
  stand with the support in \<open>Development_Request_Scope\<close> (@{thm [source] request_support_mentions},
  @{thm [source] request_support_inside}) and are consumed here.
\<close>

text \<open>
  In a state whose \<open>undeclared\<close> field holds, every support constant is declared: the half of the
  declarations condition that is the request state's own.
\<close>

lemma request_support_declared:
  assumes closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and d: "d |\<in>| development_request_support (snd S) c"
  shows "\<exists>e\<in>set (snd (snd S)). isabelle_declared_constant e=Some d"
proof -
  obtain e where scope: "e\<in>set (development_constant_scope (snd S) c)" and m: "d\<in>set (entity_mentions e)"
    using d by (auto simp: request_support_mentions)
  have "d\<in>set (isabelle_mentioned_constants (fst S) (snd S))"
    using scope m by (auto simp: mentioned_constants_member development_constant_scope_member)
  then have "d\<in>set (List.map_filter isabelle_declared_constant (snd (snd S)))"
    using closed by (simp add: undeclared_constants_empty)
  then show ?thesis by (auto simp: declared_constants_member entity_declared_def split: option.splits)
qed

subsection \<open>The field \<open>declarations cited\<close>\<close>

text \<open>
  At every key of \<open>ks\<close> the declaration store is searched with the store's own search, whose checker is
  membership in the list \<open>es\<close> (@{locale list_cited_program}): the row key the declaration store holds is
  cited. No rule of its own.
\<close>

locale declarations_cited_program =
    every: native_every_program P u el + call: keyed_search_call_program P el k +
    search: native_store_search_program P k w + cited: list_cited_program P w m
  for P :: "'u native_system" and u el k w m :: "'u definition_site"
begin

lemma element:
  "(el,Pair_Term (Pair_Term (keys_term es) (declaration_term Fs)) (path_term q))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>y. store_lookup (declaration_store Fs) q=Some y \<and> y\<in>set es)"
proof -
  have "(el,Pair_Term (Pair_Term (keys_term es) (declaration_term Fs)) (path_term q))\<in>positive_meaning P \<longleftrightarrow>
      (k,Pair_Term (keys_term es) (Pair_Term (path_term q) (declaration_term Fs)))\<in>positive_meaning P"
    by (rule call.exact)
  also have "\<dots> \<longleftrightarrow> (\<exists>bs v. path_term q=path_term bs \<and> store_lookup (declaration_store Fs) bs=Some v \<and>
      (w,Pair_Term (keys_term es) (path_term v))\<in>positive_meaning P)"
    unfolding declaration_term_def by (simp add: search.exact[where val=path_term, OF path_term_formed])
  also have "\<dots> \<longleftrightarrow> (\<exists>y. store_lookup (declaration_store Fs) q=Some y \<and> y\<in>set es)"
    by (simp add: path_term_injective cited.exact)
  finally show ?thesis .
qed

theorem exact:
  "(u,Pair_Term (Pair_Term (keys_term es) (declaration_term Fs)) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>q\<in>set ks. \<exists>y. store_lookup (declaration_store Fs) q=Some y \<and> y\<in>set es)"
  by (simp add: keys_term_def[of ks] every.exact element)

text \<open>
  Its contract: the declaration store's single-valuedness is derived from the exporter's obligation
  (@{thm [source] declarations_single_valued_presented}), and every key of \<open>ks\<close> is then the key of a
  constant whose declaring entity is keyed in \<open>es\<close>.
\<close>

theorem contract:
  assumes present: "state_presents key S R" and once: "isabelle_declared_once (snd S)"
    and families: "set Fs=range (state_entities R)" and keyed: "entity_rows_keyed key ekey S R"
  shows "(u,Pair_Term (Pair_Term (keys_term es) (declaration_term Fs)) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)"
proof -
  have sv: "declarations_single_valued Fs"
    by (rule declarations_single_valued_presented[OF present once]) (simp add: families)
  have rows: "(\<Union>F\<in>set Fs. set F)=presented_rows R" by (auto simp: families presented_rows_def)
  have at: "store_lookup (declaration_store Fs) q=Some y \<longleftrightarrow>
      (\<exists>z\<in>presented_rows R. fst z=y \<and> q\<in>set (row_declared (snd z)))" for q y
    unfolding declaration_store_at[OF sv] rows[symmetric] by force
  have each: "(\<exists>y. store_lookup (declaration_store Fs) q=Some y \<and> y\<in>set es) \<longleftrightarrow>
      (\<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)" for q
  proof -
    have "(\<exists>y. store_lookup (declaration_store Fs) q=Some y \<and> y\<in>set es) \<longleftrightarrow>
        (\<exists>z\<in>presented_rows R. fst z\<in>set es \<and> q\<in>set (row_declared (snd z)))"
      by (auto simp: at)
    also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). ekey e\<in>set es \<and> q\<in>set (row_declared (entity_row key (snd S) e)))"
      using keyed_rows_exist[OF present keyed, where Q="\<lambda>b p. b\<in>set es \<and> q\<in>set (row_declared p)"] by simp
    also have "\<dots> \<longleftrightarrow> (\<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)"
      by (simp only: row_declared_key) blast
    finally show ?thesis .
  qed
  show ?thesis by (simp add: exact each)
qed

text \<open>
  Under the declarations condition's half that is the request's own — the keys of \<open>ks\<close> are the keys of
  support constants — the field reads: for every support constant keyed in \<open>ks\<close>, its declaring entity is
  keyed in \<open>es\<close>. That every support constant is declared is @{thm [source] request_support_declared}.
\<close>

corollary contract_support:
  assumes present: "state_presents key S R" and once: "isabelle_declared_once (snd S)"
    and families: "set Fs=range (state_entities R)" and keyed: "entity_rows_keyed key ekey S R"
    and within: "set ks\<subseteq>key ` fset (development_request_support (snd S) c)"
  shows "(u,Pair_Term (Pair_Term (keys_term es) (declaration_term Fs)) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>d. d |\<in>| development_request_support (snd S) c \<longrightarrow> key d\<in>set ks \<longrightarrow>
      (\<exists>e\<in>set (snd (snd S)). isabelle_declared_constant e=Some d \<and> ekey e\<in>set es))"
proof -
  have inj: "inj_on key {..<length (fst (snd S))}"
    by (rule state_presents_key_injective[OF present])
  have same: "d=d'" if "d |\<in>| development_request_support (snd S) c" "e\<in>set (snd (snd S))"
      "isabelle_declared_constant e=Some d'" "key d=key d'" for d d' e
    using inj request_support_inside[OF present that(1)] declared_inside[OF present that(2,3)] that(4)
    by (auto simp: inj_on_eq_iff)
  show ?thesis unfolding contract[OF present once families keyed]
  proof
    assume all: "\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
    show "\<forall>d. d |\<in>| development_request_support (snd S) c \<longrightarrow> key d\<in>set ks \<longrightarrow>
        (\<exists>e\<in>set (snd (snd S)). isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)"
    proof (intro allI impI)
      fix d
      assume d: "d |\<in>| development_request_support (snd S) c" and k: "key d\<in>set ks"
      obtain d' e where "key d=key d'" "e\<in>set (snd (snd S))" "isabelle_declared_constant e=Some d'" "ekey e\<in>set es"
        using all k by blast
      then show "\<exists>e\<in>set (snd (snd S)). isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
        using same[OF d] by metis
    qed
  next
    assume all: "\<forall>d. d |\<in>| development_request_support (snd S) c \<longrightarrow> key d\<in>set ks \<longrightarrow>
        (\<exists>e\<in>set (snd (snd S)). isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)"
    show "\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
    proof
      fix q
      assume q: "q\<in>set ks"
      obtain d where d: "d |\<in>| development_request_support (snd S) c" "q=key d" using within q by blast
      then show "\<exists>d e. q=key d \<and> e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
        using all q by blast
    qed
  qed
qed

end

subsection \<open>The field \<open>support sound\<close>\<close>

text \<open>
  At every key of \<open>ks\<close> the reach table is searched with the store's own search; the row found holds a status
  and the list of the key's predecessors, and its checker asks, by membership, that the subject's key be
  among them. The checker is membership's rule that passes the rest of a pair on
  (@{const native_member_later}) at the membership site: a row's status read and its predecessors passed
  on, which is what the reach's step does at its some-element site.
\<close>

locale predecessor_check_program = native_rule_family P ch "[([0],native_member_later m)]" +
    members: native_member_program P m
  for P :: "'u native_system" and ch m :: "'u definition_site"

sublocale predecessor_check_program \<subseteq> rearranged: native_rearranging_program P ch
  "Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))" m
  "Finite_Pattern_Pair (native_var 0) (native_var 2)"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def
  using native_rule_family_axioms[unfolded native_member_later_def] by auto

context predecessor_check_program
begin

theorem exact:
  "(ch,Pair_Term x (Pair_Term st w))\<in>positive_meaning P \<longleftrightarrow> term_formed st \<and> (m,Pair_Term x w)\<in>positive_meaning P"
  using rearranged.at[of "native_values [x,st,w]"] by (simp add: insert_Diff_if)

end

locale support_sound_program =
    every: native_every_program P u el + call: keyed_search_call_program P el k +
    search: native_store_search_program P k ch + check: predecessor_check_program P ch m
  for P :: "'u native_system" and u el k ch m :: "'u definition_site"
begin

lemma element:
  "(el,Pair_Term (Pair_Term (path_term q0) (reach_table_term T)) (path_term q))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>v. store_lookup (path_store T) q=Some v \<and> q0\<in>set (snd v))"
proof -
  have "(el,Pair_Term (Pair_Term (path_term q0) (reach_table_term T)) (path_term q))\<in>positive_meaning P \<longleftrightarrow>
      (k,Pair_Term (path_term q0) (Pair_Term (path_term q) (reach_table_term T)))\<in>positive_meaning P"
    by (rule call.exact)
  also have "\<dots> \<longleftrightarrow> (\<exists>v. store_lookup (path_store T) q=Some v \<and>
      (ch,Pair_Term (path_term q0) (reach_row_value v))\<in>positive_meaning P)"
    unfolding reach_table_term_def
    by (simp add: search.exact[where val=reach_row_value, OF reach_row_value_formed] path_term_injective)
  also have "\<dots> \<longleftrightarrow> (\<exists>v. store_lookup (path_store T) q=Some v \<and> q0\<in>set (snd v))"
    by (simp add: reach_row_value_def reach_value_def check.exact check.members.exact)
  finally show ?thesis .
qed

theorem exact:
  "(u,Pair_Term (Pair_Term (path_term q0) (reach_table_term T)) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>q\<in>set ks. \<exists>v. store_lookup (path_store T) q=Some v \<and> q0\<in>set (snd v))"
  by (simp add: keys_term_def every.exact element)

text \<open>
  Its contract, by the reach table's row lemma (@{thm [source] state_reach_table_row}): the predecessors of a
  key are the keys of the subjects of the rows mentioning it, so the subject's key is among them exactly when
  some row of the subject's scope mentions the key, and every key of \<open>ks\<close> is the key of a support constant.
\<close>

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and families: "set Fs=range (state_entities R)"
  shows "(u,Pair_Term (Pair_Term (path_term (key c))
      (reach_table_term (state_reach_table (state_atoms R) (state_roots R) Fs))) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
    set ks\<subseteq>key ` fset (development_request_support (snd S) c)"
proof -
  let ?T="state_reach_table (state_atoms R) (state_roots R) Fs"
  have sv: "single_valued (set ?T)" using state_reach_table_formed by (simp add: reach_table_formed_def)
  have at: "(\<exists>v. store_lookup (path_store ?T) q=Some v \<and> key c\<in>set (snd v)) \<longleftrightarrow>
      q\<in>fst ` set (state_atoms R) \<and> key c\<in>set (state_reach_predecessors Fs q)" for q
    by (auto simp: path_store_lookup[OF sv] state_reach_table_row split_paired_Ex)
  have each: "q\<in>fst ` set (state_atoms R) \<and> key c\<in>set (state_reach_predecessors Fs q) \<longleftrightarrow>
    q\<in>key ` fset (development_request_support (snd S) c)" for q
  proof
    assume "q\<in>fst ` set (state_atoms R) \<and> key c\<in>set (state_reach_predecessors Fs q)"
    then obtain d where d: "d<length (fst (snd S))" "q=key d"
      and pred: "key c\<in>set (state_reach_predecessors Fs (key d))"
      using state_atom_keys[OF present families] by auto
    obtain e s where e: "e\<in>set (snd (snd S))" and ks: "key c=key s" and m: "d\<in>set (entity_mentions e)"
      and sj: "s\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
      using pred state_reach_predecessor_at[OF present families d(1)] by blast
    have sb: "set [s]\<subseteq>{..<length (fst (snd S))}"
      using state_presents_subject_inside[OF present e sj] by simp
    have "c=s" using state_presents_key_member[OF present bound sb] ks by simp
    then have "e\<in>set (development_constant_scope (snd S) c)"
      using e sj by (simp add: development_constant_scope_member)
    then have "d |\<in>| development_request_support (snd S) c"
      using m by (auto simp: request_support_mentions)
    then show "q\<in>key ` fset (development_request_support (snd S) c)" by (simp add: d(2))
  next
    assume "q\<in>key ` fset (development_request_support (snd S) c)"
    then obtain d where d: "d |\<in>| development_request_support (snd S) c" "q=key d" by auto
    obtain e where scope: "e\<in>set (development_constant_scope (snd S) c)" and m: "d\<in>set (entity_mentions e)"
      using d(1) by (auto simp: request_support_mentions)
    have bd: "d<length (fst (snd S))" by (rule request_support_inside[OF present d(1)])
    have "key c\<in>set (state_reach_predecessors Fs (key d))"
      using scope m state_reach_predecessor_at[OF present families bd]
      by (auto simp: development_constant_scope_member)
    then show "q\<in>fst ` set (state_atoms R) \<and> key c\<in>set (state_reach_predecessors Fs q)"
      using atoms_present_atom[OF state_presents_atoms[OF present] bd] d(2) by force
  qed
  have "(u,Pair_Term (Pair_Term (path_term (key c)) (reach_table_term ?T)) (keys_term ks))\<in>positive_meaning P \<longleftrightarrow>
      (\<forall>q\<in>set ks. \<exists>v. store_lookup (path_store ?T) q=Some v \<and> key c\<in>set (snd v))"
    by (rule exact)
  also have "\<dots> \<longleftrightarrow> (\<forall>q\<in>set ks. q\<in>key ` fset (development_request_support (snd S) c))"
    by (simp only: at each)
  also have "\<dots> \<longleftrightarrow> set ks\<subseteq>key ` fset (development_request_support (snd S) c)" by blast
  finally show ?thesis .
qed

end

subsection \<open>The field \<open>context sound\<close>\<close>

text \<open>
  At every key of \<open>es\<close> the state's rows are searched by row key over every family, and the row found is read
  in the context of the list \<open>ks\<close> and the subject's key: it has the subject's key among its
  subjects — the row reading of subjects in that context, @{const permitted_subject_rule} — or it declares a
  key of \<open>ks\<close> — the one new rule, a \<open>some\<close> over its declared keys cited in the list \<open>ks\<close>. The two cases
  are two rules at one site, and both read membership at one site.
\<close>

definition declares_cited_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "declares_cited_rule s=finite_native_rule
    (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3) (native_var 4)
      (native_var 5) (native_var 6))
    [([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))]"

definition context_sound_row_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "context_sound_row_rules mm s=[([0],permitted_subject_rule mm),([1],declares_cited_rule s)]"

locale context_sound_row_program = native_rule_family P r "context_sound_row_rules mm s" +
    somes: native_some_program P s w + cited: list_cited_program P w mm
  for P :: "'u native_system" and r mm s w :: "'u definition_site"
begin

sublocale law: native_rule_law P r "context_sound_row_rules mm s"
  by (rule native_rule_lawI[OF native_rule_family_axioms])
    (auto simp: context_sound_row_rules_def permitted_subject_rule_def declares_cited_rule_def)


theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)"
proof
  assume "(r,Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (state_row_term ident z))\<in>positive_meaning P"
  then obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (context_sound_row_rules mm s)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=
      Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (state_row_term ident z)"
    and support: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    unfolding law.exact by (elim exE conjE) (rule that; assumption)
  have p: "p=row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3)
      (native_var 4) (native_var 5) (native_var 6)"
    using rule by (auto simp: context_sound_row_rules_def permitted_subject_rule_def declares_cited_rule_def
      finite_native_rule_eq_iff)
  have fields: "f [0]=keys_term ks" "f [1]=path_term q0" "f [3]=keys_term (row_declared (snd z))"
      "f [4]=keys_term (row_subjects (snd z))"
    using shape by (simp_all add: p row_pattern_def state_row_term_def)
  have subject_field: "f [Suc 0]=path_term q0" using fields(2) by simp
  from rule consider "set ps={([0],(mm,Finite_Pattern_Pair (native_var 1) (native_var 4)))}"
      | "set ps={([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))}"
    by (auto simp: context_sound_row_rules_def permitted_subject_rule_def declares_cited_rule_def
      finite_native_rule_eq_iff)
  then show "q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)"
  proof cases
    case 1
    have "(mm,Pair_Term (f [1]) (f [4]))\<in>positive_meaning P" using support 1 by auto
    then show ?thesis by (simp add: fields subject_field keys_term_def cited.members.exact)
  next
    case 2
    have "(s,Pair_Term (f [0]) (f [3]))\<in>positive_meaning P" using support 2 by auto
    then show ?thesis by (auto simp: fields keys_term_def[of "row_declared (snd z)"] somes.exact cited.exact)
  qed
next
  assume either: "q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)"
  let ?f="native_values [keys_term ks,path_term q0,path_term (fst z),keys_term (row_declared (snd z)),
    keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))]"
  let ?p="row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3)
    (native_var 4) (native_var 5) (native_var 6)"
  from either consider (subject) "q0\<in>set (row_subjects (snd z))"
    | (declared) "\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks" by blast
  then have "(r,evaluate_pattern ?f (decode_finite_pattern ?p))\<in>positive_meaning P"
  proof cases
    case subject
    show ?thesis
      by (rule law.step_at[where c="[0]" and ps="[([0],(mm,Finite_Pattern_Pair (native_var 1) (native_var 4)))]"])
        (use subject identity in \<open>simp_all add: context_sound_row_rules_def permitted_subject_rule_def
          row_pattern_def keys_term_def cited.members.exact data_list_term_formed insert_Diff_if\<close>)
  next
    case declared
    show ?thesis
      by (rule law.step_at[where c="[1]" and ps="[([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))]"])
        (use declared identity in \<open>simp_all add: context_sound_row_rules_def declares_cited_rule_def
          row_pattern_def keys_term_def[of "row_declared (snd z)"] somes.exact cited.exact data_list_term_formed
          insert_Diff_if\<close>)
  qed
  then show "(r,Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (state_row_term ident z))\<in>positive_meaning P"
    by (simp add: row_pattern_def state_row_term_def)
qed

end

locale context_sound_program = rows: context_sound_row_program P r mm s w +
    search: native_store_search_program P k r + call: keyed_search_call_program P el k +
    every: native_every_program P u el
  for P :: "'u native_system" and u el k r mm s w :: "'u definition_site" +
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma element:
  "(el,Pair_Term (Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (family_row_term ident Fs)) (path_term a))
      \<in>positive_meaning P \<longleftrightarrow>
    (\<exists>z. store_lookup (family_row_store Fs) a=Some z \<and>
      (q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)))"
proof -
  have "(el,Pair_Term (Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (family_row_term ident Fs)) (path_term a))
      \<in>positive_meaning P \<longleftrightarrow>
    (k,Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (Pair_Term (path_term a) (family_row_term ident Fs)))
      \<in>positive_meaning P"
    by (rule call.exact)
  also have "\<dots> \<longleftrightarrow> (\<exists>z. store_lookup (family_row_store Fs) a=Some z \<and>
      (r,Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (state_row_term ident z))\<in>positive_meaning P)"
    unfolding family_row_term_def
    by (simp add: search.exact[where val="state_row_term ident", OF state_row_term_formed[OF identity]]
      path_term_injective)
  also have "\<dots> \<longleftrightarrow> (\<exists>z. store_lookup (family_row_store Fs) a=Some z \<and>
      (q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)))"
    by (simp add: rows.exact[OF identity])
  finally show ?thesis .
qed

theorem exact:
  "(u,Pair_Term (Pair_Term (Pair_Term (keys_term ks) (path_term q0)) (family_row_term ident Fs)) (keys_term es))
      \<in>positive_meaning P \<longleftrightarrow>
    (\<forall>a\<in>set es. \<exists>z. store_lookup (family_row_store Fs) a=Some z \<and>
      (q0\<in>set (row_subjects (snd z)) \<or> (\<exists>d\<in>set (row_declared (snd z)). d\<in>set ks)))"
  by (simp add: keys_term_def[of es] every.exact element family_row_term_formed[OF identity])

text \<open>
  Its contract, under the entity-key condition: every key of \<open>es\<close> is the key of an entity of the subject's
  scope or of an entity declaring a constant keyed in \<open>ks\<close>.
\<close>

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and families: "set Fs=range (state_entities R)" and keyed: "entity_rows_keyed key ekey S R"
  shows "(u,Pair_Term (Pair_Term (Pair_Term (keys_term ks) (path_term (key c))) (family_row_term ident Fs))
      (keys_term es))\<in>positive_meaning P \<longleftrightarrow>
    set es\<subseteq>ekey ` (set (development_constant_scope (snd S) c) \<union>
      {e\<in>set (snd (snd S)). \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks})"
proof -
  let ?Q="\<lambda>p. key c\<in>set (row_subjects p) \<or> (\<exists>d\<in>set (row_declared p). d\<in>set ks)"
  let ?X="set (development_constant_scope (snd S) c) \<union>
    {e\<in>set (snd (snd S)). \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}"
  have rows_eq: "(\<Union>F\<in>set Fs. set F)=presented_rows R" by (auto simp: families presented_rows_def)
  have sv: "single_valued (\<Union>F\<in>set Fs. set F)"
    unfolding rows_eq by (rule state_presents_rows_single_valued[OF present])
  have at: "(\<exists>z. store_lookup (family_row_store Fs) a=Some z \<and> ?Q (snd z)) \<longleftrightarrow>
      (\<exists>z\<in>presented_rows R. fst z=a \<and> ?Q (snd z))" for a
  proof -
    have mem: "(\<exists>F\<in>set Fs. z\<in>set F) \<longleftrightarrow> z\<in>presented_rows R" for z using rows_eq by blast
    show ?thesis by (force simp: family_row_store_lookup[OF sv] mem)
  qed
  have sub: "key c\<in>set (row_subjects (entity_row key (snd S) e)) \<longleftrightarrow>
      e\<in>set (development_constant_scope (snd S) c)" if "e\<in>set (snd (snd S))" for e
    using entity_row_subject_key[OF present bound that] that by (simp add: development_constant_scope_member)
  have point: "(ekey e=a \<and> ?Q (entity_row key (snd S) e)) \<longleftrightarrow>
      (ekey e=a \<and> (e\<in>set (development_constant_scope (snd S) c) \<or>
        (\<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks)))" if "e\<in>set (snd (snd S))" for e a
    using sub[OF that] unfolding Bex_def row_declared_key by blast
  have each: "(\<exists>z\<in>presented_rows R. fst z=a \<and> ?Q (snd z)) \<longleftrightarrow> a\<in>ekey ` ?X" for a
  proof -
    have "(\<exists>z\<in>presented_rows R. fst z=a \<and> ?Q (snd z)) \<longleftrightarrow>
        (\<exists>e\<in>set (snd (snd S)). ekey e=a \<and> ?Q (entity_row key (snd S) e))"
      by (rule keyed_rows_exist[OF present keyed, where Q="\<lambda>b p. b=a \<and> ?Q p"])
    also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). ekey e=a \<and> (e\<in>set (development_constant_scope (snd S) c) \<or>
        (\<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks)))" (is "?L \<longleftrightarrow> ?R")
    proof
      assume ?L
      then obtain e where e: "e\<in>set (snd (snd S))" and h: "ekey e=a \<and> ?Q (entity_row key (snd S) e)" by blast
      then show ?R using point[OF e] by blast
    next
      assume ?R
      then obtain e where e: "e\<in>set (snd (snd S))" and h: "ekey e=a \<and> (e\<in>set (development_constant_scope (snd S) c) \<or>
          (\<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks))" by blast
      then show ?L using point[OF e] by blast
    qed
    also have "\<dots> \<longleftrightarrow> a\<in>ekey ` ?X" by (auto simp: development_constant_scope_member)
    finally show ?thesis .
  qed
  have "(u,Pair_Term (Pair_Term (Pair_Term (keys_term ks) (path_term (key c))) (family_row_term ident Fs))
      (keys_term es))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>a\<in>set es. \<exists>z. store_lookup (family_row_store Fs) a=Some z \<and> ?Q (snd z))"
    by (rule exact)
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>set es. a\<in>ekey ` ?X)" by (simp only: at each)
  also have "\<dots> \<longleftrightarrow> set es\<subseteq>ekey ` ?X" by blast
  finally show ?thesis .
qed

end

end
