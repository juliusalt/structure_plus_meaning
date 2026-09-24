theory Development_Verdict_Mentions
imports Development_Subject_Index
begin

section \<open>Two fields of one shape: a row's mentions read against a family of atoms\<close>

text \<open>
  The verdict's field \<open>excess\<close> reads the statements of one subject against the support of a request;
  the assessment's field \<open>undeclared\<close> reads every row, and every root, against the declared atoms of the
  whole state. Both pass a row's mentions, as a list, to a mention checker given the context: the support,
  the list of keys the request's body holds, of which each mention must be a member, and the declaration
  store, built from the state's declaring rows, in which each must be found. They are one row reading at
  two checkers, kept apart at what each demands of the state: \<open>excess\<close> the rows about one key,
  \<open>undeclared\<close> every row.

  Both are stated positively. Acceptance reads that every mention is found; the list of the offending
  constants, which needs a store's absence, is not built here. \<open>excess\<close> reads the rows about the subject
  through the subject index of each family (theory \<open>Development_Subject_Index\<close>): it
  visits no row that is not about the key and compares no key with another.
\<close>

section \<open>A key is found in a store\<close>

text \<open>
  A store of atoms is searched by a key with the store's own search, whose checker accepts every value
  found: finding a key reads the store at its path and nothing of the value there. A mention is found when
  the store given as the context holds a value at its key; a row's mentions are found when each is.
\<close>

definition native_any_rule :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_any_rule=finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 1)) []"

definition store_found_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "store_found_rule k=native_context_call_rule k"

declare native_any_rule_def [code_unfold]

locale store_found_program = native_rule_family P m "[([0],store_found_rule k)]" +
    search: native_store_search_program P k ch + any: native_rule_family P ch "[([0],native_any_rule)]"
  for P :: "'u native_system" and m k ch :: "'u definition_site"
begin

sublocale call: native_context_call_program P m k
  unfolding native_context_call_program_def using native_rule_family_axioms by (simp only: store_found_rule_def)

sublocale any_law: native_rule_law P ch "[([0],native_any_rule)]"
  by (rule native_rule_lawI[OF any.native_rule_family_axioms]) (auto simp: native_any_rule_def)

lemma any_exact: "(ch,Pair_Term x y)\<in>positive_meaning P \<longleftrightarrow> term_formed x \<and> term_formed y"
proof
  assume "(ch,Pair_Term x y)\<in>positive_meaning P"
  then show "term_formed x \<and> term_formed y" using any.holds_formed by fastforce
next
  assume formed: "term_formed x \<and> term_formed y"
  show "(ch,Pair_Term x y)\<in>positive_meaning P"
    unfolding any_law.exact
    by (rule exI[of _ "[0]"], rule exI[of _ "Finite_Pattern_Pair (native_var 0) (native_var 1)"],
      rule exI[of _ "[]"], rule exI[of _ "native_values [x,y]"]) (use formed in \<open>auto simp: native_any_rule_def\<close>)
qed

theorem exact:
  assumes valued: "\<And>y. term_formed (val y)"
  shows "(m,Pair_Term (store_term val T) (path_term q))\<in>positive_meaning P \<longleftrightarrow> store_lookup T q\<noteq>None"
proof -
  have sf: "term_formed (store_term val T)" by (rule store_term_formed[OF valued])
  have "(k,Pair_Term (store_term val T) (Pair_Term (path_term q) (store_term val T)))\<in>positive_meaning P
      \<longleftrightarrow> store_lookup T q\<noteq>None"
    using sf by (auto simp: search.exact[OF valued] any_exact valued path_term_injective)
  then show ?thesis by (simp only: call.exact)
qed

end

definition row_mentions_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_mentions_rule e=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(e,Finite_Pattern_Pair (native_var 0) (native_var 4)))]"

text \<open>
  A row's mentions are read by a mention checker: @{const row_mentions_rule} passes the list of the keys a
  row mentions, beside the context, to the checker \<open>e\<close>. The reading is stated once, over any checker
  (@{text row_mentions_program.exact}); the checkers are the store a mention is found in
  (@{text store_mentions_program}, which \<open>undeclared\<close> reads) and the list a mention is a member of
  (@{text mentions_cited_program}, which \<open>excess\<close> and request construction's \<open>support complete\<close> read).
\<close>

locale row_mentions_program = native_rule_family P r "[([0],row_mentions_rule e)]"
  for P :: "'u native_system" and r e :: "'u definition_site"
begin

sublocale rearranged: native_rearranging_program P r
    "row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)" e
    "Finite_Pattern_Pair (native_var 0) (native_var 4)"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def
  using native_rule_family_axioms[unfolded row_mentions_rule_def] by (auto simp: row_pattern_def)

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term x (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    (e,Pair_Term x (keys_term (row_mentions (snd z))))\<in>positive_meaning P"
  by (simp add: rearranged.row_at[OF refl _ identity] row_valuation_def)

end

text \<open>The first checker: every mention is found in the store given as the context (@{locale store_found_program}).\<close>

locale store_mentions_program = mentions: row_mentions_program P r e + found: store_found_program P m k ch +
    every: native_every_program P e m
  for P :: "'u native_system" and r e m k ch :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)" and valued: "\<And>y. term_formed (val y)"
  shows "(r,Pair_Term (store_term val T) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>q\<in>set (row_mentions (snd z)). store_lookup T q\<noteq>None)"
  using store_term_formed[OF valued, where T=T]
  by (simp add: mentions.exact[OF identity] keys_term_def every.exact found.exact[OF valued])

end

text \<open>
  The second checker: every mention is a member of the list given as the context. A key is cited in a list
  of keys when it is a member of it (@{locale list_cited_program}, theory \<open>Native_Collection_Programs\<close>); its
  reading at a list of keys is stated once here, and every call that asks whether a key is cited in a family
  of keys reads it.
\<close>

context list_cited_program
begin

theorem exact: "(w,Pair_Term (keys_term ks) (path_term q))\<in>positive_meaning P \<longleftrightarrow> q\<in>set ks"
  by (simp add: keys_term_def list_exact)

end

locale mentions_cited_program = mentions: row_mentions_program P r e +
    every: native_every_program P e w + cited: list_cited_program P w m
  for P :: "'u native_system" and r e w m :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (keys_term ks) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    set (row_mentions (snd z))\<subseteq>set ks"
  by (auto simp: mentions.exact[OF identity] keys_term_def[of "row_mentions (snd z)"] every.exact cited.exact)

end

section \<open>The support store and the declaration store\<close>

text \<open>
  The support store holds each key of a family of keys at its own path, and is single-valued by
  construction; the witnesses of \<open>excess\<close> read it.
  The declaration store holds, at the key of each declared constant, the key of the row
  declaring it: the index of the declaring rows by the constant declared. Its single-valuedness follows,
  under \<^const>\<open>state_presents\<close>, from the exporter's obligation that every constant of the state is declared
  by at most one entity (@{text declarations_single_valued_presented}); \<open>undeclared\<close> needs only that a key
  is present, which holds whatever the rows.
\<close>

definition support_store :: "state_key list \<Rightarrow> state_key binary_path_store" where
  "support_store ks=path_store (map (\<lambda>q. (q,q)) ks)"

definition support_term :: "state_key list \<Rightarrow> factor_term" where
  "support_term ks=store_term path_term (support_store ks)"

lemma support_term_formed [simp]: "term_formed (support_term ks)"
  unfolding support_term_def by (rule store_term_formed) simp

lemma support_store_lookup: "store_lookup (support_store ks) q\<noteq>None \<longleftrightarrow> q\<in>set ks"
  unfolding support_store_def by (simp only: path_store_present) (force simp: image_image)


definition declaration_rows :: "'i state_family list \<Rightarrow> (state_key\<times>state_key) list" where
  "declaration_rows Fs=concat (map (\<lambda>F. concat (map (\<lambda>z. map (\<lambda>d. (d,fst z)) (row_declared (snd z))) F)) Fs)"

lemma declaration_rows_member:
  "(d,e)\<in>set (declaration_rows Fs) \<longleftrightarrow> (\<exists>F\<in>set Fs. \<exists>p. (e,p)\<in>set F \<and> d\<in>set (row_declared p))"
  by (auto simp: declaration_rows_def) (blast, force)

definition declaration_store :: "'i state_family list \<Rightarrow> state_key binary_path_store" where
  "declaration_store Fs=path_store (declaration_rows Fs)"

definition declaration_term :: "'i state_family list \<Rightarrow> factor_term" where
  "declaration_term Fs=store_term path_term (declaration_store Fs)"

lemma declaration_term_formed [simp]: "term_formed (declaration_term Fs)"
  unfolding declaration_term_def by (rule store_term_formed) simp

definition declarations_single_valued :: "'i state_family list \<Rightarrow> bool" where
  "declarations_single_valued Fs \<longleftrightarrow> single_valued (set (declaration_rows Fs))"

theorem declaration_store_at:
  assumes sv: "declarations_single_valued Fs"
  shows "store_lookup (declaration_store Fs) d=Some e \<longleftrightarrow>
    (\<exists>F\<in>set Fs. \<exists>p. (e,p)\<in>set F \<and> d\<in>set (row_declared p))"
  using path_store_lookup[OF sv[unfolded declarations_single_valued_def]]
  by (simp add: declaration_store_def declaration_rows_member)

theorem declaration_store_declared:
  "store_lookup (declaration_store Fs) d\<noteq>None \<longleftrightarrow> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. d\<in>set (row_declared (snd z)))"
  unfolding declaration_store_def path_store_present by (force simp: declaration_rows_def)

lemma declaration_store_found:
  "(\<exists>y. store_lookup (declaration_store Fs) d=Some y) \<longleftrightarrow> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. d\<in>set (row_declared (snd z)))"
  using declaration_store_declared[of Fs d] by auto

text \<open>
  A search of the declaration store, with any checker, finds at a constant's key the key of its one
  declaring row: the store search's own contract read through the carried single-valuedness.
\<close>

theorem declaration_store_search:
  assumes search: "native_store_search_program P k ch" and sv: "declarations_single_valued Fs"
  shows "(k,Pair_Term x (Pair_Term (path_term d) (declaration_term Fs)))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<exists>e. (\<exists>F\<in>set Fs. \<exists>p. (e,p)\<in>set F \<and> d\<in>set (row_declared p)) \<and>
      (ch,Pair_Term x (path_term e))\<in>positive_meaning P)"
proof -
  have "(k,Pair_Term x (Pair_Term (path_term d) (store_term path_term (declaration_store Fs))))\<in>positive_meaning P \<longleftrightarrow>
      term_formed x \<and> (\<exists>bs v. path_term d=path_term bs \<and> store_lookup (declaration_store Fs) bs=Some v \<and>
        (ch,Pair_Term x (path_term v))\<in>positive_meaning P)"
    by (rule native_store_search_program.exact[OF search]) simp
  then show ?thesis by (auto simp: declaration_term_def path_term_injective declaration_store_at[OF sv])
qed

section \<open>The exporter's obligation: every constant is declared by at most one entity\<close>

text \<open>
  The obligation that no two entities of the state declare one constant is stated once, on the Isabelle
  state, where the state's own entities decide it (@{const isabelle_declared_once}, beside the reading it
  constrains in theory \<open>Isabelle_Entities\<close>); its owner is the exporter. The carried single-valuedness
  of the declaration store is not a condition of its own: under \<^const>\<open>state_presents\<close> it is this
  obligation read through the presentation (@{text declarations_single_valued_presented}), as distinct
  names, vacuous unknown positions and distinct roots are for task 46's carried conditions.
\<close>

theorem declarations_single_valued_presented:
  assumes present: "state_presents key S R" and once: "isabelle_declared_once (snd S)"
    and families: "set Fs\<subseteq>range (state_entities R)"
  shows "declarations_single_valued Fs"
  unfolding declarations_single_valued_def single_valued_def
proof (intro allI impI)
  fix d a b
  assume da: "(d,a)\<in>set (declaration_rows Fs)" and db: "(d,b)\<in>set (declaration_rows Fs)"
  have declared_inside: "\<And>e c. e\<in>set (snd (snd S)) \<Longrightarrow> c\<in>set (entity_declared e) \<Longrightarrow> c<length (fst (snd S))"
    by (rule state_presents_declared_inside[OF present])
  have inj: "inj_on key {..<length (fst (snd S))}"
    by (rule atoms_present_key_injective[OF state_presents_atoms[OF present]])
  obtain F p where F: "F\<in>set Fs" and ap: "(a,p)\<in>set F" and dp: "d\<in>set (row_declared p)"
    using da by (auto simp: declaration_rows_member)
  obtain G q where G: "G\<in>set Fs" and bq: "(b,q)\<in>set G" and dq: "d\<in>set (row_declared q)"
    using db by (auto simp: declaration_rows_member)
  obtain m where m: "F=state_entities R m" using F families by auto
  obtain n where n: "G=state_entities R n" using G families by auto
  have ar: "(a,p)\<in>set (state_entities R m)" using ap m by simp
  have br: "(b,q)\<in>set (state_entities R n)" using bq n by simp
  obtain e where e: "e\<in>set (snd (snd S))" and pe: "p=entity_row key (snd S) e"
    using state_presents_row_origin[OF present ar] by metis
  obtain e' where e': "e'\<in>set (snd (snd S))" and qe: "q=entity_row key (snd S) e'"
    using state_presents_row_origin[OF present br] by metis
  obtain c1 where c1: "c1\<in>set (entity_declared e)" "d=key c1" using dp pe by auto
  obtain c2 where c2: "c2\<in>set (entity_declared e')" "d=key c2" using dq qe by auto
  have "c1=c2"
    using inj declared_inside[OF e c1(1)] declared_inside[OF e' c2(1)] c1(2) c2(2) by (auto simp: inj_on_eq_iff)
  then have "isabelle_declared_constant e=Some c1" "isabelle_declared_constant e'=Some c1"
    using c1(1) c2(1) by (auto simp: entity_declared_def split: option.splits)
  then have "e=e'" using once e e' unfolding isabelle_declared_once_def by blast
  then have "q=p" using pe qe by simp
  then show "a=b"
    using keyed_agreeD[OF state_presents_row_keys[OF present] presented_rows_member[OF ar] presented_rows_member[OF br]]
    by simp
qed

section \<open>The program of the two fields\<close>

abbreviation verdict_found_any :: "local_address option definition_site" where
  "verdict_found_any \<equiv> (Some [],[23])"
abbreviation verdict_found_search :: "local_address option definition_site" where
  "verdict_found_search \<equiv> (Some [],[24])"
abbreviation verdict_key_found :: "local_address option definition_site" where
  "verdict_key_found \<equiv> (Some [],[25])"
abbreviation verdict_keys_found :: "local_address option definition_site" where
  "verdict_keys_found \<equiv> (Some [],[26])"
abbreviation verdict_row_found :: "local_address option definition_site" where
  "verdict_row_found \<equiv> (Some [],[27])"
abbreviation verdict_subject_search :: "local_address option definition_site" where
  "verdict_subject_search \<equiv> (Some [],[28])"
abbreviation verdict_subject_family :: "local_address option definition_site" where
  "verdict_subject_family \<equiv> (Some [],[29])"
abbreviation verdict_excess :: "local_address option definition_site" where
  "verdict_excess \<equiv> (Some [],[30])"
abbreviation verdict_found_family :: "local_address option definition_site" where
  "verdict_found_family \<equiv> (Some [],[31])"
abbreviation verdict_found_selection :: "local_address option definition_site" where
  "verdict_found_selection \<equiv> (Some [],[32])"
abbreviation verdict_undeclared :: "local_address option definition_site" where
  "verdict_undeclared \<equiv> (Some [],[33])"

abbreviation verdict_key_cited :: "local_address option definition_site" where
  "verdict_key_cited \<equiv> (Some [],[19])"
abbreviation verdict_mentions_cited :: "local_address option definition_site" where
  "verdict_mentions_cited \<equiv> (Some [],[20])"
abbreviation verdict_row_cited :: "local_address option definition_site" where
  "verdict_row_cited \<equiv> (Some [],[21])"
abbreviation verdict_cited_family :: "local_address option definition_site" where
  "verdict_cited_family \<equiv> (Some [],[22])"

definition undeclared_rule :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "undeclared_rule u f=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(u,Finite_Pattern_Pair (native_var 0) (native_var 1))),([1],(f,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

text \<open>
  A field reading two selections calls both on one context: @{const undeclared_rule}, whose conclusion pairs
  the context with the two arguments and whose two premises call the two sites, is that conjunction for any
  two sites. Its program is the family's law (@{locale native_rule_law}) at the one rule with two premises,
  and its contract is stated once here: every site of the rule is an instance of this program.
\<close>

locale conjoined_calls_program = native_rule_family P s "[([0],undeclared_rule u f)]"
  for P :: "'u native_system" and s u f :: "'u definition_site"
begin

sublocale law: native_rule_law P s "[([0],undeclared_rule u f)]"
  by (rule native_rule_lawI[OF native_rule_family_axioms]) (auto simp: undeclared_rule_def)

theorem exact: "(s,Pair_Term x (Pair_Term a b))\<in>positive_meaning P \<longleftrightarrow>
    (u,Pair_Term x a)\<in>positive_meaning P \<and> (f,Pair_Term x b)\<in>positive_meaning P"
proof
  assume "(s,Pair_Term x (Pair_Term a b))\<in>positive_meaning P"
  then obtain c p ps g where rule: "(c,finite_native_rule p ps)\<in>set [([0]::local_address,undeclared_rule u f)]"
    and shape: "evaluate_pattern g (decode_finite_pattern p)=Pair_Term x (Pair_Term a b)"
    and support: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern g (decode_finite_pattern q))\<in>positive_meaning P"
    unfolding law.exact by blast
  from rule have p: "p=Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))"
    and ps: "set ps={([0],(u,Finite_Pattern_Pair (native_var 0) (native_var 1))),
      ([1],(f,Finite_Pattern_Pair (native_var 0) (native_var 2)))}"
    by (simp_all add: undeclared_rule_def finite_native_rule_eq_iff)
  have fields: "g [0]=x" "g [1]=a" "g [2]=b" using shape by (simp_all add: p)
  show "(u,Pair_Term x a)\<in>positive_meaning P \<and> (f,Pair_Term x b)\<in>positive_meaning P"
    using support fields by (auto simp: ps)
next
  assume both: "(u,Pair_Term x a)\<in>positive_meaning P \<and> (f,Pair_Term x b)\<in>positive_meaning P"
  have formed: "term_formed x" "term_formed a" "term_formed b"
    using both by (auto dest: positive_meaning_term_formed)
  show "(s,Pair_Term x (Pair_Term a b))\<in>positive_meaning P"
    unfolding law.exact
    by (rule exI[of _ "[0]"],
      rule exI[of _ "Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))"],
      rule exI[of _ "[([0],(u,Finite_Pattern_Pair (native_var 0) (native_var 1))),
        ([1],(f,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"],
      rule exI[of _ "native_values [x,a,b]"]) (use both formed in \<open>auto simp: undeclared_rule_def\<close>)
qed

end

text \<open>
  The list checker's membership is the rows program's, at @{text verdict_row_member}: the mentions program
  holds it first, so it is closed alone, and the verdict's program, which holds the rows program, drops it
  there (theory \<open>Development_Native_Verdict\<close>).
\<close>

definition verdict_mentions_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "verdict_mentions_definitions=[(verdict_row_member,native_member_rules verdict_row_member),
    (verdict_found_any,[([0],native_any_rule)]),
    (verdict_found_search,native_store_search_rules verdict_found_search verdict_found_any),
    (verdict_key_found,[([0],store_found_rule verdict_found_search)]),
    (verdict_keys_found,native_every_rules verdict_keys_found verdict_key_found),
    (verdict_row_found,[([0],row_mentions_rule verdict_keys_found)]),
    (verdict_key_cited,[([0],native_swap_rule verdict_row_member)]),
    (verdict_mentions_cited,native_every_rules verdict_mentions_cited verdict_key_cited),
    (verdict_row_cited,[([0],row_mentions_rule verdict_mentions_cited)]),
    (verdict_cited_family,native_every_rules verdict_cited_family verdict_row_cited),
    (verdict_subject_search,native_store_search_rules verdict_subject_search verdict_cited_family),
    (verdict_subject_family,[([0],subject_call_rule verdict_subject_search)]),
    (verdict_excess,native_every_rules verdict_excess verdict_subject_family),
    (verdict_found_family,native_every_rules verdict_found_family verdict_row_found),
    (verdict_found_selection,native_every_rules verdict_found_selection verdict_found_family),
    (verdict_undeclared,[([0],undeclared_rule verdict_found_selection verdict_found_family)])]"

definition finite_verdict_mentions :: "local_address option finite_native_system" where
  "finite_verdict_mentions=finite_rule_program verdict_mentions_definitions"

definition verdict_mentions_system :: "local_address option native_system" where
  "verdict_mentions_system=decode_finite_system finite_verdict_mentions"

lemma finite_verdict_mentions_formed: "finite_system_formed finite_verdict_mentions"
  by code_simp

lemma verdict_mentions_formed: "schema_system_formed verdict_mentions_system"
  using finite_verdict_mentions_formed by (simp only: verdict_mentions_system_def finite_system_formed_correct)

lemma verdict_mentions_family:
  assumes member: "(d,rs)\<in>set verdict_mentions_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family verdict_mentions_system d rs"
  unfolding verdict_mentions_system_def finite_verdict_mentions_def
  by (rule finite_rule_program_family[OF verdict_mentions_formed[unfolded verdict_mentions_system_def
      finite_verdict_mentions_def] _ member plain]) (simp add: verdict_mentions_definitions_def)

lemmas verdict_mentions_rule_defs = verdict_mentions_definitions_def native_every_rules_def native_every_nil_def
  native_every_step_def native_store_search_rules_def
  native_store_found_rule_def native_store_left_rule_def native_store_right_rule_def native_any_rule_def
  store_found_rule_def native_context_call_rule_def row_mentions_rule_def subject_call_rule_def undeclared_rule_def
  native_member_rules_def native_member_here_def native_member_later_def native_swap_rule_def

interpretation mention_found: store_mentions_program verdict_mentions_system verdict_row_found verdict_keys_found
    verdict_key_found verdict_found_search verdict_found_any
  unfolding store_mentions_program_def row_mentions_program_def store_found_program_def
    native_store_search_program_def native_every_program_def
  by (intro conjI; rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation cited_mentions: mentions_cited_program verdict_mentions_system verdict_row_cited
    verdict_mentions_cited verdict_key_cited verdict_row_member
  unfolding mentions_cited_program_def row_mentions_program_def list_cited_program_def
    native_swap_program_def native_member_program_def native_every_program_def
  by (intro conjI; rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation subject_searches: native_store_search_program verdict_mentions_system verdict_subject_search
    verdict_cited_family
  unfolding native_store_search_program_def
  by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation subject_calls: native_rule_family verdict_mentions_system verdict_subject_family
    "[([0],subject_call_rule verdict_subject_search)]"
  by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation subject_selections: native_every_program verdict_mentions_system verdict_excess
    verdict_subject_family
  unfolding native_every_program_def by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation found_families: native_every_program verdict_mentions_system verdict_found_family verdict_row_found
  unfolding native_every_program_def by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation found_selections: native_every_program verdict_mentions_system verdict_found_selection
    verdict_found_family
  unfolding native_every_program_def by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

interpretation undeclared_entry: conjoined_calls_program verdict_mentions_system verdict_undeclared
    verdict_found_selection verdict_found_family
  unfolding conjoined_calls_program_def
  by (rule verdict_mentions_family) (simp_all add: verdict_mentions_rule_defs)

section \<open>The field \<open>excess\<close>, over any program, any selection and any support\<close>

lemma answer_statements_excess_empty:
  "development_answer_statements_excess kind C P S=[] \<longleftrightarrow>
    (\<forall>e\<in>set (development_answer_statements kind C P). \<forall>d\<in>set (entity_mentions e). d |\<in>| S)"
proof
  assume empty: "development_answer_statements_excess kind C P S=[]"
  show "\<forall>e\<in>set (development_answer_statements kind C P). \<forall>d\<in>set (entity_mentions e). d |\<in>| S"
  proof (intro ballI)
    fix e d
    assume e: "e\<in>set (development_answer_statements kind C P)" and d: "d\<in>set (entity_mentions e)"
    then obtain p where p: "isabelle_specified_proposition e=Some p" "d\<in>set (isabelle_term_constants p)"
      by (cases "isabelle_specified_proposition e") (auto simp: entity_mentions_def)
    have "isabelle_term_constants p\<in>set (List.map_filter (map_option isabelle_term_constants \<circ>
        isabelle_specified_proposition) (development_answer_statements kind C P))"
      unfolding map_filter_member using e p(1) by (intro bexI[of _ e]) simp_all
    then show "d |\<in>| S"
      using empty p(2) unfolding development_answer_statements_excess_def remdups_eq_nil_iff filter_empty_conv
      by auto
  qed
next
  assume "\<forall>e\<in>set (development_answer_statements kind C P). \<forall>d\<in>set (entity_mentions e). d |\<in>| S"
  then show "development_answer_statements_excess kind C P S=[]"
    unfolding development_answer_statements_excess_def remdups_eq_nil_iff filter_empty_conv
    by (auto simp: map_filter_member entity_mentions_def split: option.splits)
qed

text \<open>
  The field \<open>excess\<close> is the subject index's selection reading (@{locale subject_selection_program}) at a row
  reading that holds of a presented support and a row exactly when every key the row mentions is a key of
  the support. The locale is stated over that row reading and the support's presentation, so it holds at any
  mention checker that reads so: \<open>excess\<close>'s own program holds it at the list the request's body holds,
  through @{locale mentions_cited_program} (@{text verdict_excess_program}), which \<open>O\<close>'s closure of theory
  \<open>Development_Edited_Reach\<close> reads at \<open>O\<close>'s own keys, the same list. Its contract
  (@{text excess_program_contract}, stated beside it because it reads the rows of a presented state) holds
  for any program holding it, any \<open>kinds_present\<close> selection and any support family. Request construction's
  \<open>support complete\<close> is the same program at the same list, over the selection of every family (theory
  \<open>Development_Request_Scope\<close>).
\<close>

locale excess_program = search: native_store_search_program P k v + family: native_every_program P v r +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r :: "'u definition_site" +
  fixes ident :: "'i \<Rightarrow> factor_term" and present :: "state_key list \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)" and present_formed: "\<And>ks. term_formed (present ks)"
    and row_exact: "\<And>ks z. (r,Pair_Term (present ks) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
      set (row_mentions (snd z))\<subseteq>set ks"
begin

sublocale selection: subject_selection_program P s g k v r present ident
    "\<lambda>ks z. set (row_mentions (snd z))\<subseteq>set ks"
  by unfold_locales (simp_all add: identity row_exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (present ks)) (subject_indexes_term ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set ks)"
  by (simp add: selection.exact[OF atom] present_formed)

end

theorem excess_program_contract:
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes program: "excess_program P s g k v r ident present"
    and present: "state_presents key S R" and kinds: "kinds_present replaceable ks"
    and selection: "set Fs=state_entities R ` ks" and bound: "c<length (fst (snd S))"
    and support: "\<And>d. d<length (fst (snd S)) \<Longrightarrow> key d\<in>set ss \<longleftrightarrow> d |\<in>| X"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (present ss))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    development_answer_statements_excess replaceable (snd S) {|c|} X=[]"
proof -
  let ?es="snd (snd S)"
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have mentions_inside: "\<And>e d. e\<in>set ?es \<Longrightarrow> d\<in>set (entity_mentions e) \<Longrightarrow> d<length (fst (snd S))"
    by (rule state_presents_mentions_inside[OF present])
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (present ss))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set ss)"
    by (rule excess_program.exact[OF program atom])
  also have "\<dots> \<longleftrightarrow> (\<forall>a p. (\<exists>k\<in>ks. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p) \<longrightarrow>
      set (row_mentions p)\<subseteq>set ss)"
    using selection_rows_all[OF selection, where P="\<lambda>z. key c\<in>set (row_subjects (snd z))"
      and Q="\<lambda>z. set (row_mentions (snd z))\<subseteq>set ss"] by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>a p. (a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set ?es. replaceable e \<and>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants ?es) e) \<and>
      p=entity_row key (snd S) e) \<longrightarrow> set (row_mentions p)\<subseteq>set ss)"
    by (intro all_cong1 imp_cong selection_rows_about[OF present kinds bound] refl)
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set ?es. replaceable e \<longrightarrow>
      (c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants ?es) e) \<longrightarrow>
      set (row_mentions (entity_row key (snd S) e))\<subseteq>set ss))"
    using entity_row_presented[OF present] by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set ?es. replaceable e \<longrightarrow>
      (c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants ?es) e) \<longrightarrow>
      (\<forall>d\<in>set (entity_mentions e). d |\<in>| X)))"
  proof -
    have m: "set (row_mentions (entity_row key (snd S) e))\<subseteq>set ss \<longleftrightarrow> (\<forall>d\<in>set (entity_mentions e). d |\<in>| X)"
      if e: "e\<in>set ?es" for e
      using mentions_inside[OF e] support by (auto simp: subset_iff)
    show ?thesis using m by blast
  qed
  also have "\<dots> \<longleftrightarrow> development_answer_statements_excess replaceable (snd S) {|c|} X=[]"
    by (auto simp: answer_statements_excess_empty development_answer_statements_def
      development_answer_statement_def list_ex_iff)
  finally show ?thesis .
qed

text \<open>
  \<open>excess\<close>'s own program holds the field at its sites, at the list the request's body holds; the verdict's
  field is this interpretation.
\<close>

lemma verdict_excess_program:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "excess_program verdict_mentions_system verdict_excess verdict_subject_family
    verdict_subject_search verdict_cited_family verdict_row_cited ident keys_term"
  unfolding excess_program_def excess_program_axioms_def native_store_search_program_def native_every_program_def
  by (intro conjI allI; (rule verdict_mentions_family | rule identity | rule keys_term_formed |
      rule cited_mentions.exact[OF identity])?) (simp_all add: verdict_mentions_rule_defs)


theorem native_excess_rows:
  assumes identity: "\<And>y. term_formed (ident y)" and atom: "k\<in>set A"
  shows "(verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks)) (subject_indexes_term ident A Fs))
      \<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. k\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set ks)"
  by (rule excess_program.exact[OF verdict_excess_program[OF identity] atom])

section \<open>The field \<open>excess\<close> of a presented state\<close>

theorem native_excess_exact:
  assumes present: "state_presents key S R" and kinds: "kinds_present replaceable ks"
    and selection: "set Fs=state_entities R ` ks" and bound: "c<length (fst (snd S))"
    and support: "\<And>d. d<length (fst (snd S)) \<Longrightarrow> key d\<in>set ss \<longleftrightarrow> d |\<in>| P"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (keys_term ss))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    development_answer_statements_excess replaceable (snd S) {|c|} P=[]"
  by (rule excess_program_contract[OF verdict_excess_program[OF identity] present kinds selection bound support])

text \<open>
  The verdict reads the field in the answer state, with the request's subject and support carried there by
  the correspondence of the two tables. Both are consumed from @{const request_presents}: the subject's key
  unchanged, and the support as the list of the request's support keys, the list the request's body holds,
  which the store of the development's rows finds at the request's locus. A support constant the answer
  state drops is carried outside the answer's table, and so is never mentioned there; the list holds its
  key, which no atom of the answer state carries.
\<close>

corollary native_excess_answer:
  assumes request: "request_presents key S R rows r k ks" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and named: "(!) (fst (snd S)) ` fset (problem_subject (fst r))\<subseteq>set (fst (snd S'))"
    and kinds: "kinds_present replaceable kinds" and selection: "set Fs=state_entities R' ` kinds"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks))
      (subject_indexes_term ident (map fst (state_atoms R')) Fs))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    development_answer_statements_excess replaceable (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject (fst r)))
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (fst (snd (snd r))))=[]"
proof -
  have present: "state_presents key S R" using request by (simp add: request_presents_def)
  have range: "fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}" using request by (simp add: request_presents_def)
  obtain c where subject: "problem_subject (fst r)={|c|}" and k: "k=key c" and bound: "c<length (fst (snd S))"
    and "(k,fst (snd S)!c)\<in>set (state_atoms R)" and keys: "set ks=key ` fset (fst (snd (snd r)))"
    and "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF request])
  let ?f="isabelle_state_embedding (fst (snd S)) (fst (snd S'))"
  have name: "fst (snd S)!c\<in>set (fst (snd S'))" using named subject by simp
  have carried: "key' (?f c)=key c" by (rule keys_shared_embedding[OF present present' shared bound name])
  have "isabelle_name_at (fst (snd S')) (?f c)=Some (fst (snd S)!c)"
    by (rule isabelle_state_embedding_shared) (simp_all add: isabelle_name_at_def bound name)
  then have bound': "?f c<length (fst (snd S'))" by (simp add: isabelle_name_at_def split: if_splits)
  have image: "fimage ?f (problem_subject (fst r))={|?f c|}" using subject by simp
  have distinct': "distinct (fst (snd S'))" by (rule state_presents_distinct_names[OF present'])
  have support: "key' q\<in>set ks \<longleftrightarrow> q |\<in>| fimage ?f (fst (snd (snd r)))" if q: "q<length (fst (snd S'))" for q
  proof
    assume "key' q\<in>set ks"
    then obtain d where d: "d |\<in>| fst (snd (snd r))" "key' q=key d" using keys by auto
    have dl: "d<length (fst (snd S))" using range d(1) by auto
    have names: "fst (snd S)!d=fst (snd S')!q" using keys_shared_atom[OF present present' shared dl q] d(2) by simp
    have "?f d=q"
      using isabelle_state_embedding_named[of "fst (snd S)" d "fst (snd S)!d" "fst (snd S')" q]
        isabelle_name_position_at[OF distinct' q] names dl by (simp add: isabelle_name_at_def)
    then show "q |\<in>| fimage ?f (fst (snd (snd r)))" using d(1) by force
  next
    assume "q |\<in>| fimage ?f (fst (snd (snd r)))"
    then obtain d where d: "d |\<in>| fst (snd (snd r))" "q=?f d" by auto
    have dl: "d<length (fst (snd S))" using range d(1) by auto
    have named_d: "fst (snd S)!d\<in>set (fst (snd S'))"
    proof (rule ccontr)
      assume unnamed: "fst (snd S)!d\<notin>set (fst (snd S'))"
      have "?f d=length (fst (snd S'))+d"
        by (rule isabelle_state_embedding_unshared) (use unnamed dl in \<open>simp add: isabelle_name_at_def\<close>)
      then show False using q d(2) by simp
    qed
    have "isabelle_name_at (fst (snd S')) (?f d)=Some (fst (snd S)!d)"
      by (rule isabelle_state_embedding_shared) (simp_all add: isabelle_name_at_def dl named_d)
    then have "fst (snd S')!q=fst (snd S)!d" using q d(2) by (simp add: isabelle_name_at_def)
    then have "key d=key' q" using keys_shared_atom[OF present present' shared dl q] by simp
    then show "key' q\<in>set ks" using keys d(1) by force
  qed
  show ?thesis
    unfolding k carried[symmetric] image
    by (rule native_excess_exact[OF present' kinds selection bound' support identity])
qed

section \<open>The field \<open>undeclared\<close>\<close>

lemma undeclared_entry_exact:
  "(verdict_undeclared,Pair_Term x (Pair_Term y w))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (verdict_found_selection,Pair_Term x y)\<in>positive_meaning verdict_mentions_system \<and>
    (verdict_found_family,Pair_Term x w)\<in>positive_meaning verdict_mentions_system"
  by (rule undeclared_entry.exact)

theorem native_mentions_found:
  assumes identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
    and valued: "\<And>y. term_formed (val y)"
  shows "(verdict_undeclared,Pair_Term (store_term val T) (Pair_Term (state_families_term ident Fs)
      (state_family_term identr Rs)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). store_lookup T q\<noteq>None) \<and>
    (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). store_lookup T q\<noteq>None)"
proof -
  interpret entities: selection_every_reading verdict_mentions_system verdict_found_selection verdict_found_family
      verdict_row_found "store_term val" ident "\<lambda>T z. \<forall>q\<in>set (row_mentions (snd z)). store_lookup T q\<noteq>None"
    by unfold_locales (simp_all add: identity mention_found.exact[OF identity valued])
  interpret roots: family_every_reading verdict_mentions_system verdict_found_family verdict_row_found
      "store_term val" identr "\<lambda>T z. \<forall>q\<in>set (row_mentions (snd z)). store_lookup T q\<noteq>None"
    by unfold_locales (simp_all add: roots mention_found.exact[OF roots valued])
  show ?thesis by (simp add: undeclared_entry_exact entities.exact roots.exact store_term_formed[OF valued])
qed

lemma mentioned_constants_member:
  "c\<in>set (isabelle_mentioned_constants roots C) \<longleftrightarrow>
    (\<exists>t\<in>set roots. c\<in>set (root_mentions t)) \<or> (\<exists>e\<in>set (snd C). c\<in>set (entity_mentions e))"
  by (auto simp: isabelle_mentioned_constants_def map_filter_member root_mentions_def entity_mentions_def
    split: option.splits; metis)

lemma declared_constants_member:
  "c\<in>set (List.map_filter isabelle_declared_constant es) \<longleftrightarrow> (\<exists>e\<in>set es. c\<in>set (entity_declared e))"
  by (auto simp: map_filter_member entity_declared_def split: option.splits; metis)

lemma undeclared_constants_empty:
  "isabelle_undeclared_constants roots C=[] \<longleftrightarrow>
    (\<forall>c\<in>set (isabelle_mentioned_constants roots C). c\<in>set (List.map_filter isabelle_declared_constant (snd C)))"
proof
  assume empty: "isabelle_undeclared_constants roots C=[]"
  show "\<forall>c\<in>set (isabelle_mentioned_constants roots C). c\<in>set (List.map_filter isabelle_declared_constant (snd C))"
  proof
    fix c
    assume mentioned: "c\<in>set (isabelle_mentioned_constants roots C)"
    show "c\<in>set (List.map_filter isabelle_declared_constant (snd C))"
    proof (rule ccontr)
      assume "c\<notin>set (List.map_filter isabelle_declared_constant (snd C))"
      then have "c\<in>set (isabelle_undeclared_constants roots C)"
        using isabelle_undeclared_constants_exact mentioned by blast
      then show False using empty by simp
    qed
  qed
next
  assume all: "\<forall>c\<in>set (isabelle_mentioned_constants roots C). c\<in>set (List.map_filter isabelle_declared_constant (snd C))"
  show "isabelle_undeclared_constants roots C=[]"
  proof (rule ccontr)
    assume "isabelle_undeclared_constants roots C\<noteq>[]"
    then obtain c where "c\<in>set (isabelle_undeclared_constants roots C)"
      by (cases "isabelle_undeclared_constants roots C") auto
    then show False using all isabelle_undeclared_constants_exact by blast
  qed
qed

text \<open>
  A constant of a presented state has a declaration row exactly when the declaration store holds a row at
  its key, and the found program reads that positively. Where the state meets the exporter's obligation
  (@{const isabelle_declared_once}), the declaration store is single-valued
  (@{thm [source] declarations_single_valued_presented}) and the row it holds is the constant's one
  declaration (@{thm [source] declaration_store_at}).
\<close>

lemma covering_families_entity_rows:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
  shows "(\<Union>F\<in>set Fs. set (map snd F))=entity_row key (snd S) ` set (snd (snd S))"
  using kinds_present_rows[OF present, of "\<lambda>_. True" UNIV] families by (simp add: kinds_present_def)

theorem declaration_store_constant:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and bound: "h<length (fst (snd S))"
  shows "store_lookup (declaration_store Fs) (key h)\<noteq>None \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
proof -
  have inj: "inj_on key {..<length (fst (snd S))}"
    by (rule atoms_present_key_injective[OF state_presents_atoms[OF present]])
  have declared_inside: "\<And>e d. e\<in>set (snd (snd S)) \<Longrightarrow> d\<in>set (entity_declared e) \<Longrightarrow> d<length (fst (snd S))"
    by (rule state_presents_declared_inside[OF present])
  have "store_lookup (declaration_store Fs) (key h)\<noteq>None \<longleftrightarrow>
      (\<exists>p\<in>(\<Union>F\<in>set Fs. set (map snd F)). key h\<in>set (row_declared p))"
    by (auto simp: declaration_store_declared declaration_store_found)
  also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). key h\<in>key ` set (entity_declared e))"
    by (simp only: covering_families_entity_rows[OF present families]) auto
  also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
    using declared_inside inj bound by (auto simp: inj_on_eq_iff)
  finally show ?thesis .
qed

theorem native_declared_exact:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and bound: "h<length (fst (snd S))"
  shows "(verdict_key_found,Pair_Term (declaration_term Fs) (path_term (key h)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (\<exists>e\<in>set (snd (snd S)). h\<in>set (entity_declared e))"
  unfolding declaration_term_def
  by (subst mention_found.found.exact) (use declaration_store_constant[OF present families bound] in auto)+

theorem native_undeclared_exact:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
  shows "(verdict_undeclared,Pair_Term (declaration_term Fs) (Pair_Term (state_families_term ident Fs)
      (state_family_term identr (state_roots R))))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    isabelle_undeclared_constants (fst S) (snd S)=[]"
proof -
  let ?C="snd S" and ?es="snd (snd S)" and ?n="fst (snd S)"
  have rows: "(\<Union>F\<in>set Fs. set (map snd F))=entity_row key ?C ` set ?es"
    by (rule covering_families_entity_rows[OF present families])
  have root_rows: "snd ` set (state_roots R)=root_row key ?C ` set (fst S)"
    using state_presents_root_family[OF present] by (metis list.set_map)
  have inj: "inj_on key {..<length ?n}" by (rule atoms_present_key_injective[OF state_presents_atoms[OF present]])
  have declared_inside: "\<And>e d. e\<in>set ?es \<Longrightarrow> d\<in>set (entity_declared e) \<Longrightarrow> d<length ?n"
    by (rule state_presents_declared_inside[OF present])
  have mentions_inside: "\<And>e d. e\<in>set ?es \<Longrightarrow> d\<in>set (entity_mentions e) \<Longrightarrow> d<length ?n"
    by (rule state_presents_mentions_inside[OF present])
  have roots_inside: "\<And>t d. t\<in>set (fst S) \<Longrightarrow> d\<in>set (root_mentions t) \<Longrightarrow> d<length ?n"
    by (rule state_presents_root_mentions_inside[OF present])
  have found: "store_lookup (declaration_store Fs) q\<noteq>None \<longleftrightarrow> (\<exists>e\<in>set ?es. q\<in>key ` set (entity_declared e))" for q
  proof -
    have "store_lookup (declaration_store Fs) q\<noteq>None \<longleftrightarrow>
        (\<exists>p\<in>(\<Union>F\<in>set Fs. set (map snd F)). q\<in>set (row_declared p))"
      by (auto simp: declaration_store_declared declaration_store_found)
    then show ?thesis unfolding rows by auto
  qed
  have key_declared: "key d\<in>key ` set (entity_declared e') \<longleftrightarrow> d\<in>set (entity_declared e')"
    if "d<length ?n" "e'\<in>set ?es" for d e'
    using that declared_inside inj by (auto simp: inj_on_eq_iff)
  have "(verdict_undeclared,Pair_Term (declaration_term Fs) (Pair_Term (state_families_term ident Fs)
      (state_family_term identr (state_roots R))))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (\<forall>p\<in>(\<Union>F\<in>set Fs. set (map snd F)). \<forall>q\<in>set (row_mentions p). store_lookup (declaration_store Fs) q\<noteq>None) \<and>
    (\<forall>p\<in>snd ` set (state_roots R). \<forall>q\<in>set (row_mentions p). store_lookup (declaration_store Fs) q\<noteq>None)"
    unfolding declaration_term_def by (auto simp: native_mentions_found[OF identity roots])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set ?es. \<forall>d\<in>set (entity_mentions e). \<exists>e'\<in>set ?es. d\<in>set (entity_declared e')) \<and>
      (\<forall>t\<in>set (fst S). \<forall>d\<in>set (root_mentions t). \<exists>e'\<in>set ?es. d\<in>set (entity_declared e'))"
    unfolding rows root_rows found using key_declared mentions_inside roots_inside by auto
  also have "\<dots> \<longleftrightarrow> isabelle_undeclared_constants (fst S) (snd S)=[]"
    by (auto simp: undeclared_constants_empty mentioned_constants_member declared_constants_member)
  finally show ?thesis .
qed

end
