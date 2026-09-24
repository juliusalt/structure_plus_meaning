theory Development_Request_Scope
imports Development_Verdict_Mentions Development_Requests
begin

section \<open>Two fields of request construction that read the rows about the subject\<close>

text \<open>
  Request construction checks a request body, a support family \<open>ks\<close> and a context family \<open>es\<close>, against the
  presented request state. Two of its fields read the rows about the subject, and both read them through the
  subject index's selection reading (theory \<open>Development_Subject_Index\<close>) over every family of the state:
  \<open>support complete\<close> asks that every mention of a row about the subject's key be a key of \<open>ks\<close>, and
  \<open>scope cited\<close> asks that the key of every row about the subject be a key of \<open>es\<close>. Each field's call has the
  selection reading's shape: the subject's key with the body's family as context, the indexes of the
  families as value; the family is presented as the store of its keys (@{const support_term}).

  \<open>support complete\<close> is no new notion: it is \<open>excess\<close> (@{locale excess_program}) interpreted at the
  selection of every family, read with the request's own support family; the verdict reads the same field
  in the answer state. The one new rule here is the row predicate "its key is cited": the row's key is found
  in the store given as the context. No field reads a kind, a row's identity or a store's absence.
\<close>

subsection \<open>The rows about the subject, over every family, are the rows of its scope\<close>

text \<open>
  Over the selection of every family of a presented state, the rows having the subject's key among their
  subjects are exactly the rows of the entities of the subject's scope: @{thm [source] selection_rows_about}
  at the selection of every kind. This is what \<open>scope cited\<close>'s contract consumes.
\<close>

lemma request_rows_about:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> Q z) \<longleftrightarrow>
    (\<forall>e\<in>set (development_constant_scope (snd S) c). \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow>
      Q (a,entity_row key (snd S) e))"
proof -
  have kinds: "kinds_present (\<lambda>_. True) UNIV" by (simp add: kinds_present_def)
  have "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> Q z) \<longleftrightarrow>
      (\<forall>a p. (\<exists>k\<in>UNIV. (a,p)\<in>set (state_entities R k)) \<and> key c\<in>set (row_subjects p) \<longrightarrow> Q (a,p))"
    using selection_rows_all[OF selection, where P="\<lambda>z. key c\<in>set (row_subjects (snd z))" and Q=Q] by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>a p. (a,p)\<in>presented_rows R \<and> (\<exists>e\<in>set (snd (snd S)). True \<and>
      c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<and>
      p=entity_row key (snd S) e) \<longrightarrow> Q (a,p))"
    by (intro all_cong1 imp_cong selection_rows_about[OF present kinds bound] refl)
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set (development_constant_scope (snd S) c). \<forall>a.
      (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow> Q (a,entity_row key (snd S) e))"
    by (simp only: Ball_def development_constant_scope_member) blast
  finally show ?thesis .
qed

subsection \<open>The support of a request, read through the mentions of its scope\<close>

text \<open>
  The support of a request is the constants the statements of its subject's scope mention, and each of
  them is a position of the state (@{thm [source] state_presents_mentions_inside}). Both stand here, with
  the support; the field below and the fields of \<open>Development_Request_Citations\<close> consume them.
\<close>

lemma request_support_mentions:
  "d |\<in>| development_request_support C c \<longleftrightarrow>
    (\<exists>e\<in>set (development_constant_scope C c). d\<in>set (entity_mentions e))"
proof -
  have "d\<in>set (entity_mentions e) \<longleftrightarrow>
      (\<exists>p. isabelle_specified_proposition e=Some p \<and> d\<in>set (isabelle_term_constants p))" for e
    by (cases "isabelle_specified_proposition e") (simp_all add: entity_mentions_def)
  then show ?thesis by (simp add: development_request_support_member)
qed

lemma request_support_inside:
  assumes present: "state_presents key S R" and d: "d |\<in>| development_request_support (snd S) c"
  shows "d<length (fst (snd S))"
  using d state_presents_mentions_inside[OF present]
  by (force simp: request_support_mentions development_constant_scope_member)

subsection \<open>The field \<open>support complete\<close> is \<open>excess\<close> at every family\<close>

text \<open>
  The field is @{locale excess_program} at the selection of every kind (\<open>kinds_present (\<lambda>_. True) UNIV\<close>):
  its row reading, its \<open>exact\<close> and its contract are the locale's. Its contract here reads the locale's at
  the support family of the constants the scope's statements mention, taken by name through
  @{thm [source] development_request_support_member}.
\<close>

locale support_complete_program = excess: excess_program P s g k v r e m kf ch ident
  for P :: "'u native_system" and s g k v r e m kf ch :: "'u definition_site"
    and ident :: "isabelle_context \<Rightarrow> factor_term"
begin

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    key ` fset (development_request_support (snd S) c)\<subseteq>set ks"
proof -
  let ?scope="set (development_constant_scope (snd S) c)"
  let ?Y="development_request_support (snd S) c"
  let ?X="ffilter (\<lambda>d. key d\<in>set ks) (fset_of_list [0..<length (fst (snd S))])"
  have kinds: "kinds_present (\<lambda>_. True) UNIV" by (simp add: kinds_present_def)
  have X: "d |\<in>| ?X \<longleftrightarrow> d<length (fst (snd S)) \<and> key d\<in>set ks" for d by (auto simp: fset_of_list_elem)
  have support: "key d\<in>set ks \<longleftrightarrow> d |\<in>| ?X" if "d<length (fst (snd S))" for d using that X by blast
  have Y: "d |\<in>| ?Y \<longleftrightarrow> (\<exists>e\<in>?scope. d\<in>set (entity_mentions e))" for d
    by (rule request_support_mentions)
  have inside: "d<length (fst (snd S))" if "d |\<in>| ?Y" for d
    by (rule request_support_inside[OF present that])
  have statements: "set (development_answer_statements (\<lambda>_. True) (snd S) {|c|})=?scope"
    by (auto simp: development_answer_statements_def development_answer_statement_def list_ex_iff
      development_constant_scope_member)
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    development_answer_statements_excess (\<lambda>_. True) (snd S) {|c|} ?X=[]"
  proof -
    have program: "excess_program P s g k v r e m kf ch ident" by intro_locales
    show ?thesis by (rule excess_program_contract[OF program present kinds selection bound support])
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. \<forall>d\<in>set (entity_mentions e). d |\<in>| ?X)"
    by (simp only: answer_statements_excess_empty statements)
  also have "\<dots> \<longleftrightarrow> (\<forall>d. d |\<in>| ?Y \<longrightarrow> d |\<in>| ?X)" by (simp only: Y) blast
  also have "\<dots> \<longleftrightarrow> key ` fset ?Y\<subseteq>set ks" using X inside by auto
  finally show ?thesis .
qed

text \<open>At the support's own keys the field holds: the request state stays within its own support.\<close>

corollary contract_own:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(s,Pair_Term (Pair_Term (path_term (key c))
      (support_term (map key (sorted_list_of_fset (development_request_support (snd S) c)))))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P"
  by (simp add: contract[OF present bound selection])

end

text \<open>The field's HOL counterpart holds of every state, by the member equation of the support.\<close>

lemma request_support_excess:
  "development_answer_statements_excess (\<lambda>_. True) C {|c|} (development_request_support C c)=[]"
proof (subst answer_statements_excess_empty, intro ballI)
  fix e d
  assume e: "e\<in>set (development_answer_statements (\<lambda>_. True) C {|c|})" and d: "d\<in>set (entity_mentions e)"
  have scope: "e\<in>set (development_constant_scope C c)"
    using e by (auto simp: development_answer_statements_def development_answer_statement_def list_ex_iff
      development_constant_scope_member)
  obtain p where "isabelle_specified_proposition e=Some p" "d\<in>set (isabelle_term_constants p)"
    using d by (cases "isabelle_specified_proposition e") (simp_all add: entity_mentions_def)
  then show "d |\<in>| development_request_support C c"
    using scope by (auto simp: development_request_support_member)
qed

text \<open>\<open>excess\<close>'s own program holds the field at its sites: the field and \<open>excess\<close> are one notion.\<close>

lemma support_complete_excess:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "support_complete_program verdict_mentions_system verdict_excess verdict_subject_family
    verdict_subject_search verdict_found_family verdict_row_found verdict_keys_found verdict_key_found
    verdict_found_search verdict_found_any ident"
  unfolding support_complete_program_def by (rule verdict_excess_program[OF identity])

corollary request_support_complete:
  assumes identity: "\<And>y. term_formed (ident y)"
    and present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(verdict_excess,Pair_Term (Pair_Term (path_term (key c)) (support_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    key ` fset (development_request_support (snd S) c)\<subseteq>set ks"
  by (rule support_complete_program.contract[OF support_complete_excess[OF identity] present bound selection])

subsection \<open>The row predicate "its key is cited"\<close>

text \<open>
  A row's key is cited when the store given as the context holds it: the store's found search at the row's
  key, which reads nothing of the value found.
\<close>

definition key_cited_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "key_cited_rule m=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"

locale key_cited_program = native_rule_family P r "[([0],key_cited_rule m)]" + found: store_found_program P m k ch
  for P :: "'u native_system" and r m k ch :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)" and valued: "\<And>y. term_formed (val y)"
  shows "(r,Pair_Term (store_term val T) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    store_lookup T (fst z)\<noteq>None"
proof
  assume holds: "(r,Pair_Term (store_term val T) (state_row_term ident z))\<in>positive_meaning P"
  obtain c F f where rule: "(c,F)\<in>set [([0]::local_address,key_cited_rule m)]"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
      Pair_Term (store_term val T) (state_row_term ident z)"
    and support: "\<forall>s d q. (s,d,q)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f q)\<in>positive_meaning P"
    by (rule holds_cases[OF holds]) (rule that; assumption)
  have F: "F=key_cited_rule m" using rule by simp
  have premise: "(m,Pair_Term (f [0]) (f [1]))\<in>positive_meaning P"
    using native_rule_support[OF support[unfolded F key_cited_rule_def]] by simp
  have fields: "f [0]=store_term val T" "f [1]=path_term (fst z)"
    using shape by (simp_all add: F key_cited_rule_def row_pattern_def state_row_term_def)
  show "store_lookup T (fst z)\<noteq>None"
    using premise fields by (simp add: found.exact[OF valued])
next
  assume cited: "store_lookup T (fst z)\<noteq>None"
  have sf: "term_formed (store_term val T)" by (rule store_term_formed[OF valued])
  have found: "(m,Pair_Term (store_term val T) (path_term (fst z)))\<in>positive_meaning P"
    using cited by (simp add: found.exact[OF valued])
  have "(r,evaluate_pattern (native_values [store_term val T,path_term (fst z),keys_term (row_declared (snd z)),
      keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))])
      (decode_finite_pattern (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3)
        (native_var 4) (native_var 5))))\<in>positive_meaning P"
    by (rule native_step[where c="[0]" and ps="[([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
      (use found sf identity in \<open>simp_all add: key_cited_rule_def row_pattern_def\<close>)
  then show "(r,Pair_Term (store_term val T) (state_row_term ident z))\<in>positive_meaning P"
    by (simp add: row_pattern_def state_row_term_def)
qed

end

subsection \<open>The field \<open>scope cited\<close> is the selection reading at "its key is cited"\<close>

locale scope_cited_program = cited: key_cited_program P r m kf ch +
    search: native_store_search_program P k v + family: native_every_program P v r +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r m kf ch :: "'u definition_site" +
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma row_exact:
  "(r,Pair_Term (support_term es) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> fst z\<in>set es"
  unfolding support_term_def
  by (subst cited.exact[OF identity]) (auto simp: support_store_lookup support_store_found)

sublocale selection: subject_selection_program P s g k v r support_term ident "\<lambda>es z. fst z\<in>set es"
  by unfold_locales (simp_all add: identity row_exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (support_term es)) (subject_indexes_term ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> fst z\<in>set es)"
  by (simp add: selection.exact[OF atom])

text \<open>
  The contract is stated under the named entity-key condition: the entity key keys every entity's row as
  the presentation does. It is a condition of the presentation, never an assumption of the program.
\<close>

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
    and keyed: "entity_rows_keyed key ekey S R"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term es))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    ekey ` set (development_constant_scope (snd S) c)\<subseteq>set es"
proof -
  let ?scope="set (development_constant_scope (snd S) c)"
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term es))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> fst z\<in>set es)"
    by (rule exact[OF atom])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow> a\<in>set es)"
    using request_rows_about[OF present bound selection, where Q="\<lambda>z. fst z\<in>set es"] by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. ekey e\<in>set es)"
  proof -
    have point: "(\<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow> a\<in>set es) \<longleftrightarrow> ekey e\<in>set es"
      if e: "e\<in>?scope" for e
    proof -
      have "e\<in>set (snd (snd S))" using e by (simp add: development_constant_scope_member)
      then show ?thesis by (rule keyed_rows_all[OF present keyed])
    qed
    show ?thesis using point by blast
  qed
  also have "\<dots> \<longleftrightarrow> ekey ` ?scope\<subseteq>set es" by blast
  finally show ?thesis .
qed

end

end
