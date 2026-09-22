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

  \<open>support complete\<close> is no new notion: it is \<open>excess\<close> (theory \<open>Development_Verdict_Mentions\<close>) at the
  selection of every family, read with the request's own support family; the verdict reads the same field
  in the answer state. The one new rule here is the row predicate "its key is cited": the row's key is found
  in the store given as the context. No field reads a kind, a row's identity or a store's absence.
\<close>

subsection \<open>The rows about the subject, over every family, are the rows of its scope\<close>

text \<open>
  Over the selection of every family of a presented state, the rows having the subject's key among their
  subjects are exactly the rows of the entities of the subject's scope. This is what both contracts consume.
\<close>

lemma request_rows_about:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> Q z) \<longleftrightarrow>
    (\<forall>e\<in>set (development_constant_scope (snd S) c). \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow>
      Q (a,entity_row key (snd S) e))"
proof
  assume rows: "\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> Q z"
  show "\<forall>e\<in>set (development_constant_scope (snd S) c). \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow>
      Q (a,entity_row key (snd S) e)"
  proof (intro ballI allI impI)
    fix e a
    assume e: "e\<in>set (development_constant_scope (snd S) c)" and row: "(a,entity_row key (snd S) e)\<in>presented_rows R"
    have member: "e\<in>set (snd (snd S))"
      and subject: "c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
      using e by (simp_all add: development_constant_scope_member)
    obtain k where family: "(a,entity_row key (snd S) e)\<in>set (state_entities R k)"
      by (rule presented_rows_family[OF row])
    have Fk: "state_entities R k\<in>set Fs" using selection by simp
    have about: "key c\<in>set (row_subjects (entity_row key (snd S) e))"
      using subject by (simp only: entity_row_subject_key[OF present bound member])
    show "Q (a,entity_row key (snd S) e)" using rows Fk family about by fastforce
  qed
next
  assume scope: "\<forall>e\<in>set (development_constant_scope (snd S) c). \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow>
      Q (a,entity_row key (snd S) e)"
  show "\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> Q z"
  proof (intro ballI impI)
    fix F z
    assume F: "F\<in>set Fs" and z: "z\<in>set F" and about: "key c\<in>set (row_subjects (snd z))"
    obtain k where Fk: "F=state_entities R k" using F selection by auto
    obtain a p where zp: "z=(a,p)" by (cases z)
    have row: "(a,p)\<in>set (state_entities R k)" using z Fk zp by simp
    obtain e where member: "e\<in>set (snd (snd S))" and "entity_kind_of e=k" and p: "p=entity_row key (snd S) e"
      by (rule state_presents_row_origin[OF present row])
    have about': "key c\<in>set (row_subjects (entity_row key (snd S) e))" using about zp p by simp
    have "c\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
      using about' by (simp only: entity_row_subject_key[OF present bound member])
    then have e: "e\<in>set (development_constant_scope (snd S) c)"
      using member by (simp add: development_constant_scope_member)
    have "(a,entity_row key (snd S) e)\<in>presented_rows R" using presented_rows_member[OF row] p by simp
    then show "Q z" using scope e zp p by blast
  qed
qed

subsection \<open>The field \<open>support complete\<close> is \<open>excess\<close> at every family\<close>

text \<open>
  The field's row reading is the mentions reading of \<open>excess\<close> (@{locale row_mentions_program}) at the store
  of the support family; the field is the index's selection reading at it. The locale names the sites of
  \<open>excess\<close>'s program shape, so a program that holds it at its sites inherits \<open>exact\<close> and the contract;
  \<open>excess\<close>'s own program holds it at its sites (@{text support_complete_excess}).
\<close>

locale support_complete_program = mentions: row_mentions_program P r e m kf ch +
    search: native_store_search_program P k v + family: native_every_program P v r +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r e m kf ch :: "'u definition_site" +
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma row_exact:
  "(r,Pair_Term (support_term ks) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    set (row_mentions (snd z))\<subseteq>set ks"
  unfolding support_term_def
  by (subst mentions.exact[OF identity]) (auto simp: support_store_lookup support_store_found)

sublocale selection: subject_selection_program P s g k v r support_term ident
    "\<lambda>ks z. set (row_mentions (snd z))\<subseteq>set ks"
  by unfold_locales (simp_all add: identity row_exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (support_term ks)) (subject_indexes_term ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set ks)"
  by (simp add: selection.exact[OF atom])

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    key ` fset (development_request_support (snd S) c)\<subseteq>set ks"
proof -
  let ?scope="set (development_constant_scope (snd S) c)"
  let ?X="development_request_support (snd S) c"
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have rows: "\<exists>a. (a,entity_row key (snd S) e)\<in>presented_rows R" if "e\<in>?scope" for e
  proof -
    have "e\<in>set (snd (snd S))" using that by (simp add: development_constant_scope_member)
    then obtain a where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
      by (rule state_presents_row[OF present])
    then show ?thesis by (blast intro: presented_rows_member)
  qed
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set ks)"
    by (rule exact[OF atom])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow>
      set (row_mentions (entity_row key (snd S) e))\<subseteq>set ks)"
    using request_rows_about[OF present bound selection, where Q="\<lambda>z. set (row_mentions (snd z))\<subseteq>set ks"]
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. key ` set (entity_mentions e)\<subseteq>set ks)"
    using rows unfolding entity_row_fields set_map by blast
  also have "\<dots> \<longleftrightarrow> key ` fset ?X\<subseteq>set ks"
  proof
    assume each: "\<forall>e\<in>?scope. key ` set (entity_mentions e)\<subseteq>set ks"
    show "key ` fset ?X\<subseteq>set ks"
    proof
      fix y assume "y\<in>key ` fset ?X"
      then obtain d where d: "d |\<in>| ?X" "y=key d" by blast
      then obtain e p where e: "e\<in>?scope" "isabelle_specified_proposition e=Some p" "d\<in>set (isabelle_term_constants p)"
        by (auto simp: development_request_support_member)
      then have "d\<in>set (entity_mentions e)" by (simp add: entity_mentions_def)
      then show "y\<in>set ks" using each e(1) d(2) by blast
    qed
  next
    assume support: "key ` fset ?X\<subseteq>set ks"
    show "\<forall>e\<in>?scope. key ` set (entity_mentions e)\<subseteq>set ks"
    proof (intro ballI subsetI)
      fix e y assume e: "e\<in>?scope" and "y\<in>key ` set (entity_mentions e)"
      then obtain d where d: "d\<in>set (entity_mentions e)" "y=key d" by blast
      obtain p where "isabelle_specified_proposition e=Some p" "d\<in>set (isabelle_term_constants p)"
        using d(1) by (cases "isabelle_specified_proposition e") (simp_all add: entity_mentions_def)
      then have "d |\<in>| ?X" using e by (auto simp: development_request_support_member)
      then show "y\<in>set ks" using support d(2) by blast
    qed
  qed
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
  unfolding support_complete_program_def support_complete_program_axioms_def row_mentions_program_def
    store_found_program_def native_store_search_program_def native_every_program_def
  by (intro conjI allI; (rule verdict_mentions_family | rule identity)) (simp_all add: verdict_mentions_rule_defs)

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
    and keyed: "\<forall>e\<in>set (snd (snd S)). (ekey e,entity_row key (snd S) e)\<in>presented_rows R"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term es))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    ekey ` set (development_constant_scope (snd S) c)\<subseteq>set es"
proof -
  let ?scope="set (development_constant_scope (snd S) c)"
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have own: "(ekey e,entity_row key (snd S) e)\<in>presented_rows R" if "e\<in>?scope" for e
    using keyed that by (simp add: development_constant_scope_member)
  have same: "a=ekey e" if "e\<in>?scope" "(a,entity_row key (snd S) e)\<in>presented_rows R" for e a
    using keyed_agreeD[OF state_presents_row_keys[OF present] that(2) own[OF that(1)]] by simp
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (support_term es))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. key c\<in>set (row_subjects (snd z)) \<longrightarrow> fst z\<in>set es)"
    by (rule exact[OF atom])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. \<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow> a\<in>set es)"
    using request_rows_about[OF present bound selection, where Q="\<lambda>z. fst z\<in>set es"] by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. ekey e\<in>set es)"
    using own same by blast
  also have "\<dots> \<longleftrightarrow> ekey ` ?scope\<subseteq>set es" by blast
  finally show ?thesis .
qed

end

end
