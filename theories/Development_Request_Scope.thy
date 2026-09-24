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
  families as value. The family is read as the list the body holds (@{const keys_term}), a key being cited
  when it is a member of that list (\<open>list_cited_program\<close> below): no store is built from the list.

  \<open>support complete\<close> is the verdict's \<open>excess\<close> (@{locale excess_program}) at the same reading: the selection
  of every family with the row rule @{const row_mentions_rule}, each mention found in the list \<open>ks\<close> by
  membership (@{locale mentions_cited_program}), one program at one reading. The one new rule here is the
  row predicate "its key is cited": the row's key is a member of the list given as the context. No field
  reads a kind, a row's identity or a store's absence.
\<close>

subsection \<open>A key is cited in a list\<close>

text \<open>
  A key is cited in a family of keys when it is a member of the list the family is: the collection notion
  @{locale list_cited_program} (theory \<open>Native_Collection_Programs\<close>), membership's program behind the swap
  that puts the list, which is the context of every call below, first. Its reading at a family of keys,
  @{text list_cited_program.exact}, is stated once, in theory \<open>Development_Verdict_Mentions\<close> where the
  verdict's \<open>excess\<close> reads it, and every field of request construction that asks whether a key is cited in
  a body family reads it.
\<close>

subsection \<open>The rows about the subject, over every family, are the rows of its scope\<close>

text \<open>
  Over the selection of every family of a presented state, the rows having the subject's key among their
  subjects are exactly the rows of the entities of the subject's scope: @{thm [source] selection_rows_about}
  at the selection of every kind. This is what both fields' contracts consume.
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

subsection \<open>The field \<open>support complete\<close>\<close>

text \<open>
  A row's mentions are cited in the list given as the context when each of them is a member of it:
  @{locale mentions_cited_program}, the row reading the verdict's \<open>excess\<close> reads. The field is
  @{locale excess_program} at that reading, the list the body holds as its support, over the selection of
  every family: the verdict's field and this one are one program. Its contract is
  @{thm [source] excess_program_contract} at every kind, the support read through the positions its keys
  key, and @{thm [source] request_support_mentions}.
\<close>

locale support_complete_program = mentions: mentions_cited_program P r e w m +
    search: native_store_search_program P k v + family: native_every_program P v r +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r e w m :: "'u definition_site" +
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma excess_instance: "excess_program P s g k v r ident keys_term"
  by unfold_locales (simp_all add: identity mentions.exact[OF identity])

sublocale excess: excess_program P s g k v r ident keys_term
  by (rule excess_instance)

lemmas exact = excess.exact

theorem contract:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (keys_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    key ` fset (development_request_support (snd S) c)\<subseteq>set ks"
proof -
  let ?scope="set (development_constant_scope (snd S) c)" and ?n="length (fst (snd S))"
  let ?X="fset_of_list (filter (\<lambda>d. key d\<in>set ks) [0..<?n])"
  have kinds: "kinds_present (\<lambda>_. True) UNIV" by (simp add: kinds_present_def)
  have support: "key d\<in>set ks \<longleftrightarrow> d |\<in>| ?X" if "d<?n" for d using that by (simp add: fset_of_list_elem)
  have inside: "\<And>e d. e\<in>?scope \<Longrightarrow> d\<in>set (entity_mentions e) \<Longrightarrow> d<?n"
    using state_presents_mentions_inside[OF present] by (auto simp: development_constant_scope_member)
  have statements: "set (development_answer_statements (\<lambda>_. True) (snd S) {|c|})=?scope"
    by (auto simp: development_answer_statements_def development_answer_statement_def list_ex_iff
      development_constant_scope_member)
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (keys_term ks))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    development_answer_statements_excess (\<lambda>_. True) (snd S) {|c|} ?X=[]"
    by (rule excess_program_contract[OF excess_instance present kinds selection bound support])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>?scope. \<forall>d\<in>set (entity_mentions e). d |\<in>| ?X)"
    by (simp only: answer_statements_excess_empty statements)
  also have "\<dots> \<longleftrightarrow> (\<forall>d. (\<exists>e\<in>?scope. d\<in>set (entity_mentions e)) \<longrightarrow> key d\<in>set ks)"
    using inside by (auto simp: fset_of_list_elem)
  also have "\<dots> \<longleftrightarrow> key ` fset (development_request_support (snd S) c)\<subseteq>set ks"
    unfolding image_subset_iff Ball_def request_support_mentions by blast
  finally show ?thesis .
qed

text \<open>At the support's own keys the field holds: the request state stays within its own support.\<close>

corollary contract_own:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and selection: "set Fs=range (state_entities R)"
  shows "(s,Pair_Term (Pair_Term (path_term (key c))
      (keys_term (map key (sorted_list_of_fset (development_request_support (snd S) c)))))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P"
  by (simp add: contract[OF present bound selection])

end

text \<open>
  The field's HOL counterpart is \<open>excess\<close> at the request's own support, and it holds of every state, by the
  member equation of the support.
\<close>

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

subsection \<open>The row predicate "its key is cited"\<close>

text \<open>
  A row's key is cited when it is a member of the list given as the context (@{locale list_cited_program}).
\<close>

definition key_cited_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "key_cited_rule m=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"

locale key_cited_program = native_rule_family P r "[([0],key_cited_rule w)]" + cited: list_cited_program P w m
  for P :: "'u native_system" and r w m :: "'u definition_site"
begin

sublocale rearranged: native_rearranging_program P r
    "row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)" w
    "Finite_Pattern_Pair (native_var 0) (native_var 1)"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def row_pattern_variables
  using native_rule_family_axioms[unfolded key_cited_rule_def] by simp

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (keys_term es) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> fst z\<in>set es"
  by (simp add: rearranged.row_at[OF refl _ identity] row_valuation_def cited.exact)

end

subsection \<open>The field \<open>scope cited\<close> is the selection reading at "its key is cited"\<close>

locale scope_cited_program = cited: key_cited_program P r w m +
    search: native_store_search_program P k v + family: native_every_program P v r +
    call: native_rule_family P g "[([0],subject_call_rule k)]" + every: native_every_program P s g
  for P :: "'u native_system" and s g k v r w m :: "'u definition_site" +
  fixes ident :: "isabelle_context \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma row_exact:
  "(r,Pair_Term (keys_term es) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> fst z\<in>set es"
  by (rule cited.exact[OF identity])

sublocale selection: subject_selection_program P s g k v r keys_term ident "\<lambda>es z. fst z\<in>set es"
  by unfold_locales (simp_all add: identity row_exact)

theorem exact:
  assumes atom: "a\<in>set A"
  shows "(s,Pair_Term (Pair_Term (path_term a) (keys_term es)) (subject_indexes_term ident A Fs))\<in>positive_meaning P \<longleftrightarrow>
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
  shows "(s,Pair_Term (Pair_Term (path_term (key c)) (keys_term es))
      (subject_indexes_term ident (map fst (state_atoms R)) Fs))\<in>positive_meaning P \<longleftrightarrow>
    ekey ` set (development_constant_scope (snd S) c)\<subseteq>set es"
proof -
  let ?scope="set (development_constant_scope (snd S) c)"
  have atom: "key c\<in>set (map fst (state_atoms R))"
    using atoms_present_atom[OF state_presents_atoms[OF present] bound] by force
  have "(s,Pair_Term (Pair_Term (path_term (key c)) (keys_term es))
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
