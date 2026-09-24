theory Development_Native_Request
imports Development_Request_Citations Development_State_Presenter Development_Request_Keys
  Factor_Finite_Payload_Literals
begin

section \<open>Request construction is one native definition over the request state's rows\<close>

text \<open>
  A request of a problem of constant \<open>c\<close> is two families of citations: the support's constant keys \<open>ks\<close> and
  the least context's row keys \<open>es\<close> (@{const development_request_body}). Its construction is the native
  admission of a proposed body against the presented request state: five fields, each built with its own
  program and contract (\<open>support complete\<close> and \<open>scope cited\<close> in \<open>Development_Request_Scope\<close>,
  \<open>declarations cited\<close>, \<open>context sound\<close> and \<open>support sound\<close> in \<open>Development_Request_Citations\<close>), held here
  at sites of one program, and one rule of its own at its entry: five premises, one per field, each passed
  only the part of the argument it reads. The construction admits; it does not produce. It reads no issue
  row, no problem row and no kind, and every premise is positive.
\<close>


subsection \<open>The argument: the subject's key, the presentations the fields read, and the body\<close>

text \<open>
  The call's context is the subject's key beside the presented request state as its fields read it: the
  subject indexes of every family (the two fields that read the rows about the subject), the declaration
  store (\<open>declarations cited\<close>), the store of the rows by row key (\<open>context sound\<close>) and the reach table
  (\<open>support sound\<close>). Every part is computed from the presented rows; nothing is supplied beside them.
\<close>

definition request_state_term :: "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> state_rows \<Rightarrow> factor_term" where
  "request_state_term ident R=Pair_Term (subject_indexes_term ident (map fst (state_atoms R)) (state_all_families R))
    (Pair_Term (declaration_term (state_all_families R)) (Pair_Term (family_row_term ident (state_all_families R))
      (reach_table_term (state_reach_table (state_atoms R) (state_roots R) (state_all_families R)))))"

subsection \<open>The sites\<close>

abbreviation request_entry :: "local_address option definition_site" where
  "request_entry \<equiv> (Some [],[0])"
abbreviation request_cited :: "local_address option definition_site" where
  "request_cited \<equiv> (Some [],[1])"
abbreviation request_member :: "local_address option definition_site" where
  "request_member \<equiv> (Some [],[2])"
abbreviation request_complete :: "local_address option definition_site" where
  "request_complete \<equiv> (Some [],[3])"
abbreviation request_complete_call :: "local_address option definition_site" where
  "request_complete_call \<equiv> (Some [],[4])"
abbreviation request_complete_search :: "local_address option definition_site" where
  "request_complete_search \<equiv> (Some [],[5])"
abbreviation request_complete_family :: "local_address option definition_site" where
  "request_complete_family \<equiv> (Some [],[6])"
abbreviation request_complete_row :: "local_address option definition_site" where
  "request_complete_row \<equiv> (Some [],[7])"
abbreviation request_complete_mentions :: "local_address option definition_site" where
  "request_complete_mentions \<equiv> (Some [],[8])"
abbreviation request_scope :: "local_address option definition_site" where
  "request_scope \<equiv> (Some [],[9])"
abbreviation request_scope_call :: "local_address option definition_site" where
  "request_scope_call \<equiv> (Some [],[10])"
abbreviation request_scope_search :: "local_address option definition_site" where
  "request_scope_search \<equiv> (Some [],[11])"
abbreviation request_scope_family :: "local_address option definition_site" where
  "request_scope_family \<equiv> (Some [],[12])"
abbreviation request_scope_row :: "local_address option definition_site" where
  "request_scope_row \<equiv> (Some [],[13])"
abbreviation request_declarations :: "local_address option definition_site" where
  "request_declarations \<equiv> (Some [],[14])"
abbreviation request_declarations_call :: "local_address option definition_site" where
  "request_declarations_call \<equiv> (Some [],[15])"
abbreviation request_declarations_search :: "local_address option definition_site" where
  "request_declarations_search \<equiv> (Some [],[16])"
abbreviation request_context :: "local_address option definition_site" where
  "request_context \<equiv> (Some [],[17])"
abbreviation request_context_call :: "local_address option definition_site" where
  "request_context_call \<equiv> (Some [],[18])"
abbreviation request_context_search :: "local_address option definition_site" where
  "request_context_search \<equiv> (Some [],[19])"
abbreviation request_context_row :: "local_address option definition_site" where
  "request_context_row \<equiv> (Some [],[20])"
abbreviation request_context_declares :: "local_address option definition_site" where
  "request_context_declares \<equiv> (Some [],[21])"
abbreviation request_sound :: "local_address option definition_site" where
  "request_sound \<equiv> (Some [],[22])"
abbreviation request_sound_call :: "local_address option definition_site" where
  "request_sound_call \<equiv> (Some [],[23])"
abbreviation request_sound_search :: "local_address option definition_site" where
  "request_sound_search \<equiv> (Some [],[24])"
abbreviation request_sound_check :: "local_address option definition_site" where
  "request_sound_check \<equiv> (Some [],[25])"
abbreviation request_admission :: "local_address option definition_site" where
  "request_admission \<equiv> (Some [],[26])"

subsection \<open>The entry rule: one rule, five premise sockets, one per field\<close>

definition request_entry_conclusion :: "local_address finite_term_pattern" where
  "request_entry_conclusion=Finite_Pattern_Pair
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
      (Finite_Pattern_Pair (native_var 2) (Finite_Pattern_Pair (native_var 3) (native_var 4)))))
    (Finite_Pattern_Pair (native_var 5) (native_var 6))"

definition request_entry_premises ::
    "(local_address\<times>(local_address option definition_site\<times>local_address finite_term_pattern)) list" where
  "request_entry_premises=[
    ([0],(request_complete,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 5)) (native_var 1))),
    ([1],(request_scope,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 6)) (native_var 1))),
    ([2],(request_declarations,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 6) (native_var 2)) (native_var 5))),
    ([3],(request_context,Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 5) (native_var 0)) (native_var 3)) (native_var 6))),
    ([4],(request_sound,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 4)) (native_var 5)))]"

definition request_entry_rule ::
    "(local_address,local_address,local_address option definition_site) finite_factor_schema" where
  "request_entry_rule=finite_native_rule request_entry_conclusion request_entry_premises"

subsection \<open>The program: every consumed rule family at a site of its own, and the entry\<close>

text \<open>
  The one list citation (membership behind the swap) is held once and read by four fields. The rest are the
  fields' own families: the subject index's selection reading of every family at two row readings, the
  declaration store's search, the search of the rows by row key and the reach table's search, each an
  \<open>every\<close> over a body family.
\<close>

definition native_request_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "native_request_definitions=[
    (request_cited,[([0],native_swap_rule request_member)]),
    (request_member,native_member_rules request_member),
    (request_complete,native_every_rules request_complete request_complete_call),
    (request_complete_call,[([0],subject_call_rule request_complete_search)]),
    (request_complete_search,native_store_search_rules request_complete_search request_complete_family),
    (request_complete_family,native_every_rules request_complete_family request_complete_row),
    (request_complete_row,[([0],row_mentions_rule request_complete_mentions)]),
    (request_complete_mentions,native_every_rules request_complete_mentions request_cited),
    (request_scope,native_every_rules request_scope request_scope_call),
    (request_scope_call,[([0],subject_call_rule request_scope_search)]),
    (request_scope_search,native_store_search_rules request_scope_search request_scope_family),
    (request_scope_family,native_every_rules request_scope_family request_scope_row),
    (request_scope_row,[([0],key_cited_rule request_cited)]),
    (request_declarations,native_every_rules request_declarations request_declarations_call),
    (request_declarations_call,[([0],keyed_search_call_rule request_declarations_search)]),
    (request_declarations_search,native_store_search_rules request_declarations_search request_cited),
    (request_context,native_every_rules request_context request_context_call),
    (request_context_call,[([0],keyed_search_call_rule request_context_search)]),
    (request_context_search,native_store_search_rules request_context_search request_context_row),
    (request_context_row,context_sound_row_rules request_member request_context_declares),
    (request_context_declares,native_some_rules request_context_declares request_cited),
    (request_sound,native_every_rules request_sound request_sound_call),
    (request_sound_call,[([0],keyed_search_call_rule request_sound_search)]),
    (request_sound_search,native_store_search_rules request_sound_search request_sound_check),
    (request_sound_check,[([0],native_member_later request_member)]),
    (request_admission,native_store_search_rules request_admission request_entry),
    (request_entry,[([0],request_entry_rule)])]"

definition finite_native_request :: "local_address option finite_native_system" where
  "finite_native_request=finite_rule_program native_request_definitions"

definition native_request_system :: "local_address option native_system" where
  "native_request_system=decode_finite_system finite_native_request"

lemma finite_native_request_formed: "finite_system_formed finite_native_request"
  by code_simp

lemma native_request_formed: "schema_system_formed native_request_system"
  using finite_native_request_formed
  by (simp only: native_request_system_def finite_system_formed_correct)

lemma native_request_distinct: "distinct (map fst native_request_definitions)"
  by code_simp

lemma native_request_plain:
  "\<forall>(d,rs)\<in>set native_request_definitions. \<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  by code_simp

lemma native_request_family:
  assumes member: "(d,rs)\<in>set native_request_definitions"
  shows "native_rule_family native_request_system d rs"
  unfolding native_request_system_def finite_native_request_def
  by (rule finite_rule_program_family[OF native_request_formed[unfolded native_request_system_def
      finite_native_request_def] native_request_distinct member]) (use native_request_plain member in blast)

subsection \<open>The consumed fields, interpreted at the program's sites\<close>

text \<open>
  Each field's locale is interpreted at its sites, so its \<open>exact\<close> and its \<open>contract\<close> are inherited. The
  three fields that read a row's identity carry the identity's formation as their locale's assumption, and are
  stated as lemmas under it.
\<close>

lemma request_complete_program:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "support_complete_program native_request_system request_complete request_complete_call
    request_complete_search request_complete_family request_complete_row request_complete_mentions
    request_cited request_member ident"
  unfolding support_complete_program_def support_complete_program_axioms_def mentions_cited_program_def
    row_mentions_program_def list_cited_program_def native_swap_program_def native_member_program_def native_store_search_program_def
    native_every_program_def
  by (intro conjI allI; (rule native_request_family | rule identity)) (simp_all add: native_request_definitions_def)

lemma request_scope_program:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "scope_cited_program native_request_system request_scope request_scope_call request_scope_search
    request_scope_family request_scope_row request_cited request_member ident"
  unfolding scope_cited_program_def scope_cited_program_axioms_def key_cited_program_def
    list_cited_program_def native_swap_program_def native_member_program_def native_store_search_program_def
    native_every_program_def
  by (intro conjI allI; (rule native_request_family | rule identity)) (simp_all add: native_request_definitions_def)

lemma request_context_program:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "context_sound_program native_request_system request_context request_context_call request_context_search
    request_context_row request_member request_context_declares request_cited ident"
  unfolding context_sound_program_def context_sound_program_axioms_def context_sound_row_program_def
    native_some_program_def list_cited_program_def native_swap_program_def native_member_program_def
    native_store_search_program_def keyed_search_call_program_def native_every_program_def
  by (intro conjI allI; (rule native_request_family | rule identity)) (simp_all add: native_request_definitions_def)

interpretation request_declared: declarations_cited_program native_request_system request_declarations
    request_declarations_call request_declarations_search request_cited request_member
  unfolding declarations_cited_program_def list_cited_program_def native_swap_program_def
    native_member_program_def native_store_search_program_def keyed_search_call_program_def
    native_every_program_def
  by (intro conjI; rule native_request_family) (simp_all add: native_request_definitions_def)

interpretation request_supported: support_sound_program native_request_system request_sound request_sound_call
    request_sound_search request_sound_check request_member
  unfolding support_sound_program_def predecessor_check_program_def native_member_program_def
    native_store_search_program_def keyed_search_call_program_def native_every_program_def
  by (intro conjI; rule native_request_family) (simp_all add: native_request_definitions_def)

subsection \<open>The entry holds exactly when its five fields do\<close>

text \<open>
  The entry's family is one rule whose premises read only variables its conclusion binds, so its meaning is
  the conjunction program's (@{locale native_conjunction_program}): the theorem below is its @{text at} at the
  conclusion's evaluation, and no argument about the rule is made here.
\<close>

interpretation request_entry_family: native_conjunction_program native_request_system request_entry
    request_entry_conclusion request_entry_premises
  unfolding native_conjunction_program_def native_conjunction_program_axioms_def
proof (intro conjI)
  show "native_rule_family native_request_system request_entry
      [([0],finite_native_rule request_entry_conclusion request_entry_premises)]"
    by (rule native_request_family) (simp add: native_request_definitions_def request_entry_rule_def)
  show "\<forall>(k,d,q)\<in>set request_entry_premises.
      pattern_variables (decode_finite_pattern q)\<subseteq>pattern_variables (decode_finite_pattern request_entry_conclusion)"
    by (simp add: request_entry_premises_def request_entry_conclusion_def)
qed

theorem native_request_entry:
  "(request_entry,Pair_Term (Pair_Term a0 (Pair_Term a1 (Pair_Term a2 (Pair_Term a3 a4)))) (Pair_Term a5 a6))
      \<in>positive_meaning native_request_system \<longleftrightarrow>
    (request_complete,Pair_Term (Pair_Term a0 a5) a1)\<in>positive_meaning native_request_system \<and>
    (request_scope,Pair_Term (Pair_Term a0 a6) a1)\<in>positive_meaning native_request_system \<and>
    (request_declarations,Pair_Term (Pair_Term a6 a2) a5)\<in>positive_meaning native_request_system \<and>
    (request_context,Pair_Term (Pair_Term (Pair_Term a5 a0) a3) a6)\<in>positive_meaning native_request_system \<and>
    (request_sound,Pair_Term (Pair_Term a0 a4) a5)\<in>positive_meaning native_request_system"
  using request_entry_family.at[of "native_values [a0,a1,a2,a3,a4,a5,a6]"]
  by (simp add: request_entry_conclusion_def request_entry_premises_def)

subsection \<open>The declarations condition\<close>

text \<open>
  The declarations condition has two owners: the declaration store is single-valued, which the exporter
  owes (@{const isabelle_declared_once}, #36's carried condition), and every support constant is declared,
  which is the request state's own \<open>undeclared\<close> field (@{thm [source] request_support_declared}). Together
  each support constant has exactly one declaring entity.
\<close>

lemma request_support_declaration:
  assumes once: "isabelle_declared_once (snd S)" and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and d: "d |\<in>| development_request_support (snd S) c"
  shows "\<exists>!e. e\<in>set (snd (snd S)) \<and> isabelle_declared_constant e=Some d"
  using request_support_declared[OF closed d] once unfolding isabelle_declared_once_def by blast

subsection \<open>The contract\<close>

text \<open>
  Under the presentation of the request state, a position \<open>c\<close> of it, the entity-key condition (the entity
  key keys every entity's row as the presentation does, @{const entity_rows_keyed}) and the declarations
  condition, the construction holds of a body exactly when its support family lists the request's support and
  its context family the request's least context, each in any order: the relation
  @{const development_requests_present} states. It is the conjunction of the five fields' contracts with
  @{thm [source] development_request_context_exact}.
\<close>

theorem native_request_exact:
  assumes present: "state_presents key S R" and bound: "c<length (fst (snd S))"
    and keyed: "entity_rows_keyed key ekey S R"
    and once: "isabelle_declared_once (snd S)" and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(request_entry,Pair_Term (Pair_Term (path_term (key c)) (request_state_term ident R))
      (development_request_body ks es))\<in>positive_meaning native_request_system \<longleftrightarrow>
    set ks=key ` fset (development_request_support (snd S) c) \<and>
    set es=ekey ` fset (development_request_context (snd S) c)"
proof -
  let ?sup="fset (development_request_support (snd S) c)"
  let ?scope="set (development_constant_scope (snd S) c)"
  let ?ctx="fset (development_request_context (snd S) c)"
  let ?E="set (snd (snd S))"
  have fam: "set (state_all_families R)=range (state_entities R)" by (rule state_all_families_range)
  have inj: "inj_on key {..<length (fst (snd S))}"
    by (rule atoms_present_key_injective[OF state_presents_atoms[OF present]])
  have ctx: "e\<in>?ctx \<longleftrightarrow> e\<in>?E \<and> (e\<in>?scope \<or> (\<exists>d. isabelle_declared_constant e=Some d \<and> d\<in>?sup))" for e
    using development_request_context_exact[of e "snd S" c] by simp
  have scope_ctx: "?scope\<subseteq>?ctx"
  proof
    fix e
    assume e: "e\<in>?scope"
    have eE: "e\<in>?E" using e unfolding development_constant_scope_member by (rule conjunct1)
    show "e\<in>?ctx" unfolding ctx using eE e by (rule conjI[OF _ disjI1])
  qed
  have entry: "(request_entry,Pair_Term (Pair_Term (path_term (key c)) (request_state_term ident R))
      (development_request_body ks es))\<in>positive_meaning native_request_system \<longleftrightarrow>
    key ` ?sup\<subseteq>set ks \<and> ekey ` ?scope\<subseteq>set es \<and>
    (\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es) \<and>
    set es\<subseteq>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}) \<and>
    set ks\<subseteq>key ` ?sup"
    unfolding request_state_term_def development_request_body_def native_request_entry
      support_complete_program.contract[OF request_complete_program[OF identity] present bound fam]
      scope_cited_program.contract[OF request_scope_program[OF identity] present bound fam keyed]
      request_declared.contract[OF present once fam keyed]
      context_sound_program.contract[OF request_context_program[OF identity] present bound fam keyed]
      request_supported.contract[OF present bound fam]
    by (rule refl)
  show ?thesis unfolding entry
  proof
    assume "key ` ?sup\<subseteq>set ks \<and> ekey ` ?scope\<subseteq>set es \<and>
      (\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es) \<and>
      set es\<subseteq>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}) \<and>
      set ks\<subseteq>key ` ?sup"
    then show "set ks=key ` ?sup \<and> set es=ekey ` ?ctx"
    proof (elim conjE)
      assume c1: "key ` ?sup\<subseteq>set ks" and c2: "ekey ` ?scope\<subseteq>set es"
        and c3: "\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
        and c4: "set es\<subseteq>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks})"
        and c5: "set ks\<subseteq>key ` ?sup"
      have ks: "set ks=key ` ?sup" by (rule subset_antisym[OF c5 c1])
      have cited: "\<forall>d. d |\<in>| development_request_support (snd S) c \<longrightarrow> key d\<in>set ks \<longrightarrow>
          (\<exists>e\<in>?E. isabelle_declared_constant e=Some d \<and> ekey e\<in>set es)"
        by (rule iffD1[OF request_declared.contract_support[OF present once fam keyed c5]
          iffD2[OF request_declared.contract[OF present once fam keyed] c3]])
      have es_sub: "set es\<subseteq>ekey ` ?ctx"
      proof
        fix a
        assume "a\<in>set es"
        then have "a\<in>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks})"
          by (rule subsetD[OF c4])
        then obtain e where e: "e\<in>?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}"
          and a: "a=ekey e"
          by blast
        show "a\<in>ekey ` ?ctx"
        proof (cases "e\<in>?scope")
          case True
          then have "e\<in>?ctx" using scope_ctx by blast
          then show ?thesis unfolding a by (rule imageI)
        next
          case False
          then have eE: "e\<in>?E" and "\<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks" using e by blast+
          then obtain d where de: "isabelle_declared_constant e=Some d" and kd: "key d\<in>set ks" by blast
          obtain d' where d': "d'\<in>?sup" "key d=key d'" using kd ks by blast
          have dn: "d\<in>{..<length (fst (snd S))}" using declared_inside[OF present eE de] by simp
          have dn': "d'\<in>{..<length (fst (snd S))}" using request_support_inside[OF present d'(1)] by simp
          have "d=d'" by (rule inj_onD[OF inj d'(2) dn dn'])
          then have "e\<in>?ctx" using ctx eE de d'(1) by blast
          then show ?thesis unfolding a by (rule imageI)
        qed
      qed
      have ctx_sub: "ekey ` ?ctx\<subseteq>set es"
      proof
        fix a
        assume "a\<in>ekey ` ?ctx"
        then obtain e where eC: "e\<in>?ctx" and a: "a=ekey e" by blast
        have eE: "e\<in>?E" and either: "e\<in>?scope \<or> (\<exists>d. isabelle_declared_constant e=Some d \<and> d\<in>?sup)"
          using ctx eC by blast+
        show "a\<in>set es"
        proof (cases "e\<in>?scope")
          case True
          then have "ekey e\<in>ekey ` ?scope" by (rule imageI)
          then show ?thesis unfolding a by (rule subsetD[OF c2])
        next
          case False
          then obtain d where de: "isabelle_declared_constant e=Some d" and ds: "d\<in>?sup" using either by blast
          have kd: "key d\<in>set ks" using ds unfolding ks by (rule imageI)
          obtain e' where e': "e'\<in>?E" "isabelle_declared_constant e'=Some d" "ekey e'\<in>set es"
            using cited ds kd by blast
          have "\<exists>!e. e\<in>?E \<and> isabelle_declared_constant e=Some d"
            by (rule request_support_declaration[OF once closed ds])
          then have "e=e'" using eE de e'(1,2) by blast
          then show ?thesis unfolding a using e'(3) by simp
        qed
      qed
      show "set ks=key ` ?sup \<and> set es=ekey ` ?ctx" using ks subset_antisym[OF es_sub ctx_sub] by (rule conjI)
    qed
  next
    assume both: "set ks=key ` ?sup \<and> set es=ekey ` ?ctx"
    then have ks: "set ks=key ` ?sup" and es: "set es=ekey ` ?ctx" by blast+
    have declarations: "\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
    proof
      fix q
      assume "q\<in>set ks"
      then obtain d where d: "d\<in>?sup" "q=key d" using ks by blast
      have "\<exists>!e. e\<in>?E \<and> isabelle_declared_constant e=Some d"
        by (rule request_support_declaration[OF once closed d(1)])
      then obtain e where e: "e\<in>?E" "isabelle_declared_constant e=Some d" by blast
      then have "e\<in>?ctx" using ctx d(1) by blast
      then have "ekey e\<in>set es" unfolding es by (rule imageI)
      then show "\<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es"
        using d(2) e by blast
    qed
    have in_context: "set es\<subseteq>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks})"
    proof
      fix a
      assume "a\<in>set es"
      then have "a\<in>ekey ` ?ctx" unfolding es .
      then obtain e where eC: "e\<in>?ctx" and a: "a=ekey e" by blast
      have eE: "e\<in>?E" and either: "e\<in>?scope \<or> (\<exists>d. isabelle_declared_constant e=Some d \<and> d\<in>?sup)"
        using ctx eC by blast+
      have "e\<in>?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}"
      proof (cases "e\<in>?scope")
        case True
        then show ?thesis by (rule UnI1)
      next
        case False
        then obtain d where de: "isabelle_declared_constant e=Some d" and ds: "d\<in>?sup" using either by blast
        have "key d\<in>set ks" using ds unfolding ks by (rule imageI)
        then show ?thesis using eE de by blast
      qed
      then show "a\<in>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks})"
        unfolding a by (rule imageI)
    qed
    have sup_ks: "key ` ?sup\<subseteq>set ks" by (simp add: ks)
    have scope_es: "ekey ` ?scope\<subseteq>set es" unfolding es by (rule image_mono[OF scope_ctx])
    have ks_sup: "set ks\<subseteq>key ` ?sup" by (simp add: ks)
    show "key ` ?sup\<subseteq>set ks \<and> ekey ` ?scope\<subseteq>set es \<and>
      (\<forall>q\<in>set ks. \<exists>d e. q=key d \<and> e\<in>?E \<and> isabelle_declared_constant e=Some d \<and> ekey e\<in>set es) \<and>
      set es\<subseteq>ekey ` (?scope\<union>{e\<in>?E. \<exists>d. isabelle_declared_constant e=Some d \<and> key d\<in>set ks}) \<and>
      set ks\<subseteq>key ` ?sup"
      by (intro conjI sup_ks scope_es declarations in_context ks_sup)
  qed
qed

subsection \<open>The entity-key condition, discharged at the presenter's rows\<close>

text \<open>
  The presenter of a state's rows keys every entity row by @{const development_entity_key}
  (@{thm [source] state_presenter_entity_rows_keyed}, the condition's owner), so at its rows the contract holds
  with the entity key the development rows fix.
\<close>

corollary native_request_presented:
  assumes presented: "state_presenter S=Some R" and bound: "c<length (fst (snd S))"
    and once: "isabelle_declared_once (snd S)" and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(request_entry,Pair_Term (Pair_Term (path_term (state_constant_key c)) (request_state_term ident R))
      (development_request_body ks es))\<in>positive_meaning native_request_system \<longleftrightarrow>
    set ks=state_constant_key ` fset (development_request_support (snd S) c) \<and>
    set es=development_entity_key (snd S) ` fset (development_request_context (snd S) c)"
  by (rule native_request_exact[OF state_presenter_presents[OF presented] bound
    state_presenter_entity_rows_keyed[OF presented] once closed identity])

subsection \<open>The payload audit\<close>

text \<open>
  The payloads a program states literally are the octets it reads as structure
  (@{thm [source] finite_system_payloads_exact}). The composed program — the entry, every consumed field's
  families and the admission search — states none but the empty payload, the leaf the collection notions and
  the path store read, so every octet of a row the construction reads is inert to it. It is proved once, over
  the program.
\<close>

theorem finite_native_request_payloads: "finite_system_payloads finite_native_request |\<subseteq>| {|[]|}"
  by code_simp

corollary native_request_payloads: "system_payloads native_request_system\<subseteq>{[]}"
  using finite_native_request_payloads
  by (simp add: native_request_system_def finite_system_payloads_exact[symmetric] less_eq_fset.rep_eq)

subsection \<open>Admission at a locus\<close>

text \<open>
  The request row the loop records is admitted where it stands: the development store's search
  (@{locale native_store_search_program}) at a site of the program's own, whose check is the construction. It
  is the search @{thm [source] development_request_at} makes with the value rule as its check, the construction
  in the check's place; the search's contract for values held formed where the store holds them
  at a key where the store holds a value (@{thm [source] native_store_search_program.held_at}) and the construction's
  (@{thm [source] native_request_exact}) compose, neither restated.
\<close>

interpretation request_admitted: native_store_search_program native_request_system request_admission request_entry
  unfolding native_store_search_program_def
  by (rule native_request_family) (simp add: native_request_definitions_def)

theorem native_request_admitted:
  assumes presents: "request_presents key S R rows r k ks"
    and keyed: "entity_rows_keyed key (development_entity_key (snd S)) S R"
    and once: "isabelle_declared_once (snd S)" and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and identity: "\<And>y. term_formed (ident y)"
    and subject: "problem_subject (fst r)={|c|}"
  shows "(request_admission,Pair_Term (Pair_Term (path_term k) (request_state_term ident R))
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r))) (development_rows_term rows)))
      \<in>positive_meaning native_request_system \<longleftrightarrow>
    fst (snd (snd r))=development_request_support (snd S) c \<and> snd (snd (snd r))=development_request_context (snd S) c"
proof -
  let ?x="Pair_Term (path_term k) (request_state_term ident R)"
  let ?l="development_located_at key Development_Request_Role (fst r)"
  let ?ekey="development_entity_key (snd S)"
  obtain inert origin grant supported scope decs ps rs iss where
      present: "development_rows_present key ?ekey inert origin grant supported scope decs ps rs iss rows"
      and r: "r\<in>set rs"
    using presents unfolding request_presents_def by blast
  have state: "state_presents key S R"
    and inside: "fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}"
    using presents unfolding request_presents_def by blast+
  obtain c' where c': "problem_subject (fst r)={|c'|}" "k=key c'" "c'<length (fst (snd S))"
      "(k,fst (snd S)!c')\<in>set (state_atoms R)" "set ks=key ` fset (fst (snd (snd r)))"
      "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
    by (rule request_presents_recovery[OF presents])
  have cc: "c'=c" using c'(1) subject by simp
  have kc: "k=key c" and bound: "c<length (fst (snd S))" using c'(2,3) cc by simp_all
  have formed_rows: "\<forall>(l,w)\<in>set rows. term_formed w" by (rule development_rows_formed[OF present])
  let ?body="development_request_body (supported r) (scope r)"
  have stored: "store_lookup (path_store rows) ?l=Some ?body"
    using development_row_lookup_at[OF formed_rows, where v="?body" and l="?l"]
      development_request_at[OF present r, of ?body] by simp
  have held: "term_formed (id y)" if "store_lookup (path_store rows) bs=Some y" for bs y
    using path_store_found[OF that] formed_rows by (simp only: id_apply) blast
  have "(request_admission,Pair_Term ?x (Pair_Term (path_term ?l) (development_rows_term rows)))
      \<in>positive_meaning native_request_system \<longleftrightarrow>
    (request_entry,Pair_Term ?x ?body)\<in>positive_meaning native_request_system"
    unfolding development_rows_term_def using request_admitted.held_at[OF held stored] by (simp only: id_apply)
  also have "\<dots> \<longleftrightarrow> set (supported r)=key ` fset (development_request_support (snd S) c) \<and>
      set (scope r)=?ekey ` fset (development_request_context (snd S) c)"
    by (simp only: kc native_request_exact[OF state bound keyed once closed identity])
  also have "\<dots> \<longleftrightarrow> fst (snd (snd r))=development_request_support (snd S) c \<and>
      snd (snd (snd r))=development_request_context (snd S) c"
  proof -
    have requested: "development_requests_present key ?ekey supported scope ps rs rows"
      using present unfolding development_rows_present_def by blast
    have rows_sup: "set (supported r)=key ` fset (fst (snd (snd r)))"
      and rows_scope: "set (scope r)=?ekey ` fset (snd (snd (snd r)))"
      using requested r unfolding development_requests_present_def by blast+
    have inj: "inj_on key {..<length (fst (snd S))}"
      by (rule atoms_present_key_injective[OF state_presents_atoms[OF state]])
    have sup_in: "fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}" using inside by blast
    have req_in: "fset (development_request_support (snd S) c)\<subseteq>{..<length (fst (snd S))}"
    proof
      fix d assume d: "d\<in>fset (development_request_support (snd S) c)"
      show "d\<in>{..<length (fst (snd S))}" using request_support_inside[OF state d] by simp
    qed
    have sup_eq: "key ` fset (fst (snd (snd r)))=key ` fset (development_request_support (snd S) c) \<longleftrightarrow>
        fst (snd (snd r))=development_request_support (snd S) c"
      using inj_on_image_eq_iff[OF inj sup_in req_in] by (simp add: fset_inject)
    have ctx_in: "fset (development_request_context (snd S) c)\<subseteq>set (snd (snd S))"
      by (auto simp: development_request_context_exact)
    have ent_eq: "?ekey ` fset (snd (snd (snd r)))=?ekey ` fset (development_request_context (snd S) c) \<longleftrightarrow>
        snd (snd (snd r))=development_request_context (snd S) c"
    proof
      assume same: "?ekey ` fset (snd (snd (snd r)))=?ekey ` fset (development_request_context (snd S) c)"
      have E_in: "fset (snd (snd (snd r)))\<subseteq>set (snd (snd S))"
      proof
        fix e assume "e\<in>fset (snd (snd (snd r)))"
        then have "?ekey e\<in>?ekey ` fset (development_request_context (snd S) c)" using same by blast
        then obtain e' where e': "e'\<in>fset (development_request_context (snd S) c)" "?ekey e=?ekey e'" by blast
        show "e\<in>set (snd (snd S))"
          by (rule first_occurrence_key_member[where xs="snd (snd S)" and x=e and y=e'])
            (use e' ctx_in in \<open>auto simp: development_entity_key_def\<close>)
      qed
      show "snd (snd (snd r))=development_request_context (snd S) c"
        using inj_on_image_eq_iff[OF development_entity_key_injective E_in ctx_in] same by (simp add: fset_inject)
    next
      assume "snd (snd (snd r))=development_request_context (snd S) c"
      then show "?ekey ` fset (snd (snd (snd r)))=?ekey ` fset (development_request_context (snd S) c)" by simp
    qed
    show ?thesis by (simp only: rows_sup rows_scope sup_eq ent_eq)
  qed
  finally show ?thesis .
qed

subsection \<open>The two kinds are one construction\<close>

text \<open>
  For every reading and every kind, a request the HOL constructor builds from the state and a rows presentation
  holds is admitted at its locus: the construction holds of the body the store holds there. The refinement
  request (@{const development_refinement_request}) and the definition request
  (@{text development_definition_request}) are this corollary at their readings; neither is a lemma of its
  own, since no field reads the reading or the kind. The introduction of @{const request_presents}
  (@{thm [source] request_presents_intro}) and the admission contract compose.
\<close>

corollary native_request_kinds:
  assumes state: "state_presents key S R" and keyed: "entity_rows_keyed key (development_entity_key (snd S)) S R"
    and once: "isabelle_declared_once (snd S)" and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and identity: "\<And>y. term_formed (ident y)"
    and present: "development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows"
    and r: "r\<in>set rs"
    and built: "development_constant_request reading kind (snd S) ra a c=Some r"
  shows "(request_admission,Pair_Term (Pair_Term (path_term (key c)) (request_state_term ident R))
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r))) (development_rows_term rows)))
      \<in>positive_meaning native_request_system"
proof -
  obtain p s Sup E where shape: "r=(p,s,Sup,E)" by (cases r)
  have fields: "problem_subject p={|c|}" "Sup=development_request_support (snd S) c"
      "E=development_request_context (snd S) c"
    using development_constant_request_fields[OF built[unfolded shape]] by blast+
  have subject: "problem_subject (fst r)={|c|}" using fields shape by simp
  have presents: "request_presents key S R rows r (key c) (supported r)"
    by (rule request_presents_intro[OF state present r built])
  show ?thesis
    by (rule iffD2[OF native_request_admitted[OF presents keyed once closed identity subject]])
      (simp add: shape fields)
qed

end
