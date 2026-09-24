theory Development_Request_Keys
imports Development_Located_Rows Development_State_Rows Development_Requests
begin

section \<open>A request's subject and support as keys of a presented state\<close>

text \<open>
  The verdict of a kind reads a request for two things: the key of its subject, which the fields
  \<open>statements\<close> and the permitted rows compare with the subjects of the state's rows, and the keys of
  its support, which \<open>excess\<close> searches the mentions of the replaceable rows in. Both are read here once,
  as keys over the presented state, so no field reaches into a request for itself.

  One constant-key assignment serves both presentations: the state's rows (@{const state_presents}) and
  the development's rows (@{const development_rows_present}) take the same \<open>key\<close>, so they cannot key a
  constant differently. The development rows' entity key is the state's own first-occurrence key
  (@{const development_entity_key}). The request is not looked up by a name or a list position: the
  subject's key is what follows the role and the kind in the request's locus, and the support is the
  family the development store's one search finds at that locus. The subject and the support are
  constants of the state, so their keys are keys of its atoms.

  The support is presented as the family the request's row carries, not as a store: the search that
  \<open>excess\<close> makes of it is a store built from this family, and that construction is the field's.
\<close>

definition request_presents ::
    "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_rooted_context \<Rightarrow> state_rows \<Rightarrow> development_store_rows \<Rightarrow>
      development_request \<Rightarrow> state_key \<Rightarrow> state_key list \<Rightarrow> bool" where
  "request_presents key S R rows r k ks \<longleftrightarrow>
    state_presents key S R \<and>
    (\<exists>inert origin grant supported scope decs ps rs iss.
      development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows \<and>
      r\<in>set rs) \<and>
    fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))} \<and>
    k=drop 6 (development_located_at key Development_Request_Role (fst r)) \<and>
    (\<exists>es. (development_row_search,Pair_Term (development_request_body ks es)
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program)"

text \<open>
  The rows' entity key is injective on every family of the state's entities, by the injectivity of the
  first-occurrence key (@{thm development_entity_key_injective}); a presentation whose request contexts
  hold the state's entities discharges that premise of @{const development_rows_present} with it.
\<close>

lemma request_entity_key_injective:
  assumes "development_row_entities rs\<subseteq>set (snd C)"
  shows "inj_on (development_entity_key C) (development_row_entities rs)"
  by (rule inj_on_subset[OF development_entity_key_injective assms])

section \<open>The subject and the support are recovered from the relation\<close>

theorem request_presents_recovery:
  assumes presents: "request_presents key S R rows r k ks"
  obtains c where "problem_subject (fst r)={|c|}" "k=key c" "c<length (fst (snd S))"
    "(k,fst (snd S)!c)\<in>set (state_atoms R)"
    "set ks=key ` fset (fst (snd (snd r)))"
    "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
proof -
  obtain inert origin grant supported scope decs ps rs iss where
      present: "development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows"
      and r: "r\<in>set rs"
    using presents unfolding request_presents_def by blast
  have state: "state_presents key S R"
    and inside: "fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}"
    and k: "k=drop 6 (development_located_at key Development_Request_Role (fst r))"
    using presents unfolding request_presents_def by blast+
  obtain es where found: "(development_row_search,Pair_Term (development_request_body ks es)
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program"
    using presents unfolding request_presents_def by blast
  have "development_request_body ks es=development_request_body (supported r) (scope r)"
    using development_request_at[OF present r, of "development_request_body ks es"] found by blast
  then have ks: "ks=supported r" by (simp only: development_request_body_injective)
  obtain c where c: "problem_subject (fst r)={|c|}"
    by (rule development_rows_problem[OF present development_rows_request(1)[OF present r]])
  have kc: "k=key c"
    using k by (simp only: development_located_at_subject[OF c] development_locus_parts(3))
  have atoms: "atoms_present key (fst (snd S)) R" by (rule state_presents_atoms[OF state])
  have cb: "c<length (fst (snd S))" using inside c by auto
  show thesis
  proof (rule that[OF c kc cb])
    show "(k,fst (snd S)!c)\<in>set (state_atoms R)" using kc atoms_present_atom[OF atoms cb] by simp
    show "set ks=key ` fset (fst (snd (snd r)))" using ks development_rows_request(3)[OF present r] by simp
    show "\<forall>d\<in>fset (fst (snd (snd r))). (key d,fst (snd S)!d)\<in>set (state_atoms R)"
      using inside atoms_present_atom[OF atoms] by auto
  qed
qed

text \<open>
  The keys are determined by the request and the store: the store holds one value at the request's
  locus, so two presentations of one request find the same support family.
\<close>

theorem request_presents_unique:
  assumes first: "request_presents key S R rows r k ks" and second: "request_presents key S R' rows r k' ks'"
  shows "k=k' \<and> ks=ks'"
proof -
  obtain inert origin grant supported scope decs ps rs iss where
      present: "development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows"
      and r: "r\<in>set rs"
    using first unfolding request_presents_def by blast
  obtain es where found: "(development_row_search,Pair_Term (development_request_body ks es)
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program"
    using first unfolding request_presents_def by blast
  obtain es' where found': "(development_row_search,Pair_Term (development_request_body ks' es')
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program"
    using second unfolding request_presents_def by blast
  have "development_request_body ks es=development_request_body ks' es'"
    using development_request_at[OF present r, of "development_request_body ks es"]
      development_request_at[OF present r, of "development_request_body ks' es'"] found found' by simp
  then have "ks=ks'" by (simp only: development_request_body_injective)
  moreover have "k=k'" using first second unfolding request_presents_def by simp
  ultimately show ?thesis by simp
qed

text \<open>
  The subject's key is also the tail of the problem's locus: a problem and its request stand at one locus
  under two role prefixes (@{thm development_request_problem_locus}).
\<close>

lemma request_presents_problem_locus:
  assumes presents: "request_presents key S R rows r k ks"
  shows "k=drop 6 (development_located_at key Development_Problem_Role (fst r))"
proof -
  obtain inert origin grant supported scope decs ps rs iss where
      present: "development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows"
      and r: "r\<in>set rs"
    using presents unfolding request_presents_def by blast
  have k: "k=drop 6 (development_located_at key Development_Request_Role (fst r))"
    using presents unfolding request_presents_def by blast
  show ?thesis
    using k development_request_problem_locus[OF present development_rows_request(1)[OF present r]] by simp
qed

text \<open>
  For a request constructed from the state, the recovered keys are the keys of the constant it is about
  and of the support construction reads for it (@{thm development_constant_request_fields}).
\<close>

corollary request_presents_constant_request:
  assumes presents: "request_presents key S R rows r k ks"
    and built: "development_constant_request reading kind (snd S) ra a c=Some r"
  shows "k=key c" "set ks=key ` fset (development_request_support (snd S) c)"
proof -
  obtain p s Sup E where shape: "r=(p,s,Sup,E)" by (cases r)
  have subject: "problem_subject p={|c|}" and support: "Sup=development_request_support (snd S) c"
    using development_constant_request_fields[OF built[unfolded shape]] by blast+
  obtain d where d: "problem_subject (fst r)={|d|}" and kd: "k=key d"
    and ks: "set ks=key ` fset (fst (snd (snd r)))"
    by (rule request_presents_recovery[OF presents])
  have "d=c" using d subject shape by simp
  then show "k=key c" using kd by simp
  show "set ks=key ` fset (development_request_support (snd S) c)" using ks support shape by simp
qed

section \<open>A request constructed from the state is presented\<close>

text \<open>
  The introduction of the relation, beside its elimination @{thm request_presents_recovery}. The rows'
  entity key is not assumed injective: a request constructed from the state carries the least context of
  its constant, whose entities are the state's (@{thm development_request_context_exact}), so a family of
  constructed requests keys only entities of the state, where the first-occurrence key is injective
  (@{thm request_entity_key_injective}).
\<close>

lemma request_rows_entity_key_injective:
  assumes requests: "\<And>q. q\<in>set rs \<Longrightarrow>
      \<exists>reading kind ra a d. development_constant_request reading kind (snd S) ra a d=Some q"
  shows "inj_on (development_entity_key (snd S)) (development_row_entities rs)"
proof (rule request_entity_key_injective, rule subsetI)
  fix e assume "e\<in>development_row_entities rs"
  then obtain q where q: "q\<in>set rs" "e\<in>fset (snd (snd (snd q)))"
    unfolding development_row_entities_def by blast
  obtain reading kind ra a d where built: "development_constant_request reading kind (snd S) ra a d=Some q"
    using requests[OF q(1)] by blast
  obtain p s Sup E where shape: "q=(p,s,Sup,E)" by (cases q)
  have "E=development_request_context (snd S) d"
    by (rule development_constant_request_fields(5)[OF built[unfolded shape]])
  then have "e |\<in>| development_request_context (snd S) d" using q(2) shape by simp
  then show "e\<in>set (snd (snd S))" by (simp only: development_request_context_exact)
qed

text \<open>
  The subject and the support of a constructed request are positions of the state: the subject is declared
  by an entity of the state and every constant of the support is mentioned by a statement of its scope, and
  a constant an entity of a presented state declares or mentions is a position of its table
  (@{thm [source] state_presents_declared_inside}, @{thm [source] state_presents_mentions_inside}).
\<close>

lemma request_constructed_positions:
  assumes state: "state_presents key S R"
    and built: "development_constant_request reading kind (snd S) ra a c=Some r"
  shows "fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}"
proof -
  obtain p s Sup E where shape: "r=(p,s,Sup,E)" by (cases r)
  have subject: "problem_subject p={|c|}" and support: "Sup=development_request_support (snd S) c"
    using development_constant_request_fields[OF built[unfolded shape]] by blast+
  have "development_stated_constant reading (snd S) c\<noteq>None"
    using built unfolding development_constant_request_def by auto
  then obtain t where "development_stated_constant reading (snd S) c=Some t" by blast
  then obtain e where e: "e\<in>set (snd (snd S))" "isabelle_declared_constant e=Some c"
    using development_stated_constant_declared by blast
  have "c\<in>set (entity_declared e)" by (simp add: entity_declared_def e(2))
  then have cp: "c<length (fst (snd S))" by (rule state_presents_declared_inside[OF state e(1)])
  have dp: "d<length (fst (snd S))" if d: "d |\<in>| Sup" for d
  proof -
    obtain e' q where e': "e'\<in>set (development_constant_scope (snd S) c)"
      and q: "isabelle_specified_proposition e'=Some q" "d\<in>set (isabelle_term_constants q)"
      using d support development_request_support_member by blast
    have m: "d\<in>set (entity_mentions e')" using q by (simp add: entity_mentions_def)
    have inside: "e'\<in>set (snd (snd S))" using e' by (simp only: development_constant_scope_member)
    show ?thesis by (rule state_presents_mentions_inside[OF state inside m])
  qed
  show ?thesis using cp dp subject shape by auto
qed

text \<open>
  A request constructed from the state, held by a development-rows presentation that takes the state's
  constant key and the rows' entity key @{term "development_entity_key (snd S)"}, is presented with the key
  of its constant and the support family its row carries. The presentation's conjuncts are taken as they
  stand, but its entity key's injectivity, which is derived from every request of the family being
  constructed from the state. The subject's being exactly one constant is the construction's own
  (@{thm development_constant_request_fields}), so no request without a locus enters.
\<close>

theorem request_presents_constructed:
  assumes state: "state_presents key S R"
    and sv: "single_valued (set rows)" and formed: "\<forall>(l,v)\<in>set rows. term_formed v"
    and keys: "inj_on key (development_row_constants ps rs)"
    and inerts: "inj_on inert (development_contract_term ` problem_contract ` set ps)"
    and problems: "development_problems_present key inert origin grant ps rows"
    and requested: "development_requests_present key (development_entity_key (snd S)) supported scope ps rs rows"
    and issues: "development_issues_present key decs ps iss rows"
    and requests: "\<And>q. q\<in>set rs \<Longrightarrow>
      \<exists>reading kind ra a d. development_constant_request reading kind (snd S) ra a d=Some q"
    and r: "r\<in>set rs"
    and built: "development_constant_request reading kind (snd S) ra a c=Some r"
  shows "request_presents key S R rows r (key c) (supported r)"
proof -
  have present: "development_rows_present key (development_entity_key (snd S)) inert origin grant supported scope decs ps rs iss rows"
    unfolding development_rows_present_def
    using sv formed keys request_rows_entity_key_injective[of rs S, OF requests] inerts problems requested issues
    by blast
  obtain p s Sup E where shape: "r=(p,s,Sup,E)" by (cases r)
  have subject: "problem_subject (fst r)={|c|}"
    using development_constant_request_fields(3)[OF built[unfolded shape]] shape by simp
  have k: "key c=drop 6 (development_located_at key Development_Request_Role (fst r))"
    by (simp only: development_located_at_subject[OF subject] development_locus_parts(3))
  have found: "(development_row_search,Pair_Term (development_request_body (supported r) (scope r))
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program"
    using development_request_at[OF present r, of "development_request_body (supported r) (scope r)"] by simp
  have positions: "fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}"
    by (rule request_constructed_positions[OF state built])
  show ?thesis
    unfolding request_presents_def
  proof (intro conjI)
    show "state_presents key S R" by (rule state)
    show "\<exists>inert origin grant supported' scope decs ps rs iss.
        development_rows_present key (development_entity_key (snd S)) inert origin grant supported' scope decs ps rs iss rows \<and>
        r\<in>set rs" using present r by blast
    show "fset (problem_subject (fst r)) \<union> fset (fst (snd (snd r)))\<subseteq>{..<length (fst (snd S))}" by (rule positions)
    show "key c=drop 6 (development_located_at key Development_Request_Role (fst r))" by (rule k)
    show "\<exists>es. (development_row_search,Pair_Term (development_request_body (supported r) es)
      (Pair_Term (path_term (development_located_at key Development_Request_Role (fst r)))
        (development_rows_term rows)))\<in>positive_meaning development_rows_program" using found by blast
  qed
qed

end
