theory Development_Rows
imports Development_Loci Development_Publication
begin

section \<open>A citation is a path, and its absence is the store's own optional value\<close>

text \<open>
  The development's store holds rows at loci. A row cites other rows, and a citation is the path of the
  locus cited: nothing but its shapes. An optional citation is the store's own optional value, reused
  and not redefined (@{const store_option_term}): absent is the empty payload and present is a pair of
  the empty payload and the path, so an absence is a positive shape a rule matches, never a failure to
  find. A family of citations is the data list of their paths; a family of families is the shape native
  readiness already reads a problem's decompositions in (@{const readiness_decompositions}).
\<close>

definition development_row_citation :: "bool list option \<Rightarrow> factor_term" where
  "development_row_citation l=store_option_term path_term l"

lemma development_row_citation_simps [simp]:
  "development_row_citation None=Payload_Term []"
  "development_row_citation (Some l)=Pair_Term (Payload_Term []) (path_term l)"
  by (simp_all add: development_row_citation_def store_option_term_def)

lemma development_row_citation_injective:
  "development_row_citation l=development_row_citation m \<longleftrightarrow> l=m"
  by (cases l; cases m) (simp_all add: path_term_injective)

lemma development_row_citation_absent: "development_row_citation l=Payload_Term [] \<longleftrightarrow> l=None"
  by (cases l) simp_all

lemma path_term_inj: "inj path_term"
  by (rule injI) (simp add: path_term_injective)

definition development_row_family :: "bool list list \<Rightarrow> factor_term" where
  "development_row_family ls=data_list_term (map path_term ls)"

lemma development_row_family_injective:
  "development_row_family ls=development_row_family ms \<longleftrightarrow> ls=ms"
  by (simp add: development_row_family_def data_list_term_injective inj_map_eq_map[OF path_term_inj])

lemma development_row_family_inj: "inj development_row_family"
  by (rule injI) (simp add: development_row_family_injective)

lemma readiness_decompositions_family:
  "readiness_decompositions hs=data_list_term (map development_row_family hs)"
proof -
  have "(\<lambda>h. data_list_term (map path_term h))=development_row_family"
    by (simp add: fun_eq_iff development_row_family_def)
  then show ?thesis by (simp add: readiness_decompositions_def)
qed

lemma readiness_decompositions_injective:
  "readiness_decompositions hs=readiness_decompositions gs \<longleftrightarrow> hs=gs"
  by (simp add: readiness_decompositions_family data_list_term_injective
    inj_map_eq_map[OF development_row_family_inj])

section \<open>The four bodies\<close>

text \<open>
  A body holds what the loop's decisions read of a notion and nothing else. A problem's body is its
  origin citation, its authority citation and its contract term carried inert; its subject and its
  kind are the locus. A request's body is its support and its context, two families of citations; it
  carries neither its problem nor its subject, which are the locus. An answer's body is
  not stated here: its removed rows are rows of the request state and its added rows are rows of the
  answer state, which only the answer state gives an identity, and reading an edit so is the reduction
  of an edit that the comparison across two states owns. An issue's body is the family of decompositions that applied, each a family
  of premise loci, empty when none did.

  The inert presentation of a contract term and the key of a state's row are supplied, as the key of
  a constant is: they are the state's own assignments, of which every contract below asks injectivity
  on the values in question and nothing else, so no definition here waits on the state that fixes
  them. The contract term is read by no decision of the loop; @{const development_contract_term}
  takes it out of the contract whose constructor the locus already carries.
\<close>

definition development_problem_body ::
    "(isabelle_term \<Rightarrow> factor_term) \<Rightarrow> bool list option \<Rightarrow> bool list option \<Rightarrow> development_contract \<Rightarrow> factor_term" where
  "development_problem_body inert x y k=Pair_Term (development_row_citation x)
    (Pair_Term (development_row_citation y) (inert (development_contract_term k)))"

definition development_request_body :: "bool list list \<Rightarrow> bool list list \<Rightarrow> factor_term" where
  "development_request_body S E=Pair_Term (development_row_family S) (development_row_family E)"

lemma development_problem_body_injective:
  "development_problem_body inert x y k=development_problem_body inert x' y' k' \<longleftrightarrow>
    x=x' \<and> y=y' \<and> inert (development_contract_term k)=inert (development_contract_term k')"
  by (simp add: development_problem_body_def development_row_citation_injective)

lemma development_request_body_injective:
  "development_request_body S E=development_request_body S' E' \<longleftrightarrow> S=S' \<and> E=E'"
  by (simp add: development_request_body_def development_row_family_injective)

lemma development_contract_by_kind:
  assumes "development_kind_path k=development_kind_path l"
    and "development_contract_term k=development_contract_term l"
  shows "k=l"
  using assms by (cases k; cases l) simp_all

section \<open>The locus of a presented notion\<close>

text \<open>
  A notion stands at the locus of its problem under its role. The locus is stated where the problem's
  subject is one constant (@{const development_problem_locus_at}); every presented problem has one, so
  its row locus is that locus.
\<close>

definition development_located_at ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_role \<Rightarrow> development_problem \<Rightarrow> bool list" where
  "development_located_at key r p=the (development_problem_locus_at key r p)"

lemma development_located_at_subject:
  assumes subject: "problem_subject p={|c|}"
  shows "development_located_at key r p=development_locus key r (problem_contract p) c"
proof -
  have "development_subject_constant p=Some c" using subject development_subject_constant_exact by blast
  then show ?thesis by (simp add: development_located_at_def development_problem_locus_at_def)
qed

section \<open>The presentation relation\<close>

type_synonym development_store_rows = "(bool list\<times>factor_term) list"
type_synonym development_issue = "development_problem\<times>(nat\<times>development_problem) fset fset"

text \<open>
  The relation is stated in the shape of @{const readiness_presents}: the key assignments are
  parameters, the distinctness of loci is a premise under @{const inj_on}, the store's single-valuedness
  is a premise, and each condition is over actual rows. Families are presented through listings the
  presentation chooses, as @{const readiness_presents} takes @{text hs}: a request's support and context
  listings, an issue's decomposition listing. Origin and authority are optional citations: a problem
  cites nothing as its origin exactly when it is a residual and nothing as its authority exactly when it
  is generated. Truth has no counterpart among citations, so a problem whose authority is truth is not
  presented. The store is the path store of the rows.
\<close>

definition development_row_constants :: "development_problem list \<Rightarrow> development_request list \<Rightarrow> nat set" where
  "development_row_constants ps rs=(\<Union>p\<in>set ps. fset (problem_subject p)) \<union> (\<Union>r\<in>set rs. fset (fst (snd (snd r))))"

definition development_row_entities ::
    "development_request list \<Rightarrow> isabelle_entity set" where
  "development_row_entities rs=(\<Union>r\<in>set rs. fset (snd (snd (snd r))))"

definition development_problems_present ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> factor_term) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> development_problem list \<Rightarrow> development_store_rows \<Rightarrow> bool" where
  "development_problems_present key inert origin grant ps rows \<longleftrightarrow>
    inj_on (development_located_at key Development_Problem_Role) (set ps) \<and>
    (\<forall>p\<in>set ps. (\<exists>c. problem_subject p={|c|}) \<and> problem_authority p\<noteq>Development_Truth \<and>
      (origin p=None \<longleftrightarrow> problem_origin p=Development_Residual) \<and>
      (grant p=None \<longleftrightarrow> problem_authority p=Development_Generated) \<and>
      (development_located_at key Development_Problem_Role p,
        development_problem_body inert (origin p) (grant p) (problem_contract p))\<in>set rows)"

definition development_requests_present ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_entity \<Rightarrow> bool list) \<Rightarrow> (development_request \<Rightarrow> bool list list) \<Rightarrow>
      (development_request \<Rightarrow> bool list list) \<Rightarrow> development_problem list \<Rightarrow> development_request list \<Rightarrow>
      development_store_rows \<Rightarrow> bool" where
  "development_requests_present key ekey supported scope ps rs rows \<longleftrightarrow>
    (\<forall>r\<in>set rs. fst r\<in>set ps \<and> development_contract_term (problem_contract (fst r))=fst (snd r) \<and>
      set (supported r)=key ` fset (fst (snd (snd r))) \<and> set (scope r)=ekey ` fset (snd (snd (snd r))) \<and>
      (development_located_at key Development_Request_Role (fst r),
        development_request_body (supported r) (scope r))\<in>set rows)"

definition development_issues_present ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (development_issue \<Rightarrow> bool list list list) \<Rightarrow> development_problem list \<Rightarrow>
      development_issue list \<Rightarrow> development_store_rows \<Rightarrow> bool" where
  "development_issues_present key decs ps iss rows \<longleftrightarrow>
    (\<forall>i\<in>set iss. fst i\<in>set ps \<and> (\<forall>H\<in>fset (snd i). snd ` fset H\<subseteq>set ps) \<and>
      set (map set (decs i))=(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i) \<and>
      (development_located_at key Development_Issue_Role (fst i),readiness_decompositions (decs i))\<in>set rows)"

definition development_rows_present ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_entity \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      (development_request \<Rightarrow> bool list list) \<Rightarrow> (development_request \<Rightarrow> bool list list) \<Rightarrow>
      (development_issue \<Rightarrow> bool list list list) \<Rightarrow> development_problem list \<Rightarrow> development_request list \<Rightarrow>
      development_issue list \<Rightarrow> development_store_rows \<Rightarrow> bool" where
  "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows \<longleftrightarrow>
    single_valued (set rows) \<and> inj_on key (development_row_constants ps rs) \<and>
    inj_on ekey (development_row_entities rs) \<and>
    inj_on inert (development_contract_term ` problem_contract ` set ps) \<and>
    development_problems_present key inert origin grant ps rows \<and>
    development_requests_present key ekey supported scope ps rs rows \<and>
    development_issues_present key decs ps iss rows"

context
  fixes key ekey inert origin grant supported scope decs ps rs iss rows
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
begin

lemma development_rows_single_valued: "single_valued (set rows)"
  using present by (simp add: development_rows_present_def)

lemma development_rows_key_injective: "inj_on key (development_row_constants ps rs)"
  using present by (simp add: development_rows_present_def)

lemma development_rows_entity_injective: "inj_on ekey (development_row_entities rs)"
  using present by (simp add: development_rows_present_def)

lemma development_rows_inert_injective: "inj_on inert (development_contract_term ` problem_contract ` set ps)"
  using present by (simp add: development_rows_present_def)

lemma development_rows_problem_loci: "inj_on (development_located_at key Development_Problem_Role) (set ps)"
  using present by (simp add: development_rows_present_def development_problems_present_def)

lemma development_rows_parts:
  "development_problems_present key inert origin grant ps rows"
  "development_requests_present key ekey supported scope ps rs rows"
  "development_issues_present key decs ps iss rows"
  using present unfolding development_rows_present_def by blast+

text \<open>At most one row stands at a locus: a premise of the presentation, never a check in a decision.\<close>

lemma development_rows_lookup:
  assumes "(l,v)\<in>set rows"
  shows "store_lookup (path_store rows) l=Some v"
  using path_store_lookup[OF development_rows_single_valued] assms by simp

lemma development_rows_unique:
  assumes "(l,v)\<in>set rows" "(l,w)\<in>set rows"
  shows "v=w"
  using development_rows_single_valued assms by (rule single_valued_outputs)

lemma development_rows_problem:
  assumes p: "p\<in>set ps"
  obtains c where "problem_subject p={|c|}" "problem_authority p\<noteq>Development_Truth"
    "origin p=None \<longleftrightarrow> problem_origin p=Development_Residual"
    "grant p=None \<longleftrightarrow> problem_authority p=Development_Generated"
    "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (development_problem_body inert (origin p) (grant p) (problem_contract p))"
proof -
  have "(\<exists>c. problem_subject p={|c|}) \<and> problem_authority p\<noteq>Development_Truth \<and>
      (origin p=None \<longleftrightarrow> problem_origin p=Development_Residual) \<and>
      (grant p=None \<longleftrightarrow> problem_authority p=Development_Generated) \<and>
      (development_located_at key Development_Problem_Role p,
        development_problem_body inert (origin p) (grant p) (problem_contract p))\<in>set rows"
    using bspec[OF conjunct2[OF development_rows_parts(1)[unfolded development_problems_present_def]] p] .
  note all = this
  from all[THEN conjunct1] obtain c where c: "problem_subject p={|c|}" by (rule exE)
  show ?thesis by (rule that[OF c all[THEN conjunct2, THEN conjunct1]
    all[THEN conjunct2, THEN conjunct2, THEN conjunct1] all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
    development_rows_lookup[OF all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]]])
qed

lemma development_rows_subject_constant:
  assumes p: "p\<in>set ps" and c: "problem_subject p={|c|}"
  shows "c\<in>development_row_constants ps rs"
  unfolding development_row_constants_def by (rule UnI1, rule UN_I[OF p]) (simp add: c)

text \<open>
  A locus under any role determines the problem: two presented problems whose loci agree under one
  role agree on their kind and their constant, so their problem loci agree, and those are distinct.
\<close>

lemma development_rows_same_locus:
  assumes p: "p\<in>set ps" and q: "q\<in>set ps"
    and same: "development_located_at key r p=development_located_at key r q"
  shows "p=q"
proof -
  obtain c where c: "problem_subject p={|c|}" by (rule development_rows_problem[OF p])
  obtain d where d: "problem_subject q={|d|}" by (rule development_rows_problem[OF q])
  have "development_locus key r (problem_contract p) c=development_locus key r (problem_contract q) d"
    using same by (simp add: development_located_at_subject[OF c] development_located_at_subject[OF d])
  then have "r=r \<and> development_kind_path (problem_contract p)=development_kind_path (problem_contract q) \<and> c=d"
    by (rule development_locus_injective[OF development_rows_key_injective development_rows_subject_constant[OF p c]
      development_rows_subject_constant[OF q d]])
  then have "development_located_at key Development_Problem_Role p=development_located_at key Development_Problem_Role q"
    by (simp add: development_located_at_subject[OF c] development_located_at_subject[OF d] development_locus_def)
  then show "p=q" using inj_onD[OF development_rows_problem_loci _ p q] by blast
qed

section \<open>Residuals and generated problems are shapes of the stored row\<close>

text \<open>
  Which problems are residuals is no longer a comparison of an origin value: it is the shape test that
  the origin a presented problem's row cites is the empty payload. Which problems are generated is the
  same test on the authority it cites.
\<close>

theorem development_rows_residual_shape:
  assumes p: "p\<in>set ps"
  shows "p\<in>set (development_residual_problems ps) \<longleftrightarrow>
    (\<exists>v. store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (Pair_Term (Payload_Term []) v))"
proof -
  obtain c where "problem_subject p={|c|}" and "problem_authority p\<noteq>Development_Truth"
    and origin: "origin p=None \<longleftrightarrow> problem_origin p=Development_Residual"
    and "grant p=None \<longleftrightarrow> problem_authority p=Development_Generated"
    and found: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (development_problem_body inert (origin p) (grant p) (problem_contract p))"
    by (rule development_rows_problem[OF p])
  have "p\<in>set (development_residual_problems ps) \<longleftrightarrow> origin p=None"
    using p origin by (simp add: development_residual_problems_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>v. development_problem_body inert (origin p) (grant p) (problem_contract p)=
      Pair_Term (Payload_Term []) v)"
    by (simp add: development_problem_body_def development_row_citation_absent)
  finally show ?thesis using found by simp
qed

theorem development_rows_generated_shape:
  assumes p: "p\<in>set ps"
  shows "problem_authority p=Development_Generated \<longleftrightarrow>
    (\<exists>u v. store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (Pair_Term u (Pair_Term (Payload_Term []) v)))"
proof -
  obtain c where "problem_subject p={|c|}" and "problem_authority p\<noteq>Development_Truth"
    and "origin p=None \<longleftrightarrow> problem_origin p=Development_Residual"
    and grant: "grant p=None \<longleftrightarrow> problem_authority p=Development_Generated"
    and found: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (development_problem_body inert (origin p) (grant p) (problem_contract p))"
    by (rule development_rows_problem[OF p])
  have "problem_authority p=Development_Generated \<longleftrightarrow> grant p=None" using grant by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>u v. development_problem_body inert (origin p) (grant p) (problem_contract p)=
      Pair_Term u (Pair_Term (Payload_Term []) v))"
    by (simp add: development_problem_body_def development_row_citation_absent)
  finally show ?thesis using found by simp
qed

section \<open>The store determines the requests and issues it presents\<close>

lemma development_rows_request:
  assumes r: "r\<in>set rs"
  shows "fst r\<in>set ps" "development_contract_term (problem_contract (fst r))=fst (snd r)"
    "set (supported r)=key ` fset (fst (snd (snd r)))" "set (scope r)=ekey ` fset (snd (snd (snd r)))"
    "store_lookup (path_store rows) (development_located_at key Development_Request_Role (fst r))=
      Some (development_request_body (supported r) (scope r))"
proof -
  have all: "fst r\<in>set ps \<and> development_contract_term (problem_contract (fst r))=fst (snd r) \<and>
      set (supported r)=key ` fset (fst (snd (snd r))) \<and> set (scope r)=ekey ` fset (snd (snd (snd r))) \<and>
      (development_located_at key Development_Request_Role (fst r),
        development_request_body (supported r) (scope r))\<in>set rows"
    using bspec[OF development_rows_parts(2)[unfolded development_requests_present_def] r] .
  note all = this
  show "fst r\<in>set ps" "development_contract_term (problem_contract (fst r))=fst (snd r)"
    "set (supported r)=key ` fset (fst (snd (snd r)))" "set (scope r)=ekey ` fset (snd (snd (snd r)))"
    by (rule all[THEN conjunct1] all[THEN conjunct2, THEN conjunct1] all[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])+
  show "store_lookup (path_store rows) (development_located_at key Development_Request_Role (fst r))=
      Some (development_request_body (supported r) (scope r))"
    by (rule development_rows_lookup[OF all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]])
qed

theorem development_rows_request_recovery:
  assumes r: "r\<in>set rs" and s: "s\<in>set rs"
    and same: "development_located_at key Development_Request_Role (fst r)=
      development_located_at key Development_Request_Role (fst s)"
  shows "r=s"
proof -
  have problem: "fst r=fst s" by (rule development_rows_same_locus[OF development_rows_request(1)[OF r] development_rows_request(1)[OF s] same])
  have "development_request_body (supported r) (scope r)=development_request_body (supported s) (scope s)"
    using development_rows_request(5)[OF r] development_rows_request(5)[OF s] same by simp
  then have lists: "supported r=supported s" "scope r=scope s" by (simp_all add: development_request_body_injective)
  have support_inside: "fset (fst (snd (snd r)))\<subseteq>development_row_constants ps rs"
    "fset (fst (snd (snd s)))\<subseteq>development_row_constants ps rs"
    using r s by (auto simp: development_row_constants_def)
  have "key ` fset (fst (snd (snd r)))=key ` fset (fst (snd (snd s)))"
    using development_rows_request(3)[OF r] development_rows_request(3)[OF s] lists by simp
  then have support: "fst (snd (snd r))=fst (snd (snd s))"
    using inj_on_image_eq_iff[OF development_rows_key_injective support_inside] by (simp add: fset_inject)
  have context_inside: "fset (snd (snd (snd r)))\<subseteq>development_row_entities rs"
    "fset (snd (snd (snd s)))\<subseteq>development_row_entities rs"
    using r s by (auto simp: development_row_entities_def)
  have "ekey ` fset (snd (snd (snd r)))=ekey ` fset (snd (snd (snd s)))"
    using development_rows_request(4)[OF r] development_rows_request(4)[OF s] lists by simp
  then have scoped: "snd (snd (snd r))=snd (snd (snd s))"
    using inj_on_image_eq_iff[OF development_rows_entity_injective context_inside] by (simp add: fset_inject)
  have term_eq: "fst (snd r)=fst (snd s)" using development_rows_request(2)[OF r] development_rows_request(2)[OF s] problem by simp
  show "r=s" using problem term_eq support scoped by (simp add: prod_eq_iff)
qed

lemma development_rows_issue:
  assumes i: "i\<in>set iss"
  shows "fst i\<in>set ps" "\<forall>H\<in>fset (snd i). snd ` fset H\<subseteq>set ps"
    "set (map set (decs i))=(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i)"
    "store_lookup (path_store rows) (development_located_at key Development_Issue_Role (fst i))=
      Some (readiness_decompositions (decs i))"
proof -
  have all: "fst i\<in>set ps \<and> (\<forall>H\<in>fset (snd i). snd ` fset H\<subseteq>set ps) \<and>
      set (map set (decs i))=(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i) \<and>
      (development_located_at key Development_Issue_Role (fst i),readiness_decompositions (decs i))\<in>set rows"
    using bspec[OF development_rows_parts(3)[unfolded development_issues_present_def] i] .
  show "fst i\<in>set ps" "\<forall>H\<in>fset (snd i). snd ` fset H\<subseteq>set ps"
    "set (map set (decs i))=(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i)"
    by (rule all[THEN conjunct1] all[THEN conjunct2, THEN conjunct1] all[THEN conjunct2, THEN conjunct2, THEN conjunct1])+
  show "store_lookup (path_store rows) (development_located_at key Development_Issue_Role (fst i))=
      Some (readiness_decompositions (decs i))"
    by (rule development_rows_lookup[OF all[THEN conjunct2, THEN conjunct2, THEN conjunct2]])
qed

text \<open>
  An issue at a locus is determined up to its premise sockets: the family of premise families that
  applied is recovered exactly, the sockets of each premise being dropped as readiness drops them.
\<close>

theorem development_rows_issue_recovery:
  assumes i: "i\<in>set iss" and j: "j\<in>set iss"
    and same: "development_located_at key Development_Issue_Role (fst i)=
      development_located_at key Development_Issue_Role (fst j)"
  shows "fst i=fst j" "(\<lambda>H. snd ` fset H) ` fset (snd i)=(\<lambda>H. snd ` fset H) ` fset (snd j)"
proof -
  show "fst i=fst j" by (rule development_rows_same_locus[OF development_rows_issue(1)[OF i] development_rows_issue(1)[OF j] same])
  have "readiness_decompositions (decs i)=readiness_decompositions (decs j)"
    using development_rows_issue(4)[OF i] development_rows_issue(4)[OF j] same by simp
  then have "decs i=decs j" by (simp add: readiness_decompositions_injective)
  note decs_eq = this
  have "(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i)=set (map set (decs i))"
    by (rule sym[OF development_rows_issue(3)[OF i]])
  also have "\<dots>=set (map set (decs j))" by (simp only: decs_eq)
  also have "\<dots>=(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd j)"
    by (rule development_rows_issue(3)[OF j])
  finally have "(\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd i)=
      (\<lambda>H. development_located_at key Development_Problem_Role ` snd ` fset H) ` fset (snd j)" .
  then have "image (image (development_located_at key Development_Problem_Role)) ((\<lambda>H. snd ` fset H) ` fset (snd i))=
      image (image (development_located_at key Development_Problem_Role)) ((\<lambda>H. snd ` fset H) ` fset (snd j))"
    by (simp add: image_image)
  moreover have sub_i: "(\<lambda>H. snd ` fset H) ` fset (snd i)\<subseteq>Pow (set ps)"
    using development_rows_issue(2)[OF i] by auto
  moreover have sub_j: "(\<lambda>H. snd ` fset H) ` fset (snd j)\<subseteq>Pow (set ps)"
    using development_rows_issue(2)[OF j] by auto
  ultimately show "(\<lambda>H. snd ` fset H) ` fset (snd i)=(\<lambda>H. snd ` fset H) ` fset (snd j)"
    by (simp only: inj_on_image_eq_iff[OF inj_on_image_Pow[OF development_rows_problem_loci] sub_i sub_j])
qed

end

section \<open>The store determines the problems it presents\<close>

text \<open>
  Two presentations by one store and one set of key assignments that place problems at one locus agree
  on everything the row carries: the subject and the contract, which are the locus and the inert term,
  both citations, and so whether the problem is a residual and its authority. The five other origins are
  told apart by the family of the locus cited, which the families that hold owner, obligation and
  refusal records will state; that is not a part of this row.
\<close>

theorem development_rows_problem_recovery:
  assumes P: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and Q: "development_rows_present key ekey' inert origin' grant' supported' scope' decs' ps' rs' iss' rows"
    and keys: "inj_on key (development_row_constants ps rs \<union> development_row_constants ps' rs')"
    and inerts: "inj_on inert (development_contract_term ` problem_contract ` (set ps \<union> set ps'))"
    and p: "p\<in>set ps" and q: "q\<in>set ps'"
    and same: "development_located_at key Development_Problem_Role p=development_located_at key Development_Problem_Role q"
  shows "problem_subject p=problem_subject q" "problem_contract p=problem_contract q"
    "origin p=origin' q" "grant p=grant' q" "problem_authority p=problem_authority q"
    "problem_origin p=Development_Residual \<longleftrightarrow> problem_origin q=Development_Residual"
proof -
  obtain c where c: "problem_subject p={|c|}" and pt: "problem_authority p\<noteq>Development_Truth"
    and po: "origin p=None \<longleftrightarrow> problem_origin p=Development_Residual"
    and pg: "grant p=None \<longleftrightarrow> problem_authority p=Development_Generated"
    and pf: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role p)=
      Some (development_problem_body inert (origin p) (grant p) (problem_contract p))"
    by (rule development_rows_problem[OF P p])
  obtain d where d: "problem_subject q={|d|}" and qt: "problem_authority q\<noteq>Development_Truth"
    and qo: "origin' q=None \<longleftrightarrow> problem_origin q=Development_Residual"
    and qg: "grant' q=None \<longleftrightarrow> problem_authority q=Development_Generated"
    and qf: "store_lookup (path_store rows) (development_located_at key Development_Problem_Role q)=
      Some (development_problem_body inert (origin' q) (grant' q) (problem_contract q))"
    by (rule development_rows_problem[OF Q q])
  have "development_problem_body inert (origin p) (grant p) (problem_contract p)=
      development_problem_body inert (origin' q) (grant' q) (problem_contract q)"
    using pf qf same by simp
  then have cites: "origin p=origin' q" "grant p=grant' q"
    and inert_eq: "inert (development_contract_term (problem_contract p))=inert (development_contract_term (problem_contract q))"
    by (simp_all add: development_problem_body_injective)
  have terms: "development_contract_term (problem_contract p)=development_contract_term (problem_contract q)"
    using inj_onD[OF inerts inert_eq] p q by blast
  have cin: "c\<in>development_row_constants ps rs \<union> development_row_constants ps' rs'"
    using development_rows_subject_constant[OF P p c] by blast
  have din: "d\<in>development_row_constants ps rs \<union> development_row_constants ps' rs'"
    using development_rows_subject_constant[OF Q q d] by blast
  have loc: "development_locus key Development_Problem_Role (problem_contract p) c=
      development_locus key Development_Problem_Role (problem_contract q) d"
    using same by (simp add: development_located_at_subject[OF c] development_located_at_subject[OF d])
  have "Development_Problem_Role=Development_Problem_Role \<and>
      development_kind_path (problem_contract p)=development_kind_path (problem_contract q) \<and> c=d"
    by (rule development_locus_injective[OF keys cin din loc])
  then have kind: "development_kind_path (problem_contract p)=development_kind_path (problem_contract q)"
    and cd: "c=d" by simp_all
  show "problem_subject p=problem_subject q" using c d cd by simp
  show "problem_contract p=problem_contract q" by (rule development_contract_by_kind[OF kind terms])
  show "origin p=origin' q" "grant p=grant' q" by (fact cites)+
  show "problem_origin p=Development_Residual \<longleftrightarrow> problem_origin q=Development_Residual"
    using po qo cites by simp
  show "problem_authority p=problem_authority q"
    using pt qt pg qg cites by (cases "problem_authority p"; cases "problem_authority q") simp_all
qed

section \<open>Readiness at the locus\<close>

text \<open>
  @{const readiness_presents} asks of its key assignment only that it be injective on the problems, so
  any injective change of keys carries a presentation to another: the keys in every decomposition and
  every row of every cone move with it. The locus is such a change of the positional key
  @{const development_readiness_key}, so @{thm development_readiness_presents} and
  @{thm native_development_ready} are consumed at the locus and not one line of them is restated.
\<close>

lemma readiness_presents_rekey:
  assumes presents: "readiness_presents key D answered ps hs cone"
    and injective: "inj_on g (key ` set ps)"
  shows "readiness_presents (g \<circ> key) D answered ps (\<lambda>p. map (map g) (hs p))
    (\<lambda>p. map (\<lambda>(k,a,h). (g k,a,map (map g) h)) (cone p))"
proof -
  note all = presents[unfolded readiness_presents_def]
  have inj: "inj_on key (set ps)"
    and rows: "\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)"
    and answers: "fset answered\<subseteq>set ps"
    and decs: "\<forall>p\<in>set ps. set (map set (hs p))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
    and cones: "\<forall>p\<in>set ps. set (cone p)=readiness_entry key answered hs `
      {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}"
    by (rule all[THEN conjunct1] all[THEN conjunct2, THEN conjunct1] all[THEN conjunct2, THEN conjunct2, THEN conjunct1]
      all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
      all[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])+
  have inj': "inj_on (g \<circ> key) (set ps)" using inj injective by (rule comp_inj_on)
  have decs': "\<forall>p\<in>set ps. set (map set (map (map g) (hs p)))=
      (\<lambda>H. (g \<circ> key) ` snd ` fset H) ` fset (development_decompositions D p)"
  proof
    fix p assume p: "p\<in>set ps"
    have "set (map set (map (map g) (hs p)))=image (image g) (set (map set (hs p)))" by (simp add: image_image)
    also have "\<dots>=image (image g) ((\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p))"
      using decs p by simp
    also have "\<dots>=(\<lambda>H. (g \<circ> key) ` snd ` fset H) ` fset (development_decompositions D p)"
      by (simp add: image_image image_comp)
    finally show "set (map set (map (map g) (hs p)))=
        (\<lambda>H. (g \<circ> key) ` snd ` fset H) ` fset (development_decompositions D p)" .
  qed
  have cones': "\<forall>p\<in>set ps. set (map (\<lambda>(k,a,h). (g k,a,map (map g) h)) (cone p))=
      readiness_entry (g \<circ> key) answered (\<lambda>p. map (map g) (hs p)) ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}"
  proof
    fix p assume p: "p\<in>set ps"
    have "set (map (\<lambda>(k,a,h). (g k,a,map (map g) h)) (cone p))=
        (\<lambda>(k,a,h). (g k,a,map (map g) h)) ` (readiness_entry key answered hs ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+})"
      using cones p by simp
    also have "\<dots>=readiness_entry (g \<circ> key) answered (\<lambda>p. map (map g) (hs p)) ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}"
      by (simp add: image_image readiness_entry_def)
    finally show "set (map (\<lambda>(k,a,h). (g k,a,map (map g) h)) (cone p))=
        readiness_entry (g \<circ> key) answered (\<lambda>p. map (map g) (hs p)) ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}" .
  qed
  show ?thesis unfolding readiness_presents_def using inj' rows answers decs' cones' by (intro conjI) (assumption+)
qed

definition development_row_rekey ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_problem list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "development_row_rekey key ps k=development_located_at key Development_Problem_Role
    (the_inv_into (set ps) (development_readiness_key ps) k)"

definition development_row_decompositions ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_dependencies \<Rightarrow> development_problem list \<Rightarrow>
      development_problem \<Rightarrow> bool list list list" where
  "development_row_decompositions key D ps=(\<lambda>p. map (map (development_row_rekey key ps))
    (development_readiness_decompositions D ps p))"

definition development_row_cone ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      development_problem \<Rightarrow> readiness_table" where
  "development_row_cone key D answered ps=(\<lambda>p. map (\<lambda>(k,a,h). (development_row_rekey key ps k,a,
    map (map (development_row_rekey key ps)) h))
    (development_readiness_cone D answered ps (development_readiness_closure D answered) p))"

lemma development_readiness_key_inj: "inj_on (development_readiness_key ps) (set ps)"
  unfolding inj_on_def using development_readiness_key_injective by blast

lemma development_row_rekey_at:
  assumes p: "p\<in>set ps"
  shows "development_row_rekey key ps (development_readiness_key ps p)=development_located_at key Development_Problem_Role p"
  by (simp add: development_row_rekey_def the_inv_into_f_f[OF development_readiness_key_inj p])

lemma development_row_rekey_injective:
  assumes loci: "inj_on (development_located_at key Development_Problem_Role) (set ps)"
  shows "inj_on (development_row_rekey key ps) (development_readiness_key ps ` set ps)"
proof (rule inj_onI)
  fix k l
  assume k: "k\<in>development_readiness_key ps ` set ps" and l: "l\<in>development_readiness_key ps ` set ps"
    and same: "development_row_rekey key ps k=development_row_rekey key ps l"
  from k obtain p where p: "p\<in>set ps" and kp: "k=development_readiness_key ps p" by blast
  from l obtain q where q: "q\<in>set ps" and lq: "l=development_readiness_key ps q" by blast
  have "development_located_at key Development_Problem_Role p=development_located_at key Development_Problem_Role q"
    using same by (simp add: kp lq development_row_rekey_at[OF p] development_row_rekey_at[OF q])
  then have "p=q" using inj_onD[OF loci _ p q] by blast
  then show "k=l" by (simp add: kp lq)
qed

theorem development_rows_readiness_presents:
  assumes loci: "inj_on (development_located_at key Development_Problem_Role) (set ps)"
    and closed: "development_readiness_scope_closed D answered ps"
  shows "readiness_presents (development_row_rekey key ps \<circ> development_readiness_key ps) D answered ps
    (development_row_decompositions key D ps) (development_row_cone key D answered ps)"
  using readiness_presents_rekey[OF development_readiness_presents[OF closed] development_row_rekey_injective[OF loci]]
  unfolding development_row_decompositions_def development_row_cone_def .

theorem development_rows_native_ready:
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and closed: "development_readiness_scope_closed D answered ps"
    and p: "p\<in>set ps" and xf: "term_formed x"
  shows "(readiness_ready,Pair_Term x (Pair_Term (readiness_table_term (development_row_cone key D answered ps p))
      (Pair_Term (path_term (development_located_at key Development_Problem_Role p))
        (readiness_value (p |\<in>| answered) (development_row_decompositions key D ps p)))))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> development_ready D answered p"
proof -
  have loci: "inj_on (development_located_at key Development_Problem_Role) (set ps)"
    by (rule development_rows_problem_loci[OF present])
  have "(readiness_ready,Pair_Term x (Pair_Term (readiness_table_term (development_row_cone key D answered ps p))
      (Pair_Term (path_term ((development_row_rekey key ps \<circ> development_readiness_key ps) p))
        (readiness_value (p |\<in>| answered) (development_row_decompositions key D ps p)))))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> development_ready D answered p"
    by (rule native_development_ready[OF development_rows_readiness_presents[OF loci closed] p xf])
  then show ?thesis by (simp only: comp_apply development_row_rekey_at[OF p])
qed

end
