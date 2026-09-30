theory Factor_Native_Committed_Registrations
  imports Factor_Committed_Registrations Factor_Varied_Constructions Factor_Varied_Narrowed_Transfer
begin

section \<open>(3): the native form of the committed resolution with complete registrations\<close>

text \<open>
  rc's native form. R5's native reading (@{const native_committed_resolution}) resolves every call of a finite set
  and the demand at once: the calls are kept, each resolved call carries a nonempty certificate family the finite proof
  checker accepts in the program as given, refuted calls are false and the demand is exact. Inside a registered
  commitment it is R5's @{thm [source] native_committed_resolution_exact} at the construction's formation, the
  commitment's exchanges and the lifts its completeness gives, as W4a's native forms compose it. The statement has the
  shape of R4's @{thm [source] native_call_resolution_exact}; unresolved asserts nothing. The program is any finite one:
  the installed site's reading among them, as the corollary below gives it.
\<close>

text \<open>At a formed selection (@{text registered_commitment_by_in}): R5's native form at the table, from the premises there.\<close>

theorem native_committed_registered_exact_by_in:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "registered_commitment_by_in \<Theta> sel \<kappa> P K"
    and result: "native_committed_resolution_by_in \<Theta> sel \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_resolution_by_exact_in[OF registered_commitment_by_in.exact_premises_by_in[OF registered] result]
  by blast+

theorem native_committed_registered_exact_at:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "registered_commitment_at prio \<kappa> P K"
    and result: "native_committed_resolution_by (finite_resolution_select_at prio \<kappa> P) \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_resolution_by_exact[OF registered_commitment_at.exact_premises[OF registered] result] by blast+

text \<open>The default is the instance at the commitment's own priority.\<close>

theorem native_committed_registered_exact:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "registered_commitment \<kappa> P K"
    and result: "native_committed_resolution \<kappa> K P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_registered_exact_at[OF registered_commitment.registered_at_default[OF registered]
    result[unfolded native_committed_resolution_select]] by blast+

text \<open>The declared commitment at narrowed sockets with productions is one such commitment, at any priority.\<close>

lemmas native_committed_registrations_exact =
  native_committed_registered_exact[OF committed_registrations.registered]

lemmas native_committed_registrations_exact_at =
  native_committed_registered_exact_at[OF committed_registrations.registered_at]

text \<open>(3): at the moded selection (O1), no premise reading a mode.\<close>

theorem native_committed_moded_exact:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "committed_registrations \<kappa> P m D \<Phi> corr"
    and result: "native_committed_resolution_by (finite_moded_select \<kappa> (finite_narrowed_commitment P m D \<Phi>) Dm M P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_registered_exact_at[OF committed_registrations.registered_moded[OF registered] result] by blast+

text \<open>At a table: rc's native form at a priority, from rc's premises at the table; at the moded priority it is the
  moded form at the table.\<close>

theorem native_committed_moded_exact_in:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "committed_registrations_in \<kappa> P m D \<Phi> corr \<Theta>"
    and result: "native_committed_resolution_by_in \<Theta> (finite_resolution_select_in \<Theta> prio \<kappa> P) \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_resolution_by_exact_in[OF registered_commitment_at_in.exact_premises_in[OF
    committed_registrations_in.registered_at_in[OF registered]] result] by blast+

text \<open>At the waiting moded selection, at a table whose calls are true: rc's native form there.\<close>

theorem native_committed_waiting_exact_in:
  fixes P :: "local_address option finite_native_system"
  assumes registered: "committed_registrations \<kappa> P m D \<Phi> corr" and true: "finite_table_true P \<Theta>"
    and result: "native_committed_resolution_by_in \<Theta> (finite_waiting_moded_select_in \<Theta> \<kappa>
      (finite_narrowed_commitment P m D \<Phi>) Dm \<Psi> M P) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_registered_exact_by_in[OF committed_registrations.registered_waiting[OF registered true] result]
  by blast+

section \<open>The produced record relocated\<close>

text \<open>
  A produced record is relocated by a map g of its sites as its truncation is (@{const declarations_relocated}): each
  socket at the site g e and the schema with its callees relocated. Its narrowing and production at a relocated key are
  the source's at the key the relocation came from, recovered by the inverse of g on the record's declared sites, the
  schema's callees mapped back by it; a production is its registration relocated as @{const finite_relocated_construction}
  relocates a construction: at the site g d, the schema renamed, the variable kept, and its families' queries and
  identity asked at the relocated sites. Nothing is claimed of the relocated registration's value at the relocated
  program: the search's equivariance under a site relocation is not stated (q138), and the productions' discharge at
  the program that reads the record stays a premise of its consumers. With g injective on the declared sites, the
  relocated truncation is the relocated record's by definition (@{text produced_relocated_truncate}) and the narrowing
  at a relocated socket is the source's (@{text produced_relocated_keys}), the two premises
  @{text committed_registrations_relocated} takes of its record.
\<close>

text \<open>A callee map with a left inverse on a schema's callees is undone by it, as for structures
  (@{thm [source] push_structure_left_inverse}).\<close>

lemma finite_rename_schema_left_inverse:
  assumes inverse: "\<And>d. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> k (g d) = d"
  shows "finite_rename_schema id id k (finite_rename_schema id id g S) = S"
proof -
  have same: "rename_schema id id (k \<circ> g) (decode_finite_schema S) = rename_schema id id id (decode_finite_schema S)"
    by (rule rename_schema_agreement) (use inverse in auto)
  have undone: "rename_schema id id (k \<circ> g) (decode_finite_schema S) = decode_finite_schema S" using same by simp
  have "decode_finite_schema (finite_rename_schema id id k (finite_rename_schema id id g S)) =
      rename_schema id id (k \<circ> g) (decode_finite_schema S)"
    by (simp only: finite_rename_schema_correct rename_schema_composition id_comp)
  from this undone have "decode_finite_schema (finite_rename_schema id id k (finite_rename_schema id id g S)) =
      decode_finite_schema S" by (rule trans)
  then show ?thesis by simp
qed

definition query_relocated :: "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'d,'v) collection_query \<Rightarrow> ('a,'e,'v) collection_query" where
  "query_relocated g q = \<lparr>query_equations = query_equations q, query_site = g (query_site q),
    query_goal = query_goal q, query_element = query_element q\<rparr>"

definition identity_relocated :: "('d \<Rightarrow> 'e) \<Rightarrow> ('d,'v) collection_identity \<Rightarrow> ('e,'v) collection_identity" where
  "identity_relocated g I = \<lparr>identity_left = identity_left I, identity_right = identity_right I,
    identity_site = g (identity_site I), identity_goal = identity_goal I\<rparr>"

definition family_relocated :: "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow> ('a,'e,'v) collection_family" where
  "family_relocated g F = \<lparr>family_base = map (query_relocated g) (family_base F),
    family_step = map_option (\<lambda>(q,p). (query_relocated g q,p)) (family_step F),
    family_key = family_key F, family_identity = map_option (identity_relocated g) (family_identity F)\<rparr>"

fun families_relocated ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'d,'v) registration_families \<Rightarrow> ('a,'e,'v) registration_families" where
  "families_relocated g (Single_Family F) = Single_Family (family_relocated g F)"
| "families_relocated g (Paired_Families F G) = Paired_Families (family_relocated g F) (family_relocated g G)"
| "families_relocated g (Determined_Value p) = Determined_Value p"

definition registration_relocated ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow> ('a,'s,'e,'v) collection_registration" where
  "registration_relocated g R = \<lparr>registration_site = g (registration_site R),
    registration_schema = finite_rename_schema id id g (registration_schema R),
    registration_variable = registration_variable R,
    registration_families = families_relocated g (registration_families R)\<rparr>"

lemma registration_relocated_fields [simp]:
  "registration_site (registration_relocated g R) = g (registration_site R)"
  "registration_schema (registration_relocated g R) = finite_rename_schema id id g (registration_schema R)"
  "registration_variable (registration_relocated g R) = registration_variable R"
  "registration_families (registration_relocated g R) = families_relocated g (registration_families R)"
  by (simp_all add: registration_relocated_def)

abbreviation produced_site_back :: "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow> 'e \<Rightarrow> 'd" where
  "produced_site_back g PD \<equiv> inv_into (declared_sites (resolution_declarations.truncate PD)) g"

definition produced_relocated ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'e,'v) produced_declarations" where
  "produced_relocated g PD = produced (narrowed (declarations_relocated g (resolution_declarations.truncate PD))
      (\<lambda>e S s. declared_narrowing PD (produced_site_back g PD e)
        (finite_rename_schema id id (produced_site_back g PD) S) s))
    (\<lambda>e S s. map_option (registration_relocated g) (declared_production PD (produced_site_back g PD e)
      (finite_rename_schema id id (produced_site_back g PD) S) s))"

lemma produced_relocated_truncate:
  "narrowed_declarations.truncate (produced_relocated g PD) =
    narrowed (declarations_relocated g (resolution_declarations.truncate PD)) (declared_narrowing (produced_relocated g PD))"
  by (simp add: produced_relocated_def)

lemma produced_relocated_keys:
  assumes injective: "inj_on g (declared_sites (resolution_declarations.truncate PD))"
    and socket: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
  shows "declared_narrowing (produced_relocated g PD) (g e) (finite_rename_schema id id g S) s =
      declared_narrowing PD e S s"
    and "declared_production (produced_relocated g PD) (g e) (finite_rename_schema id id g S) s =
      map_option (registration_relocated g) (declared_production PD e S s)"
proof -
  have m: "(e,S,s,keep,Vp,Vh) \<in> fset (declared_sockets (resolution_declarations.truncate PD))"
    using socket by simp
  have sites: "insert e (schema_dependencies (decode_finite_schema S)) \<subseteq>
      declared_sites (resolution_declarations.truncate PD)"
    unfolding declared_sites_def
    by (rule subset_trans[OF _ Un_upper2], rule subset_trans[OF _ UN_upper[OF m]]) simp
  have back_e: "produced_site_back g PD (g e) = e"
    by (rule inv_into_f_f[OF injective]) (use sites in blast)
  have back_S: "finite_rename_schema id id (produced_site_back g PD) (finite_rename_schema id id g S) = S"
    by (rule finite_rename_schema_left_inverse, rule inv_into_f_f[OF injective]) (use sites in blast)
  show "declared_narrowing (produced_relocated g PD) (g e) (finite_rename_schema id id g S) s =
      declared_narrowing PD e S s"
    by (simp add: produced_relocated_def back_e back_S)
  show "declared_production (produced_relocated g PD) (g e) (finite_rename_schema id id g S) s =
      map_option (registration_relocated g) (declared_production PD e S s)"
    by (simp add: produced_relocated_def back_e back_S)
qed

subsection \<open>The keyed join over a produced base, relocated and varied\<close>

text \<open>
  The override (@{const produced_override}) is carried to an installed program piecewise. Relocation commutes with
  it at every socket, the placement injective on both records' sites: the two records have the same producers,
  consumers and sockets and the same class and production at every socket (@{text produced_relocated_override}),
  which is all a variation reads (@{text produced_declarations_varied_cong}); nothing is claimed of their values away
  from the sockets. Variation commutes with it outright where the sources at the overriding record's sites are unique:
  a varied socket's sources lie among the overriding record's sockets exactly when the overriding record's variation
  declares it (@{text produced_declarations_varied_override}). The two give @{text produced_carried_override}.
\<close>

lemma produced_relocated_sockets:
  "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PD) \<longleftrightarrow>
    (\<exists>e0 S0. (e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<and> e = g e0 \<and> S = finite_rename_schema id id g S0)"
proof
  assume "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PD)"
  then show "\<exists>e0 S0. (e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<and> e = g e0 \<and> S = finite_rename_schema id id g S0"
    by (auto simp: produced_relocated_def declarations_relocated_def)
next
  assume "\<exists>e0 S0. (e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<and> e = g e0 \<and> S = finite_rename_schema id id g S0"
  then obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "e = g e0"
      "S = finite_rename_schema id id g S0" by blast
  have "(g e0,finite_rename_schema id id g S0,s,keep,Vp,Vh) |\<in>|
      fimage (\<lambda>(e,S,s,keep,Vp,Vh). (g e,finite_rename_schema id id g S,s,keep,Vp,Vh)) (declared_sockets PD)"
    by (rule rev_fimage_eqI[OF m(1)]) simp
  then show "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PD)"
    unfolding m(2,3) by (simp add: produced_relocated_def declarations_relocated_def)
qed

lemma produced_relocated_keyed:
  assumes injective: "inj_on g U" and sites: "declared_sites (resolution_declarations.truncate PK) \<subseteq> U"
    and e: "e \<in> U" and deps: "schema_dependencies (decode_finite_schema S) \<subseteq> U"
  shows "socket_keyed (resolution_declarations.truncate (produced_relocated g PK)) (g e)
      (finite_rename_schema id id g S) s \<longleftrightarrow> socket_keyed (resolution_declarations.truncate PK) e S s"
proof
  assume "socket_keyed (resolution_declarations.truncate (produced_relocated g PK)) (g e)
      (finite_rename_schema id id g S) s"
  then obtain keep Vp Vh where "(g e,finite_rename_schema id id g S,s,keep,Vp,Vh) |\<in>|
      declared_sockets (produced_relocated g PK)" unfolding socket_keyed_iff truncate_fields by blast
  then obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PK" "g e = g e0"
      "finite_rename_schema id id g S = finite_rename_schema id id g S0"
    unfolding produced_relocated_sockets by blast
  have m': "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate PK)" using m(1) by simp
  have e0: "e0 \<in> U" and deps0: "schema_dependencies (decode_finite_schema S0) \<subseteq> U"
    using declared_sites_members(4,5)[OF m'] sites by blast+
  have ee: "e0 = e" by (rule inj_onD[OF injective m(2)[symmetric] e0 e])
  have "S0 = finite_rename_schema id id (inv_into U g) (finite_rename_schema id id g S0)"
    by (rule finite_rename_schema_left_inverse[symmetric]) (use deps0 injective in \<open>auto intro: inv_into_f_f\<close>)
  also have "\<dots> = finite_rename_schema id id (inv_into U g) (finite_rename_schema id id g S)" by (simp only: m(3))
  also have "\<dots> = S"
    by (rule finite_rename_schema_left_inverse) (use deps injective in \<open>auto intro: inv_into_f_f\<close>)
  finally have SS: "S0 = S" .
  show "socket_keyed (resolution_declarations.truncate PK) e S s"
    unfolding socket_keyed_iff truncate_fields using m(1) ee SS by blast
next
  assume "socket_keyed (resolution_declarations.truncate PK) e S s"
  then obtain keep Vp Vh where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK"
    unfolding socket_keyed_iff truncate_fields by blast
  then have "(g e,finite_rename_schema id id g S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PK)"
    unfolding produced_relocated_sockets by blast
  then show "socket_keyed (resolution_declarations.truncate (produced_relocated g PK)) (g e)
      (finite_rename_schema id id g S) s" unfolding socket_keyed_iff truncate_fields by blast
qed

lemma declared_sites_covered:
  assumes p: "fset (declared_producers D) \<subseteq> fset (declared_producers D1) \<union> fset (declared_producers D2)"
    and c: "fset (declared_consumers D) \<subseteq> fset (declared_consumers D1) \<union> fset (declared_consumers D2)"
    and s: "fset (declared_sockets D) \<subseteq> fset (declared_sockets D1) \<union> fset (declared_sockets D2)"
  shows "declared_sites D \<subseteq> declared_sites D1 \<union> declared_sites D2"
proof
  fix x assume "x \<in> declared_sites D"
  then have "x \<in> fst ` fset (declared_producers D) \<or>
      (\<exists>a\<in>fset (declared_consumers D). x \<in> (case a of (d,e,V,i) \<Rightarrow> {d,e})) \<or>
      (\<exists>a\<in>fset (declared_sockets D).
        x \<in> (case a of (e,S,s,keep,Vp,Vh) \<Rightarrow> insert e (schema_dependencies (decode_finite_schema S))))"
    unfolding declared_sites_def by (simp only: Un_iff UN_iff disj_assoc)
  then show "x \<in> declared_sites D1 \<union> declared_sites D2"
    unfolding declared_sites_def Un_iff UN_iff using p c s by blast
qed

lemma produced_override_sites:
  "declared_sites (resolution_declarations.truncate (produced_override PD PK)) \<subseteq>
    declared_sites (resolution_declarations.truncate PD) \<union> declared_sites (resolution_declarations.truncate PK)"
proof -
  have "fset (declared_producers (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
      fset (declared_producers (resolution_declarations.truncate PD)) \<union>
      fset (declared_producers (resolution_declarations.truncate PK))"
    "fset (declared_consumers (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
      fset (declared_consumers (resolution_declarations.truncate PD)) \<union>
      fset (declared_consumers (resolution_declarations.truncate PK))"
    "fset (declared_sockets (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
      fset (declared_sockets (resolution_declarations.truncate PD)) \<union>
      fset (declared_sockets (resolution_declarations.truncate PK))"
  proof -
    show "fset (declared_producers (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
        fset (declared_producers (resolution_declarations.truncate PD)) \<union>
        fset (declared_producers (resolution_declarations.truncate PK))"
      by (rule subsetI) simp
    show "fset (declared_consumers (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
        fset (declared_consumers (resolution_declarations.truncate PD)) \<union>
        fset (declared_consumers (resolution_declarations.truncate PK))"
      by (rule subsetI) simp
    show "fset (declared_sockets (resolution_declarations.truncate (produced_override PD PK))) \<subseteq>
        fset (declared_sockets (resolution_declarations.truncate PD)) \<union>
        fset (declared_sockets (resolution_declarations.truncate PK))"
    proof
      fix z assume a: "z \<in> fset (declared_sockets (resolution_declarations.truncate (produced_override PD PK)))"
      obtain e S s keep Vp Vh where z: "z = (e,S,s,keep,Vp,Vh)" by (rule prod_cases6)
      show "z \<in> fset (declared_sockets (resolution_declarations.truncate PD)) \<union>
          fset (declared_sockets (resolution_declarations.truncate PK))"
        using a unfolding z truncate_fields produced_override_sockets by blast
    qed
  qed
  then show ?thesis by (rule declared_sites_covered)
qed

lemma produced_override_within:
  assumes base: "narrowings_within A PD" and over: "narrowings_within A PK"
  shows "narrowings_within A (produced_override PD PK)"
  unfolding narrowings_within_def
proof (intro allI impI)
  fix e S s keep Vp Vh
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_override PD PK)" and out: "e \<notin> A"
  show "declared_narrowing (produced_override PD PK) e S s = (\<lambda>_. True)"
  proof (cases "socket_keyed (resolution_declarations.truncate PK) e S s")
    case True
    then obtain keep' Vp' Vh' where "(e,S,s,keep',Vp',Vh') |\<in>| declared_sockets PK"
      unfolding socket_keyed_iff truncate_fields by blast
    then have "declared_narrowing PK e S s = (\<lambda>_. True)" using over out unfolding narrowings_within_def by blast
    then show ?thesis using True by simp
  next
    case False
    have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
      using m False unfolding produced_override_sockets socket_keyed_iff truncate_fields by blast
    then have "declared_narrowing PD e S s = (\<lambda>_. True)" using base out unfolding narrowings_within_def by blast
    then show ?thesis using False by simp
  qed
qed

lemma produced_relocated_override:
  assumes injective: "inj_on g (declared_sites (resolution_declarations.truncate PD) \<union>
      declared_sites (resolution_declarations.truncate PK))"
  shows "declared_producers (produced_relocated g (produced_override PD PK)) =
      declared_producers (produced_override (produced_relocated g PD) (produced_relocated g PK))"
    and "declared_consumers (produced_relocated g (produced_override PD PK)) =
      declared_consumers (produced_override (produced_relocated g PD) (produced_relocated g PK))"
    and "declared_sockets (produced_relocated g (produced_override PD PK)) =
      declared_sockets (produced_override (produced_relocated g PD) (produced_relocated g PK))"
    and "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g (produced_override PD PK)) \<Longrightarrow>
      declared_narrowing (produced_relocated g (produced_override PD PK)) e S s =
        declared_narrowing (produced_override (produced_relocated g PD) (produced_relocated g PK)) e S s \<and>
      declared_production (produced_relocated g (produced_override PD PK)) e S s =
        declared_production (produced_override (produced_relocated g PD) (produced_relocated g PK)) e S s"
proof -
  let ?U = "declared_sites (resolution_declarations.truncate PD) \<union> declared_sites (resolution_declarations.truncate PK)"
  let ?O = "produced_override PD PK"
  let ?R = "produced_override (produced_relocated g PD) (produced_relocated g PK)"
  let ?k = "socket_keyed (resolution_declarations.truncate (produced_relocated g PK))"
  let ?kK = "socket_keyed (resolution_declarations.truncate PK)"
  have iO: "inj_on g (declared_sites (resolution_declarations.truncate ?O))"
    by (rule inj_on_subset[OF injective produced_override_sites])
  have iD: "inj_on g (declared_sites (resolution_declarations.truncate PD))" by (rule inj_on_subset[OF injective]) simp
  have iK: "inj_on g (declared_sites (resolution_declarations.truncate PK))" by (rule inj_on_subset[OF injective]) simp
  have keyed: "?k (g e0) (finite_rename_schema id id g S0) s0 \<longleftrightarrow> ?kK e0 S0 s0"
    if "(e0,S0,s0,keep,Vp,Vh) |\<in>| declared_sockets PD \<or> (e0,S0,s0,keep,Vp,Vh) |\<in>| declared_sockets PK"
    for e0 S0 s0 keep Vp Vh
  proof -
    have "e0 \<in> ?U \<and> schema_dependencies (decode_finite_schema S0) \<subseteq> ?U"
      using that declared_sites_members(4,5)[of e0 S0 s0 keep Vp Vh "resolution_declarations.truncate PD"]
        declared_sites_members(4,5)[of e0 S0 s0 keep Vp Vh "resolution_declarations.truncate PK"] by auto
    then show ?thesis by (intro produced_relocated_keyed[OF injective]) auto
  qed
  show "declared_producers (produced_relocated g ?O) = declared_producers ?R"
    by (simp add: produced_relocated_def declarations_relocated_def fimage_funion)
  show "declared_consumers (produced_relocated g ?O) = declared_consumers ?R"
    by (simp add: produced_relocated_def declarations_relocated_def fimage_funion)
  have sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g ?O) \<longleftrightarrow>
      (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?R" for e S s keep Vp Vh
  proof
    assume "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g ?O)"
    then obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" "e = g e0"
        "S = finite_rename_schema id id g S0" unfolding produced_relocated_sockets by blast
    from m(1) consider (d) "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "\<not> ?kK e0 S0 s"
      | (k) "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PK" unfolding produced_override_sockets by blast
    then show "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?R"
    proof cases
      case d
      have "\<not> ?k e S s" unfolding m(2,3) using keyed[OF disjI1[OF d(1)]] d(2) by simp
      moreover have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PD)"
        unfolding produced_relocated_sockets m(2,3) using d(1) by blast
      ultimately show ?thesis unfolding produced_override_sockets by blast
    next
      case k
      have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PK)"
        unfolding produced_relocated_sockets m(2,3) using k by blast
      then show ?thesis unfolding produced_override_sockets by blast
    qed
  next
    assume "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?R"
    then consider (d) "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PD)" "\<not> ?k e S s"
      | (k) "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g PK)"
      unfolding produced_override_sockets by blast
    then show "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g ?O)"
    proof cases
      case d
      obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "e = g e0"
          "S = finite_rename_schema id id g S0" using d(1) unfolding produced_relocated_sockets by blast
      have "\<not> ?kK e0 S0 s" using d(2) keyed[OF disjI1[OF m(1)]] unfolding m(2,3) by simp
      then have "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" using m(1) unfolding produced_override_sockets by blast
      then show ?thesis unfolding produced_relocated_sockets using m(2,3) by blast
    next
      case k
      obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PK" "e = g e0"
          "S = finite_rename_schema id id g S0" using k unfolding produced_relocated_sockets by blast
      then have "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" unfolding produced_override_sockets by blast
      then show ?thesis unfolding produced_relocated_sockets using m(2,3) by blast
    qed
  qed
  show "declared_sockets (produced_relocated g ?O) = declared_sockets ?R"
  proof (rule fset_eqI)
    fix z
    show "z |\<in>| declared_sockets (produced_relocated g ?O) \<longleftrightarrow> z |\<in>| declared_sockets ?R"
    proof -
      obtain e S s keep Vp Vh where "z = (e,S,s,keep,Vp,Vh)" by (rule prod_cases6)
      then show ?thesis by (simp only: sock)
    qed
  qed
  assume a: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated g ?O)"
  obtain e0 S0 where m: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" "e = g e0"
      "S = finite_rename_schema id id g S0" using a unfolding produced_relocated_sockets by blast
  note o = produced_relocated_keys[OF iO m(1)]
  from m(1) consider (d) "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "\<not> ?kK e0 S0 s"
    | (k) "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets PK" unfolding produced_override_sockets by blast
  then show "declared_narrowing (produced_relocated g ?O) e S s = declared_narrowing ?R e S s \<and>
      declared_production (produced_relocated g ?O) e S s = declared_production ?R e S s"
  proof cases
    case d
    note r = produced_relocated_keys[OF iD d(1)]
    have nk: "\<not> ?k (g e0) (finite_rename_schema id id g S0) s" using keyed[OF disjI1[OF d(1)]] d(2) by simp
    show ?thesis unfolding m(2,3) o r produced_override_fields using d(2) nk by simp
  next
    case k
    note r = produced_relocated_keys[OF iK k]
    have kK: "?kK e0 S0 s" unfolding socket_keyed_iff truncate_fields using k by blast
    have kk: "?k (g e0) (finite_rename_schema id id g S0) s" using keyed[OF disjI2[OF k]] kK by simp
    show ?thesis unfolding m(2,3) o r produced_override_fields using kK kk by simp
  qed
qed

lemma narrowing_varied_sources:
  assumes sources: "varied_socket_sources P N (declared_sockets ND') e T t =
      varied_socket_sources P N (declared_sockets ND) e T t"
    and at: "\<And>S s. (S,s) |\<in>| varied_socket_sources P N (declared_sockets ND) e T t \<Longrightarrow>
      declared_narrowing ND' e S s = declared_narrowing ND e S s"
  shows "narrowing_varied P N ND' e T t = narrowing_varied P N ND e T t"
proof (rule ext)
  fix y
  show "narrowing_varied P N ND' e T t y = narrowing_varied P N ND e T t y"
  proof
    assume a: "narrowing_varied P N ND' e T t y"
    show "narrowing_varied P N ND e T t y" unfolding narrowing_varied_def
    proof (rule fBallI)
      fix z assume z: "z |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
      obtain S s where zs: "z = (S,s)" by (cases z)
      have "declared_narrowing ND' e S s y"
        using fbspec[OF a[unfolded narrowing_varied_def sources] z] zs by simp
      then show "case z of (S,s) \<Rightarrow> declared_narrowing ND e S s y" using at z zs by simp
    qed
  next
    assume a: "narrowing_varied P N ND e T t y"
    show "narrowing_varied P N ND' e T t y" unfolding narrowing_varied_def sources
    proof (rule fBallI)
      fix z assume z: "z |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
      obtain S s where zs: "z = (S,s)" by (cases z)
      have "declared_narrowing ND e S s y" using fbspec[OF a[unfolded narrowing_varied_def] z] zs by simp
      then show "case z of (S,s) \<Rightarrow> declared_narrowing ND' e S s y" using at z zs by simp
    qed
  qed
qed

lemma production_varied_sources:
  assumes sources: "varied_socket_sources P N (declared_sockets PD') e T t =
      varied_socket_sources P N (declared_sockets PD) e T t"
    and at: "\<And>S s. (S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t \<Longrightarrow>
      declared_production PD' e S s = declared_production PD e S s"
  shows "production_varied P N PD' e T t = production_varied P N PD e T t"
proof -
  have img: "fimage (\<lambda>(S,s). production_carried P N (declared_production PD' e S s))
      (varied_socket_sources P N (declared_sockets PD) e T t) =
    fimage (\<lambda>(S,s). production_carried P N (declared_production PD e S s))
      (varied_socket_sources P N (declared_sockets PD) e T t)"
    by (rule fset.map_cong[OF refl]) (use at in \<open>auto split: prod.splits\<close>)
  show ?thesis unfolding production_varied_def sources img ..
qed

lemma produced_declarations_varied_cong:
  assumes producers: "declared_producers D' = declared_producers D"
    and consumers: "declared_consumers D' = declared_consumers D"
    and sockets: "declared_sockets D' = declared_sockets D"
    and at: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D' \<Longrightarrow>
      declared_narrowing D' e S s = declared_narrowing D e S s \<and> declared_production D' e S s = declared_production D e S s"
  shows "produced_declarations_varied P N D' = produced_declarations_varied P N D"
proof -
  have src: "declared_narrowing D' e S s = declared_narrowing D e S s \<and>
      declared_production D' e S s = declared_production D e S s"
    if a: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets D) e T t" for e T t S s
  proof -
    obtain keep Vp Vh c c' f h where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
      using a unfolding varied_socket_sources_member by blast
    then have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D'" by (simp only: sockets)
    then show ?thesis by (rule at)
  qed
  have n: "narrowing_varied P N D' e T t = narrowing_varied P N D e T t" for e T t
    by (rule narrowing_varied_sources[OF _ conjunct1[OF src]]) (simp only: sockets)
  have p: "production_varied P N D' e T t = production_varied P N D e T t" for e T t
    by (rule production_varied_sources[OF _ conjunct2[OF src]]) (simp only: sockets)
  have n': "narrowing_varied P N D' = narrowing_varied P N D" by (intro ext) (simp only: n)
  have p': "production_varied P N D' = production_varied P N D" by (intro ext) (simp only: p)
  have tr: "resolution_declarations.truncate D' = resolution_declarations.truncate D"
    using producers consumers sockets by (simp add: resolution_declarations.truncate_def)
  show ?thesis by (simp only: produced_declarations_varied_def narrowed_declarations_varied_def tr n' p')
qed

lemma produced_declarations_eqI:
  fixes D D' :: "('a,'s,'d,'v) produced_declarations"
  assumes "declared_producers D = declared_producers D'" "declared_consumers D = declared_consumers D'"
    "declared_sockets D = declared_sockets D'" "declared_narrowing D = declared_narrowing D'"
    "declared_production D = declared_production D'"
  shows "D = D'"
  using assms by (cases D, cases D') (auto intro: trans[OF unit_eq unit_eq[symmetric]])

lemma varied_source_key:
  assumes "(S,s) |\<in>| varied_socket_sources P N Z e T t" and "(e,S,s,keep,Vp,Vh) |\<in>| Z'"
  shows "(S,s) |\<in>| varied_socket_sources P N Z' e T t"
  using assms unfolding varied_socket_sources_member by blast

lemma varied_sources_unique:
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique_at A P N" and e: "e \<in> A"
    and a: "(S,s) |\<in>| varied_socket_sources P N Z e T t" and b: "(S',s') |\<in>| varied_socket_sources P N Z' e T t"
  shows "S' = S \<and> s' = s"
proof -
  obtain keep Vp Vh c c' f h where ma: "(e,S,s,keep,Vp,Vh) |\<in>| Z"
      "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
    using a unfolding varied_socket_sources_member by blast
  obtain keep' Vp' Vh' c1 c1' f' h' where mb: "(e,S',s',keep',Vp',Vh') |\<in>| Z'"
      "((e,c1),S') |\<in>| finite_system_clauses P" "s' \<in> schema_sockets (decode_finite_schema S')"
      "((e,c1'),T) |\<in>| finite_system_clauses N" "finite_schema_match S' T = Some (f',h')" "t = h' s'"
    using b unfolding varied_socket_sources_member by blast
  have SS: "S' = S" using unique e ma(2,4,5) mb(2,5) unfolding finite_varied_sources_unique_at_def by blast
  interpret matched: finite_schema_matched S T f h
    by (rule finite_schema_matched.intro[OF finite_system_clause_formed[OF Pf ma(2)]
      finite_system_clause_formed[OF Nf ma(4)] ma(5)])
  have hh: "h' = h" using mb(5) ma(5) SS by simp
  have "s' = s" by (rule inj_onD[OF matched.sockets]) (use ma mb SS hh in auto)
  then show ?thesis using SS by simp
qed

lemma varied_keyed_sources:
  "socket_keyed (resolution_declarations.truncate (produced_declarations_varied P N PD)) e T t \<longleftrightarrow>
    (\<exists>S s. (S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t)"
  unfolding socket_keyed_iff truncate_fields produced_declarations_varied_fields declarations_varied_sockets_member
    varied_socket_sources_member by blast

lemma produced_varied_sockets_member:
  "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD) \<longleftrightarrow>
    (\<exists>S s. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<and>
      (S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t)"
  unfolding produced_declarations_varied_fields declarations_varied_sockets_member varied_socket_sources_member
    truncate_fields by blast

lemma varied_override_sources:
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique_at A P N"
    and sites: "\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK \<longrightarrow> e \<in> A"
  shows "varied_socket_sources P N (declared_sockets (produced_override PD PK)) e T t =
      (if socket_keyed (resolution_declarations.truncate (produced_declarations_varied P N PK)) e T t
        then varied_socket_sources P N (declared_sockets PK) e T t
        else varied_socket_sources P N (declared_sockets PD) e T t)"
    and "(S,s) |\<in>| varied_socket_sources P N (declared_sockets (produced_override PD PK)) e T t \<Longrightarrow>
      socket_keyed (resolution_declarations.truncate PK) e S s \<longleftrightarrow>
        socket_keyed (resolution_declarations.truncate (produced_declarations_varied P N PK)) e T t"
proof -
  let ?V = "varied_socket_sources P N"
  let ?O = "declared_sockets (produced_override PD PK)"
  let ?K = "socket_keyed (resolution_declarations.truncate (produced_declarations_varied P N PK)) e T t"
  have keyed_at: "?K" if a: "(S,s) |\<in>| ?V Z e T t" and k: "socket_keyed (resolution_declarations.truncate PK) e S s"
    for S s Z
  proof -
    obtain keep Vp Vh where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK"
      using k unfolding socket_keyed_iff truncate_fields by blast
    then have "(S,s) |\<in>| ?V (declared_sockets PK) e T t" by (rule varied_source_key[OF a])
    then show ?K unfolding varied_keyed_sources by blast
  qed
  have from_K: "(S,s) |\<in>| ?V (declared_sockets PK) e T t \<and> socket_keyed (resolution_declarations.truncate PK) e S s"
    if K: ?K and a: "(S,s) |\<in>| ?V Z e T t" for S s Z
  proof -
    obtain S0 s0 where b: "(S0,s0) |\<in>| ?V (declared_sockets PK) e T t" using K unfolding varied_keyed_sources by blast
    obtain keep Vp Vh c c' f h where k: "(e,S0,s0,keep,Vp,Vh) |\<in>| declared_sockets PK"
      using b unfolding varied_socket_sources_member by blast
    have "S = S0 \<and> s = s0" by (rule varied_sources_unique[OF Pf Nf unique sites[rule_format, OF k] b a])
    then show ?thesis using b k unfolding socket_keyed_iff truncate_fields by blast
  qed
  show "(S,s) |\<in>| ?V ?O e T t \<Longrightarrow> socket_keyed (resolution_declarations.truncate PK) e S s \<longleftrightarrow> ?K"
    using keyed_at from_K by blast
  show "?V ?O e T t = (if ?K then ?V (declared_sockets PK) e T t else ?V (declared_sockets PD) e T t)"
  proof (cases ?K)
    case True
    have "?V ?O e T t = ?V (declared_sockets PK) e T t"
    proof (rule fset_eqI)
      fix z
      show "z |\<in>| ?V ?O e T t \<longleftrightarrow> z |\<in>| ?V (declared_sockets PK) e T t"
      proof (cases z)
        case (Pair S s)
        show ?thesis unfolding Pair
      proof
        assume "(S,s) |\<in>| ?V ?O e T t"
        then show "(S,s) |\<in>| ?V (declared_sockets PK) e T t" using from_K[OF True] by blast
      next
        assume a: "(S,s) |\<in>| ?V (declared_sockets PK) e T t"
        obtain keep Vp Vh c c' f h where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK"
          using a unfolding varied_socket_sources_member by blast
        then have "(e,S,s,keep,Vp,Vh) |\<in>| ?O" unfolding produced_override_sockets by blast
        then show "(S,s) |\<in>| ?V ?O e T t" by (rule varied_source_key[OF a])
      qed
      qed
    qed
    then show ?thesis using True by simp
  next
    case False
    have "?V ?O e T t = ?V (declared_sockets PD) e T t"
    proof (rule fset_eqI)
      fix z
      show "z |\<in>| ?V ?O e T t \<longleftrightarrow> z |\<in>| ?V (declared_sockets PD) e T t"
      proof (cases z)
        case (Pair S s)
        show ?thesis unfolding Pair
      proof
        assume a: "(S,s) |\<in>| ?V ?O e T t"
        obtain keep Vp Vh c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| ?O"
          using a unfolding varied_socket_sources_member by blast
        have "\<not> socket_keyed (resolution_declarations.truncate PK) e S s" using keyed_at[OF a] False by blast
        then have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
          using m unfolding produced_override_sockets socket_keyed_iff truncate_fields by blast
        then show "(S,s) |\<in>| ?V (declared_sockets PD) e T t" by (rule varied_source_key[OF a])
      next
        assume a: "(S,s) |\<in>| ?V (declared_sockets PD) e T t"
        obtain keep Vp Vh c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
          using a unfolding varied_socket_sources_member by blast
        have "\<not> socket_keyed (resolution_declarations.truncate PK) e S s" using keyed_at[OF a] False by blast
        then have "(e,S,s,keep,Vp,Vh) |\<in>| ?O" using m unfolding produced_override_sockets by blast
        then show "(S,s) |\<in>| ?V ?O e T t" by (rule varied_source_key[OF a])
      qed
      qed
    qed
    then show ?thesis using False by simp
  qed
qed

theorem produced_declarations_varied_override:
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique_at A P N"
    and sites: "\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK \<longrightarrow> e \<in> A"
  shows "produced_declarations_varied P N (produced_override PD PK) =
    produced_override (produced_declarations_varied P N PD) (produced_declarations_varied P N PK)"
proof (rule produced_declarations_eqI)
  let ?V = "varied_socket_sources P N"
  let ?O = "produced_override PD PK"
  let ?L = "produced_declarations_varied P N (produced_override PD PK)"
  let ?R = "produced_override (produced_declarations_varied P N PD) (produced_declarations_varied P N PK)"
  let ?K = "\<lambda>e T t. socket_keyed (resolution_declarations.truncate (produced_declarations_varied P N PK)) e T t"
  note src = varied_override_sources[OF Pf Nf unique sites]
  show "declared_producers ?L = declared_producers ?R" by (simp add: produced_declarations_varied_fields)
  show "declared_consumers ?L = declared_consumers ?R" by (simp add: produced_declarations_varied_fields)
  have sock: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?L \<longleftrightarrow> (e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?R"
    for e T t keep Vp Vh
  proof
    assume "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?L"
    then obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?O"
        and a: "(S,s) |\<in>| ?V (declared_sockets ?O) e T t"
      unfolding produced_varied_sockets_member by blast
    have k: "socket_keyed (resolution_declarations.truncate PK) e S s \<longleftrightarrow> ?K e T t" by (rule src(2)[OF a])
    show "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?R"
    proof (cases "?K e T t")
      case True
      have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK" using m k True unfolding produced_override_sockets by blast
      moreover have "(S,s) |\<in>| ?V (declared_sockets PK) e T t" using a src(1) True by simp
      ultimately have "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PK)"
        unfolding produced_varied_sockets_member by blast
      then show ?thesis unfolding produced_override_sockets by blast
    next
      case False
      have nk: "\<not> socket_keyed (resolution_declarations.truncate PK) e S s" using k False by simp
      have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
        using m nk unfolding produced_override_sockets socket_keyed_iff truncate_fields by blast
      moreover have "(S,s) |\<in>| ?V (declared_sockets PD) e T t" using a src(1) False by simp
      ultimately have "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD)"
        unfolding produced_varied_sockets_member by blast
      then show ?thesis using False unfolding produced_override_sockets by blast
    qed
  next
    assume "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?R"
    then consider (d) "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD)" "\<not> ?K e T t"
      | (k) "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PK)"
      unfolding produced_override_sockets by blast
    then show "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?L"
    proof cases
      case d
      obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD"
          and a: "(S,s) |\<in>| ?V (declared_sockets PD) e T t"
        using d(1) unfolding produced_varied_sockets_member by blast
      have a': "(S,s) |\<in>| ?V (declared_sockets ?O) e T t" using a src(1) d(2) by simp
      have "\<not> socket_keyed (resolution_declarations.truncate PK) e S s" using src(2)[OF a'] d(2) by blast
      then have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" using m unfolding produced_override_sockets by blast
      then show ?thesis using a' unfolding produced_varied_sockets_member by blast
    next
      case k
      obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK"
          and a: "(S,s) |\<in>| ?V (declared_sockets PK) e T t"
        using k unfolding produced_varied_sockets_member by blast
      have K: "?K e T t" unfolding varied_keyed_sources using a by blast
      have a': "(S,s) |\<in>| ?V (declared_sockets ?O) e T t" using a src(1) K by simp
      have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" using m unfolding produced_override_sockets by blast
      then show ?thesis using a' unfolding produced_varied_sockets_member by blast
    qed
  qed
  show "declared_sockets ?L = declared_sockets ?R"
  proof (rule fset_eqI)
    fix z
    show "z |\<in>| declared_sockets ?L \<longleftrightarrow> z |\<in>| declared_sockets ?R"
    proof -
      obtain e T t keep Vp Vh where "z = (e,T,t,keep,Vp,Vh)" by (rule prod_cases6)
      then show ?thesis by (simp only: sock)
    qed
  qed
  have at: "declared_narrowing ?L e T t = declared_narrowing ?R e T t \<and>
      declared_production ?L e T t = declared_production ?R e T t" for e T t
  proof (cases "?K e T t")
    case True
    have same: "?V (declared_sockets ?O) e T t = ?V (declared_sockets PK) e T t" using src(1) True by simp
    have keyed: "socket_keyed (resolution_declarations.truncate PK) e S s"
      if "(S,s) |\<in>| ?V (declared_sockets PK) e T t" for S s
    proof -
      have "(S,s) |\<in>| ?V (declared_sockets ?O) e T t" using that same by simp
      then show ?thesis using src(2) True by blast
    qed
    have "narrowing_varied P N ?O e T t = narrowing_varied P N PK e T t"
      by (rule narrowing_varied_sources[OF same]) (simp add: keyed)
    moreover have "production_varied P N ?O e T t = production_varied P N PK e T t"
      by (rule production_varied_sources[OF same]) (simp add: keyed)
    ultimately show ?thesis using True by (simp add: produced_declarations_varied_fields)
  next
    case False
    have same: "?V (declared_sockets ?O) e T t = ?V (declared_sockets PD) e T t" using src(1) False by simp
    have unkeyed: "\<not> socket_keyed (resolution_declarations.truncate PK) e S s"
      if "(S,s) |\<in>| ?V (declared_sockets PD) e T t" for S s
    proof -
      have "(S,s) |\<in>| ?V (declared_sockets ?O) e T t" using that same by simp
      then show ?thesis using src(2) False by blast
    qed
    have "narrowing_varied P N ?O e T t = narrowing_varied P N PD e T t"
      by (rule narrowing_varied_sources[OF same]) (simp add: unkeyed)
    moreover have "production_varied P N ?O e T t = production_varied P N PD e T t"
      by (rule production_varied_sources[OF same]) (simp add: unkeyed)
    ultimately show ?thesis using False by (simp add: produced_declarations_varied_fields)
  qed
  show "declared_narrowing ?L = declared_narrowing ?R" by (intro ext) (simp only: conjunct1[OF at])
  show "declared_production ?L = declared_production ?R" by (intro ext) (simp only: conjunct2[OF at])
qed

theorem produced_carried_override:
  assumes injective: "inj_on g (declared_sites (resolution_declarations.truncate PD) \<union>
      declared_sites (resolution_declarations.truncate PK))"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique_at A P N"
    and sites: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PK \<Longrightarrow> g e \<in> A"
  shows "produced_declarations_varied P N (produced_relocated g (produced_override PD PK)) =
    produced_override (produced_declarations_varied P N (produced_relocated g PD))
      (produced_declarations_varied P N (produced_relocated g PK))"
proof -
  note c = produced_relocated_override[OF injective]
  have "produced_declarations_varied P N (produced_relocated g (produced_override PD PK)) =
      produced_declarations_varied P N (produced_override (produced_relocated g PD) (produced_relocated g PK))"
    by (rule produced_declarations_varied_cong[OF c(1,2,3) c(4)])
  also have "\<dots> = produced_override (produced_declarations_varied P N (produced_relocated g PD))
      (produced_declarations_varied P N (produced_relocated g PK))"
    by (rule produced_declarations_varied_override[OF Pf Nf unique])
      (fastforce simp: produced_relocated_sockets intro: sites)
  finally show ?thesis .
qed

section \<open>The corollary: relocated, carried by the clause match, at the program the installed site reads\<close>

text \<open>
  In a finite mapped extension, the numbered program Q's committed registrations reach the finite program the installed
  site reads (@{const native_package_at} at the installation's result), which is only an alpha variant of the placed
  program @{text goal} (@{thm [source] finite_mapped_native_extension.installed_variant}). The construction is relocated
  by the placement (W4a) and varied along task 642's clause match (V1): complete there (@{thm [source]
  finite_mapped_native_extension.varied_relocated_complete}). The narrowed record is relocated with its classes given at
  the relocated sites (R5e) and varied along the match (V2b): discharged there (@{thm [source]
  narrowed_declarations_relocated_varied_discharged}); its frames are relocated and varied likewise (@{thm [source]
  narrowed_frames_relocated_varied_discharged}), the frames at the installed program the varied relocated frames. The
  installed program's own facts are the sources' classes agreeing there, the productions' discharge there (R5f2's
  premise, a premise of the corollary, which each consuming program discharges by the semantic lemma, q138, or, where
  the values are carried, by @{thm [source] productions_varied_at_values}; from it the completeness at a narrowed
  socket is derived at the installed program) and the varied record's static premise (derived by
  @{thm [source] narrowed_productions_declared_varied} under unique sources and each production carrying to one
  registration). Nothing is proved again: the corollary composes the relocation, the variation and the native form, and
  the installation's alpha variance is consumed as the verification that the placed and installed presentations agree,
  the installed one being the one evaluated.
\<close>

text \<open>
  The corollary's premises are one block, stated once as the assumptions of @{text relocated_registrations} (task 820,
  from review 805's follow-up 1): the installation's result and the installed site's reading, the numbered program's
  committed registrations with their declared and frame sites among its definitions, the relocation of the record and
  of its classes, and at the installed program the sources' classes agreeing, the productions' discharge and the
  varied record's static premise. The five forms are proved inside it; the statements in
  @{text finite_mapped_native_extension} are its instances by one interpretation each, and a consumer (the given's
  produced record, the check instances of rc's forms, the first request) instantiates it by one interpretation.
\<close>

locale relocated_registrations = finite_mapped_native_extension E P Q pu pr N g
  for E P Q pu pr N g +
  fixes Inst :: "local_address option finite_native_system"
    and F u \<kappa> m ND \<Phi> corr D' \<nu> m'
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
begin

lemma registrations_installed:
  "committed_registrations (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst D') (frames_varied goal Inst (frames_relocated placement \<Phi>))
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
proof -
  note Qr = committed_registrations.formed[OF registered] committed_registrations.complete[OF registered]
    committed_registrations.discharged[OF registered] committed_registrations.frames[OF registered]
  have alpha: "system_alpha_variant (decode_finite_system goal) (decode_finite_system Inst)"
    by (rule installed_variant[OF result read])
  have Qf: "schema_system_formed (decode_finite_system Q)" using target by (simp only: finite_system_formed_correct)
  have within: "system_definitions (decode_finite_system Q) \<union> declared_sites (resolution_declarations.truncate ND) =
      system_definitions (decode_finite_system Q)"
    "system_definitions (decode_finite_system Q) \<union> declared_sites (resolution_declarations.truncate ND) \<union> frame_sites \<Phi> =
      system_definitions (decode_finite_system Q)"
    using sites frame_sites by blast+
  have inj: "inj_on placement (system_definitions (decode_finite_system Q) \<union>
      declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate ND)))"
    using maps.injective within(1) by simp
  have injF: "inj_on placement (system_definitions (decode_finite_system Q) \<union>
      declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate ND)) \<union> frame_sites \<Phi>)"
    using maps.injective within(2) by simp
  have rel: "narrowed_declarations.truncate D' =
      narrowed (declarations_relocated placement (resolution_declarations.truncate (narrowed_declarations.truncate ND))) \<nu>"
    using relocated by simp
  have rels: "\<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing (narrowed_declarations.truncate ND) e S s"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate ND)" for e S s keep Vp Vh
    using relocates[of e S s keep Vp Vh] that by simp
  have inv: "inv_into (declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate ND))) placement =
      inv_into (declared_sites (resolution_declarations.truncate ND)) placement" by simp
  have dR: "narrowed_declarations_discharged (positive_meaning (decode_finite_system goal))
      (narrowed_declarations.truncate D') (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
    using narrowed_declarations_relocated_discharged[OF Qf inj Qr(3) rels] rel inv by simp
  have formedD: "declarations_formed (resolution_declarations.truncate D')" using narrowed_formed[OF dR] by simp
  have Pf: "finite_system_formed goal" and Nf: "finite_system_formed Inst"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  have same: "\<And>d x. (d,x) \<in> positive_meaning (decode_finite_system Inst) \<longleftrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system goal)"
    using system_alpha_positive_meaning[OF alpha] by simp
  have dN: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Inst))
      (narrowed_declarations.truncate (produced_declarations_varied goal Inst D'))
      (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
    unfolding produced_declarations_varied_truncate
    by (rule narrowed_declarations_varied_discharged[where P=goal and N=Inst and PD=D']) (rule Pf Nf agree dR same)+
  have fR: "narrowed_frames_discharged (positive_meaning (decode_finite_system goal))
      (narrowed_declarations.truncate D') (frames_relocated placement \<Phi>)"
    unfolding rel by (rule narrowed_frames_relocated_discharged[OF Qf injF rels Qr(4)])
  have fN: "narrowed_frames_discharged (positive_meaning (decode_finite_system Inst))
      (narrowed_declarations.truncate (produced_declarations_varied goal Inst D'))
      (frames_varied goal Inst (frames_relocated placement \<Phi>))"
    unfolding produced_declarations_varied_truncate
    by (rule narrowed_frames_varied_discharged[where P=goal and N=Inst and ND=D']) (rule Pf Nf agree formedD fR same)+
  show ?thesis
    by (rule committed_registrations.intro[OF finite_varied_construction_formed[OF finite_relocated_construction_formed[OF Qr(1)]]
      varied_relocated_complete[OF result read Qr(2)] dN fN productions declared])
qed

lemma registered_installed_at:
  "registered_commitment_at prio (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
      (frames_varied goal Inst (frames_relocated placement \<Phi>)))"
  by (rule committed_registrations.registered_at[OF registrations_installed])

theorem native_installed_at:
  assumes resolution: "native_committed_resolution_by
      (finite_resolution_select_at prio (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>)) Inst)
      (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
  using native_committed_registered_exact_at[OF registered_installed_at resolution] by blast+

theorem native_installed:
  assumes resolution: "native_committed_resolution (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
  using native_installed_at[OF resolution[unfolded native_committed_resolution_select]] by blast+

theorem native_installed_moded:
  assumes resolution: "native_committed_resolution_by
      (finite_moded_select (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
        (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
          (frames_varied goal Inst (frames_relocated placement \<Phi>))) Dm (modes_relocated placement M) Inst)
      (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
  using native_installed_at[OF resolution] by blast+

end

text \<open>
  The forms in @{text finite_mapped_native_extension}, each the locale's instance through its introduction, stated once
  (@{text relocated_registrations_at}; next-edits 334, review 820's follow-up 1).
\<close>

context finite_mapped_native_extension
begin

lemma relocated_registrations_at:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
  shows "relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'"
  by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
    rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
      productions declared], rule relocates)

lemma committed_registrations_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
  shows "committed_registrations (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst D') (frames_varied goal Inst (frames_relocated placement \<Phi>))
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
  by (rule relocated_registrations.registrations_installed[OF relocated_registrations_at[OF result read registered
    sites frame_sites relocated relocates agree productions declared]])

text \<open>At a priority of the installed program: the varied record's exchange holds at every one (O2).\<close>

lemma committed_registrations_relocated_at:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
  shows "registered_commitment_at prio (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
      (frames_varied goal Inst (frames_relocated placement \<Phi>)))"
  by (rule relocated_registrations.registered_installed_at[OF relocated_registrations_at[OF result read registered
    sites frame_sites relocated relocates agree productions declared]])

theorem native_committed_registered_relocated_at:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
    and resolution: "native_committed_resolution_by
      (finite_resolution_select_at prio (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>)) Inst)
      (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
proof -
  have registrations: "relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'"
    by (rule relocated_registrations_at[OF result read registered sites frame_sites relocated relocates agree
      productions declared])
  note exact = relocated_registrations.native_installed_at[OF registrations resolution]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}" by (rule exact(4))
qed

text \<open>At the produced record relocated by the placement, the relocation's two premises hold (the placement injective on
  Q's definitions, among which the record's sites stand).\<close>

lemma committed_registrations_produced_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and agree: "varied_narrowings_agree goal Inst (produced_relocated placement ND)"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst (produced_relocated placement ND))"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst (produced_relocated placement ND))"
  shows "committed_registrations (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst (produced_relocated placement ND))
    (frames_varied goal Inst (frames_relocated placement \<Phi>))
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
proof -
  have inj: "inj_on placement (declared_sites (resolution_declarations.truncate ND))"
    by (rule inj_on_subset[OF maps.injective sites])
  show ?thesis
    by (rule relocated_registrations.registrations_installed[OF relocated_registrations_at[OF result read registered
      sites frame_sites produced_relocated_truncate produced_relocated_keys(1)[OF inj] agree productions declared]])
qed

theorem native_committed_registered_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
    and resolution: "native_committed_resolution (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
proof -
  have registrations: "relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'"
    by (rule relocated_registrations_at[OF result read registered sites frame_sites relocated relocates agree
      productions declared])
  note exact = relocated_registrations.native_installed[OF registrations resolution]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}" by (rule exact(4))
qed

text \<open>
  (3), relocated: at the moded selection of the installed program, its modes the numbered program's relocated by the
  placement (@{const modes_relocated}, O1); a view reads the call, so the clause match leaves it as it is.
\<close>

theorem native_committed_moded_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and registered: "committed_registrations \<kappa> Q m ND \<Phi> corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and frame_sites: "frame_sites \<Phi> \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate (D' :: (_,_,_,'v) produced_declarations) =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
    and resolution: "native_committed_resolution_by
      (finite_moded_select (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
        (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
          (frames_varied goal Inst (frames_relocated placement \<Phi>))) Dm (modes_relocated placement M) Inst)
      (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
        (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
proof -
  have registrations: "relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'"
    by (rule relocated_registrations_at[OF result read registered sites frame_sites relocated relocates agree
      productions declared])
  note exact = relocated_registrations.native_installed_moded[OF registrations resolution]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}" by (rule exact(4))
qed

end

text \<open>
  The installed record's premises at a table whose calls are true at the installed program: its exchange at every
  priority (@{text committed_registrations.exchanges_at_true}) and, with the construction premise there, rc's premises
  at the table (review 943's follow-up 3: the locale below cites these, one fact with one proof).
\<close>

context relocated_registrations
begin

lemma installed_exchanges_true:
  assumes true: "finite_table_true Inst \<Theta>"
  shows "finite_commitment_exchanges_at_in \<Theta> prio (\<lambda>_. False)
    (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D')
      (frames_varied goal Inst (frames_relocated placement \<Phi>))) Inst"
  by (rule committed_registrations.exchanges_at_true[OF registrations_installed true])

lemma registrations_installed_true:
  assumes true: "finite_table_true Inst \<Theta>"
  shows "committed_registrations_in (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst D') (frames_varied goal Inst (frames_relocated placement \<Phi>))
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement) \<Theta>"
  by (rule committed_registrations_in_true[OF registrations_installed true])

end

section \<open>The relocated block at a table\<close>

text \<open>
  #820's block with a table at the installed program and its two premises there (the construction premise and the
  varied record's exchange at every priority, their discharges the exchange's, GT2b): rc's premises at the table at
  the installed program (@{text registrations_installed_in}), and from them the native forms there, the moded among
  them; at the empty table these are the block's own (@{text committed_registrations_in_empty}).
\<close>

locale relocated_registrations_in = relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
  for E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m' +
  fixes \<Theta> :: "(local_address,local_address,local_address option definition_site,local_address) resolution_table"
  assumes installed_true: "finite_table_true Inst \<Theta>"
begin

text \<open>
  The block's two premises at the table, each rc's at the installed program (task 942): the construction premise by
  the complete construction's lifting at the table, the exchange by the installed record's
  (@{text relocated_registrations.installed_exchanges_true}).
\<close>

lemma installed_lifts: "finite_construction_lifts_in \<Theta> (\<lambda>_. False)
      (finite_varied_construction (finite_rename_system (finite_program_coordinates E (finite_system_definitions P)
        (finite_system_definitions Q) g) Q) Inst (finite_relocated_construction (finite_program_coordinates E
        (finite_system_definitions P) (finite_system_definitions Q) g) Q \<kappa>)) Inst"
  by (rule finite_construction_complete_lifts_in[OF committed_registrations.complete[OF registrations_installed]])

lemma installed_exchanges: "finite_commitment_exchanges_at_in \<Theta> prio (\<lambda>_. False)
      (finite_varied_construction (finite_rename_system (finite_program_coordinates E (finite_system_definitions P)
        (finite_system_definitions Q) g) Q) Inst (finite_relocated_construction (finite_program_coordinates E
        (finite_system_definitions P) (finite_system_definitions Q) g) Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied (finite_rename_system (finite_program_coordinates E
        (finite_system_definitions P) (finite_system_definitions Q) g) Q) Inst D')
        (frames_varied (finite_rename_system (finite_program_coordinates E (finite_system_definitions P)
          (finite_system_definitions Q) g) Q) Inst (frames_relocated (finite_program_coordinates E
          (finite_system_definitions P) (finite_system_definitions Q) g) \<Phi>))) Inst"
  by (rule installed_exchanges_true[OF installed_true])

lemma registrations_installed_in:
  "committed_registrations_in (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst D') (frames_varied goal Inst (frames_relocated placement \<Phi>))
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement) \<Theta>"
  by (rule registrations_installed_true[OF installed_true])

lemmas native_committed_moded_installed_in = native_committed_moded_exact_in[OF registrations_installed_in]

lemmas native_committed_waiting_installed_in = native_committed_waiting_exact_in[OF registrations_installed installed_true]

end


end
