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

text \<open>A record declaring no narrowing and no production is one: its discharges are R5d's
  (@{thm [source] declarations_discharged_unnarrowed}, @{thm [source] frames_discharged_unnarrowed}).\<close>

lemma committed_registrations_unnarrowed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> P"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
  shows "committed_registrations \<kappa> P m (unproduced (unnarrowed D)) \<Phi> corr"
proof (rule committed_registrations.intro[OF \<kappa> complete])
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D))) corr"
    using discharged by (simp add: declarations_discharged_unnarrowed)
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D))) \<Phi>"
    using frames by (simp add: frames_discharged_unnarrowed)
  show "productions_discharged (positive_meaning (decode_finite_system P)) P m (unproduced (unnarrowed D))"
    by (rule productions_discharged_none) simp
  show "narrowed_productions_declared (unproduced (unnarrowed D))" by (rule narrowed_productions_declared_unnarrowed)
qed

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

text \<open>The forms in @{text finite_mapped_native_extension}, each the locale's instance by one interpretation.\<close>

context finite_mapped_native_extension
begin

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
proof -
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
        productions declared], rule relocates)
  show ?thesis by (rule L.registrations_installed)
qed

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
proof -
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
        productions declared], rule relocates)
  show ?thesis by (rule L.registered_installed_at)
qed

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
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
        productions declared], rule relocates)
  note exact = L.native_installed_at[OF resolution]
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
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr "produced_relocated placement ND"
      "declared_narrowing (produced_relocated placement ND)" m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites produced_relocated_truncate _
        agree productions declared], rule produced_relocated_keys(1)[OF inj])
  show ?thesis by (rule L.registrations_installed)
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
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
        productions declared], rule relocates)
  note exact = L.native_installed[OF resolution]
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
  interpret L: relocated_registrations E P Q pu pr N g Inst F u \<kappa> m ND \<Phi> corr D' \<nu> m'
    by (rule relocated_registrations.intro[OF finite_mapped_native_extension_axioms],
      rule relocated_registrations_axioms.intro[OF result read registered sites frame_sites relocated _ agree
        productions declared], rule relocates)
  note exact = L.native_installed_moded[OF resolution]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}" by (rule exact(4))
qed

end

end
