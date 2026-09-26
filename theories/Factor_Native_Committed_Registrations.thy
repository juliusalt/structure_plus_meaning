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
proof -
  interpret registered_commitment \<kappa> P K by (rule registered)
  note exact = native_committed_resolution_exact[OF formed exchanges lifts result]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}" by (rule exact(4))
qed

text \<open>The declared commitment at narrowed sockets with productions is one such commitment.\<close>

lemmas native_committed_registrations_exact =
  native_committed_registered_exact[OF committed_registrations.registered]

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
  premise, which each consuming program discharges by the semantic lemma, q138: a production's head registration, its
  produces and answers hypotheses carried by #651's lemmas along the producer's match, from which the completeness at a
  narrowed socket is derived at the installed program) and the varied record's static premise (derived by
  @{thm [source] narrowed_productions_declared_varied} under unique sources and each production carrying to one
  registration). Nothing is proved again: the corollary composes the relocation, the variation and the native form, and
  the installation's alpha variance is consumed as the verification that the placed and installed presentations agree,
  the installed one being the one evaluated.
\<close>

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
  note exact = native_committed_registrations_exact[OF committed_registrations_relocated[OF result read registered
    sites frame_sites relocated relocates agree productions declared] resolution]
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
