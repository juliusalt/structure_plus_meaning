theory Factor_Native_Committed_Registrations
  imports Factor_Committed_Registrations Factor_Varied_Constructions Factor_Varied_Narrowed_Transfer
begin

section \<open>(3): the native form of the committed resolution with complete registrations\<close>

text \<open>
  rc's native form. R5's native reading (@{const native_committed_resolution}) resolves every call of a finite set
  and the demand at once: the calls are kept, each resolved call carries a nonempty certificate family the finite proof
  checker accepts in the program as given (R5's @{thm [source] native_committed_resolution_sound}), and the refutations
  and the demand are the previous part's numbered forms (1) and (2) (@{thm [source]
  registered_commitment.committed_registered_resolution_exact}, @{thm [source]
  registered_commitment.committed_registered_demand_exact}) read at each call. The statement has the shape of R4's
  @{thm [source] native_call_resolution_exact}, a refutation being any result that refutes (a refusal, or every diagnosis
  a witnessed failure at a registration proved complete); unresolved asserts nothing. The program is any finite one:
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
  from result have T: "T = fimage (\<lambda>q. (q,finite_committed_resolution \<kappa> K P (fst q) (snd q) n)) R"
    and A: "A = finite_committed_demand \<kappa> K P R n"
    by (simp_all add: native_committed_resolution_def)
  show "fimage fst T = R" by (rule native_committed_resolution_sound(1)[OF result])
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    by (rule native_committed_resolution_sound(2)[OF result])
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
  proof -
    assume "(q,r) |\<in>| T" and refutes: "finite_resolution_refutes r"
    then have "r = finite_committed_resolution \<kappa> K P (fst q) (snd q) n" unfolding T by auto
    with refutes have "finite_resolution_refutes (finite_committed_resolution \<kappa> K P (fst q) (snd q) n)" by simp
    then show "decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
      using committed_registered_resolution_exact(2)[where d="fst q" and t="snd q" and n=n]
      by (simp add: decode_finite_call_term_fields)
  qed
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
    using committed_registered_demand_exact unfolding A by blast
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
  In a finite mapped extension, the numbered program Q's premises reach the finite program the installed site reads
  (@{const native_package_at} at the installation's result), which is only an alpha variant of the placed program
  @{text goal} (@{thm [source] finite_mapped_native_extension.installed_variant}). The construction is relocated by the
  placement (W4a) and varied along task 642's clause match (V1): complete there (@{thm [source]
  finite_mapped_native_extension.varied_relocated_complete}). The narrowed record is relocated with its classes given at the
  relocated sites (R5e) and varied along the match (V2b): discharged there (@{thm [source]
  narrowed_declarations_relocated_varied_discharged}); its productions, discharged at the placed program as R5f2's
  relocation transfer takes them, are discharged there (@{thm [source] productions_relocated_varied_discharged}), the
  completeness at a narrowed socket of a head-variable registration carried by #651's lemmas along the producer's
  match. The frames at the installed program and the static premise of the varied record stand as premises, as V2b's
  forms take them: no fact carries a narrowed frame along the match. Nothing is proved again: the corollary composes
  the relocation, the variation and the native form, and the installation's alpha variance is consumed as the
  verification that the placed and installed presentations agree, the installed one being the one evaluated.
\<close>

context finite_mapped_native_extension
begin

lemma committed_registrations_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q)) ND corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate D' =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system goal)) goal m D'"
    and carried: "\<And>e S s keep Vp Vh Rg Rg'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D' \<Longrightarrow>
      declared_production D' e S s = Some Rg \<Longrightarrow> Rg' |\<in>| registrations_varied goal Inst Rg \<Longrightarrow>
      production_values_carried (finite_collection_construction [Rg] m) goal
        (finite_collection_construction [Rg'] m') Inst Rg"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system Inst))
      (narrowed_declarations.truncate (produced_declarations_varied goal Inst D')) \<Phi>"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
  shows "committed_registrations (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
    Inst m' (produced_declarations_varied goal Inst D') \<Phi>
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
proof -
  have alpha: "system_alpha_variant (decode_finite_system goal) (decode_finite_system Inst)"
    by (rule installed_variant[OF result read])
  have Qf: "schema_system_formed (decode_finite_system Q)" using target by (simp only: finite_system_formed_correct)
  have inj: "inj_on placement (system_definitions (decode_finite_system Q) \<union>
      declared_sites (resolution_declarations.truncate ND))"
    using maps.injective sites by (simp add: Un_absorb2)
  have dR: "narrowed_declarations_discharged (positive_meaning (decode_finite_system goal))
      (narrowed_declarations.truncate D') (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
    using narrowed_declarations_relocated_discharged[OF Qf inj discharged relocates] relocated by simp
  have formedD: "declarations_formed (resolution_declarations.truncate D')" using narrowed_formed[OF dR] by simp
  have dN: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Inst))
      (narrowed_declarations.truncate (produced_declarations_varied goal Inst D'))
      (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) placement)"
    unfolding produced_declarations_varied_truncate
    by (rule narrowed_declarations_relocated_varied_discharged[OF Qf inj discharged relocated relocates alpha agree])
  have pN: "productions_discharged (positive_meaning (decode_finite_system Inst)) Inst m'
      (produced_declarations_varied goal Inst D')"
    by (rule productions_relocated_varied_discharged[OF alpha agree formedD productions carried])
  show ?thesis
    by (rule committed_registrations.intro[OF finite_varied_construction_formed[OF finite_relocated_construction_formed[OF \<kappa>]]
      varied_relocated_complete[OF result read complete] dN frames pN declared])
qed

theorem native_committed_registered_relocated:
  fixes Inst :: "local_address option finite_native_system"
  assumes result: "finite_extend_mapped_native E P Q g = Some (F,u)"
    and read: "native_package_at (decode_finite_environment F) u [] (decode_finite_system Inst)"
    and \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q)) ND corr"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions (decode_finite_system Q)"
    and relocated: "narrowed_declarations.truncate D' =
      narrowed (declarations_relocated placement (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (placement e) (finite_rename_schema id id placement S) s = declared_narrowing ND e S s"
    and agree: "varied_narrowings_agree goal Inst D'"
    and productions: "productions_discharged (positive_meaning (decode_finite_system goal)) goal m D'"
    and carried: "\<And>e S s keep Vp Vh Rg Rg'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D' \<Longrightarrow>
      declared_production D' e S s = Some Rg \<Longrightarrow> Rg' |\<in>| registrations_varied goal Inst Rg \<Longrightarrow>
      production_values_carried (finite_collection_construction [Rg] m) goal
        (finite_collection_construction [Rg'] m') Inst Rg"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system Inst))
      (narrowed_declarations.truncate (produced_declarations_varied goal Inst D')) \<Phi>"
    and declared: "narrowed_productions_declared (produced_declarations_varied goal Inst D')"
    and resolution: "native_committed_resolution (finite_varied_construction goal Inst (finite_relocated_construction placement Q \<kappa>))
      (finite_narrowed_commitment Inst m' (produced_declarations_varied goal Inst D') \<Phi>) Inst R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof Inst p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system Inst)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system Inst) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system Inst)}"
proof -
  note exact = native_committed_registrations_exact[OF committed_registrations_relocated[OF result read \<kappa> complete
    discharged sites relocated relocates agree productions carried frames declared] resolution]
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
