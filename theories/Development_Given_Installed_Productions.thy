theory Development_Given_Installed_Productions
  imports Development_Given_Productions
begin

text \<open>
  The given's production of 12's input carried to the installed programs (I3 of correction (13) of "Committed choice,
  for refusals", DECISIONS.md, task 495's entry, its second part). The first part's record
  (@{const given_input_declarations}, #782's record overridden at the lookup socket's key) is carried to the asked
  relation's installed guard (526 in the native course) and to the first request's installed program (561 at the
  installation) as #798 carries @{const given_declarations}: relocated with the placement and varied along the clause
  match (@{thm [source] finite_mapped_native_extension.committed_registrations_produced_relocated}).

  The carried record is the override of #798's installed record by the lookup record carried
  (@{thm [source] produced_carried_override}; the lookup socket's sources are unique at 37, which has one clause). Its
  productions and its static premise are #798's and the lookup record's, joined by the override's facts; the lookup
  record's production is I2's input registration of 12, relocated (@{thm [source] input_registration_relocated_eq})
  and varied (@{thm [source] finite_schema_matched.input_registration_varied}), reflexive at the installed 12 by the
  installation's meaning. Its narrowings agree within #798's five sites of 48's callers, the lookup socket's class
  being every answer. Nothing of the given's readers is refined, restated or added, and no search is read.
\<close>

section \<open>At the rooted readers: the lookup record's sites and frames, and the clauses of 37 and 12\<close>

text \<open>37 and 12 each have one clause at the rooted readers: artifact lookup's and artifact identity's.\<close>

lemma lookup_rooted_clause:
  "((37,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema lookup_socket_schema"
proof -
  have r37: "37 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  have agree: "systems_agree_on artifact_lookup_system given_rooted_readers_system
      (system_definitions artifact_lookup_system \<inter> system_definitions given_rooted_readers_system)"
    by (rule given_agreements(3)[OF artifact_lookup_system_formed guard_lookup_agreement])
  have d37: "37 \<in> system_definitions artifact_lookup_system"
    using artifact_lookup_system_formed artifact_lookup_clause[of 0 artifact_lookup_schema]
    unfolding schema_system_formed_def by blast
  have "((37,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> ((37,c),S) \<in> system_clauses artifact_lookup_system"
    using agree d37 r37 unfolding systems_agree_on_def by blast
  then show ?thesis by (simp add: lookup_socket_decoded)
qed

lemma identity_rooted_clause:
  "((12,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema identity_socket_schema"
proof -
  have r12: "12 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  have agree: "systems_agree_on artifact_identity_system given_rooted_readers_system
      (system_definitions artifact_identity_system \<inter> system_definitions given_rooted_readers_system)"
    by (rule given_agreements(3)[OF artifact_identity_system_formed guard_identity_agreement])
  have d12: "12 \<in> system_definitions artifact_identity_system" by simp
  have "((12,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> ((12,c),S) \<in> system_clauses artifact_identity_system"
    using agree d12 r12 unfolding systems_agree_on_def by blast
  then show ?thesis by (simp add: identity_socket_decoded)
qed

lemma lookup_given_socket:
  "(37,lookup_socket_schema,2,False,view_identity,lookup_view) |\<in>| declared_sockets given_declarations"
  unfolding given_declarations_sockets using lookup_socket_plain given_union_sites by fastforce

lemma lookup_input_sites:
  "declared_sites (resolution_declarations.truncate lookup_input_declarations) \<subseteq>
    declared_sites (resolution_declarations.truncate given_declarations)"
proof -
  have m: "(37,lookup_socket_schema,2,False,view_identity,lookup_view) |\<in>|
      declared_sockets (resolution_declarations.truncate given_declarations)"
    using lookup_given_socket by simp
  show ?thesis using declared_sites_members(4,5)[OF m] by (auto simp: declared_sites_def)
qed

lemma given_input_sites:
  "declared_sites (resolution_declarations.truncate given_input_declarations) \<subseteq>
    declared_sites (resolution_declarations.truncate given_declarations)"
  unfolding given_input_declarations_def
  by (rule subset_trans[OF produced_override_sites]) (use lookup_input_sites in blast)

lemma given_input_frame_sites: "frame_sites given_input_frames \<subseteq> system_definitions given_rooted_readers_system"
proof
  fix x assume "x \<in> frame_sites given_input_frames"
  then obtain e S s C where f: "(e,S,s,C) |\<in>| given_narrowed_frames \<or> (e,S,s,C) |\<in>| lookup_frames"
      and x: "x = e \<or> x \<in> schema_dependencies (decode_finite_schema S)"
    unfolding frame_sites_def given_input_frames_def frames_join_def by auto
  show "x \<in> system_definitions given_rooted_readers_system"
    using f
  proof
    assume "(e,S,s,C) |\<in>| given_narrowed_frames"
    then have "x \<in> frame_sites given_narrowed_frames" using x unfolding frame_sites_def by auto
    then show ?thesis using given_narrowed_frame_sites by blast
  next
    assume "(e,S,s,C) |\<in>| lookup_frames"
    then have "e = 37" "S = lookup_socket_schema" by (simp_all add: lookup_frames_def)
    then have "x \<in> declared_sites (resolution_declarations.truncate lookup_input_declarations)"
      using x by (auto simp: declared_sites_def)
    then show ?thesis using lookup_input_sites given_declarations_sites by blast
  qed
qed

context given_readers_extension
begin

subsection \<open>At the numbered program: the first part's discharges carried by agreement\<close>

lemma lookup_reflexive_Q: "producer_reflexive (positive_meaning (decode_finite_system Q)) 12 view_identity"
proof -
  have r12: "12 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  have "producer_reflexive (positive_meaning (decode_finite_system Q)) 12 view_identity \<longleftrightarrow>
      producer_reflexive (positive_meaning (decode_finite_system finite_rooted_given_readers)) 12 view_identity"
    by (rule producer_reflexive_agree) (simp add: rooted_meaning_Q[OF r12] finite_rooted_given_readers_exact)
  then show ?thesis using given_rooted_identity_reflexive by simp
qed

lemma given_input_sites_Q:
  "declared_sites (resolution_declarations.truncate given_input_declarations) \<subseteq> system_definitions (decode_finite_system Q)"
  using given_input_sites given_declarations_sites_Q by blast

lemma given_input_frame_sites_Q: "frame_sites given_input_frames \<subseteq> system_definitions (decode_finite_system Q)"
  using given_input_frame_sites by (auto intro: rooted_in_Q)

lemma given_input_discharged_Q:
  "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
    (narrowed_declarations.truncate given_input_declarations) given_declarations_correspondence"
  "narrowed_frames_discharged (positive_meaning (decode_finite_system Q))
    (narrowed_declarations.truncate given_input_declarations) given_input_frames"
  "productions_discharged (positive_meaning (decode_finite_system Q)) Q m given_input_declarations"
proof -
  note carried = produced_record_discharged_Q[OF given_input_declarations_discharged(1) given_input_frames_discharged
    subset_trans[OF given_input_sites given_declarations_sites]]
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate given_input_declarations) given_declarations_correspondence"
    by (rule carried(1))
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate given_input_declarations) given_input_frames"
    by (rule carried(2))
  show "productions_discharged (positive_meaning (decode_finite_system Q)) Q m given_input_declarations"
    unfolding given_input_declarations_def
    by (rule produced_override_productions[OF given_declarations_discharged_Q(3)
      lookup_input_productions_at[OF lookup_reflexive_Q]])
qed

theorem committed_input_registrations_Q:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
  shows "committed_registrations \<kappa> Q m given_input_declarations given_input_frames given_declarations_correspondence"
  by (rule produced_committed_registrations_Q[OF \<kappa> complete given_input_declarations_discharged(1)
    given_input_frames_discharged subset_trans[OF given_input_sites given_declarations_sites] given_input_discharged_Q(3)
    given_input_declarations_discharged(3)])

subsection \<open>The lookup record at the installed program\<close>

definition installed_lookup_declarations where
  "installed_lookup_declarations = produced_declarations_varied (finite_rename_system installed_placement Q)
    installed_presentation (produced_relocated installed_placement lookup_input_declarations)"

lemma installed_lookup_narrowing: "declared_narrowing installed_lookup_declarations e T t x"
  unfolding installed_lookup_declarations_def produced_declarations_varied_fields narrowing_varied_def
  by (rule fBallI) (auto simp: produced_relocated_def split: prod.splits)

lemma installed_lookup_declared: "narrowed_productions_declared installed_lookup_declarations"
proof -
  have "declared_narrowing installed_lookup_declarations e T t = (\<lambda>_. True)" for e T t
    by (rule ext) (simp add: installed_lookup_narrowing)
  then show ?thesis unfolding narrowed_productions_declared_def by simp
qed

lemma lookup_reflexive_installed:
  "producer_reflexive (positive_meaning (decode_finite_system installed_presentation)) (installed_placement 12)
    view_identity"
proof -
  have r12: "12 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  show ?thesis using lookup_reflexive_Q unfolding producer_reflexive_def installed_presentation_exact(3)
    by (simp add: installed_meaning[OF rooted_in_Q[OF r12]])
qed

text \<open>
  The lookup socket's sources at the installed program are unique, and 12 has one placed and one installed clause:
  37 and 12 each have one clause, so both are instances of @{thm [source] installed_single_clause}.
\<close>

lemma installed_lookup_sources:
  "finite_varied_sources_unique_at {installed_placement 37} (finite_rename_system installed_placement Q)
    installed_presentation"
  by (rule installed_single_clause(3)[OF given_rooted_declared_sites lookup_rooted_clause]) simp

lemma placed_identity_clause:
  "((installed_placement 12,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q) \<longleftrightarrow>
    c = 0 \<and> S = finite_rename_schema id id installed_placement identity_socket_schema"
  by (rule installed_single_clause(1)[OF given_rooted_declared_sites identity_rooted_clause]) simp

lemma installed_identity_clause:
  "\<exists>c1 T1 f1 h1. ((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id installed_placement identity_socket_schema) T1 = Some (f1,h1) \<and>
    (\<forall>c T. ((installed_placement 12,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1)"
  by (rule installed_single_clause(2)[OF given_rooted_declared_sites identity_rooted_clause]) simp

text \<open>
  The lookup record's production at the installed program, computed once: every socket of the carried record stands
  at the placed 37, and its production there is 12's input registration varied to 12's one installed clause.
\<close>

lemma installed_lookup_value:
  assumes sock: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets installed_lookup_declarations"
  obtains c1 T1 f1 h1 where "e = installed_placement 37"
    "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
    "finite_schema_match (finite_rename_schema id id installed_placement identity_socket_schema) T1 = Some (f1,h1)"
    "declared_production installed_lookup_declarations e T t =
      Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
proof -
  let ?P = "finite_rename_system installed_placement Q"
  let ?L = "produced_relocated installed_placement lookup_input_declarations"
  let ?S = "finite_rename_schema id id installed_placement identity_socket_schema"
  define R :: "(nat,nat,local_address option definition_site,nat) collection_registration"
    where "R = input_registration (installed_placement 12) ?S view_identity 1"
  obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?L"
      and src: "(S,s) |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t"
    using sock unfolding installed_lookup_declarations_def produced_varied_sockets_member by blast
  have Lsock: "(e',S',s',k',V',W') |\<in>| declared_sockets ?L \<longleftrightarrow> e' = installed_placement 37 \<and>
      S' = finite_rename_schema id id installed_placement lookup_socket_schema \<and> s' = 2 \<and> k' = False \<and>
      V' = view_identity \<and> W' = lookup_view" for e' S' s' k' V' W'
    unfolding produced_relocated_sockets by auto
  have e37: "e = installed_placement 37" and Ss: "S = finite_rename_schema id id installed_placement lookup_socket_schema"
      "s = 2"
    using m unfolding Lsock by blast+
  have one_src: "S' = S \<and> s' = s"
    if src': "(S',s') |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t" for S' s'
  proof -
    obtain keep' Vp' Vh' where "(e,S',s',keep',Vp',Vh') |\<in>| declared_sockets ?L"
      using src' unfolding varied_socket_sources_member by blast
    then have "S' = finite_rename_schema id id installed_placement lookup_socket_schema" "s' = 2"
      unfolding Lsock by blast+
    then show ?thesis using Ss by simp
  qed
  have srcs: "varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t = {|(S,s)|}"
  proof (rule fset_eqI)
    fix z
    show "z |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t \<longleftrightarrow> z |\<in>| {|(S,s)|}"
    proof
      assume a: "z |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t"
      obtain S' s' where z: "z = (S',s')" by (cases z)
      have "S' = S \<and> s' = s" using a unfolding z by (rule one_src)
      then show "z |\<in>| {|(S,s)|}" unfolding z by simp
    next
      assume "z |\<in>| {|(S,s)|}"
      then have "z = (S,s)" by simp
      then show "z |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?L) e T t" using src by simp
    qed
  qed
  have inj: "inj_on installed_placement (declared_sites (resolution_declarations.truncate lookup_input_declarations))"
    by (rule inj_on_subset[OF installation(5)]) (use given_declarations_sites_Q lookup_input_sites in blast)
  have m0: "(37,lookup_socket_schema,2,False,view_identity,lookup_view) |\<in>| declared_sockets lookup_input_declarations"
    by simp
  have LR: "declared_production ?L e S s = Some R"
    unfolding e37 Ss produced_relocated_keys(2)[OF inj m0]
    by (simp add: R_def identity_input_registration_def input_registration_relocated_eq)
  have pc: "((installed_placement 12,0),?S) |\<in>| finite_system_clauses ?P" by (simp add: placed_identity_clause)
  have site: "registration_site R = installed_placement 12" "registration_schema R = ?S"
    by (simp_all add: R_def input_registration_def)
  have r12: "12 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  obtain c1 T1 f1 h1 where u: "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match ?S T1 = Some (f1,h1)"
      "\<forall>c T. ((installed_placement 12,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1"
      "registrations_varied ?P installed_presentation R = {|registration_varied f1 T1 R|}"
    by (rule installed_single_registration[OF r12 identity_rooted_clause site])
  have Sf: "finite_schema_formed ?S" by (rule finite_system_clause_formed[OF installed_presentation_formed(2) pc])
  have Tf: "finite_schema_formed T1" by (rule finite_system_clause_formed[OF installed_presentation_formed(1) u(1)])
  interpret matched: finite_schema_matched ?S T1 f1 h1 by (rule finite_schema_matched.intro[OF Sf Tf u(2)])
  have head: "head_registration view_identity ?S 1" using identity_input_registration_head by simp
  have R': "registration_varied f1 T1 R = input_registration (installed_placement 12) T1 view_identity (f1 1)"
    unfolding R_def by (rule matched.input_registration_varied[OF head])
  have carried: "production_carried ?P installed_presentation (Some R) =
      Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    unfolding production_carried_some using u(4) R' by simp
  have prod: "declared_production installed_lookup_declarations e T t =
      Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    unfolding installed_lookup_declarations_def produced_declarations_varied_fields production_varied_def Let_def srcs
    using LR carried by simp
  then show ?thesis by (rule that[OF e37 u(1) u(2)])
qed

theorem installed_lookup_productions:
  "productions_discharged (positive_meaning (decode_finite_system installed_presentation)) installed_presentation m
    installed_lookup_declarations"
proof (rule input_productions_discharged)
  let ?L = "produced_relocated installed_placement lookup_input_declarations"
  let ?S = "finite_rename_schema id id installed_placement identity_socket_schema"
  fix e T t keep Vp Vh R'
  assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets installed_lookup_declarations"
    and p: "declared_production installed_lookup_declarations e T t = Some R'"
  obtain c1 T1 f1 h1 where v: "e = installed_placement 37"
      "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match ?S T1 = Some (f1,h1)"
      "declared_production installed_lookup_declarations e T t =
        Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    by (rule installed_lookup_value[OF mem])
  have R'': "R' = input_registration (installed_placement 12) T1 view_identity (f1 1)" using p v(4) by simp
  obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?L"
    using mem unfolding installed_lookup_declarations_def produced_varied_sockets_member by blast
  have V: "Vp = view_identity" using m by (auto simp: produced_relocated_sockets)
  have pc: "((installed_placement 12,0),?S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    by (simp add: placed_identity_clause)
  have Sf: "finite_schema_formed ?S" by (rule finite_system_clause_formed[OF installed_presentation_formed(2) pc])
  have Tf: "finite_schema_formed T1" by (rule finite_system_clause_formed[OF installed_presentation_formed(1) v(2)])
  interpret matched: finite_schema_matched ?S T1 f1 h1 by (rule finite_schema_matched.intro[OF Sf Tf v(3)])
  have head: "head_registration view_identity ?S 1" using identity_input_registration_head by simp
  have headT: "head_registration view_identity T1 (f1 1)" by (rule matched.head_registration_matched[OF head])
  have narrowing: "\<forall>x. declared_narrowing installed_lookup_declarations e T t x" by (simp add: installed_lookup_narrowing)
  show "(R' = input_registration (registration_site R') (registration_schema R') Vp (registration_variable R') \<and>
        head_registration Vp (registration_schema R') (registration_variable R') \<and>
        producer_reflexive (positive_meaning (decode_finite_system installed_presentation)) (registration_site R') Vp \<and>
        (\<forall>x. declared_narrowing installed_lookup_declarations e T t x)) \<or>
      (head_registration Vp (registration_schema R') (registration_variable R') \<and>
        head_registration_produces (finite_collection_construction [R'] m) installed_presentation (registration_site R')
          (registration_schema R') (registration_variable R') (declared_narrowing installed_lookup_declarations e T t) \<and>
        head_registration_answers (positive_meaning (decode_finite_system installed_presentation))
          (finite_collection_construction [R'] m) installed_presentation (registration_site R') (registration_schema R') Vp
          (registration_variable R'))"
    unfolding R'' V using headT lookup_reflexive_installed narrowing by (simp add: input_registration_def)
qed


subsection \<open>The given's input record at the installed program\<close>

lemma input_injective:
  "inj_on installed_placement (declared_sites (resolution_declarations.truncate given_declarations) \<union>
    declared_sites (resolution_declarations.truncate lookup_input_declarations))"
  by (rule inj_on_subset[OF installation(5)]) (use given_declarations_sites_Q lookup_input_sites in blast)

definition installed_input_declarations where
  "installed_input_declarations = produced_declarations_varied (finite_rename_system installed_placement Q)
    installed_presentation (produced_relocated installed_placement given_input_declarations)"

definition installed_input_frames where
  "installed_input_frames = frames_varied (finite_rename_system installed_placement Q) installed_presentation
    (frames_relocated installed_placement given_input_frames)"

definition installed_input_correspondence where
  "installed_input_correspondence = given_declarations_correspondence \<circ>
    inv_into (declared_sites (resolution_declarations.truncate given_input_declarations)) installed_placement"

theorem installed_input_override:
  "installed_input_declarations = produced_override installed_given_declarations installed_lookup_declarations"
  unfolding installed_input_declarations_def installed_given_declarations_def installed_lookup_declarations_def
    given_input_declarations_def
  by (rule produced_carried_override[OF input_injective installed_presentation_formed(2,1) installed_lookup_sources])
    simp

lemma installed_input_within:
  "narrowings_within (installed_placement ` {50,55,57,60,63})
    (produced_relocated installed_placement given_input_declarations)"
proof -
  let ?O = "produced_override (produced_relocated installed_placement given_declarations)
    (produced_relocated installed_placement lookup_input_declarations)"
  note c = produced_relocated_override[OF input_injective]
  have lw: "narrowings_within A (produced_relocated installed_placement lookup_input_declarations)" for A
    unfolding narrowings_within_def by (simp add: produced_relocated_def)
  have o: "narrowings_within (installed_placement ` {50,55,57,60,63}) ?O"
    by (rule produced_override_within[OF relocated_within lw])
  show ?thesis unfolding narrowings_within_def given_input_declarations_def
  proof (intro allI impI)
    fix e S s keep Vp Vh
    assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement
        (produced_override given_declarations lookup_input_declarations))"
      and out: "e \<notin> installed_placement ` {50,55,57,60,63}"
    have m': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?O" using m c(3) by simp
    have "declared_narrowing ?O e S s = (\<lambda>_. True)" using o m' out unfolding narrowings_within_def by blast
    then show "declared_narrowing (produced_relocated installed_placement
        (produced_override given_declarations lookup_input_declarations)) e S s = (\<lambda>_. True)"
      using conjunct1[OF c(4)[OF m]] by simp
  qed
qed

theorem installed_input_agree:
  "varied_narrowings_agree (finite_rename_system installed_placement Q) installed_presentation
    (produced_relocated installed_placement given_input_declarations)"
  by (rule varied_narrowings_agree_within[OF installed_presentation_formed(2,1) installed_union_sources
    installed_input_within])

theorem installed_input_productions:
  "productions_discharged (positive_meaning (decode_finite_system installed_presentation)) installed_presentation m
    installed_input_declarations"
  unfolding installed_input_override
  by (rule produced_override_productions[OF installed_productions[folded installed_given_declarations_def]
    installed_lookup_productions])

theorem installed_input_declared: "narrowed_productions_declared installed_input_declarations"
  unfolding installed_input_override
  by (rule produced_override_declared[OF installed_declared[folded installed_given_declarations_def]
    installed_lookup_declared])

subsection \<open>12's production at the varied lookup socket\<close>

text \<open>
  At every socket of the lookup record carried to the installed program, the given's input record declares 12's
  input registration, varied to 12's one installed clause: the committed search at 526 and 561 takes 12's input from
  this production. The production applies at every goal whose pattern the identity view reads: its conclusion's
  input is a variable, which matches every input.
\<close>

theorem installed_lookup_production:
  assumes sock: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets installed_lookup_declarations"
  obtains c1 T1 f1 h1 where "e = installed_placement 37"
    "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
    "finite_schema_match (finite_rename_schema id id installed_placement identity_socket_schema) T1 = Some (f1,h1)"
    "declared_production installed_input_declarations e T t =
      Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
proof -
  obtain c1 T1 f1 h1 where v: "e = installed_placement 37"
      "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match (finite_rename_schema id id installed_placement identity_socket_schema) T1 = Some (f1,h1)"
      "declared_production installed_lookup_declarations e T t =
        Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    by (rule installed_lookup_value[OF sock])
  have keyed: "socket_keyed (resolution_declarations.truncate installed_lookup_declarations) e T t"
    unfolding socket_keyed_iff truncate_fields using sock by blast
  have "declared_production installed_input_declarations e T t =
      Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    unfolding installed_input_override using keyed v(4) by simp
  then show ?thesis by (rule that[OF v(1) v(2) v(3)])
qed

corollary installed_lookup_production_present:
  assumes "(installed_placement 37,T,t,keep,Vp,Vh) |\<in>| declared_sockets installed_lookup_declarations"
  shows "declared_production installed_input_declarations (installed_placement 37) T t \<noteq> None"
  by (rule installed_lookup_production[OF assms]) simp

theorem installed_lookup_applies:
  assumes sock: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets installed_lookup_declarations"
    and p: "declared_production installed_input_declarations e T t = Some R'"
    and view: "resolution_view_pattern view_identity p \<noteq> None"
  shows "finite_registration_applies view_identity R' (installed_placement 12) p"
proof -
  let ?S = "finite_rename_schema id id installed_placement identity_socket_schema"
  obtain c1 T1 f1 h1 where u: "e = installed_placement 37"
      "((installed_placement 12,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match ?S T1 = Some (f1,h1)"
      "declared_production installed_input_declarations e T t =
        Some (input_registration (installed_placement 12) T1 view_identity (f1 1))"
    by (rule installed_lookup_production[OF sock])
  have R': "R' = input_registration (installed_placement 12) T1 view_identity (f1 1)" using p u(4) by simp
  have pc: "((installed_placement 12,0),?S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    by (simp add: placed_identity_clause)
  have Sf: "finite_schema_formed ?S" by (rule finite_system_clause_formed[OF installed_presentation_formed(2) pc])
  have Tf: "finite_schema_formed T1" by (rule finite_system_clause_formed[OF installed_presentation_formed(1) u(2)])
  have T1: "T1 = finite_rename_schema f1 h1 id ?S" using finite_schema_match_exact(1)[OF Sf Tf u(3)] by blast
  have conc: "resolution_view_pattern view_identity (finite_schema_conclusion T1) =
      Some (Finite_Variable (f1 0),Finite_Variable (f1 1))"
    unfolding T1 by (simp add: finite_rename_schema_def identity_socket_schema_def view_identity_pattern)
  obtain x y where xy: "resolution_view_pattern view_identity p = Some (x,y)" using view by auto
  have val: "finite_binding_valuation {|(f1 0,finite_residual_term x)|} (f1 0) = finite_residual_term x"
    by (rule finite_binding_valuation_member) (simp_all add: finite_relation_functional_def)
  have site: "registration_site R' = installed_placement 12" and schema: "registration_schema R' = T1"
    unfolding R' by (simp_all add: input_registration_def)
  show ?thesis
    unfolding finite_registration_applies_def site schema xy conc
    by (simp only: option.case fst_conv finite_matching_bindings.simps(1) resolution_value_constructors(1) val
      simp_thms)
qed

subsection \<open>The committed registrations at the installed program\<close>

theorem installed_input_committed_registrations:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
  shows "committed_registrations (installed_construction \<kappa>) installed_presentation m' installed_input_declarations
    installed_input_frames installed_input_correspondence"
  unfolding installed_input_declarations_def installed_input_frames_def installed_input_correspondence_def
    installed_construction_def
  using install.committed_registrations_produced_relocated[OF installed_built installed_presentation_read
    committed_input_registrations_Q[OF \<kappa> complete] given_input_sites_Q given_input_frame_sites_Q
    installed_input_agree[unfolded installed_placement_def]
    installed_input_productions[unfolded installed_input_declarations_def installed_placement_def]
    installed_input_declared[unfolded installed_input_declarations_def installed_placement_def],
    folded installed_placement_def] .

theorem installed_input_committed_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and resolution: "native_committed_resolution (installed_construction \<kappa>)
      (finite_narrowed_commitment installed_presentation m' installed_input_declarations installed_input_frames)
      installed_presentation R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning installed_program"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning installed_program"
    and "A = Some B \<Longrightarrow> schema_system_formed installed_program \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning installed_program}"
  using native_committed_registrations_exact[OF installed_input_committed_registrations[OF \<kappa> complete] resolution,
    unfolded installed_presentation_exact(3)] by blast+

end

text \<open>
  The record with 12's input production at the asked relation over additions' installed guard (990 in the native
  course, #707, AX4) and at the first request's installed program (561 at the installation, #547, #399): committed
  with every complete construction of the numbered program. #798's carrying of @{const given_declarations} stands as
  @{thm [source] asked_additions_installed_declarations_discharged} and
  @{thm [source] first_request_installed_declarations_discharged}.
\<close>

theorem asked_additions_installed_input_declarations_discharged:
  assumes "finite_witness_construction_formed \<kappa>" "finite_construction_complete \<kappa> finite_asked_additions_program"
  shows "committed_registrations (asked_additions_extension.installed_construction \<kappa>)
    asked_additions_installed_presentation m'
    asked_additions_extension.installed_input_declarations asked_additions_extension.installed_input_frames
    asked_additions_extension.installed_input_correspondence"
  unfolding asked_additions_installed_presentation_def
  by (rule asked_additions_extension.installed_input_committed_registrations[OF assms])

theorem first_request_installed_input_declarations_discharged:
  assumes "finite_witness_construction_formed \<kappa>" "finite_construction_complete \<kappa> finite_first_request_program"
  shows "committed_registrations (first_request_extension.installed_construction \<kappa>) first_request_installed_presentation
    m' first_request_extension.installed_input_declarations first_request_extension.installed_input_frames
    first_request_extension.installed_input_correspondence"
  unfolding first_request_installed_presentation_def
  by (rule first_request_extension.installed_input_committed_registrations[OF assms])

end
