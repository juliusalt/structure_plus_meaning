theory Factor_Varied_Narrowed_Transfer
  imports Factor_Varied_Narrowed_Sockets Factor_Narrowed_Productions
begin

text \<open>
  V2b's (3) of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an
  installed package by matching its clauses against the placed ones" (task 642), with the correction closing task 495's
  addition "The given's remaining producers" (task 725): R5f2's committed forms and transfer at #651's varied record
  with narrowed sockets and productions. Nothing here is proved again: the narrowed discharge at N is #651's
  (@{thm [source] declarations_varied_narrowed_discharged}), taken at the record's productions dropped as #651's own
  unnarrowed instance takes it; the productions' discharge at N (#599's hypotheses at the carried production) is carried
  by #651's lemmas along the producer's match (@{thm [source] finite_schema_matched.head_registration_matched},
  @{thm [source] head_registration_produces_varied}, @{thm [source] head_registration_answers_varied}); the exchange and
  the four forms are R5f2's (@{thm [source] finite_narrowed_commitment_exchanges}, @{thm [source] finite_narrowed_forms_exact})
  at N. The frames at N and the static premise of the varied record stand as premises: no fact carries a narrowed frame
  along the match, and a carried socket declares a production only where every source's carries to one.
\<close>

section \<open>The narrowed discharge at N\<close>

text \<open>The varied narrowed record reads the record's truncation and classes alone, never its productions.\<close>

lemma narrowed_declarations_varied_unproduced:
  "narrowed_declarations_varied P N (unproduced (narrowed_declarations.truncate PD) :: ('a,'s::linorder,'d,'v) produced_declarations) =
    narrowed_declarations_varied P N PD"
  by (simp add: narrowed_declarations_varied_def fun_eq_iff narrowing_varied_def)

theorem narrowed_declarations_varied_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
    (narrowed_declarations_varied P N PD) corr"
proof -
  define PD0 :: "('a,'s,'d,'v) produced_declarations" where "PD0 = unproduced (narrowed_declarations.truncate PD)"
  define \<kappa> :: "('a,'s,'d,'c) finite_witness_construction" where "\<kappa> = undefined"
  define \<kappa>' :: "('b,'t,'d,'e) finite_witness_construction" where "\<kappa>' = undefined"
  have none: "declared_production PD0 e S s = None" for e S s by (simp add: PD0_def)
  have at0: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD0) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    using at by (simp add: PD0_def)
  have sk: "declared_sockets PD0 = declared_sockets PD" and nw: "declared_narrowing PD0 = declared_narrowing PD"
    by (simp_all add: PD0_def)
  have agree0: "varied_narrowings_agree P N PD0"
    unfolding varied_narrowings_agree_def sk nw using agree[unfolded varied_narrowings_agree_def] .
  have dis0: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD0) corr"
    using discharged by (simp add: PD0_def)
  have complete: "productions_complete (positive_meaning (decode_finite_system P)) \<kappa> P PD0"
    by (simp add: productions_complete_def none)
  have carried: "production_values_carried \<kappa> P \<kappa>' N R"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD0" "declared_production PD0 e S s = Some R" for e S s keep Vp Vh R
    using that(2) by (simp add: none)
  have "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD0)) corr"
    by (rule declarations_varied_narrowed_discharged(1)[OF Pf Nf at0 agree0 dis0 complete carried])
  then show ?thesis by (simp add: produced_declarations_varied_truncate PD0_def narrowed_declarations_varied_unproduced)
qed

section \<open>The productions discharged at N\<close>

text \<open>
  A production's discharge (#599's hypotheses, @{const productions_discharged}) at a carried socket reads the carried
  production: its head registration is the source's at the image of its variable along the producer's match, and its
  values and answers are the source's wherever the carried production's collection construction at N gives the
  source's values at the bindings carried back (@{const production_values_carried}) and the programs mean the same at
  the production's site.
\<close>

theorem productions_discharged_varied:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and formed: "declarations_formed (resolution_declarations.truncate PD)"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
  shows "productions_discharged (positive_meaning (decode_finite_system N)) N m' (produced_declarations_varied P N PD)"
  unfolding productions_discharged_def
proof (intro allI impI)
  fix e T t keep Vp Vh R'
  assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD)"
    and pr: "declared_production (produced_declarations_varied P N PD) e T t = Some R'"
  obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate PD)"
      "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
    using mem[unfolded produced_declarations_varied_fields declarations_varied_sockets_member] by blast
  have m1: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" using m(1) by simp
  have src: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
    unfolding varied_socket_sources_member using m1 m(2-6) by blast
  obtain R where R: "declared_production PD e S s = Some R" "registrations_varied P N R = {|R'|}"
    using production_varied_source[OF pr[unfolded produced_declarations_varied_fields] src] by blast
  have R': "R' |\<in>| registrations_varied P N R" using R(2) by simp
  then obtain c1 c2 TR fR hR where r: "((registration_site R,c1),registration_schema R) |\<in>| finite_system_clauses P"
      "((registration_site R,c2),TR) |\<in>| finite_system_clauses N"
      "finite_schema_match (registration_schema R) TR = Some (fR,hR)" "R' = registration_varied fR TR R"
    unfolding registrations_varied_member by blast
  have matched: "finite_schema_matched (registration_schema R) TR fR hR"
    by unfold_locales (rule finite_system_clause_formed[OF Pf r(1)], rule finite_system_clause_formed[OF Nf r(2)], rule r(3))
  interpret Pr: finite_schema_matched "registration_schema R" TR fR hR by (rule matched)
  have pd: "head_registration Vp (registration_schema R) (registration_variable R)"
      "head_registration_produces (finite_collection_construction [R] m) P (registration_site R) (registration_schema R)
        (registration_variable R) (declared_narrowing PD e S s)"
      "head_registration_answers (positive_meaning (decode_finite_system P)) (finite_collection_construction [R] m) P
        (registration_site R) (registration_schema R) Vp (registration_variable R)"
    using productions m1 R(1) unfolding productions_discharged_def by blast+
  have "fBall (declared_sockets (resolution_declarations.truncate PD)) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
    using formed by (simp add: declarations_formed_def)
  from fbspec[OF this m(1)] have Vpf: "view_formed Vp" by simp
  have vals: "\<And>B v. witness_value (finite_collection_construction [R'] m') N (registration_site R) TR B
      (fR (registration_variable R)) = Some v \<Longrightarrow>
    witness_value (finite_collection_construction [R] m) P (registration_site R) (registration_schema R)
      (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
    using carried[OF m1 R(1) R'] r(2,3) unfolding production_values_carried_def by blast
  have eqd: "\<And>x. (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    by (rule at_productions[OF m1 R(1)])
  have K: "declared_narrowing (produced_declarations_varied P N PD) e T t = declared_narrowing PD e S s"
    using narrowing_varied_source[OF agree src] by (simp add: produced_declarations_varied_fields)
  have fields: "registration_site R' = registration_site R" "registration_schema R' = TR"
      "registration_variable R' = fR (registration_variable R)"
    using r(4) by simp_all
  show "head_registration Vp (registration_schema R') (registration_variable R') \<and>
      head_registration_produces (finite_collection_construction [R'] m') N (registration_site R') (registration_schema R')
        (registration_variable R') (declared_narrowing (produced_declarations_varied P N PD) e T t) \<and>
      head_registration_answers (positive_meaning (decode_finite_system N)) (finite_collection_construction [R'] m') N
        (registration_site R') (registration_schema R') Vp (registration_variable R')"
    unfolding fields K
  proof (intro conjI)
    show "head_registration Vp TR (fR (registration_variable R))" by (rule Pr.head_registration_matched[OF pd(1)])
    show "head_registration_produces (finite_collection_construction [R'] m') N (registration_site R) TR
        (fR (registration_variable R)) (declared_narrowing PD e S s)"
      by (rule head_registration_produces_varied[where
        G="\<lambda>B. finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B", OF pd(2) vals])
    show "head_registration_answers (positive_meaning (decode_finite_system N)) (finite_collection_construction [R'] m') N
        (registration_site R) TR Vp (fR (registration_variable R))"
      by (rule head_registration_answers_varied[OF matched Vpf pd(3) eqd vals])
  qed
qed

section \<open>The committed forms at the varied narrowed record\<close>

text \<open>
  The exchange premise at N is R5f2's, from the carried narrowed discharge and productions (never transferred); the four
  forms at N are R5f2's forms there. A construction at N is any whose registrations are premise-only and whose lifts
  hold there; V1's varied construction is one wherever the source's is complete
  (@{text finite_varied_construction_conditions}, from @{thm [source] varied_construction_complete}).
\<close>

theorem finite_varied_narrowed_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
    (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N"
proof -
  have formed: "declarations_formed (resolution_declarations.truncate PD)"
    using discharged by (simp add: narrowed_declarations_discharged_def)
  have dN: "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    using narrowed_declarations_varied_discharged[OF Pf Nf at agree discharged]
    by (simp add: produced_declarations_varied_truncate)
  show ?thesis
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa>' dN frames'
      productions_discharged_varied[OF Pf Nf at_productions agree formed productions carried] declared' only'])
qed

theorem finite_varied_narrowed_refutation_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and refutes: "finite_resolution_refutes (finite_committed_resolution \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system N)"
  by (rule finite_committed_resolution_refutation_exact[OF \<kappa>' finite_varied_narrowed_commitment_exchanges[OF \<kappa>' Pf Nf
    at at_productions agree discharged productions carried frames' declared' only'] constructions refutes])

theorem finite_varied_narrowed_verdict_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and verdict: "finite_resolution_verdict (finite_committed_resolution \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system N)"
  by (rule finite_committed_verdict_exact[OF \<kappa>' finite_varied_narrowed_commitment_exchanges[OF \<kappa>' Pf Nf
    at at_productions agree discharged productions carried frames' declared' only'] constructions verdict])

theorem finite_varied_narrowed_demand_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and result: "finite_committed_demand \<kappa>' (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>')
      N Q n = Some A"
  shows "schema_system_formed (decode_finite_system N)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)}"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N"
    by (rule finite_varied_narrowed_commitment_exchanges[OF \<kappa>' Pf Nf at at_productions agree discharged productions
      carried frames' declared' only'])
  from finite_committed_demand_exact[OF \<kappa>' ex constructions result]
  show "schema_system_formed (decode_finite_system N)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)}" by blast+
qed

theorem native_varied_narrowed_resolution_exact:
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N" and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and result: "native_committed_resolution \<kappa>' (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>')
      N R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof N p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system N)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system N) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)}"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N"
    by (rule finite_varied_narrowed_commitment_exchanges[OF \<kappa>' Pf Nf at at_productions agree discharged productions
      carried frames' declared' only'])
  note exact = native_committed_resolution_exact[OF \<kappa>' ex constructions result]
  show "fimage fst T = R" by (rule exact(1))
  show "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof N p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)" by (rule exact(2))
  show "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system N)" by (rule exact(3))
  show "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system N) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system N)}" by (rule exact(4))
qed

lemmas finite_varied_narrowed_forms_exact = finite_varied_narrowed_refutation_exact finite_varied_narrowed_verdict_exact
  finite_varied_narrowed_demand_exact native_varied_narrowed_resolution_exact

text \<open>V1's varied construction meets the forms' construction premises at N wherever the source's is complete.\<close>

lemma finite_varied_construction_conditions:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and complete: "finite_construction_complete \<kappa> P" and agree: "finite_varied_meanings_agree P N"
  shows "finite_witness_construction_formed (finite_varied_construction P N \<kappa>)"
    "finite_registrations_premise_only (finite_varied_construction P N \<kappa>) N"
    "finite_construction_lifts U (finite_varied_construction P N \<kappa>) N"
  using finite_varied_construction_formed[OF \<kappa>]
    finite_complete_registrations_premise_only[OF varied_construction_complete[OF Pf Nf complete agree]]
    finite_construction_complete_lifts[OF varied_construction_complete[OF Pf Nf complete agree]] by blast+

section \<open>The transfer to a varied presentation\<close>

text \<open>
  A program and its varied presentation give the same committed verdict at records with narrowed sockets and
  productions: each verdict is the call's meaning in its own program (R5f2's forms at P, and at N from the carried
  record), and alpha variants mean the same. At a record declaring no narrowing and no production the varied record is
  V2a's (@{text produced_declarations_varied_unnarrowed}) and R5f2's commitment the framed one
  (@{thm [source] finite_unproduced_commitment}), so V2a's @{thm [source] finite_framed_variant_transfer}, and at no frame
  its @{thm [source] finite_committed_variant_transfer}'s record, is the instance.
\<close>

lemma produced_declarations_varied_unnarrowed:
  "produced_declarations_varied P N (unproduced (unnarrowed D) :: ('a,'s::linorder,'d,'v) produced_declarations) =
    (unproduced (unnarrowed (declarations_varied P N D)) :: ('b,'t::linorder,'d,'v) produced_declarations)"
proof -
  let ?PD = "unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations"
  have top: "narrowing_varied P N ?PD = (\<lambda>_ _ _ _. True)" by (rule narrowing_varied_top) simp
  have none: "production_varied P N ?PD = (\<lambda>_ _ _. None)"
  proof (intro ext)
    fix e T t
    let ?X = "varied_socket_sources P N (declared_sockets ?PD) e T t"
    have "fimage (\<lambda>(S,s). production_carried P N (declared_production ?PD e S s)) ?X =
        (if ?X = {||} then {||} else {|None|})"
      by (auto simp: production_carried_def)
    moreover have ne: "\<And>y. {||} \<noteq> {|y|}" by (metis fempty_iff finsertI1)
    ultimately show "production_varied P N ?PD e T t = None" by (simp add: production_varied_def Let_def ne)
  qed
  show ?thesis
    by (simp add: produced_declarations_varied_def narrowed_declarations_varied_def top none)
qed

corollary finite_committed_variant_transfer_narrowed:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and declared: "narrowed_productions_declared PD"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and agree: "varied_narrowings_agree P N PD"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied P N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
    and frames': "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) \<Phi>'"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
    and only': "finite_registrations_premise_only \<kappa>' N" and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m PD \<Phi>) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) \<Phi>') N d t n') = Some b'"
  shows "b = b'"
proof -
  have Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  have same: "\<And>d x. (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    by (simp add: system_alpha_positive_meaning[OF alpha])
  have "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    by (rule finite_narrowed_verdict_exact[OF \<kappa> discharged frames productions declared only cl v])
  moreover have "b' \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system N)"
    by (rule finite_varied_narrowed_verdict_exact[OF \<kappa>' Pf Nf same same agree discharged productions carried
      frames' declared' only' cl' v'])
  ultimately show ?thesis using same by simp
qed

section \<open>After the relocation\<close>

text \<open>
  As V2a's @{thm [source] declarations_relocated_varied_discharged} composes relocation and variation: a narrowed record
  discharged at the numbered program, relocated with its classes given at the relocated sites (R5e's
  @{thm [source] narrowed_declarations_relocated_discharged}) into a record at the placed program, and varied to an
  alpha variant of the placed program, is discharged there; the relocated record's productions, discharged at the placed
  program as R5f2's relocation transfer takes them, are discharged there too.
\<close>

theorem narrowed_declarations_relocated_varied_discharged:
  fixes Q :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
    and N :: "('b,'t::linorder,'e,'f) finite_schema_system" and D' :: "('a,'s,'e,'v) produced_declarations"
  assumes Qf: "schema_system_formed (decode_finite_system Q)"
    and injective: "inj_on g (system_definitions (decode_finite_system Q) \<union>
      declared_sites (resolution_declarations.truncate ND))"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q)) ND corr"
    and relocated: "narrowed_declarations.truncate D' =
      narrowed (declarations_relocated g (resolution_declarations.truncate ND)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing ND e S s"
    and alpha: "system_alpha_variant (decode_finite_system (finite_rename_system g Q)) (decode_finite_system N)"
    and agree: "varied_narrowings_agree (finite_rename_system g Q) N D'"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
    (narrowed_declarations_varied (finite_rename_system g Q) N D')
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) g)"
proof -
  have Pf: "finite_system_formed (finite_rename_system g Q)" and Nf: "finite_system_formed N"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  have dR: "narrowed_declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system g Q)))
      (narrowed_declarations.truncate D') (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) g)"
    using narrowed_declarations_relocated_discharged[OF Qf injective discharged relocates] relocated by simp
  show ?thesis
    by (rule narrowed_declarations_varied_discharged[OF Pf Nf _ agree dR]) (simp only: system_alpha_positive_meaning[OF alpha])
qed

corollary productions_relocated_varied_discharged:
  fixes Q :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
    and N :: "('b,'t::linorder,'e,'f) finite_schema_system" and D' :: "('a,'s,'e,'v) produced_declarations"
  assumes alpha: "system_alpha_variant (decode_finite_system (finite_rename_system g Q)) (decode_finite_system N)"
    and agree: "varied_narrowings_agree (finite_rename_system g Q) N D'"
    and formed: "declarations_formed (resolution_declarations.truncate D')"
    and productions': "productions_discharged (positive_meaning (decode_finite_system (finite_rename_system g Q)))
      (finite_rename_system g Q) m D'"
    and carried: "\<And>e S s keep Vp Vh R R'. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D' \<Longrightarrow>
      declared_production D' e S s = Some R \<Longrightarrow> R' |\<in>| registrations_varied (finite_rename_system g Q) N R \<Longrightarrow>
      production_values_carried (finite_collection_construction [R] m) (finite_rename_system g Q)
        (finite_collection_construction [R'] m') N R"
  shows "productions_discharged (positive_meaning (decode_finite_system N)) N m'
    (produced_declarations_varied (finite_rename_system g Q) N D')"
proof -
  have Pf: "finite_system_formed (finite_rename_system g Q)" and Nf: "finite_system_formed N"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  show ?thesis
    by (rule productions_discharged_varied[OF Pf Nf _ agree formed productions' carried])
      (simp only: system_alpha_positive_meaning[OF alpha])
qed

end
