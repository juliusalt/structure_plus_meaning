theory Factor_Varied_Narrowed_Transfer
  imports Factor_Varied_Narrowed_Sockets Factor_Narrowed_Productions
begin

text \<open>
  V2b's (3) and (4) of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an
  installed package by matching its clauses against the placed ones" (task 642), with the correction closing task 495's
  addition "The given's remaining producers" (task 725): R5f2's committed forms and transfer at #651's varied record
  with narrowed sockets and productions. Nothing is proved again: the narrowed discharge at N is #651's
  (@{thm [source] declarations_varied_narrowed_discharged}), taken at the record's productions dropped as #651's own
  unnarrowed instance takes it; the productions' discharge at N (#599's hypotheses at the carried production) is carried
  by #651's lemmas along the producer's match (@{thm [source] finite_schema_matched.head_registration_matched},
  @{thm [source] head_registration_produces_varied}, @{thm [source] head_registration_answers_varied}); the narrowed
  frames are carried along the clause match as B2b's frames are (@{thm [source] frames_varied_discharged}); the
  exchange and the forms are R5f2's (@{thm [source] finite_narrowed_commitment_exchanges},
  @{thm [source] finite_narrowed_forms_exact}) at the carried record. The premises are stated once, in the locale
  @{text varied_narrowed_record}. Two conditions stand as named predicates: that a production carries to one
  registration (@{text productions_carry_uniquely}), from which with unique sources the varied record's static premise
  follows, and that W2's registration value at the carried registration is the source's at the bindings carried back
  (@{text registration_values_carried}), which the search's equivariance under the match would give and which is not
  built (q138).
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

section \<open>The values at the carried production\<close>

text \<open>
  At R5f2's own construction of a production, the target's values at the carried production are the source's exactly
  where W2's registration value at the carried registration is the source's at the bindings carried back: the
  collection construction of one registration returns that registration's value at its own site, clause and variable
  and nothing elsewhere. That condition is stated as it stands; it is what the resolution search's equivariance under
  the clause match would give, which is not built (q138).
\<close>

definition registration_values_carried ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) collection_registration \<Rightarrow> bool" where
  "registration_values_carried P m N m' R \<longleftrightarrow> (\<forall>c' T f h B v. ((registration_site R,c'),T) |\<in>| finite_system_clauses N \<longrightarrow>
    finite_schema_match (registration_schema R) T = Some (f,h) \<longrightarrow>
    finite_registration_value N m' (registration_varied f T R) B = Some v \<longrightarrow>
    finite_registration_value P m R (finite_bindings_carried_back f (finite_schema_variables (registration_schema R)) B) = Some v)"

theorem production_values_carried_collection:
  assumes values_at: "registration_values_carried P m N m' R" and R': "R' |\<in>| registrations_varied P N R"
  shows "production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
  unfolding production_values_carried_def
proof (intro allI impI)
  fix c' T f h B v
  assume T: "((registration_site R,c'),T) |\<in>| finite_system_clauses N"
    and fh: "finite_schema_match (registration_schema R) T = Some (f,h)"
    and val: "witness_value (finite_collection_construction [R'] m') N (registration_site R) T B
      (f (registration_variable R)) = Some v"
  obtain c2 T2 f2 h2 where r: "((registration_site R,c2),T2) |\<in>| finite_system_clauses N"
      "finite_schema_match (registration_schema R) T2 = Some (f2,h2)" "R' = registration_varied f2 T2 R"
    using R' unfolding registrations_varied_member by blast
  obtain R0 where R0: "R0 \<in> set [R']" "finite_registration_matches (registration_site R) T R0"
      "registration_variable R0 = f (registration_variable R)" "finite_registration_value N m' R0 B = Some v"
    using finite_collection_construction_value[OF val] by blast
  have "R0 = R'" using R0(1) by simp
  then have T2: "T2 = T" using R0(2) r(3) by (simp add: finite_registration_matches_def)
  have f2: "f2 = f" using r(2) fh T2 by simp
  have "finite_registration_value N m' (registration_varied f T R) B = Some v"
    using R0(4) \<open>R0 = R'\<close> r(3) T2 f2 by simp
  then have "finite_registration_value P m R
      (finite_bindings_carried_back f (finite_schema_variables (registration_schema R)) B) = Some v"
    using values_at T fh unfolding registration_values_carried_def by blast
  then show "witness_value (finite_collection_construction [R] m) P (registration_site R) (registration_schema R)
      (finite_bindings_carried_back f (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
    by (simp add: finite_collection_construction_def finite_registration_matches_def)
qed

section \<open>The varied record's static premise\<close>

text \<open>
  A carried socket declares a production wherever its source does and the source's production carries to one
  registration: with unique sources (@{const finite_varied_sources_unique}) the carried key has exactly one source,
  whose class is the carried class, so a class narrower than every answer is a source's, which declares a production.
\<close>

definition productions_carry_uniquely ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> bool" where
  "productions_carry_uniquely P N PD \<longleftrightarrow> (\<forall>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<longrightarrow>
    declared_production PD e S s = Some R \<longrightarrow> (\<exists>R'. registrations_varied P N R = {|R'|}))"

theorem narrowed_productions_declared_varied:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique P N"
    and declared: "narrowed_productions_declared PD" and carry: "productions_carry_uniquely P N PD"
  shows "narrowed_productions_declared (produced_declarations_varied P N PD)"
  unfolding narrowed_productions_declared_def
proof (intro allI impI)
  fix e T t keep Vp Vh
  assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD)"
    and nt: "declared_narrowing (produced_declarations_varied P N PD) e T t \<noteq> (\<lambda>_. True)"
  obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate PD)"
      "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
    using mem[unfolded produced_declarations_varied_fields declarations_varied_sockets_member] by blast
  have m1: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" using m(1) by simp
  have src: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
    unfolding varied_socket_sources_member using m1 m(2-6) by blast
  have agree: "varied_narrowings_agree P N PD" by (rule varied_narrowings_agree_unique[OF Pf Nf unique])
  have K: "declared_narrowing (produced_declarations_varied P N PD) e T t = declared_narrowing PD e S s"
    using narrowing_varied_source[OF agree src] by (simp add: produced_declarations_varied_fields)
  have "declared_narrowing PD e S s \<noteq> (\<lambda>_. True)" using nt K by simp
  then obtain R where R: "declared_production PD e S s = Some R"
    using declared m1 unfolding narrowed_productions_declared_def by blast
  obtain R' where R': "registrations_varied P N R = {|R'|}"
    using carry m1 R unfolding productions_carry_uniquely_def by blast
  interpret matched: finite_schema_matched S T f h
    by unfold_locales (rule finite_system_clause_formed[OF Pf m(2)], rule finite_system_clause_formed[OF Nf m(4)], rule m(5))
  have srcs: "varied_socket_sources P N (declared_sockets PD) e T t = {|(S,s)|}"
  proof (rule fset_eqI)
    fix z
    show "z |\<in>| varied_socket_sources P N (declared_sockets PD) e T t \<longleftrightarrow> z |\<in>| {|(S,s)|}"
    proof
      assume z: "z |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
      obtain S' s' where zs: "z = (S',s')" by (cases z)
      obtain keep' Vp' Vh' c1 c1' f' h' where mb: "(e,S',s',keep',Vp',Vh') |\<in>| declared_sockets PD"
          "((e,c1),S') |\<in>| finite_system_clauses P" "s' \<in> schema_sockets (decode_finite_schema S')"
          "((e,c1'),T) |\<in>| finite_system_clauses N" "finite_schema_match S' T = Some (f',h')" "t = h' s'"
        using z[unfolded zs varied_socket_sources_member] by blast
      have SS: "S' = S" using unique m(2,4,5) mb(2,5) unfolding finite_varied_sources_unique_def by blast
      have hh: "h' = h" using mb(5) m(5) SS by simp
      have "s' = s" by (rule inj_onD[OF matched.sockets]) (use m mb SS hh in auto)
      then show "z |\<in>| {|(S,s)|}" using zs SS by simp
    next
      assume "z |\<in>| {|(S,s)|}"
      then show "z |\<in>| varied_socket_sources P N (declared_sockets PD) e T t" using src by simp
    qed
  qed
  have "production_varied P N PD e T t = Some R'"
    by (simp add: production_varied_def Let_def srcs R production_carried_def R')
  then show "declared_production (produced_declarations_varied P N PD) e T t \<noteq> None"
    by (simp add: produced_declarations_varied_fields)
qed

section \<open>The narrowed frames along the match\<close>

text \<open>
  A narrowed frame is carried as B2b's frame is (@{thm [source] finite_schema_matched.socket_framed_matched}): the
  narrowing reads a true instance of T back through the binder map, and the framed obligation over the class is the
  frame's obligation read at the answers in the class, its frame mapped by the binder map.
\<close>

context finite_schema_matched
begin

theorem narrowed_socket_framed_matched:
  assumes src: "narrowed_socket_framed M S s keep Vp Vh K C"
    and sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and Vpf: "view_formed Vp" and Vhf: "view_formed Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "narrowed_socket_framed M' T (h s) keep Vp Vh K (f ` C)"
  unfolding narrowed_socket_framed_def socket_narrowing_def
proof (intro conjI allI impI)
  fix v d p xi yo
  assume vT: "clause_true M' (decode_finite_schema T) v" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
    and vp: "resolution_view_pattern Vp p = Some (xi,yo)"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_framed_def by fastforce
  have xy: "xi = map_finite_term_pattern f xi0" "yo = map_finite_term_pattern f yo0"
    using resolution_view_pattern_map[OF v0, of f] vp p0(2) by simp_all
  have vS: "clause_true M (decode_finite_schema S) (v \<circ> f)" using vT clause_true_along[OF eq] by blast
  have "K (evaluate_pattern (v \<circ> f) (decode_finite_pattern yo0))"
    using src vS p0(1) v0 unfolding narrowed_socket_framed_def socket_narrowing_def by blast
  then show "K (evaluate_pattern v (decode_finite_pattern yo))" by (simp add: xy evaluate_map_finite_pattern)
next
  fix d p assume at: "(h s,d,p) |\<in>| finite_schema_premises T"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_framed_def by fastforce
  show "resolution_view_pattern Vp p \<noteq> None" using resolution_view_pattern_map[OF v0, of f] p0(2) by simp
next
  fix v d p xi yo t y'
  assume vT: "clause_true M' (decode_finite_schema T) v" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
    and vp: "resolution_view_pattern Vp p = Some (xi,yo)" and dt: "(d,t) \<in> M'"
    and vt: "resolution_view_term Vp t = Some (evaluate_pattern v (decode_finite_pattern xi),y')" and n: "K y'"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_framed_def by fastforce
  have xy: "xi = map_finite_term_pattern f xi0" "yo = map_finite_term_pattern f yo0"
    using resolution_view_pattern_map[OF v0, of f] vp p0(2) by simp_all
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)"
    by (rule schema_dependencies_premise[of s d "decode_finite_pattern p0"]) (use p0(1) in \<open>auto simp: finite_premise_decoded\<close>)
  have dt0: "(d,t) \<in> M" using dt eq[OF dep] by simp
  have vS: "clause_true M (decode_finite_schema S) (v \<circ> f)" using vT clause_true_along[OF eq] by blast
  have vt0: "resolution_view_term Vp t = Some (evaluate_pattern (v \<circ> f) (decode_finite_pattern xi0),y')"
    using vt by (simp add: xy evaluate_map_finite_pattern)
  obtain h2 where h2: "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S (v \<circ> f) h2"
      "\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h2 a = (v \<circ> f) a"
      "evaluate_pattern h2 (decode_finite_pattern xi0) = evaluate_pattern (v \<circ> f) (decode_finite_pattern xi0)"
      "evaluate_pattern h2 (decode_finite_pattern yo0) = y'"
    using src vS p0(1) v0 dt0 vt0 n unfolding narrowed_socket_framed_def by blast
  have pv: "fset (finite_pattern_variables p0) \<subseteq> schema_variables (decode_finite_schema S)" by (rule call_scope[OF p0(1)])
  have xv: "fset (finite_pattern_variables xi0) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(1)[OF Vpf v0] pv by blast
  have yv: "fset (finite_pattern_variables yo0) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(2)[OF Vpf v0] pv by blast
  show "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T v h' \<and>
      (\<forall>a\<in>schema_variables (decode_finite_schema T) - f ` C. h' a = v a) \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern v (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = y'"
  proof (intro exI conjI)
    show "clause_true M' (decode_finite_schema T) (h2 \<circ> binder_inverse)" by (rule clause_true_back[OF eq h2(1)])
    show "head_kept keep Vh T v (h2 \<circ> binder_inverse)" by (rule head_kept_along[OF h2(2) Vhf])
    show "\<forall>a\<in>schema_variables (decode_finite_schema T) - f ` C. (h2 \<circ> binder_inverse) a = v a"
      by (rule frame_along[OF h2(3)])
    show "evaluate_pattern (h2 \<circ> binder_inverse) (decode_finite_pattern xi) = evaluate_pattern v (decode_finite_pattern xi)"
      using h2(4) by (simp add: xy evaluate_map_finite_pattern evaluate_back[OF xv])
    show "evaluate_pattern (h2 \<circ> binder_inverse) (decode_finite_pattern yo) = y'"
      using h2(5) by (simp add: xy evaluate_map_finite_pattern evaluate_back[OF yv])
  qed
next
  fix v N g
  assume vT: "clause_true M' (decode_finite_schema T) v"
    and at: "(h s,N) \<in> schema_material_premises (decode_finite_schema T)"
    and sat: "evaluate_material_satisfaction g N"
    and se: "evaluate_pattern g (material_source N) = evaluate_pattern v (material_source N)"
  obtain N0 where N0: "(s,N0) \<in> schema_material_premises (decode_finite_schema S)" "N = rename_material_pattern f N0"
    using material_at_image[OF sock at] .
  have vS: "clause_true M (decode_finite_schema S) (v \<circ> f)" using vT clause_true_along[OF eq] by blast
  have sat0: "evaluate_material_satisfaction (g \<circ> f) N0" using sat N0(2) evaluate_rename_material by blast
  have se0: "evaluate_pattern (g \<circ> f) (material_source N0) = evaluate_pattern (v \<circ> f) (material_source N0)"
    using se N0(2) by (simp add: rename_material_pattern_def evaluate_rename_pattern)
  obtain h2 where h2: "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S (v \<circ> f) h2"
      "\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h2 a = (v \<circ> f) a"
      "\<forall>a\<in>material_variables N0. h2 a = (g \<circ> f) a"
    using src vS N0(1) sat0 se0 unfolding narrowed_socket_framed_def by blast
  have mv: "material_variables N0 \<subseteq> schema_variables (decode_finite_schema S)"
    using N0(1) by (force simp: schema_variables_def)
  show "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T v h' \<and>
      (\<forall>a\<in>schema_variables (decode_finite_schema T) - f ` C. h' a = v a) \<and>
      (\<forall>a\<in>material_variables N. h' a = g a)"
  proof (intro exI conjI)
    show "clause_true M' (decode_finite_schema T) (h2 \<circ> binder_inverse)" by (rule clause_true_back[OF eq h2(1)])
    show "head_kept keep Vh T v (h2 \<circ> binder_inverse)" by (rule head_kept_along[OF h2(2) Vhf])
    show "\<forall>a\<in>schema_variables (decode_finite_schema T) - f ` C. (h2 \<circ> binder_inverse) a = v a"
      by (rule frame_along[OF h2(3)])
    show "\<forall>b\<in>material_variables N. (h2 \<circ> binder_inverse) b = g b"
    proof
      fix b assume "b \<in> material_variables N"
      then obtain a where a: "a \<in> material_variables N0" "b = f a" using N0(2) by (auto simp: renamed_material_variables)
      have "(h2 \<circ> binder_inverse) b = ((h2 \<circ> binder_inverse) \<circ> f) a" using a(2) by simp
      also have "\<dots> = h2 a" using inverse_agrees[of a h2] a(1) mv by blast
      also have "\<dots> = g b" using h2(4) a by simp
      finally show "(h2 \<circ> binder_inverse) b = g b" .
    qed
  qed
qed

end

text \<open>
  A narrowed frame family discharged at M is, varied, discharged at M' beside the varied narrowed record wherever the
  two mean the same at the record's sites and its sources' classes agree: a frame is carried only where its clause is
  the one clause of P at its site that the match reaches (@{const varied_unique}), else the socket is tested at its
  default frame, as B2b's frames are.
\<close>

theorem narrowed_frames_varied_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate ND) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and agree: "varied_narrowings_agree P N ND"
    and formed: "declarations_formed (resolution_declarations.truncate ND)"
    and frames: "narrowed_frames_discharged M (narrowed_declarations.truncate ND) \<Phi>"
  shows "narrowed_frames_discharged M' (narrowed_declarations_varied P N ND) (frames_varied P N \<Phi>)"
  unfolding narrowed_frames_discharged_def
proof (intro allI impI)
  fix e T t C' keep Vp Vh
  assume fr: "(e,T,t,C') |\<in>| frames_varied P N \<Phi>"
    and so: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations_varied P N ND)"
  obtain S1 s1 C c1 c1' f1 h1 where f1: "(e,S1,s1,C) |\<in>| \<Phi>" "((e,c1),S1) |\<in>| finite_system_clauses P"
      "s1 \<in> schema_sockets (decode_finite_schema S1)" "((e,c1'),T) |\<in>| finite_system_clauses N"
      "varied_unique P e S1 T" "finite_schema_match S1 T = Some (f1,h1)" "t = h1 s1" "C' = fimage f1 C"
    by (rule frames_varied_origin[OF fr])
  have so': "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N (resolution_declarations.truncate ND))"
    using so by (simp add: narrowed_declarations_varied_def)
  obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate ND)"
      "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
    using so'[unfolded declarations_varied_sockets_member] by blast
  have m1: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND" using m(1) by simp
  have S: "S = S1" using fbspec[OF f1(5)[unfolded varied_unique_def] m(2)] m(5) by simp
  have fh: "f1 = f" "h1 = h" using f1(6) m(5) S by simp_all
  interpret matched: finite_schema_matched S T f h
    by unfold_locales (rule finite_system_clause_formed[OF Pf m(2)], rule finite_system_clause_formed[OF Nf m(4)], rule m(5))
  have s: "s1 = s"
    by (rule inj_onD[OF matched.sockets]) (use f1(3) f1(7) m(3) m(6) S fh in simp_all)
  have fS: "(e,S,s,C) |\<in>| \<Phi>" using f1(1) S s by simp
  have src: "narrowed_socket_framed M S s keep Vp Vh (declared_narrowing ND e S s) (fset C)"
    using frames[unfolded narrowed_frames_discharged_def, rule_format, OF fS] m1 by simp
  have "fBall (declared_sockets (resolution_declarations.truncate ND)) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
    using formed by (simp add: declarations_formed_def)
  from fbspec[OF this m(1)] have views: "view_formed Vp" "view_formed Vh" by simp_all
  have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites (resolution_declarations.truncate ND)"
    by (rule declared_sites_members(5)[OF m(1)])
  have sources: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
    unfolding varied_socket_sources_member using m1 m(2-6) by blast
  have K: "declared_narrowing (narrowed_declarations_varied P N ND) e T t = declared_narrowing ND e S s"
    using narrowing_varied_source[OF agree sources] by (simp add: narrowed_declarations_varied_def)
  have C'': "fset C' = f ` fset C" using f1(8) fh by simp
  have "narrowed_socket_framed M' T (h s) keep Vp Vh (declared_narrowing ND e S s) (f ` fset C)"
    by (rule matched.narrowed_socket_framed_matched[OF src m(3) views]) (use at sub in blast)
  then show "narrowed_socket_framed M' T t keep Vp Vh (declared_narrowing (narrowed_declarations_varied P N ND) e T t) (fset C')"
  proof -
    have K': "declared_narrowing (narrowed_declarations_varied P N ND) e T (h s) = declared_narrowing ND e S s"
      using K m(6) by simp
    assume "narrowed_socket_framed M' T (h s) keep Vp Vh (declared_narrowing ND e S s) (f ` fset C)"
    then show ?thesis by (simp only: K' C'' m(6))
  qed
qed

section \<open>The premises stated once, and the committed forms at the varied narrowed record\<close>

text \<open>
  The locale holds the source's discharged record, frames and productions, the meanings agreeing at the record's sites
  and at the productions' sites, the sources' classes agreeing, the values at the carried registrations
  (@{const registration_values_carried}) and the varied record's static premise (@{const narrowed_productions_declared},
  derived by @{text narrowed_productions_declared_varied} under unique sources). From them the carried record, frames
  and productions are discharged at N, the exchange premise at N is R5f2's, and the forms at N are R5f2's named forms
  at the carried discharge. The native form is R5f2's @{thm [source] native_narrowed_resolution_exact} at the same three
  facts, once N is the native program type. A construction at N is any whose registrations are premise-only and whose
  lifts hold there; V1's varied construction is one wherever the source's is complete
  (@{text finite_varied_construction_conditions}, from @{thm [source] varied_construction_complete}).
\<close>

locale varied_narrowed_record =
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations" and corr :: "'d \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool"
    and \<Phi> :: "('a,'s,'d) resolution_frames" and m m' :: nat
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and at_productions: "\<And>e S s keep Vp Vh R x. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow>
      (registration_site R,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow>
        (registration_site R,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m PD"
    and values_at: "\<And>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> registration_values_carried P m N m' R"
    and declared': "narrowed_productions_declared (produced_declarations_varied P N PD)"
begin

lemma formed: "declarations_formed (resolution_declarations.truncate PD)"
  using discharged by (simp add: narrowed_declarations_discharged_def)

lemma carried:
  assumes "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "declared_production PD e S s = Some R"
    "R' |\<in>| registrations_varied P N R"
  shows "production_values_carried (finite_collection_construction [R] m) P (finite_collection_construction [R'] m') N R"
  by (rule production_values_carried_collection[OF values_at[OF assms(1,2)] assms(3)])

lemma discharged_varied: "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
    (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
  using narrowed_declarations_varied_discharged[OF Pf Nf at agree discharged]
  by (simp add: produced_declarations_varied_truncate)

lemma frames_varied_at: "narrowed_frames_discharged (positive_meaning (decode_finite_system N))
    (narrowed_declarations.truncate (produced_declarations_varied P N PD)) (frames_varied P N \<Phi>)"
  using narrowed_frames_varied_discharged[OF Pf Nf at agree formed frames]
  by (simp add: produced_declarations_varied_truncate)

lemma productions_varied_at:
  "productions_discharged (positive_meaning (decode_finite_system N)) N m' (produced_declarations_varied P N PD)"
  by (rule productions_discharged_varied[OF Pf Nf at_productions agree formed productions carried])

theorem finite_varied_narrowed_commitment_exchanges:
  assumes \<kappa>': "finite_witness_construction_formed \<kappa>'" and only': "finite_registrations_premise_only \<kappa>' N"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
    (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) (frames_varied P N \<Phi>)) N"
  by (rule finite_narrowed_commitment_exchanges[OF \<kappa>' discharged_varied frames_varied_at productions_varied_at
    declared' only'])

lemmas finite_varied_narrowed_refutation_exact =
  finite_narrowed_refutation_exact[OF _ discharged_varied frames_varied_at productions_varied_at declared']
lemmas finite_varied_narrowed_verdict_exact =
  finite_narrowed_verdict_exact[OF _ discharged_varied frames_varied_at productions_varied_at declared']
lemmas finite_varied_narrowed_demand_exact =
  finite_narrowed_demand_exact[OF _ discharged_varied frames_varied_at productions_varied_at declared']
lemmas finite_varied_narrowed_forms_exact = finite_varied_narrowed_refutation_exact
  finite_varied_narrowed_verdict_exact finite_varied_narrowed_demand_exact

text \<open>
  The transfer: a program and its alpha-variant presentation give the same committed verdict at records with narrowed
  sockets and productions, each verdict being the call's meaning in its own program (R5f2's form at P, and at N at the
  carried record and frames).
\<close>

theorem finite_committed_variant_transfer_narrowed:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and declared: "narrowed_productions_declared PD"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and only': "finite_registrations_premise_only \<kappa>' N" and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m PD \<Phi>) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>'
      (finite_narrowed_commitment N m' (produced_declarations_varied P N PD) (frames_varied P N \<Phi>)) N d t n') = Some b'"
  shows "b = b'"
proof -
  have "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    by (rule finite_narrowed_verdict_exact[OF \<kappa> discharged frames productions declared only cl v])
  moreover have "b' \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system N)"
    by (rule finite_varied_narrowed_verdict_exact[OF \<kappa>' only' cl' v'])
  ultimately show ?thesis using system_alpha_positive_meaning[OF alpha] by simp
qed

end

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

section \<open>At records declaring no narrowing and no production\<close>

text \<open>
  The varied record is V2a's there, and R5f2's commitment the framed one (@{thm [source] finite_unproduced_commitment}),
  so the locale's transfer at such a record is the framed transfer at V2a's record and B2b's frames.
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
