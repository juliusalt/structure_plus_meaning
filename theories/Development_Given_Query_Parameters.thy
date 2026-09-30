theory Development_Given_Query_Parameters
  imports Factor_Committing_Query_Parameters Development_Given_Productions Development_Given_Modes
    Development_Given_Installed_Productions Development_Rooted_Registrations Development_First_Request_Registrations
begin

section \<open>The given's committing instance\<close>

text \<open>
  The given's input record (@{const given_input_declarations}) and frames (@{const given_input_frames}) at the rooted
  readers, the check forms' program, with the given's modes (@{const given_modes}): the ground part as the check forms
  use it (@{text Development_Given_Declarations_Execution}), the lifted part the record varied along the query program's
  left injection, its commitment the root-kept restriction.
\<close>

abbreviation given_query_program :: "(nat+'v,nat,nat,nat) finite_schema_system" where
  "given_query_program \<equiv> finite_query_program finite_rooted_given_readers"

abbreviation given_query_parameters ::
    "nat \<Rightarrow> (nat,nat,nat,nat) resolution_table \<Rightarrow> (nat+'v,nat,nat,nat) resolution_table \<Rightarrow>
      (nat,nat,nat,nat,'v) query_parameters" where
  "given_query_parameters m \<Theta> \<Theta>' \<equiv> committing_query_parameters finite_rooted_given_readers m given_input_declarations
    given_input_frames given_modes \<Theta> \<Theta>'"

text \<open>
  The given's input record at the rooted readers is discharged there (#815's and #817's record, #782's overridden at
  12's lookup socket by its input production, @{thm [source]
  given_input_declarations_discharged}, @{thm [source] given_input_frames_discharged}, @{thm [source]
  given_input_declarations_productions}), and the query program means what the rooted readers mean
  (@{thm [source] finite_query_program_meaning}). The record carried along the left injection is therefore V2b's carried
  record there (@{text varied_narrowed_record}) wherever three conditions of the carrying hold at the query program:
  its sources' narrowings agree, its productions stay discharged, and every narrowed socket keeps a production.
\<close>

theorem given_query_record_from:
  assumes agree: "varied_narrowings_agree finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) given_input_declarations"
    and varied: "productions_discharged (positive_meaning (decode_finite_system (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)))
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) m
      (produced_declarations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
        given_input_declarations)"
    and declared': "narrowed_productions_declared (produced_declarations_varied finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) given_input_declarations)"
  shows "varied_narrowed_record finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
    given_input_declarations given_declarations_correspondence given_input_frames m m"
proof (rule varied_narrowed_record.intro, goal_cases)
  case 1 show ?case by (rule finite_rooted_given_readers_formed)
next
  case 2 show ?case by (rule finite_query_program_formed[OF finite_rooted_given_readers_formed])
next
  case (3 d x) show ?case by (simp only: finite_query_program_meaning[OF finite_rooted_given_readers_formed])
next
  case 4 show ?case by (rule agree)
next
  case 5 show ?case using given_input_declarations_discharged(1) by (simp add: finite_rooted_given_readers_exact)
next
  case 6 show ?case using given_input_frames_discharged by (simp add: finite_rooted_given_readers_exact)
next
  case 7 show ?case by (rule given_input_declarations_productions)
next
  case 8 show ?case by (rule varied)
next
  case 9 show ?case by (rule declared')
qed

section \<open>The given's record carried to the query program\<close>

text \<open>
  The given's input record carried along the left injection as #798 and #817 carried it to the installed programs, by the clause
  match (V2a–V2b). The query program's clauses at a definition are the rooted readers' clauses there, their variables
  lifted by @{const Inl}; a clause and its lifting match. Where the rooted readers have one clause, so has the query
  program, and a registration there varies to one registration; at 48's callers two clauses of one definition with the
  same callees are one (@{thm [source] given_union_site_distinct}), and a match keeps the callees.
\<close>

lemma query_program_clauses:
  "((d,a),Z) |\<in>| finite_system_clauses (finite_query_program P :: ('a+'v,'s,'d,'c) finite_schema_system) \<longleftrightarrow>
    (\<exists>S. ((d,a),S) |\<in>| finite_system_clauses P \<and> Z = finite_rename_schema Inl id id S)"
  unfolding finite_query_program_def by (force simp: fimage_iff fBex_member_iff)

lemma rooted_clause_decoded:
  "((d,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
    ((d,c),decode_finite_schema S) \<in> system_clauses given_rooted_readers_system"
  by (simp only: finite_system_clause_decoded finite_rooted_given_readers_exact)

theorem query_single_clause:
  assumes one: "\<And>c S. ((d,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema X"
  shows "((d,a),Z) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow> a = 0 \<and> Z = X"
    and "((d,b),W) |\<in>| finite_system_clauses (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) \<longleftrightarrow>
      b = 0 \<and> W = finite_rename_schema Inl id id X"
    and "\<exists>f h. finite_schema_match X (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema) = Some (f,h)"
    and "finite_varied_sources_unique_at {d} finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)"
proof -
  have P: "((d,a),Z) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow> a = 0 \<and> Z = X" for a Z
    by (simp only: rooted_clause_decoded one decode_finite_schema_injective)
  have N: "((d,a),Z) |\<in>| finite_system_clauses (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) \<longleftrightarrow>
      a = 0 \<and> Z = finite_rename_schema Inl id id X" for a Z
    by (auto simp: query_program_clauses P)
  show "((d,a),Z) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow> a = 0 \<and> Z = X" by (rule P)
  show "((d,b),W) |\<in>| finite_system_clauses (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) \<longleftrightarrow>
      b = 0 \<and> W = finite_rename_schema Inl id id X" by (rule N)
  have Xf: "finite_schema_formed X"
    by (rule finite_system_clause_formed[OF finite_rooted_given_readers_formed, where e=d and c=0]) (simp add: P)
  have Tf: "finite_schema_formed (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema)"
    by (rule finite_system_clause_formed[OF finite_query_program_formed[OF finite_rooted_given_readers_formed],
      where e=d and c=0]) (simp add: N)
  have alpha: "schema_alpha_variant (decode_finite_schema X)
      (decode_finite_schema (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema))"
    unfolding finite_rename_schema_correct schema_alpha_variant_def
    by (intro exI[of _ Inl] exI[of _ id]) (simp add: inj_on_def)
  have "finite_schema_match X (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema) \<noteq> None"
    by (rule finite_schema_match_complete[OF Xf Tf alpha])
  then show "\<exists>f h. finite_schema_match X (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema) =
      Some (f,h)" by (metis not_None_eq surj_pair)
  show "finite_varied_sources_unique_at {d} finite_rooted_given_readers
      (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)"
    unfolding finite_varied_sources_unique_at_def by (auto simp: P)
qed

lemma query_single_registration:
  assumes one: "\<And>c S. ((d,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema X"
    and at: "registration_site R = d" "registration_schema R = X"
  obtains f1 h1 where
    "finite_schema_match X (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema) = Some (f1,h1)"
    "registrations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) R =
      {|registration_varied f1 (finite_rename_schema Inl id id X) R|}"
proof -
  obtain f1 h1 where m:
      "finite_schema_match X (finite_rename_schema Inl id id X :: (nat+'v,nat,nat) finite_factor_schema) = Some (f1,h1)"
    using query_single_clause(3)[OF one] by blast
  have "registrations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) R =
      {|registration_varied f1 (finite_rename_schema Inl id id X) R|}"
    by (rule fset_eqI) (auto simp: registrations_varied_member at query_single_clause(1,2)[OF one] m)
  then show ?thesis by (rule that[OF m])
qed

theorem query_union_sources:
  "finite_varied_sources_unique_at {50,55,57,60,63} finite_rooted_given_readers
    (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)"
  unfolding finite_varied_sources_unique_at_def
proof (intro allI impI)
  fix e c S c' S' c'' T f h f' h'
  assume e: "e \<in> {50,55,57,60,63}"
    and S: "((e,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    and S': "((e,c'),S') |\<in>| finite_system_clauses finite_rooted_given_readers"
    and T: "((e,c''),T) |\<in>| finite_system_clauses (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)"
    and m: "finite_schema_match S T = Some (f,h)" and m': "finite_schema_match S' T = Some (f',h')"
  have Sf: "finite_schema_formed S" "finite_schema_formed S'"
    using finite_system_clause_formed[OF finite_rooted_given_readers_formed S]
      finite_system_clause_formed[OF finite_rooted_given_readers_formed S'] by blast+
  have Tf: "finite_schema_formed T"
    by (rule finite_system_clause_formed[OF finite_query_program_formed[OF finite_rooted_given_readers_formed] T])
  have TS: "T = finite_rename_schema f h id S" "T = finite_rename_schema f' h' id S'"
    using finite_schema_match_exact(1)[OF Sf(1) Tf m] finite_schema_match_exact(1)[OF Sf(2) Tf m'] by blast+
  have "schema_dependencies (decode_finite_schema T) = schema_dependencies (decode_finite_schema S)"
    "schema_dependencies (decode_finite_schema T) = schema_dependencies (decode_finite_schema S')"
    by (subst TS(1), simp add: finite_rename_schema_correct renamed_schema_dependencies)
      (subst TS(2), simp add: finite_rename_schema_correct renamed_schema_dependencies)
  then have deps: "schema_dependencies (decode_finite_schema S) = schema_dependencies (decode_finite_schema S')"
    by simp
  have rc: "((e,c),decode_finite_schema S) \<in> system_clauses given_rooted_readers_system"
    "((e,c'),decode_finite_schema S') \<in> system_clauses given_rooted_readers_system"
    using S S' by (simp_all only: rooted_clause_decoded)
  have "decode_finite_schema S = decode_finite_schema S'" by (rule given_union_site_distinct[OF e rc deps])
  then show "S = S'" by (simp only: decode_finite_schema_injective)
qed

text \<open>The record narrows at 48's callers alone: 48's sockets in #782's record, and 37's socket not at all.\<close>

lemma given_declarations_within: "narrowings_within {50,55,57,60,63} given_declarations"
  unfolding narrowings_within_def
proof (intro allI impI)
  fix e S s keep Vp Vh
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations" and out: "e \<notin> {50,55,57,60,63}"
  show "declared_narrowing given_declarations e S s = (\<lambda>_. True)"
  proof (rule ccontr)
    assume n: "declared_narrowing given_declarations e S s \<noteq> (\<lambda>_. True)"
    show False using out given_union_sites[OF given_declarations_at_union(1)[OF m disjI1[OF n]]] by blast
  qed
qed

lemma given_input_declarations_within: "narrowings_within {50,55,57,60,63} given_input_declarations"
  unfolding given_input_declarations_def
  by (rule produced_override_within[OF given_declarations_within]) (simp add: narrowings_within_def)

text \<open>A producing socket of the record is one of 48's, producing 48's registration, or 37's, producing 12's input.\<close>

lemma given_input_production:
  assumes m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_input_declarations"
    and p: "declared_production given_input_declarations e S s = Some R"
  shows "(e \<in> {50,55,57,60,63} \<and> Vp = join_view \<and> R = union_registration \<and>
      declared_narrowing given_input_declarations e S s = union_class) \<or>
    (e = 37 \<and> Vp = view_identity \<and> R = identity_input_registration)"
proof (cases "socket_keyed (resolution_declarations.truncate lookup_input_declarations) e S s")
  case True
  have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets lookup_input_declarations"
    using m True unfolding given_input_declarations_def produced_override_sockets by blast
  then show ?thesis using p True by (simp add: given_input_declarations_def)
next
  case False
  have mg: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    using m False unfolding given_input_declarations_def produced_override_sockets
    by (auto simp: socket_keyed_iff)
  have pg: "declared_production given_declarations e S s = Some R"
    using p False by (simp add: given_input_declarations_def)
  have ng: "declared_narrowing given_input_declarations e S s = declared_narrowing given_declarations e S s"
    using False by (simp add: given_input_declarations_def)
  have pn: "declared_production given_declarations e S s \<noteq> None" using pg by simp
  note u = given_declarations_at_union[OF mg disjI2[OF pn]]
  have u1: "(e,S,s,keep,Vp,Vh) |\<in>| given_union_sockets" and u2: "declared_narrowing given_declarations e S s = union_class"
    and u3: "declared_production given_declarations e S s = Some union_registration"
    using u pg by simp_all
  show ?thesis using given_union_sites[OF u1] given_union_socket_views[OF u1] u2 u3 pg ng by simp
qed

theorem given_query_agree:
  "varied_narrowings_agree finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
    given_input_declarations"
  by (rule varied_narrowings_agree_within[OF finite_rooted_given_readers_formed
    finite_query_program_formed[OF finite_rooted_given_readers_formed] query_union_sources
    given_input_declarations_within])

theorem given_query_carry:
  "productions_carry_uniquely finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
    given_input_declarations"
  unfolding productions_carry_uniquely_def
proof (intro allI impI)
  fix e S s keep Vp Vh R
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_input_declarations"
    and p: "declared_production given_input_declarations e S s = Some R"
  show "\<exists>R'. registrations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
      R = {|R'|}"
    using given_input_production[OF m p]
  proof
    assume "e \<in> {50,55,57,60,63} \<and> Vp = join_view \<and> R = union_registration \<and>
      declared_narrowing given_input_declarations e S s = union_class"
    then have Rr: "R = union_registration" by blast
    obtain f1 h1 where "registrations_varied finite_rooted_given_readers
        (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) R =
        {|registration_varied f1 (finite_rename_schema Inl id id union_schema) R|}"
      by (rule query_single_registration[OF union_rooted_clause, of R]) (simp_all add: Rr union_registration_def)
    then show ?thesis by blast
  next
    assume "e = 37 \<and> Vp = view_identity \<and> R = identity_input_registration"
    then have Rr: "R = identity_input_registration" by blast
    obtain f1 h1 where "registrations_varied finite_rooted_given_readers
        (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) R =
        {|registration_varied f1 (finite_rename_schema Inl id id identity_socket_schema) R|}"
      by (rule query_single_registration[OF identity_rooted_clause, of R])
        (simp_all add: Rr identity_input_registration_fields)
    then show ?thesis by blast
  qed
qed

theorem given_query_declared:
  "narrowed_productions_declared (produced_declarations_varied finite_rooted_given_readers
    (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) given_input_declarations)"
  by (rule narrowed_productions_declared_varied_within[OF finite_rooted_given_readers_formed
    finite_query_program_formed[OF finite_rooted_given_readers_formed] query_union_sources
    given_input_declarations_within given_input_declarations_discharged(3) given_query_carry])

text \<open>
  The productions at the query program, as at the installed programs (@{text installed_productions},
  @{text installed_lookup_productions}): 48's registration varied to 48's one lifted clause produces the union class
  and answers there, from the union's and selection's meanings; 12's input registration varied to 12's one lifted
  clause is an input registration, 12 reflexive there.
\<close>

theorem given_query_productions:
  "productions_discharged (positive_meaning (decode_finite_system (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)))
    (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) m
    (produced_declarations_varied finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
      given_input_declarations)"
proof (rule input_productions_discharged)
  let ?P = finite_rooted_given_readers
  let ?N = "given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system"
  let ?D = "produced_declarations_varied ?P ?N given_input_declarations"
  fix e T t keep Vp Vh R'
  assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets ?D" and p: "declared_production ?D e T t = Some R'"
  obtain S s where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_input_declarations"
      and src: "(S,s) |\<in>| varied_socket_sources ?P ?N (declared_sockets given_input_declarations) e T t"
    using mem unfolding produced_varied_sockets_member by blast
  obtain R where R: "declared_production given_input_declarations e S s = Some R" "registrations_varied ?P ?N R = {|R'|}"
    using production_varied_source[OF p[unfolded produced_declarations_varied_fields] src] by blast
  have K: "declared_narrowing ?D e T t = declared_narrowing given_input_declarations e S s"
    using narrowing_varied_source[OF given_query_agree src] by (simp add: produced_declarations_varied_fields)
  have mean48: "(48,x) \<in> positive_meaning (decode_finite_system ?N) \<longleftrightarrow> (48,x) \<in> positive_meaning data_union_system" for x
    using given_rooted_union_meanings(1)[of x]
    by (simp add: finite_query_program_meaning[OF finite_rooted_given_readers_formed] finite_rooted_given_readers_exact)
  have mean5: "(5,x) \<in> positive_meaning (decode_finite_system ?N) \<longleftrightarrow> (5,x) \<in> positive_meaning bag_comparison_system" for x
    using given_rooted_union_meanings(2)[of x]
    by (simp add: finite_query_program_meaning[OF finite_rooted_given_readers_formed] finite_rooted_given_readers_exact)
  show "(R' = input_registration (registration_site R') (registration_schema R') Vp (registration_variable R') \<and>
        head_registration Vp (registration_schema R') (registration_variable R') \<and>
        producer_reflexive (positive_meaning (decode_finite_system ?N)) (registration_site R') Vp \<and>
        (\<forall>x. declared_narrowing ?D e T t x)) \<or>
      (head_registration Vp (registration_schema R') (registration_variable R') \<and>
        head_registration_produces (finite_collection_construction [R'] m) ?N (registration_site R')
          (registration_schema R') (registration_variable R') (declared_narrowing ?D e T t) \<and>
        head_registration_answers (positive_meaning (decode_finite_system ?N)) (finite_collection_construction [R'] m) ?N
          (registration_site R') (registration_schema R') Vp (registration_variable R'))"
    using given_input_production[OF m R(1)]
  proof
    assume u: "e \<in> {50,55,57,60,63} \<and> Vp = join_view \<and> R = union_registration \<and>
      declared_narrowing given_input_declarations e S s = union_class"
    have Rr: "R = union_registration" and V: "Vp = join_view" using u by blast+
    have Kun: "declared_narrowing ?D e T t = union_class" using K u by simp
    let ?T = "finite_rename_schema Inl id id union_schema :: (nat+'v,nat,nat) finite_factor_schema"
    obtain f1 h1 where mt: "finite_schema_match union_schema ?T = Some (f1,h1)"
        and rv: "registrations_varied ?P ?N R = {|registration_varied f1 ?T R|}"
      by (rule query_single_registration[OF union_rooted_clause, of R]) (simp_all add: Rr union_registration_def)
    have Sf: "finite_schema_formed union_schema"
      by (rule finite_system_clause_formed[OF finite_rooted_given_readers_formed, where e=48 and c=0])
        (simp add: query_single_clause(1)[OF union_rooted_clause])
    have Tf: "finite_schema_formed ?T"
      by (rule finite_system_clause_formed[OF finite_query_program_formed[OF finite_rooted_given_readers_formed],
        where e=48 and c=0]) (simp add: query_single_clause(2)[OF union_rooted_clause])
    note mx = finite_schema_match_exact(1)[OF Sf Tf mt]
    have TT: "?T = finite_rename_schema f1 h1 id union_schema" using mx by blast
    have "{0,1,2} \<subseteq> schema_variables data_union_schema" by (auto simp: schema_variables_def data_union_schema_def)
    then have vars: "{0,1,2} \<subseteq> schema_variables (decode_finite_schema union_schema)" by (simp only: union_schema_decoded)
    have inj: "inj_on f1 {0,1,2}" by (rule inj_on_subset[OF conjunct1[OF mx] vars])
    have R1: "R' = registration_varied f1 ?T R" using R(2) rv by simp
    have R3: "R' = union_registration_at 48 5 ?T (f1 2) (f1 0) (f1 1)"
      unfolding R1 Rr
      by (simp add: registration_varied_def union_registration_def union_registration_at_def union_family_def
        union_family_at_def union_query_def union_query_at_def map_collection_family_def map_collection_query_def)
    show ?thesis
      unfolding R3 union_registration_at_fields Kun V TT
      by (intro disjI2 conjI union_variant_head_registration[OF inj] union_at_registration_produces
        union_at_registration_answers[OF mean48 mean5 union_variant_input])
  next
    assume u: "e = 37 \<and> Vp = view_identity \<and> R = identity_input_registration"
    have Rr: "R = identity_input_registration" and V: "Vp = view_identity" and e37: "e = 37" using u by blast+
    let ?T = "finite_rename_schema Inl id id identity_socket_schema :: (nat+'v,nat,nat) finite_factor_schema"
    obtain f1 h1 where mt: "finite_schema_match identity_socket_schema ?T = Some (f1,h1)"
        and rv: "registrations_varied ?P ?N R = {|registration_varied f1 ?T R|}"
      by (rule query_single_registration[OF identity_rooted_clause, of R])
        (simp_all add: Rr identity_input_registration_fields)
    have Sf: "finite_schema_formed identity_socket_schema"
      by (rule finite_system_clause_formed[OF finite_rooted_given_readers_formed, where e=12 and c=0])
        (simp add: query_single_clause(1)[OF identity_rooted_clause])
    have Tf: "finite_schema_formed ?T"
      by (rule finite_system_clause_formed[OF finite_query_program_formed[OF finite_rooted_given_readers_formed],
        where e=12 and c=0]) (simp add: query_single_clause(2)[OF identity_rooted_clause])
    interpret matched: finite_schema_matched identity_socket_schema ?T f1 h1
      by (rule finite_schema_matched.intro[OF Sf Tf mt])
    have head: "head_registration view_identity identity_socket_schema 1" by (rule identity_input_registration_head)
    have R1: "R' = registration_varied f1 ?T R" using R(2) rv by simp
    have R'': "R' = input_registration 12 ?T view_identity (f1 1)"
      unfolding R1 Rr identity_input_registration_def by (rule matched.input_registration_varied[OF head])
    have headT: "head_registration view_identity ?T (f1 1)" by (rule matched.head_registration_matched[OF head])
    have refl: "producer_reflexive (positive_meaning (decode_finite_system ?N)) 12 view_identity"
      using given_rooted_identity_reflexive
      by (simp only: finite_query_program_meaning[OF finite_rooted_given_readers_formed])
    have true: "declared_narrowing given_input_declarations e S s = (\<lambda>_. True)"
      using given_input_declarations_within[unfolded narrowings_within_def, rule_format, OF m] e37 by simp
    have narrowing: "\<forall>x. declared_narrowing ?D e T t x" using K true by simp
    show ?thesis unfolding R'' V using headT refl narrowing by (simp add: input_registration_def)
  qed
qed

theorem given_query_record:
  "varied_narrowed_record finite_rooted_given_readers (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system)
    given_input_declarations given_declarations_correspondence given_input_frames m m"
  by (rule given_query_record_from[OF given_query_agree given_query_productions given_query_declared])

section \<open>W5's premise at the given's committing instance\<close>

theorem given_query_exact:
  assumes true: "finite_table_true finite_rooted_given_readers \<Theta>"
    and true': "finite_table_true (given_query_program :: (nat+'v,nat,nat,nat) finite_schema_system) \<Theta>'"
  shows "finite_query_exact (given_query_parameters m \<Theta> \<Theta>' :: (nat,nat,nat,nat,'v) query_parameters)
    finite_rooted_given_readers n"
  by (rule committing_query_exact[OF given_query_record given_input_declarations_discharged(3) true true'])

section \<open>The registrations' completeness at a committing instance\<close>

text \<open>
  W4a's completeness at a query's parameters (W5's forms) holds wherever @{const finite_query_exact} does, so at a
  committing instance each is its form composed with @{thm [source] committing_query_exact}: at the given's committing
  instance for the rooted readers, at true tables alone, and at a committing instance of a record carried to the
  given's readers or to the first request's program, its carried record the premise.
\<close>

lemmas given_rooted_registrations_committing = given_rooted_registrations_complete_in[OF given_query_exact]
lemmas given_rooted_construction_committing = given_rooted_construction_complete_in[OF given_query_exact]
lemmas given_witness_registrations_committing = given_witness_registrations_complete_in[OF given_query_exact]
lemmas given_readers_registrations_committing = given_readers_registrations_complete_in[OF committing_query_exact]
lemmas given_readers_construction_committing = given_readers_construction_complete_in[OF committing_query_exact]
lemmas readers_agreement_registrations_committing = readers_agreement_registrations_complete_in[OF committing_query_exact]
lemmas first_request_registrations_committing = first_request_registrations_complete_in[OF committing_query_exact]
lemmas first_request_construction_committing = first_request_construction_complete_in[OF committing_query_exact]

end
