theory Factor_Resolution_Views
  imports Factor_Resolution_Socket_Discharges Factor_Least_Witness_Registrations
begin

section \<open>The committed forms exact under discharged declarations\<close>

text \<open>
  The discharges of #565's exchange premise (@{text finite_declared_commitment_exchanges}: the direct producer, the
  kept-head and free sockets, the material single solution, each at the states the declared test commits in) make the
  three committed forms exact under the declarations' discharge alone, at any declared views, at a program whose
  registrations are premise-only and a construction that lifts. Each form is R5's (@{text finite_committed_verdict_exact}
  and its siblings) with its exchange premise given by that discharge; nothing is proved again. The identity and swap
  views (@{const pair_declarations}) are an instance, with no form of their own.
\<close>

theorem finite_declared_refutation_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and refutes: "finite_resolution_refutes (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_resolution_refutation_exact[OF \<kappa>
    finite_declared_commitment_exchanges[OF \<kappa> discharged only] constructions refutes])

theorem finite_declared_verdict_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and verdict: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_verdict_exact[OF \<kappa>
    finite_declared_commitment_exchanges[OF \<kappa> discharged only] constructions verdict])

theorem finite_declared_demand_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "finite_committed_demand \<kappa> (finite_declared_commitment D) P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_committed_demand_exact[OF \<kappa> finite_declared_commitment_exchanges[OF \<kappa> discharged only]
    constructions result] by blast+

theorem native_declared_resolution_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "native_committed_resolution \<kappa> (finite_declared_commitment D) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_resolution_exact[OF \<kappa> finite_declared_commitment_exchanges[OF \<kappa> discharged only]
    constructions result] by blast+

text \<open>The four forms as one fact, for the route's consumers.\<close>

lemmas finite_declared_forms_exact = finite_declared_refutation_exact finite_declared_verdict_exact
  finite_declared_demand_exact native_declared_resolution_exact

section \<open>The transfer of declarations\<close>

text \<open>
  A relocation by a map on sites relocates a record: its producers and consumers by the map, a socket's site by the
  map and its schema with its callees as @{const finite_rename_system} relocates the program's clauses, its socket,
  the kept head and every view as they were. A record's declared sites are its producers, both sites of its
  consumers, its sockets' sites and their schemas' callees; its obligations read its producers, its consumers' own
  sites and its sockets' callees alone. The transfer holds at any views.
\<close>

definition declarations_relocated ::
    "('d \<Rightarrow> 'e) \<Rightarrow> ('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'e) resolution_declarations" where
  "declarations_relocated g D = \<lparr>declared_producers = fimage (\<lambda>(d,V,hs). (g d,V,hs)) (declared_producers D),
    declared_consumers = fimage (\<lambda>(d,e,V,i). (g d,g e,V,i)) (declared_consumers D),
    declared_sockets = fimage (\<lambda>(e,S,s,keep,Vp,Vh). (g e,finite_rename_schema id id g S,s,keep,Vp,Vh))
      (declared_sockets D)\<rparr>"

definition declared_sites :: "('a,'s,'d) resolution_declarations \<Rightarrow> 'd set" where
  "declared_sites D = fst ` fset (declared_producers D) \<union> (\<Union>(d,e,V,i)\<in>fset (declared_consumers D). {d,e}) \<union>
    (\<Union>(e,S,s,keep,Vp,Vh)\<in>fset (declared_sockets D). insert e (schema_dependencies (decode_finite_schema S)))"

lemma declarations_formed_relocated: "declarations_formed D \<Longrightarrow> declarations_formed (declarations_relocated g D)"
  unfolding declarations_formed_def declarations_relocated_def by auto

text \<open>
  A clause and a socket's obligation read the meaning only at the clause's callees: relocating the callees, where the
  meaning at each relocated callee is the meaning at the callee, keeps both. The identity relocation is the case of two
  meanings agreeing at the callees.
\<close>

lemma clause_true_relocated:
  assumes eq: "\<And>d x. d \<in> schema_dependencies S \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "clause_true M' (rename_schema id id g S) h \<longleftrightarrow> clause_true M S h"
proof -
  let ?R = "rename_schema id id g S"
  have prem: "(q,e,p) \<in> schema_premises ?R \<longleftrightarrow> (\<exists>d. (q,d,p) \<in> schema_premises S \<and> e = g d)" for q e p
    by (auto simp: rename_schema_def map_socket_graph_member)
  have mat: "schema_material_premises ?R = schema_material_premises S"
  proof -
    have "schema_material_premises ?R = schema_material_premises (rename_schema id id id S)"
      by (simp add: rename_schema_def)
    then show ?thesis by simp
  qed
  have vars: "schema_variables ?R = schema_variables S" by (simp add: renamed_schema_variables)
  have calls: "(\<forall>q e p. (q,e,p) \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern h p) \<in> M') \<longleftrightarrow>
      (\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern h p) \<in> M)"
  proof
    assume A: "\<forall>q e p. (q,e,p) \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern h p) \<in> M'"
    show "\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern h p) \<in> M"
    proof (intro allI impI)
      fix q d p assume qd: "(q,d,p) \<in> schema_premises S"
      have "(q,g d,p) \<in> schema_premises ?R" using qd prem by blast
      then have "(g d,evaluate_pattern h p) \<in> M'" using A by blast
      then show "(d,evaluate_pattern h p) \<in> M" using eq[OF schema_dependencies_premise[OF qd]] by simp
    qed
  next
    assume B: "\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern h p) \<in> M"
    show "\<forall>q e p. (q,e,p) \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern h p) \<in> M'"
    proof (intro allI impI)
      fix q e p assume qe: "(q,e,p) \<in> schema_premises ?R"
      then obtain d where qd: "(q,d,p) \<in> schema_premises S" and e: "e = g d" using prem by blast
      have "(d,evaluate_pattern h p) \<in> M" using B qd by blast
      then show "(e,evaluate_pattern h p) \<in> M'" using eq[OF schema_dependencies_premise[OF qd]] e by simp
    qed
  qed
  show ?thesis unfolding clause_true_def by (simp only: vars mat calls)
qed

text \<open>
  A socket's obligation, at its views, carries to a schema whose premises are the source's with their callees
  relocated, whose head and material premises are the source's, and whose clause truth is the source's: the obligation
  reads the premise and the head through the same views, and the meaning at the callees alone.
\<close>

lemma socket_discharged_callees:
  assumes src: "socket_discharged M S s keep Vp Vh"
    and prem: "\<And>q e p. (q,e,p) |\<in>| finite_schema_premises R \<longleftrightarrow>
      (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d)"
    and conc: "finite_schema_conclusion R = finite_schema_conclusion S"
    and mat: "schema_material_premises (decode_finite_schema R) = schema_material_premises (decode_finite_schema S)"
    and ct: "\<And>h. clause_true M' (decode_finite_schema R) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "socket_discharged M' R s keep Vp Vh"
proof -
  have hk: "head_kept keep Vh R h h' \<longleftrightarrow> head_kept keep Vh S h h'" for h h' unfolding head_kept_def conc ..
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)" if "(q,d,p) |\<in>| finite_schema_premises S" for q d p
    by (rule schema_dependencies_premise[of q d "decode_finite_pattern p"]) (use that in \<open>auto simp: finite_premise_decoded\<close>)
  show ?thesis unfolding socket_discharged_def
  proof (intro conjI allI impI)
    fix d p assume "(s,d,p) |\<in>| finite_schema_premises R"
    then obtain d0 where "(s,d0,p) |\<in>| finite_schema_premises S" using prem by blast
    then show "resolution_view_pattern Vp p \<noteq> None" using src unfolding socket_discharged_def by blast
  next
    fix h d p xi yo t y'
    assume h: "clause_true M' (decode_finite_schema R) h" and p: "(s,d,p) |\<in>| finite_schema_premises R"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)" and a: "(d,t) \<in> M'"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')"
    from p obtain d0 where p0: "(s,d0,p) |\<in>| finite_schema_premises S" and d: "d = g d0" using prem by blast
    have a0: "(d0,t) \<in> M" using a eq[OF dep[OF p0]] d by simp
    have hS: "clause_true M (decode_finite_schema S) h" using h ct by simp
    obtain h2 where "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S h h2"
        "evaluate_pattern h2 (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
        "evaluate_pattern h2 (decode_finite_pattern yo) = y'"
      using src hS p0 v a0 vt unfolding socket_discharged_def by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'"
      using ct hk by blast
  next
    fix h N v
    assume h: "clause_true M' (decode_finite_schema R) h"
      and m: "(s,N) \<in> schema_material_premises (decode_finite_schema R)"
      and sat: "evaluate_material_satisfaction v N"
      and se: "evaluate_pattern v (material_source N) = evaluate_pattern h (material_source N)"
    have hS: "clause_true M (decode_finite_schema S) h" using h ct by simp
    have mS: "(s,N) \<in> schema_material_premises (decode_finite_schema S)" using m by (simp only: mat)
    obtain h2 where "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S h h2"
        "\<forall>a\<in>material_variables N. h2 a = v a"
      using src hS mS sat se unfolding socket_discharged_def by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        (\<forall>a\<in>material_variables N. h' a = v a)"
      using ct hk by blast
  qed
qed

lemma socket_discharged_relocated:
  assumes src: "socket_discharged M S s keep Vp Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "socket_discharged M' (finite_rename_schema id id g S) s keep Vp Vh"
proof (rule socket_discharged_callees[OF src _ _ _ _ eq])
  let ?R = "finite_rename_schema id id g S"
  have img: "finite_schema_premises ?R = (\<lambda>(s,d,p). (s,g d,p)) |`| finite_schema_premises S"
    by (simp add: finite_rename_schema_def case_prod_unfold finite_term_pattern.map_id)
  show "(q,e,p) |\<in>| finite_schema_premises ?R \<longleftrightarrow> (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d)" for q e p
  proof
    assume "(q,e,p) |\<in>| finite_schema_premises ?R"
    then have "(q,e,p) \<in> (\<lambda>(s,d,p). (s,g d,p)) ` fset (finite_schema_premises S)" unfolding img fimage.rep_eq .
    then show "\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d" by force
  next
    assume "\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d"
    then obtain d where d: "(q,d,p) |\<in>| finite_schema_premises S" "e = g d" by blast
    have "(q,e,p) \<in> (\<lambda>(s,d,p). (s,g d,p)) ` fset (finite_schema_premises S)"
      by (rule image_eqI[of _ _ "(q,d,p)"]) (use d in simp_all)
    then show "(q,e,p) |\<in>| finite_schema_premises ?R" unfolding img fimage.rep_eq .
  qed
  show "finite_schema_conclusion ?R = finite_schema_conclusion S"
    by (simp add: finite_rename_schema_def finite_term_pattern.map_id)
  have "schema_material_premises (rename_schema id id g (decode_finite_schema S)) =
      schema_material_premises (rename_schema id id id (decode_finite_schema S))"
    by (simp add: rename_schema_def)
  then show "schema_material_premises (decode_finite_schema ?R) = schema_material_premises (decode_finite_schema S)"
    by (simp add: finite_rename_schema_correct)
  show "clause_true M' (decode_finite_schema ?R) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h" for h
    unfolding finite_rename_schema_correct by (rule clause_true_relocated[OF eq])
qed

text \<open>
  A relocation injective on the program's definitions and the record's sites keeps the meaning at every declared
  site (@{text renamed_system_positive_meaning}), so each obligation carries.
\<close>

lemma relocated_meaning_at:
  assumes Pf: "schema_system_formed P" and injective: "inj_on g (system_definitions P \<union> A)" and dA: "d \<in> A"
  shows "(g d,x) \<in> positive_meaning (rename_system g P) \<longleftrightarrow> (d,x) \<in> positive_meaning P"
proof (cases "d \<in> system_definitions P")
  case True
  then show ?thesis by (rule renamed_system_meaning_at[OF Pf inj_on_subset[OF injective Un_upper1]])
next
  case False
  have old: "(d,x) \<notin> positive_meaning P"
  proof
    assume a: "(d,x) \<in> positive_meaning P"
    have "d \<in> system_definitions P" using schema_call_formed_target[OF positive_meaning_formed[OF a]] by blast
    then show False using False by blast
  qed
  have new: "(g d,x) \<notin> positive_meaning (rename_system g P)"
  proof
    assume a: "(g d,x) \<in> positive_meaning (rename_system g P)"
    have "g d \<in> system_definitions (rename_system g P)"
      using schema_call_formed_target[OF positive_meaning_formed[OF a]] by blast
    then obtain d0 where d0: "d0 \<in> system_definitions P" "g d = g d0" by (auto simp: renamed_system_definitions)
    have "d = d0" using inj_onD[OF injective d0(2)] d0(1) dA by blast
    then show False using False d0(1) by blast
  qed
  show ?thesis using old new by blast
qed

lemma declared_sites_members:
  "(d,V,hs) |\<in>| declared_producers D \<Longrightarrow> d \<in> declared_sites D"
  "(d,e,V,i) |\<in>| declared_consumers D \<Longrightarrow> d \<in> declared_sites D"
  "(d,e,V,i) |\<in>| declared_consumers D \<Longrightarrow> e \<in> declared_sites D"
  "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow> e \<in> declared_sites D"
  "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow> schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites D"
  by (force simp: declared_sites_def)+

theorem declarations_relocated_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union> declared_sites D)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
    (declarations_relocated g D) (corr \<circ> inv_into (declared_sites D) g)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?M' = "positive_meaning (decode_finite_system (finite_rename_system g P))"
  let ?c = "corr \<circ> inv_into (declared_sites D) g"
  have at: "(g d,x) \<in> ?M' \<longleftrightarrow> (d,x) \<in> ?M" if "d \<in> declared_sites D" for d x
    using relocated_meaning_at[OF Pf injective that] by simp
  have inv: "?c (g d) = corr d" if "d \<in> declared_sites D" for d
    using inv_into_f_f[OF inj_on_subset[OF injective Un_upper2] that] by simp
  show ?thesis unfolding declarations_discharged_def
  proof (intro conjI allI impI)
    show "declarations_formed (declarations_relocated g D)"
      by (rule declarations_formed_relocated) (use discharged in \<open>simp add: declarations_discharged_def\<close>)
  next
    fix d' V hs assume "(d',V,hs) |\<in>| declared_producers (declarations_relocated g D)"
    then obtain d where d: "(d,V,hs) |\<in>| declared_producers D" and d': "d' = g d"
      by (auto simp: declarations_relocated_def)
    have ds: "d \<in> declared_sites D" by (rule declared_sites_members(1)[OF d])
    have "producer_discharged ?M d V hs (corr d)" using discharged d unfolding declarations_discharged_def by blast
    then show "producer_discharged ?M' d' V hs (?c d')"
      unfolding producer_discharged_def d' inv[OF ds] at[OF ds] .
  next
    fix d' e' V i assume "(d',e',V,i) |\<in>| declared_consumers (declarations_relocated g D)"
    then obtain d e where de: "(d,e,V,i) |\<in>| declared_consumers D" and d': "d' = g d" and e': "e' = g e"
      by (auto simp: declarations_relocated_def)
    have ds: "d \<in> declared_sites D" by (rule declared_sites_members(2)[OF de])
    have es: "e \<in> declared_sites D" by (rule declared_sites_members(3)[OF de])
    have "consumer_discharged ?M e V (corr d i)" using discharged de unfolding declarations_discharged_def by blast
    then show "consumer_discharged ?M' e' V (?c d' i)"
      unfolding consumer_discharged_def d' e' inv[OF ds] at[OF es] .
  next
    fix e' S' s keep Vp Vh assume "(e',S',s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_relocated g D)"
    then obtain e S where eS: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" and S': "S' = finite_rename_schema id id g S"
      by (auto simp: declarations_relocated_def)
    have src: "socket_discharged ?M S s keep Vp Vh" using discharged eS unfolding declarations_discharged_def by blast
    have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites D"
      by (rule declared_sites_members(5)[OF eS])
    show "socket_discharged ?M' S' s keep Vp Vh" unfolding S'
      by (rule socket_discharged_relocated[OF src at]) (use sub in blast)
  qed
qed

text \<open>
  A socket whose clause calls a site at which the meaning N holds nothing has no true instance at N; at every other
  callee N means what M means, so the socket's obligation carries from M to N.
\<close>

lemma socket_discharged_shared:
  assumes src: "socket_discharged M S s keep Vp Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> d \<in> U \<Longrightarrow> (d,x) \<in> N \<longleftrightarrow> (d,x) \<in> M"
    and out: "\<And>d x. (d,x) \<in> N \<Longrightarrow> d \<in> U"
  shows "socket_discharged N S s keep Vp Vh"
proof (cases "schema_dependencies (decode_finite_schema S) \<subseteq> U")
  case True
  have eqc: "(id d,x) \<in> N \<longleftrightarrow> (d,x) \<in> M" if "d \<in> schema_dependencies (decode_finite_schema S)" for d x
    using eq[OF that] True that by auto
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)"
    if "(q,d,p) \<in> schema_premises (decode_finite_schema S)" for q d p
    using that unfolding schema_dependencies_def rel_ran_def by force
  have eqp: "(d,x) \<in> N \<longleftrightarrow> (d,x) \<in> M" if "(q,d,p) \<in> schema_premises (decode_finite_schema S)" for q d p x
    using eqc[OF dep[OF that]] by simp
  have ct: "clause_true N (decode_finite_schema S) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h" for h
    unfolding clause_true_def by (simp add: eqp)
  show ?thesis
    by (rule socket_discharged_callees[where R=S and g=id and M'=N, OF src _ refl refl ct eqc]) simp
next
  case False
  then obtain e0 where e0: "e0 \<in> schema_dependencies (decode_finite_schema S)" "e0 \<notin> U" by blast
  have none: "\<not> clause_true N (decode_finite_schema S) h" for h
  proof
    assume ct: "clause_true N (decode_finite_schema S) h"
    obtain q p where "(q,e0,p) \<in> schema_premises (decode_finite_schema S)"
      by (rule schema_dependency_premise[OF e0(1)])
    then have "(e0,evaluate_pattern h p) \<in> N" using ct unfolding clause_true_def by blast
    then show False using out e0(2) by blast
  qed
  have c1: "\<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None"
    using src unfolding socket_discharged_def by (rule conjunct1)
  show ?thesis unfolding socket_discharged_def using c1 by (simp add: none)
qed

text \<open>
  The transfer by agreement reads the record's obligations alone: a producer's site, a consumer's own site and a
  socket's callees; a consumer's producer site names its correspondence and is not read, nor is a socket's own site.
  A program Q agreeing with P on a set V closed under P's dependencies means what P means at every site of V
  (@{thm [source] positive_meaning_dependency_locality}), and nothing at a site it does not hold
  (@{thm [source] positive_meaning_site}): a producer or a consumer there is vacuous, and a socket whose clause calls
  such a site has no true instance at Q. So the record is discharged at Q wherever each site its obligations read is
  in V or is not Q's. Agreement on every declared site (@{text declarations_agree_discharged}) and agreement on the
  common definitions, P holding the sites the obligations read (@{text declarations_shared_discharged}), are its
  instances.
\<close>

theorem declarations_agree_read_discharged:
  assumes Pf: "schema_system_formed P" and Qf: "schema_system_formed Q"
    and agree: "systems_agree_on P Q V" and closed: "system_dependency_closed P V"
    and producers: "\<And>d W hs. (d,W,hs) |\<in>| declared_producers D \<Longrightarrow> d \<in> V \<or> d \<notin> system_definitions Q"
    and consumers: "\<And>d e W i. (d,e,W,i) |\<in>| declared_consumers D \<Longrightarrow> e \<in> V \<or> e \<notin> system_definitions Q"
    and sockets: "\<And>e S s keep Vp Vh d. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> d \<in> V \<or> d \<notin> system_definitions Q"
    and discharged: "declarations_discharged (positive_meaning P) D corr"
  shows "declarations_discharged (positive_meaning Q) D corr"
proof -
  let ?M = "positive_meaning P" and ?N = "positive_meaning Q"
  have eq: "(d,x) \<in> ?N \<longleftrightarrow> (d,x) \<in> ?M" if "d \<in> V" for d x
    using positive_meaning_dependency_locality[OF Pf Qf agree closed that] by simp
  have read: "(d,x) \<in> ?N \<longleftrightarrow> (d,x) \<in> ?M" if "d \<in> V \<or> d \<notin> system_definitions Q" "d \<in> system_definitions Q"
    for d x
    using that eq by blast
  have sub: "(d,x) \<in> ?M" if "d \<in> V \<or> d \<notin> system_definitions Q" "(d,x) \<in> ?N" for d x
    using read[OF that(1) positive_meaning_site[OF that(2)]] that(2) by blast
  have dF: "declarations_formed D"
    and dP: "\<forall>d W hs. (d,W,hs) |\<in>| declared_producers D \<longrightarrow> producer_discharged ?M d W hs (corr d)"
    and dC: "\<forall>d e W i. (d,e,W,i) |\<in>| declared_consumers D \<longrightarrow> consumer_discharged ?M e W (corr d i)"
    and dS: "\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<longrightarrow> socket_discharged ?M S s keep Vp Vh"
    using discharged unfolding declarations_discharged_def by blast+
  show ?thesis unfolding declarations_discharged_def
  proof (intro conjI allI impI)
    show "declarations_formed D" by (rule dF)
  next
    fix d W hs assume m: "(d,W,hs) |\<in>| declared_producers D"
    have src: "producer_discharged ?M d W hs (corr d)" using dP m by blast
    show "producer_discharged ?N d W hs (corr d)"
      using src sub[OF producers[OF m]] unfolding producer_discharged_def by blast
  next
    fix d e W i assume m: "(d,e,W,i) |\<in>| declared_consumers D"
    have src: "consumer_discharged ?M e W (corr d i)" using dC m by blast
    show "consumer_discharged ?N e W (corr d i)"
    proof (cases "e \<in> system_definitions Q")
      case True
      then show ?thesis using src read[OF consumers[OF m] True] unfolding consumer_discharged_def by simp
    next
      case False
      then show ?thesis unfolding consumer_discharged_def by (auto dest: positive_meaning_site)
    qed
  next
    fix e S s keep Vp Vh assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    have src: "socket_discharged ?M S s keep Vp Vh" using dS m by blast
    have eqs: "(d,x) \<in> ?N \<longleftrightarrow> (d,x) \<in> ?M"
      if "d \<in> schema_dependencies (decode_finite_schema S)" "d \<in> system_definitions Q" for d x
      using read[OF sockets[OF m that(1)] that(2)] .
    show "socket_discharged ?N S s keep Vp Vh" by (rule socket_discharged_shared[OF src eqs positive_meaning_site])
  qed
qed

theorem declarations_agree_discharged:
  assumes Pf: "schema_system_formed P" and Qf: "schema_system_formed Q"
    and agree: "systems_agree_on P Q V" and closed: "system_dependency_closed P V"
    and sites: "declared_sites D \<subseteq> V"
    and discharged: "declarations_discharged (positive_meaning P) D corr"
  shows "declarations_discharged (positive_meaning Q) D corr"
proof (rule declarations_agree_read_discharged[OF Pf Qf agree closed _ _ _ discharged])
  show "d \<in> V \<or> d \<notin> system_definitions Q" if "(d,W,hs) |\<in>| declared_producers D" for d W hs
    using subsetD[OF sites declared_sites_members(1)[OF that]] by blast
  show "e \<in> V \<or> e \<notin> system_definitions Q" if "(d,e,W,i) |\<in>| declared_consumers D" for d e W i
    using subsetD[OF sites declared_sites_members(3)[OF that]] by blast
  show "d \<in> V \<or> d \<notin> system_definitions Q"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" "d \<in> schema_dependencies (decode_finite_schema S)"
    for e S s keep Vp Vh d
    using subsetD[OF sites subsetD[OF declared_sites_members(5)[OF that(1)] that(2)]] by blast
qed

theorem declarations_shared_discharged:
  assumes Pf: "schema_system_formed P" and Qf: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P \<inter> system_definitions Q)"
    and producers_in: "\<And>d V hs. (d,V,hs) |\<in>| declared_producers D \<Longrightarrow> d \<in> system_definitions P"
    and consumers_in: "\<And>d e V i. (d,e,V,i) |\<in>| declared_consumers D \<Longrightarrow> e \<in> system_definitions P"
    and sockets_in: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      schema_dependencies (decode_finite_schema S) \<subseteq> system_definitions P"
    and discharged: "declarations_discharged (positive_meaning P) D corr"
  shows "declarations_discharged (positive_meaning Q) D corr"
proof -
  have closed: "system_dependency_closed P (system_definitions P \<inter> system_definitions Q)"
    by (rule systems_agree_on_intersection_closed[OF Pf Qf agree])
  show ?thesis
  proof (rule declarations_agree_read_discharged[OF Pf Qf agree closed _ _ _ discharged])
    show "d \<in> system_definitions P \<inter> system_definitions Q \<or> d \<notin> system_definitions Q"
      if "(d,W,hs) |\<in>| declared_producers D" for d W hs
      using producers_in[OF that] by blast
    show "e \<in> system_definitions P \<inter> system_definitions Q \<or> e \<notin> system_definitions Q"
      if "(d,e,W,i) |\<in>| declared_consumers D" for d e W i
      using consumers_in[OF that] by blast
    show "d \<in> system_definitions P \<inter> system_definitions Q \<or> d \<notin> system_definitions Q"
      if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" "d \<in> schema_dependencies (decode_finite_schema S)"
      for e S s keep Vp Vh d
      using subsetD[OF sockets_in[OF that(1)] that(2)] by blast
  qed
qed

section \<open>The relocated program's premises and the transfers\<close>

text \<open>
  The relocated program's exchange premise is derived from the source's discharged declarations: they are discharged
  at the relocation (@{text declarations_relocated_discharged}), and the discharge gives the premise at every program
  whose registrations are premise-only, at any views. The two transfers of #565 then take the source's discharged
  declarations in place of each program's exchange premise.
\<close>

theorem finite_commitment_exchanges_relocated:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union> declared_sites D)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> (finite_rename_system g P)"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment (declarations_relocated g D))
    (finite_rename_system g P)"
  by (rule finite_declared_commitment_exchanges[OF \<kappa>
    declarations_relocated_discharged[OF Pf injective discharged] only])

corollary finite_declared_relocation_transfer:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and only': "finite_registrations_premise_only \<kappa>' (finite_rename_system g P)"
    and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' (finite_rename_system g P)"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P) \<union> declared_sites D))"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' (finite_declared_commitment (declarations_relocated g D))
      (finite_rename_system g P) (g d) t m) = Some b'"
  shows "b = b'"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment D) P"
    by (rule finite_declared_commitment_exchanges[OF \<kappa> discharged only])
  have ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>' (finite_declared_commitment (declarations_relocated g D))
      (finite_rename_system g P)"
    by (rule finite_commitment_exchanges_relocated[OF \<kappa>' Pf inj_on_subset[OF injective] discharged only']) blast
  have inj: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    by (rule inj_on_subset[OF injective]) blast
  show ?thesis by (rule finite_committed_relocation_transfer[OF \<kappa> ex cl \<kappa>' ex' cl' Pf inj v v'])
qed

text \<open>
  A complete construction is relocated with the program (@{text finite_relocated_construction}): its relocation is
  complete at the relocated program, so it lifts there, and its registrations are premise-only. The relocation transfer
  then takes the source's formation, discharged declarations and complete construction alone.
\<close>

lemma finite_complete_registrations_premise_only:
  "finite_construction_complete \<kappa> P \<Longrightarrow> finite_registrations_premise_only \<kappa> P"
  by (auto simp: finite_construction_complete_def finite_registrations_premise_only_def)

theorem finite_construction_lifts_relocated:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes formed: "finite_system_formed P" and injective: "inj_on g (system_definitions (decode_finite_system P))"
    and complete: "finite_construction_complete \<kappa> P"
  shows "finite_construction_lifts U (finite_relocated_construction g P \<kappa>) (finite_rename_system g P)"
  by (rule finite_construction_complete_lifts[OF finite_relocated_construction_complete[OF formed injective complete]])

corollary finite_complete_relocation_transfer:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and formed: "finite_system_formed P"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and complete: "finite_construction_complete \<kappa> P"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P) \<union> declared_sites D))"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution (finite_relocated_construction g P \<kappa>)
      (finite_declared_commitment (declarations_relocated g D)) (finite_rename_system g P) (g d) t m) = Some b'"
  shows "b = b'"
proof -
  have Pf: "schema_system_formed (decode_finite_system P)" using formed by (simp add: finite_system_formed_correct)
  have inj: "inj_on g (system_definitions (decode_finite_system P))" by (rule inj_on_subset[OF injective]) blast
  have complete': "finite_construction_complete (finite_relocated_construction g P \<kappa>) (finite_rename_system g P)"
    by (rule finite_relocated_construction_complete[OF formed inj complete])
  show ?thesis
    by (rule finite_declared_relocation_transfer[OF \<kappa> discharged finite_complete_registrations_premise_only[OF complete]
      finite_construction_complete_lifts[OF complete] finite_relocated_construction_formed[OF \<kappa>]
      finite_complete_registrations_premise_only[OF complete'] finite_construction_complete_lifts[OF complete']
      Pf injective v v'])
qed

corollary finite_declared_agreement_transfer:
  fixes P Q :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and only': "finite_registrations_premise_only \<kappa>' Q" and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and sites: "declared_sites D \<subseteq> V"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' (finite_declared_commitment D) Q d t m) = Some b'"
  shows "b = b'"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment D) P"
    by (rule finite_declared_commitment_exchanges[OF \<kappa> discharged only])
  have dQ: "declarations_discharged (positive_meaning (decode_finite_system Q)) D corr"
    by (rule declarations_agree_discharged[OF Pf Qf agree closed sites discharged])
  have ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>' (finite_declared_commitment D) Q"
    by (rule finite_declared_commitment_exchanges[OF \<kappa>' dQ only'])
  show ?thesis by (rule finite_committed_agreement_transfer[OF \<kappa> ex cl \<kappa>' ex' cl' Pf Qf agree closed dV v v'])
qed

text \<open>At complete constructions the agreement transfer takes discharged declarations and the two completenesses.\<close>

corollary finite_complete_agreement_transfer:
  fixes P Q :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> P"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'" and complete': "finite_construction_complete \<kappa>' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and sites: "declared_sites D \<subseteq> V"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' (finite_declared_commitment D) Q d t m) = Some b'"
  shows "b = b'"
  by (rule finite_declared_agreement_transfer[OF \<kappa> discharged finite_complete_registrations_premise_only[OF complete]
    finite_construction_complete_lifts[OF complete] \<kappa>' finite_complete_registrations_premise_only[OF complete']
    finite_construction_complete_lifts[OF complete'] Pf Qf agree closed dV sites v v'])

end
