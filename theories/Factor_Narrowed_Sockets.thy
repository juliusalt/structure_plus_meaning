theory Factor_Narrowed_Sockets
  imports Factor_Resolution_Views Factor_Resolution_Carriers Factor_Least_Witness_Registrations
begin

text \<open>
  Narrowed sockets (R5e of DECISIONS.md "The native evaluator constructs the missing witnesses by resolution", its
  addition "The given's remaining producers: views, carriers and narrowed sockets", (c)). A producer whose answers at
  one input form an endless class (48's unions: every list with the union's set, every order and repetition) is
  produced, not committed: at each of its uses with the output free, a consumer in the same clause narrows the class
  (49's distinct disjoint lists, site 1's distinct payloads), and within the narrowed class every holder is invariant.
  The socket is declared with a class predicate N on its output; R5's socket is its instance at N = True. Its
  obligations: (i) narrowing, every true instance of the clause holds the socket's output in N; (ii) the socket's
  obligation over N, every answer in N at the same input extends a true instance, the head changed only inside its
  output; (iii) production, the kept answer is an answer in N, a condition on the witness construction registered at
  the producer's head variable (task 496's construction, at a variable its entry did not name).

  The class predicate stands in an extension of the record at views (@{text narrowed_declarations}): the record the
  search and its tests read is its truncation, unchanged, and the predicate is read by the discharge alone, as
  carriers are.
\<close>

section \<open>The narrowed socket in the record\<close>

record ('a,'s,'d) narrowed_declarations = "('a,'s,'d) resolution_declarations" +
  declared_narrowing :: "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> factor_term \<Rightarrow> bool"

definition narrowed ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> ('d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow>
      ('a,'s,'d) narrowed_declarations" where
  "narrowed D \<nu> = \<lparr>declared_producers = declared_producers D, declared_consumers = declared_consumers D,
    declared_sockets = declared_sockets D, declared_narrowing = \<nu>\<rparr>"

lemma narrowed_fields [simp]:
  "declared_producers (narrowed D \<nu>) = declared_producers D"
  "declared_consumers (narrowed D \<nu>) = declared_consumers D"
  "declared_sockets (narrowed D \<nu>) = declared_sockets D"
  "declared_narrowing (narrowed D \<nu>) = \<nu>"
  by (simp_all add: narrowed_def)

lemma narrowed_truncate [simp]: "resolution_declarations.truncate (narrowed D \<nu>) = D"
  by (cases D) (simp add: narrowed_def resolution_declarations.truncate_def)

lemma truncate_fields [simp]:
  "declared_producers (resolution_declarations.truncate ND) = declared_producers ND"
  "declared_consumers (resolution_declarations.truncate ND) = declared_consumers ND"
  "declared_sockets (resolution_declarations.truncate ND) = declared_sockets ND"
  by (simp_all add: resolution_declarations.truncate_def)

text \<open>A record declares no narrowing when every socket's class is every term: R5's record.\<close>

abbreviation unnarrowed :: "('a,'s,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) narrowed_declarations" where
  "unnarrowed D \<equiv> narrowed D (\<lambda>_ _ _ _. True)"

section \<open>The narrowed socket's obligations\<close>

text \<open>
  (i) Narrowing: every true instance of the clause holds the output of the socket's premise, read at its view, in N.
  (ii) The socket's obligation over N: R5's (@{const socket_discharged}) at the answers in N alone. The material part is
  R5's, unchanged.
\<close>

definition socket_narrowing ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> nat resolution_view \<Rightarrow>
      (factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "socket_narrowing M S s Vp N \<longleftrightarrow> (\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
    (\<forall>d p xi yo. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow>
      N (evaluate_pattern h (decode_finite_pattern yo))))"

definition narrowed_socket_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> nat resolution_view \<Rightarrow>
      nat resolution_view \<Rightarrow> (factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "narrowed_socket_discharged M S s keep Vp Vh N \<longleftrightarrow> socket_narrowing M S s Vp N \<and>
    (\<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None) \<and>
    (\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>d p xi yo t y'. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow>
        (d,t) \<in> M \<longrightarrow> resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y')) \<and>
      (\<forall>N' g. (s,N') \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N' \<longrightarrow>
        evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N') \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>material_variables N'. h' a = g a))))"

text \<open>
  The narrowed socket's obligation at a frame C (DECISIONS.md, task 495's entry, correction (10)): the new instance
  agrees with the old one at the clause's variables outside C, over the socket's class as
  @{const narrowed_socket_discharged} reads it.
\<close>

definition narrowed_socket_framed ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> nat resolution_view \<Rightarrow>
      nat resolution_view \<Rightarrow> (factor_term \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "narrowed_socket_framed M S s keep Vp Vh N C \<longleftrightarrow> socket_narrowing M S s Vp N \<and>
    (\<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None) \<and>
    (\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>d p xi yo t y'. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow>
        (d,t) \<in> M \<longrightarrow> resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y')) \<and>
      (\<forall>N' g. (s,N') \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N' \<longrightarrow>
        evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N') \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
          (\<forall>a\<in>material_variables N'. h' a = g a))))"

lemma narrowed_socket_framed_discharged:
  assumes framed: "narrowed_socket_framed M S s keep Vp Vh N C"
  shows "narrowed_socket_discharged M S s keep Vp Vh N"
proof -
  note F = framed[unfolded narrowed_socket_framed_def]
  note O = conjunct2[OF conjunct2[OF F]]
  have calls: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = y'"
    if h: "clause_true M (decode_finite_schema S) h" and p: "(s,d,p) |\<in>| finite_schema_premises S"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)" and t: "(d,t) \<in> M"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')" and n: "N y'"
    for h d p xi yo t y'
    using conjunct1[OF mp[OF spec[OF O, of h] h], rule_format, OF p v t vt n] by blast
  have mats: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      (\<forall>a\<in>material_variables N'. h' a = g a)"
    if h: "clause_true M (decode_finite_schema S) h"
      and m: "(s,N') \<in> schema_material_premises (decode_finite_schema S)"
      and g: "evaluate_material_satisfaction g N'"
      and src: "evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N')" for h N' g
    using conjunct2[OF mp[OF spec[OF O, of h] h], rule_format, OF m g src] by blast
  show ?thesis unfolding narrowed_socket_discharged_def
    using conjunct1[OF F] conjunct1[OF conjunct2[OF F]] calls mats by blast
qed

text \<open>R5's framed socket is the narrowed framed socket at N = True.\<close>

theorem socket_framed_narrowed:
  "socket_framed M S s keep Vp Vh C \<longleftrightarrow> narrowed_socket_framed M S s keep Vp Vh (\<lambda>_. True) C"
  by (simp add: narrowed_socket_framed_def socket_narrowing_def socket_framed_def)

text \<open>R5's socket is the narrowed socket at N = True.\<close>

theorem socket_discharged_narrowed:
  "socket_discharged M S s keep Vp Vh \<longleftrightarrow> narrowed_socket_discharged M S s keep Vp Vh (\<lambda>_. True)"
  by (simp add: narrowed_socket_discharged_def socket_narrowing_def socket_discharged_def)

text \<open>
  A narrowed record is discharged when its producers and consumers are, as R5's, and each socket's narrowed
  obligation at its class. At the record declaring no narrowing it is R5's discharge; where every socket's class is
  every term it is the discharge of its truncation.
\<close>

definition narrowed_declarations_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) narrowed_declarations \<Rightarrow>
      ('d \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "narrowed_declarations_discharged M ND corr \<longleftrightarrow> declarations_formed (resolution_declarations.truncate ND) \<and>
    (\<forall>d V hs. (d,V,hs) |\<in>| declared_producers ND \<longrightarrow> producer_discharged M d V hs (corr d)) \<and>
    (\<forall>d e V i. (d,e,V,i) |\<in>| declared_consumers ND \<longrightarrow> consumer_discharged M e V (corr d i)) \<and>
    (\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<longrightarrow>
      narrowed_socket_discharged M S s keep Vp Vh (declared_narrowing ND e S s))"

lemma narrowed_formed:
  assumes "narrowed_declarations_discharged M ND corr"
  shows "declarations_formed (resolution_declarations.truncate ND)"
  using assms unfolding narrowed_declarations_discharged_def by blast

lemma narrowed_producer:
  assumes dis: "narrowed_declarations_discharged M ND corr" and d: "(d,V,hs) |\<in>| declared_producers ND"
  shows "producer_discharged M d V hs (corr d)"
proof -
  obtain a b c where V: "V = (a,b,c)" using prod_cases3 by blast
  have "(d,(a,b,c),hs) |\<in>| declared_producers ND" using d V by simp
  then show ?thesis using dis unfolding narrowed_declarations_discharged_def V by blast
qed

lemma narrowed_consumer:
  assumes dis: "narrowed_declarations_discharged M ND corr" and de: "(d,e,V,i) |\<in>| declared_consumers ND"
  shows "consumer_discharged M e V (corr d i)"
proof -
  obtain a b c where V: "V = (a,b,c)" using prod_cases3 by blast
  have "(d,e,(a,b,c),i) |\<in>| declared_consumers ND" using de V by simp
  then show ?thesis using dis unfolding narrowed_declarations_discharged_def V by blast
qed

lemma narrowed_socket:
  assumes dis: "narrowed_declarations_discharged M ND corr" and eS: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND"
  shows "narrowed_socket_discharged M S s keep Vp Vh (declared_narrowing ND e S s)"
proof -
  obtain a b c where Vp: "Vp = (a,b,c)" using prod_cases3 by blast
  obtain a' b' c' where Vh: "Vh = (a',b',c')" using prod_cases3 by blast
  have "(e,S,s,keep,(a,b,c),(a',b',c')) |\<in>| declared_sockets ND" using eS Vp Vh by simp
  then show ?thesis using dis unfolding narrowed_declarations_discharged_def Vp Vh by blast
qed

theorem narrowed_declarations_discharged_top:
  assumes top: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      declared_narrowing ND e S s = (\<lambda>_. True)"
  shows "narrowed_declarations_discharged M ND corr \<longleftrightarrow>
    declarations_discharged M (resolution_declarations.truncate ND) corr"
proof -
  have "(\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<longrightarrow>
        narrowed_socket_discharged M S s keep Vp Vh (declared_narrowing ND e S s)) \<longleftrightarrow>
      (\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<longrightarrow> socket_discharged M S s keep Vp Vh)"
    using top by (auto simp: socket_discharged_narrowed)
  then show ?thesis unfolding narrowed_declarations_discharged_def declarations_discharged_def truncate_fields
    by (simp only:)
qed

corollary declarations_discharged_unnarrowed:
  "declarations_discharged M D corr \<longleftrightarrow> narrowed_declarations_discharged M (unnarrowed D) corr"
  by (subst narrowed_declarations_discharged_top) simp_all

text \<open>
  A frame family beside a narrowed record is discharged when every frame it holds is a frame of every socket the record
  declares at that site, clause and key, over that socket's class. Beside the record declaring no narrowing it is the
  frames' discharge beside its truncation.
\<close>

definition narrowed_frames_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) narrowed_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> bool" where
  "narrowed_frames_discharged M ND \<Phi> \<longleftrightarrow> (\<forall>e S s C keep Vp Vh. (e,S,s,C) |\<in>| \<Phi> \<longrightarrow>
    (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<longrightarrow>
    narrowed_socket_framed M S s keep Vp Vh (declared_narrowing ND e S s) (fset C))"

lemma narrowed_frames_discharged_empty: "narrowed_frames_discharged M ND {||}"
  by (simp add: narrowed_frames_discharged_def)

corollary frames_discharged_unnarrowed:
  "frames_discharged M D \<Phi> \<longleftrightarrow> narrowed_frames_discharged M (unnarrowed D) \<Phi>"
  by (simp add: narrowed_frames_discharged_def frames_discharged_def socket_framed_narrowed)

section \<open>The obligation over N discharged along the clause's carriers\<close>

text \<open>
  The class restricted to N: the meaning whose answers at the socket's producer are those whose output, read at the
  socket's view, is in N (@{text narrowed_meaning}). Where every use of the producer in the clause is narrowed at every
  true instance (@{text clause_narrowed}), the clause's true instances at the restricted meaning are its true
  instances, so R5d's carrying lemma at the restricted meaning discharges the narrowed obligation: the socket's
  producer is discharged over the narrowed class alone, and every carrier and consumer reads corresponding outputs in
  N.
\<close>

definition narrowed_meaning ::
    "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> nat resolution_view \<Rightarrow> (factor_term \<Rightarrow> bool) \<Rightarrow> ('d \<times> factor_term) set" where
  "narrowed_meaning M d V N = {(e,t) \<in> M. e = d \<longrightarrow> (\<forall>x y. resolution_view_term V t = Some (x,y) \<longrightarrow> N y)}"

definition clause_narrowed ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'd \<Rightarrow> nat resolution_view \<Rightarrow>
      (factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "clause_narrowed M S d V N \<longleftrightarrow> (\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
    (\<forall>q p. (q,d,p) \<in> schema_premises (decode_finite_schema S) \<longrightarrow>
      (\<forall>x y. resolution_view_term V (evaluate_pattern h p) = Some (x,y) \<longrightarrow> N y)))"

lemma narrowed_meaning_subset: "narrowed_meaning M d V N \<subseteq> M"
  by (auto simp: narrowed_meaning_def)

lemma clause_true_narrowed_meaning:
  assumes narrowing: "clause_narrowed M S d V N"
  shows "clause_true (narrowed_meaning M d V N) (decode_finite_schema S) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h"
proof
  assume A: "clause_true (narrowed_meaning M d V N) (decode_finite_schema S) h"
  note A' = A[unfolded clause_true_def]
  have calls: "\<forall>q e p. (q,e,p) \<in> schema_premises (decode_finite_schema S) \<longrightarrow> (e,evaluate_pattern h p) \<in> M"
  proof (intro allI impI)
    fix q e p assume qp: "(q,e,p) \<in> schema_premises (decode_finite_schema S)"
    show "(e,evaluate_pattern h p) \<in> M"
      by (rule subsetD[OF narrowed_meaning_subset conjunct1[OF conjunct2[OF A'], rule_format, OF qp]])
  qed
  show "clause_true M (decode_finite_schema S) h" unfolding clause_true_def
    by (rule conjI[OF conjunct1[OF A'] conjI[OF calls conjunct2[OF conjunct2[OF A']]]])
next
  assume B: "clause_true M (decode_finite_schema S) h"
  note B' = B[unfolded clause_true_def]
  note n = mp[OF spec[OF narrowing[unfolded clause_narrowed_def]] B, rule_format]
  have calls: "\<forall>q e p. (q,e,p) \<in> schema_premises (decode_finite_schema S) \<longrightarrow>
      (e,evaluate_pattern h p) \<in> narrowed_meaning M d V N"
  proof (intro allI impI)
    fix q e p assume qp: "(q,e,p) \<in> schema_premises (decode_finite_schema S)"
    have m: "(e,evaluate_pattern h p) \<in> M" by (rule conjunct1[OF conjunct2[OF B'], rule_format, OF qp])
    have c: "e = d \<longrightarrow> (\<forall>x y. resolution_view_term V (evaluate_pattern h p) = Some (x,y) \<longrightarrow> N y)"
    proof (intro impI allI)
      fix x y assume e: "e = d" and vt: "resolution_view_term V (evaluate_pattern h p) = Some (x,y)"
      have qd: "(q,d,p) \<in> schema_premises (decode_finite_schema S)" using qp e by simp
      show "N y" by (rule n[OF qd vt])
    qed
    show "(e,evaluate_pattern h p) \<in> narrowed_meaning M d V N" using m c by (simp add: narrowed_meaning_def)
  qed
  show "clause_true (narrowed_meaning M d V N) (decode_finite_schema S) h" unfolding clause_true_def
    by (rule conjI[OF conjunct1[OF B'] conjI[OF calls conjunct2[OF conjunct2[OF B']]]])
qed

theorem narrowed_socket_framed_carried:
  assumes carried: "socket_carried (narrowed_meaning M d0 Vp N) S s keep Vp Vh c0 cs"
    and site: "finite_relation_option (finite_schema_premises S) s = Some (d0,p0)"
    and narrowing: "clause_narrowed M S d0 Vp N"
  shows "narrowed_socket_framed M S s keep Vp Vh N (carried_variables S s Vp cs)"
proof -
  let ?M = "narrowed_meaning M d0 Vp N"
  have sd: "socket_framed ?M S s keep Vp Vh (carried_variables S s Vp cs)" by (rule socket_framed_carried[OF carried])
  have ct: "\<And>h. clause_true ?M (decode_finite_schema S) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h"
    by (rule clause_true_narrowed_meaning[OF narrowing])
  note sd' = sd[unfolded socket_framed_def ct]
  note S2 = mp[OF spec[OF conjunct2[OF sd']]]
  have vp: "view_formed Vp" using carried unfolding socket_carried_def by blast
  have uniq: "d = d0 \<and> p = p0" if "(s,d,p) |\<in>| finite_schema_premises S" for d p
    using finite_relation_option_unique[OF site that] by simp
  have i: "socket_narrowing M S s Vp N" unfolding socket_narrowing_def
  proof (intro allI impI)
    fix h d p xi yo
    assume h: "clause_true M (decode_finite_schema S) h" and p: "(s,d,p) |\<in>| finite_schema_premises S"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)"
    have d: "d = d0" using uniq[OF p] by simp
    have dp: "(s,d0,decode_finite_pattern p) \<in> schema_premises (decode_finite_schema S)"
      using decoded_premise[OF p] d by simp
    have vt: "resolution_view_term Vp (evaluate_pattern h (decode_finite_pattern p)) =
        Some (evaluate_pattern h (decode_finite_pattern xi),evaluate_pattern h (decode_finite_pattern yo))"
      by (rule resolution_view_pattern_evaluate[OF vp v])
    show "N (evaluate_pattern h (decode_finite_pattern yo))"
      by (rule mp[OF spec[OF narrowing[unfolded clause_narrowed_def]] h, rule_format, OF dp vt])
  qed
  have main: "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>d p xi yo t y'. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow>
        (d,t) \<in> M \<longrightarrow> resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema S) - carried_variables S s Vp cs. h' a = h a) \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y')) \<and>
      (\<forall>N' g. (s,N') \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N' \<longrightarrow>
        evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N') \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema S) - carried_variables S s Vp cs. h' a = h a) \<and>
          (\<forall>a\<in>material_variables N'. h' a = g a)))"
  proof (intro allI impI conjI)
    fix h d p xi yo t y'
    assume h: "clause_true M (decode_finite_schema S) h" and p: "(s,d,p) |\<in>| finite_schema_premises S"
      and w: "resolution_view_pattern Vp p = Some (xi,yo)" and a: "(d,t) \<in> M"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')" and n: "N y'"
    have d: "d = d0" using uniq[OF p] by simp
    have aN: "(d,t) \<in> ?M" using a vt n d unfolding narrowed_meaning_def by auto
    show "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - carried_variables S s Vp cs. h' a = h a) \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'"
      by (rule conjunct1[OF S2[OF h], rule_format, OF p w aN vt])
  next
    fix h N' g
    assume h: "clause_true M (decode_finite_schema S) h"
      and m: "(s,N') \<in> schema_material_premises (decode_finite_schema S)"
      and sat: "evaluate_material_satisfaction g N'"
      and se: "evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N')"
    show "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - carried_variables S s Vp cs. h' a = h a) \<and>
        (\<forall>a\<in>material_variables N'. h' a = g a)"
      by (rule conjunct2[OF S2[OF h], rule_format, OF m sat se])
  qed
  show ?thesis unfolding narrowed_socket_framed_def by (rule conjI[OF i conjI[OF conjunct1[OF sd'] main]])
qed

theorem narrowed_socket_discharged_carried:
  assumes carried: "socket_carried (narrowed_meaning M d0 Vp N) S s keep Vp Vh c0 cs"
    and site: "finite_relation_option (finite_schema_premises S) s = Some (d0,p0)"
    and narrowing: "clause_narrowed M S d0 Vp N"
  shows "narrowed_socket_discharged M S s keep Vp Vh N"
  by (rule narrowed_socket_framed_discharged[OF narrowed_socket_framed_carried[OF carried site narrowing]])

section \<open>A registration at a head variable\<close>

text \<open>
  A variable free after head unification: the registered variable a of the producer's clause S (at site d) is the
  output of its head read at a view, a variable no input position holds (@{text head_registration}); it is free after
  unification exactly when the producer is called with its output free. The construction's value is read at the
  ground bindings B of the head input's variables, and B gives the input the head reads
  (@{text head_registration_input}). (iii) Production: every value the construction returns there is formed and in N
  (@{text head_registration_produces}). The construction's value is an answer wherever the producer has one at the
  same input (@{text head_registration_answers}): at the given's 48, the collection's distinct union, which the given's
  48 checks, as every list with the union's set is an answer.
\<close>

lemma finite_rename_schema_conclusion [simp]:
  "finite_schema_conclusion (finite_rename_schema id id g S) = finite_schema_conclusion S"
  by (simp add: finite_rename_schema_def finite_term_pattern.map_id)

definition head_registration :: "nat resolution_view \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a \<Rightarrow> bool" where
  "head_registration Vc S a \<longleftrightarrow> view_formed Vc \<and> (\<exists>ci. resolution_view_pattern Vc (finite_schema_conclusion S) =
    Some (ci,Finite_Variable a) \<and> a |\<notin>| finite_pattern_variables ci)"

definition head_registration_input ::
    "nat resolution_view \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> factor_term option" where
  "head_registration_input Vc S B = (case resolution_view_pattern Vc (finite_schema_conclusion S) of None \<Rightarrow> None
    | Some (ci,co) \<Rightarrow> Some (evaluate_pattern (\<lambda>x. decode_finite_term (finite_binding_valuation B x)) (decode_finite_pattern ci)))"

definition head_registration_produces ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow>
      ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a \<Rightarrow> (factor_term \<Rightarrow> bool) \<Rightarrow> bool" where
  "head_registration_produces \<kappa> P d S a N \<longleftrightarrow> (\<forall>B v. witness_value \<kappa> P d S B a = Some v \<longrightarrow>
    finite_term_formed v \<and> N (decode_finite_term v))"

definition head_registration_answers ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      'd \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> nat resolution_view \<Rightarrow> 'a \<Rightarrow> bool" where
  "head_registration_answers M \<kappa> P d S Vc a \<longleftrightarrow> (\<forall>B v x t y. witness_value \<kappa> P d S B a = Some v \<longrightarrow>
    head_registration_input Vc S B = Some x \<longrightarrow> (d,t) \<in> M \<longrightarrow> resolution_view_term Vc t = Some (x,y) \<longrightarrow>
    (\<exists>t'. (d,t') \<in> M \<and> resolution_view_term Vc t' = Some (x,decode_finite_term v)))"

text \<open>
  Completeness at a narrowed socket. At a caller clause whose premise at s calls the registered producer and is a
  narrowed socket read at the registration's view, every true instance of the clause extends to one through the
  construction's value at its input, the head changed only as the socket's obligation permits, and that value is
  formed and in N: the clause holds at some value of the socket's output in N exactly when it holds at the
  construction's value, so a check failed there refutes every value. At any other use the registration is not
  complete, and its failed checks leave the call unresolved (task 496's rule).
\<close>

theorem registration_complete_at_socket:
  assumes narrowed: "narrowed_socket_discharged M C s keep Vp Vh N" and vp: "view_formed Vp"
    and premise: "(s,d,p) |\<in>| finite_schema_premises C" and viewed: "resolution_view_pattern Vp p = Some (xi,yo)"
    and produces: "head_registration_produces \<kappa> P d S a N" and answers: "head_registration_answers M \<kappa> P d S Vp a"
    and h: "clause_true M (decode_finite_schema C) h"
    and input: "head_registration_input Vp S B = Some (evaluate_pattern h (decode_finite_pattern xi))"
    and valued: "witness_value \<kappa> P d S B a = Some v"
  shows "finite_term_formed v" "N (decode_finite_term v)"
    "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
proof -
  have pv: "finite_term_formed v \<and> N (decode_finite_term v)"
    using produces valued unfolding head_registration_produces_def by blast
  then show "finite_term_formed v" "N (decode_finite_term v)" by simp_all
  have a: "(d,evaluate_pattern h (decode_finite_pattern p)) \<in> M"
    using h decoded_premise[OF premise] unfolding clause_true_def by blast
  have vt: "resolution_view_term Vp (evaluate_pattern h (decode_finite_pattern p)) =
      Some (evaluate_pattern h (decode_finite_pattern xi),evaluate_pattern h (decode_finite_pattern yo))"
    by (rule resolution_view_pattern_evaluate[OF vp viewed])
  obtain t' where t': "(d,t') \<in> M"
      "resolution_view_term Vp t' = Some (evaluate_pattern h (decode_finite_pattern xi),decode_finite_term v)"
    using answers[unfolded head_registration_answers_def, rule_format, OF valued input a vt] by blast
  note n = narrowed[unfolded narrowed_socket_discharged_def]
  show "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
    by (rule conjunct1[OF mp[OF spec[OF conjunct2[OF conjunct2[OF n]]] h], rule_format,
        OF premise viewed t'(1) t'(2) conjunct2[OF pv]])
qed

corollary registration_complete_at_socket_iff:
  assumes narrowed: "narrowed_socket_discharged M C s keep Vp Vh N" and vp: "view_formed Vp"
    and premise: "(s,d,p) |\<in>| finite_schema_premises C" and viewed: "resolution_view_pattern Vp p = Some (xi,yo)"
    and produces: "head_registration_produces \<kappa> P d S a N" and answers: "head_registration_answers M \<kappa> P d S Vp a"
    and input: "head_registration_input Vp S B = Some x" and valued: "witness_value \<kappa> P d S B a = Some v"
  shows "(\<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      N (evaluate_pattern h (decode_finite_pattern yo))) \<longleftrightarrow>
    (\<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      evaluate_pattern h (decode_finite_pattern yo) = decode_finite_term v)"
proof
  assume "\<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      N (evaluate_pattern h (decode_finite_pattern yo))"
  then obtain h where h: "clause_true M (decode_finite_schema C) h" and x: "evaluate_pattern h (decode_finite_pattern xi) = x"
    by blast
  have i: "head_registration_input Vp S B = Some (evaluate_pattern h (decode_finite_pattern xi))" using input x by simp
  obtain h' where "clause_true M (decode_finite_schema C) h'"
      "evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
      "evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
    using registration_complete_at_socket(3)[OF narrowed vp premise viewed produces answers h i valued] by blast
  then show "\<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      evaluate_pattern h (decode_finite_pattern yo) = decode_finite_term v" using x by blast
next
  have "N (decode_finite_term v)" using produces valued unfolding head_registration_produces_def by blast
  then show "\<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      evaluate_pattern h (decode_finite_pattern yo) = decode_finite_term v \<Longrightarrow>
    \<exists>h. clause_true M (decode_finite_schema C) h \<and> evaluate_pattern h (decode_finite_pattern xi) = x \<and>
      N (evaluate_pattern h (decode_finite_pattern yo))" by auto
qed

section \<open>The transfer\<close>

text \<open>
  A narrowed socket's obligation reads the meaning only at the clause's callees, as R5's does
  (@{thm [source] socket_discharged_callees}): it carries to a schema with relocated callees and to an agreeing
  program. A narrowed record relocates with its sockets (@{const declarations_relocated}) and a narrowing at the
  relocated sockets that is the source's at each; a head registration relocates with the construction
  (@{const finite_relocated_construction}), its production and its answers at the relocated site.
\<close>

lemma narrowed_socket_discharged_callees:
  assumes src: "narrowed_socket_discharged M S s keep Vp Vh N"
    and prem: "\<And>q e p. (q,e,p) |\<in>| finite_schema_premises R \<longleftrightarrow>
      (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d)"
    and conc: "finite_schema_conclusion R = finite_schema_conclusion S"
    and mat: "schema_material_premises (decode_finite_schema R) = schema_material_premises (decode_finite_schema S)"
    and ct: "\<And>h. clause_true M' (decode_finite_schema R) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "narrowed_socket_discharged M' R s keep Vp Vh N"
proof -
  have hk: "head_kept keep Vh R h h' \<longleftrightarrow> head_kept keep Vh S h h'" for h h' unfolding head_kept_def conc ..
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)" if "(q,d,p) |\<in>| finite_schema_premises S" for q d p
    by (rule schema_dependencies_premise[of q d "decode_finite_pattern p"]) (use that in \<open>auto simp: finite_premise_decoded\<close>)
  note src' = src[unfolded narrowed_socket_discharged_def socket_narrowing_def]
  note S2 = mp[OF spec[OF conjunct2[OF conjunct2[OF src']]]]
  show ?thesis unfolding narrowed_socket_discharged_def socket_narrowing_def
  proof (intro conjI allI impI)
    fix h d p xi yo
    assume h: "clause_true M' (decode_finite_schema R) h" and p: "(s,d,p) |\<in>| finite_schema_premises R"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)"
    from p obtain d0 where p0: "(s,d0,p) |\<in>| finite_schema_premises S" using prem by blast
    have hS: "clause_true M (decode_finite_schema S) h" using h ct by simp
    show "N (evaluate_pattern h (decode_finite_pattern yo))" by (rule conjunct1[OF src', rule_format, OF hS p0 v])
  next
    fix d p assume "(s,d,p) |\<in>| finite_schema_premises R"
    then obtain d0 where "(s,d0,p) |\<in>| finite_schema_premises S" using prem by blast
    then show "resolution_view_pattern Vp p \<noteq> None" using conjunct1[OF conjunct2[OF src']] by blast
  next
    fix h d p xi yo t y'
    assume h: "clause_true M' (decode_finite_schema R) h" and p: "(s,d,p) |\<in>| finite_schema_premises R"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)" and a: "(d,t) \<in> M'"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')" and n: "N y'"
    from p obtain d0 where p0: "(s,d0,p) |\<in>| finite_schema_premises S" and d: "d = g d0" using prem by blast
    have a0: "(d0,t) \<in> M" using a eq[OF dep[OF p0]] d by simp
    have hS: "clause_true M (decode_finite_schema S) h" using h ct by simp
    obtain h2 where "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S h h2"
        "evaluate_pattern h2 (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
        "evaluate_pattern h2 (decode_finite_pattern yo) = y'"
      using conjunct1[OF S2[OF hS], rule_format, OF p0 v a0 vt n] by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'"
      using ct hk by blast
  next
    fix h N' v
    assume h: "clause_true M' (decode_finite_schema R) h"
      and m: "(s,N') \<in> schema_material_premises (decode_finite_schema R)"
      and sat: "evaluate_material_satisfaction v N'"
      and se: "evaluate_pattern v (material_source N') = evaluate_pattern h (material_source N')"
    have hS: "clause_true M (decode_finite_schema S) h" using h ct by simp
    have mS: "(s,N') \<in> schema_material_premises (decode_finite_schema S)" using m by (simp only: mat)
    obtain h2 where "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S h h2"
        "\<forall>a\<in>material_variables N'. h2 a = v a"
      using conjunct2[OF S2[OF hS], rule_format, OF mS sat se] by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        (\<forall>a\<in>material_variables N'. h' a = v a)"
      using ct hk by blast
  qed
qed

lemma narrowed_socket_discharged_relocated:
  assumes src: "narrowed_socket_discharged M S s keep Vp Vh N"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "narrowed_socket_discharged M' (finite_rename_schema id id g S) s keep Vp Vh N"
proof (rule narrowed_socket_discharged_callees[OF src _ _ _ _ eq])
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
  show "finite_schema_conclusion ?R = finite_schema_conclusion S" by simp
  have "schema_material_premises (rename_schema id id g (decode_finite_schema S)) =
      schema_material_premises (rename_schema id id id (decode_finite_schema S))"
    by (simp add: rename_schema_def)
  then show "schema_material_premises (decode_finite_schema ?R) = schema_material_premises (decode_finite_schema S)"
    by (simp add: finite_rename_schema_correct)
  show "clause_true M' (decode_finite_schema ?R) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h" for h
    unfolding finite_rename_schema_correct by (rule clause_true_relocated[OF eq])
qed

theorem narrowed_declarations_relocated_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union>
      declared_sites (resolution_declarations.truncate ND))"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P)) ND corr"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing ND e S s"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
    (narrowed (declarations_relocated g (resolution_declarations.truncate ND)) \<nu>)
    (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate ND)) g)"
proof -
  let ?D = "resolution_declarations.truncate ND"
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?M' = "positive_meaning (decode_finite_system (finite_rename_system g P))"
  let ?c = "corr \<circ> inv_into (declared_sites ?D) g"
  have at: "(g d,x) \<in> ?M' \<longleftrightarrow> (d,x) \<in> ?M" if "d \<in> declared_sites ?D" for d x
    using relocated_meaning_at[OF Pf injective that] by simp
  have inv: "?c (g d) = corr d" if "d \<in> declared_sites ?D" for d
    using inv_into_f_f[OF inj_on_subset[OF injective Un_upper2] that] by simp
  show ?thesis unfolding narrowed_declarations_discharged_def narrowed_truncate narrowed_fields
  proof (intro conjI allI impI)
    show "declarations_formed (declarations_relocated g ?D)"
      by (rule declarations_formed_relocated) (use narrowed_formed[OF discharged] in simp)
  next
    fix d' V hs assume "(d',V,hs) |\<in>| declared_producers (declarations_relocated g ?D)"
    then obtain d where d: "(d,V,hs) |\<in>| declared_producers ?D" and d': "d' = g d"
      by (auto simp: declarations_relocated_def)
    have ds: "d \<in> declared_sites ?D" by (rule declared_sites_members(1)[OF d])
    have "producer_discharged ?M d V hs (corr d)" using narrowed_producer[OF discharged] d by simp
    then show "producer_discharged ?M' d' V hs (?c d')"
      unfolding producer_discharged_def d' inv[OF ds] at[OF ds] .
  next
    fix d' e' V i assume "(d',e',V,i) |\<in>| declared_consumers (declarations_relocated g ?D)"
    then obtain d e where de: "(d,e,V,i) |\<in>| declared_consumers ?D" and d': "d' = g d" and e': "e' = g e"
      by (auto simp: declarations_relocated_def)
    have ds: "d \<in> declared_sites ?D" by (rule declared_sites_members(2)[OF de])
    have es: "e \<in> declared_sites ?D" by (rule declared_sites_members(3)[OF de])
    have "consumer_discharged ?M e V (corr d i)" using narrowed_consumer[OF discharged] de by simp
    then show "consumer_discharged ?M' e' V (?c d' i)"
      unfolding consumer_discharged_def d' e' inv[OF ds] at[OF es] .
  next
    fix e' S' s keep Vp Vh assume "(e',S',s,keep,Vp,Vh) |\<in>| declared_sockets (declarations_relocated g ?D)"
    then obtain e S where eS: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?D" and S': "S' = finite_rename_schema id id g S"
      and e': "e' = g e"
      by (auto simp: declarations_relocated_def)
    have eSN: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND" using eS by simp
    have src: "narrowed_socket_discharged ?M S s keep Vp Vh (declared_narrowing ND e S s)"
      by (rule narrowed_socket[OF discharged eSN])
    have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
      by (rule declared_sites_members(5)[OF eS])
    show "narrowed_socket_discharged ?M' S' s keep Vp Vh (\<nu> e' S' s)" unfolding S' e' relocates[OF eSN]
      by (rule narrowed_socket_discharged_relocated[OF src at]) (use sub in blast)
  qed
qed

theorem narrowed_declarations_agree_discharged:
  assumes Pf: "schema_system_formed P" and Qf: "schema_system_formed Q"
    and agree: "systems_agree_on P Q V" and closed: "system_dependency_closed P V"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> V"
    and discharged: "narrowed_declarations_discharged (positive_meaning P) ND corr"
  shows "narrowed_declarations_discharged (positive_meaning Q) ND corr"
proof -
  let ?D = "resolution_declarations.truncate ND"
  have at: "(d,x) \<in> positive_meaning Q \<longleftrightarrow> (d,x) \<in> positive_meaning P" if "d \<in> declared_sites ?D" for d x
    using positive_meaning_dependency_locality[OF Pf Qf agree closed subsetD[OF sites that]] by simp
  show ?thesis unfolding narrowed_declarations_discharged_def
  proof (intro conjI allI impI)
    show "declarations_formed ?D" by (rule narrowed_formed[OF discharged])
  next
    fix d W hs assume d: "(d,W,hs) |\<in>| declared_producers ND"
    have d': "(d,W,hs) |\<in>| declared_producers ?D" using d by simp
    have "producer_discharged (positive_meaning P) d W hs (corr d)" by (rule narrowed_producer[OF discharged d])
    then show "producer_discharged (positive_meaning Q) d W hs (corr d)"
      unfolding producer_discharged_def at[OF declared_sites_members(1)[OF d']] .
  next
    fix d e W i assume de: "(d,e,W,i) |\<in>| declared_consumers ND"
    have de': "(d,e,W,i) |\<in>| declared_consumers ?D" using de by simp
    have "consumer_discharged (positive_meaning P) e W (corr d i)" by (rule narrowed_consumer[OF discharged de])
    then show "consumer_discharged (positive_meaning Q) e W (corr d i)"
      unfolding consumer_discharged_def at[OF declared_sites_members(3)[OF de']] .
  next
    fix e S s keep Vp Vh assume eS: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND"
    have eS': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?D" using eS by simp
    have src: "narrowed_socket_discharged (positive_meaning P) S s keep Vp Vh (declared_narrowing ND e S s)"
      by (rule narrowed_socket[OF discharged eS])
    have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
      by (rule declared_sites_members(5)[OF eS'])
    have eqQ: "(id d,x) \<in> positive_meaning Q \<longleftrightarrow> (d,x) \<in> positive_meaning P"
      if "d \<in> schema_dependencies (decode_finite_schema S)" for d x
      using sub at that by (simp add: subset_iff)
    show "narrowed_socket_discharged (positive_meaning Q) S s keep Vp Vh (declared_narrowing ND e S s)"
    proof (rule narrowed_socket_discharged_callees[OF src _ _ _ _ eqQ])
      show "(q,e',p) |\<in>| finite_schema_premises S \<longleftrightarrow> (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e' = id d)"
        for q e' p by simp
      show "clause_true (positive_meaning Q) (decode_finite_schema S) h \<longleftrightarrow>
          clause_true (positive_meaning P) (decode_finite_schema S) h" for h
        using clause_true_relocated[of "decode_finite_schema S" id "positive_meaning Q" "positive_meaning P" h, OF eqQ]
        by simp
    qed simp_all
  qed
qed

text \<open>
  A head registration relocates with the construction: the relocated schema has the source's head, so the view reads
  the same input and output; the relocated construction's value at a relocated clause is a source clause's value
  (@{thm [source] finite_relocated_construction_value}), so production and answers carry.
\<close>

lemma head_registration_relocated [simp]:
  "head_registration Vc (finite_rename_schema id id g S) a \<longleftrightarrow> head_registration Vc S a"
  by (simp add: head_registration_def)

lemma head_registration_input_relocated [simp]:
  "head_registration_input Vc (finite_rename_schema id id g S) B = head_registration_input Vc S B"
  by (simp add: head_registration_input_def)

lemma head_registration_produces_relocated:
  assumes src: "\<And>d0 c S0. ((d0,c),S0) |\<in>| finite_system_clauses P \<Longrightarrow> g d0 = e \<Longrightarrow>
      finite_rename_schema id id g S0 = T \<Longrightarrow> a |\<in>| witness_registered \<kappa> d0 S0 \<Longrightarrow>
      head_registration_produces \<kappa> P d0 S0 a N"
  shows "head_registration_produces (finite_relocated_construction g P \<kappa>) Q e T a N"
  unfolding head_registration_produces_def
proof (intro allI impI)
  fix B v assume val: "witness_value (finite_relocated_construction g P \<kappa>) Q e T B a = Some v"
  obtain d0 c S0 where c: "((d0,c),S0) |\<in>| finite_system_clauses P" "g d0 = e" "finite_rename_schema id id g S0 = T"
      "a |\<in>| witness_registered \<kappa> d0 S0" "witness_value \<kappa> P d0 S0 B a = Some v"
    using finite_relocated_construction_value[OF val] by blast
  have "head_registration_produces \<kappa> P d0 S0 a N" by (rule src[OF c(1-4)])
  then show "finite_term_formed v \<and> N (decode_finite_term v)" using c(5) unfolding head_registration_produces_def by blast
qed

lemma head_registration_answers_relocated:
  assumes src: "\<And>d0 c S0. ((d0,c),S0) |\<in>| finite_system_clauses P \<Longrightarrow> g d0 = e \<Longrightarrow>
      finite_rename_schema id id g S0 = T \<Longrightarrow> a |\<in>| witness_registered \<kappa> d0 S0 \<Longrightarrow>
      head_registration_answers M \<kappa> P d0 S0 Vc a \<and> (\<forall>x. (e,x) \<in> M' \<longleftrightarrow> (d0,x) \<in> M)"
  shows "head_registration_answers M' (finite_relocated_construction g P \<kappa>) Q e T Vc a"
  unfolding head_registration_answers_def
proof (intro allI impI)
  fix B v x t y
  assume val: "witness_value (finite_relocated_construction g P \<kappa>) Q e T B a = Some v"
    and inp: "head_registration_input Vc T B = Some x" and et: "(e,t) \<in> M'"
    and vt: "resolution_view_term Vc t = Some (x,y)"
  obtain d0 c S0 where c: "((d0,c),S0) |\<in>| finite_system_clauses P" "g d0 = e" "finite_rename_schema id id g S0 = T"
      "a |\<in>| witness_registered \<kappa> d0 S0" "witness_value \<kappa> P d0 S0 B a = Some v"
    using finite_relocated_construction_value[OF val] by blast
  have ans: "head_registration_answers M \<kappa> P d0 S0 Vc a" and eq: "\<forall>x. (e,x) \<in> M' \<longleftrightarrow> (d0,x) \<in> M"
    using src[OF c(1-4)] by blast+
  have inp0: "head_registration_input Vc S0 B = Some x" using inp by (simp add: c(3)[symmetric])
  have d0t: "(d0,t) \<in> M" using et eq by blast
  obtain t' where "(d0,t') \<in> M" "resolution_view_term Vc t' = Some (x,decode_finite_term v)"
    using ans[unfolded head_registration_answers_def, rule_format, OF c(5) inp0 d0t vt] by blast
  then show "\<exists>t'. (e,t') \<in> M' \<and> resolution_view_term Vc t' = Some (x,decode_finite_term v)" using eq by blast
qed

lemma head_registration_answers_agree:
  assumes "\<And>x. (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "head_registration_answers M' \<kappa> P d S Vc a \<longleftrightarrow> head_registration_answers M \<kappa> P d S Vc a"
  unfolding head_registration_answers_def by (simp add: assms)

end
