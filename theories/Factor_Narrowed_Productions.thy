theory Factor_Narrowed_Productions
  imports Factor_Narrowed_Commitments Factor_Resolution_Socket_Discharges
begin

text \<open>
  The exchange at narrowed sockets (R5f2 of DECISIONS.md "The native evaluator constructs the missing witnesses by
  resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", the correction
  closing it, task 725). R5f1's narrowed commitment (@{const finite_narrowed_commitment}) commits where R5's framed test
  of the record's truncation commits, and at a goal committed at a narrowed socket declaring a production it runs the
  goal's sub-search from the produced state, the goal's viewed output bound to the production's value. The exchange
  premise (@{const finite_commitment_exchanges}) is derived here from the record's discharge: at a producing goal from
  the socket's obligation over its class N at the kept answer, whose output is the produced value, in N by the
  production's discharge (@{text finite_narrowed_commitment_exchange}); at a committed goal with no production and at a
  material goal from R5's discharge of the sockets whose obligation holds over every answer
  (@{text unrestricted_declarations}). Two conditions the correction does not name stand as named premises while the
  planner decides them (q134): a goal committed at a socket whose class is not every answer produces and its
  production binds (@{text finite_narrowed_committed_apply}); the produced state's support at the parent's barring
  (@{text finite_narrowed_productions_supported}).
\<close>

section \<open>The narrowed socket at a frame\<close>

lemma narrowed_socket_default_framed:
  assumes obl: "narrowed_socket_discharged M S s keep Vp Vh N" and formed: "schema_formed (decode_finite_schema S)"
  shows "narrowed_socket_framed M S s keep Vp Vh N (socket_default_frame Vp Vh S s)"
proof -
  note O = obl[unfolded narrowed_socket_discharged_def]
  have narrow: "socket_narrowing M S s Vp N" using O by (rule conjunct1)
  have first: "\<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None"
    using O by blast
  have obl2: "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>d p xi yo t y'. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow>
        (d,t) \<in> M \<longrightarrow> resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow>
        N y' \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = y')) \<and>
      (\<forall>N g. (s,N) \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N \<longrightarrow>
        evaluate_pattern g (material_source N) = evaluate_pattern h (material_source N) \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>material_variables N. h' a = g a)))"
    using conjunct2[OF conjunct2[OF O]] .
  have calls: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      (\<forall>a\<in>schema_variables (decode_finite_schema S) - socket_default_frame Vp Vh S s. h' a = h a) \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = y'"
    if h: "clause_true M (decode_finite_schema S) h" and p: "(s,d,p) |\<in>| finite_schema_premises S"
      and v: "resolution_view_pattern Vp p = Some (xi,yo)" and t: "(d,t) \<in> M"
      and vt: "resolution_view_term Vp t = Some (evaluate_pattern h (decode_finite_pattern xi),y')" and n: "N y'"
    for h d p xi yo t y'
  proof -
    obtain h' where cl: "clause_true M (decode_finite_schema S) h'" and hk: "head_kept keep Vh S h h'"
        and inp: "\<forall>a\<in>socket_inputs Vp Vh S s. h' a = h a" and yo: "evaluate_pattern h' (decode_finite_pattern yo) = y'"
      using socket_inputs_kept_class(1)[OF obl2 formed h p v t vt n] by blast
    have xi: "evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
      by (rule evaluate_pattern_cong) (use inp p v in \<open>unfold socket_inputs_def, blast\<close>)
    have fr: "\<forall>a\<in>schema_variables (decode_finite_schema S) - socket_default_frame Vp Vh S s. h' a = h a"
      using inp by (auto simp: socket_default_frame_def)
    show ?thesis using cl hk fr xi yo by blast
  qed
  have mats: "\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
      (\<forall>a\<in>schema_variables (decode_finite_schema S) - socket_default_frame Vp Vh S s. h' a = h a) \<and>
      (\<forall>a\<in>material_variables N'. h' a = g a)"
    if h: "clause_true M (decode_finite_schema S) h" and N': "(s,N') \<in> schema_material_premises (decode_finite_schema S)"
      and g: "evaluate_material_satisfaction g N'"
      and src: "evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N')" for h N' g
  proof -
    obtain h' where cl: "clause_true M (decode_finite_schema S) h'" and hk: "head_kept keep Vh S h h'"
        and inp: "\<forall>a\<in>socket_inputs Vp Vh S s. h' a = h a" and ag: "\<forall>a\<in>material_variables N'. h' a = g a"
      using socket_inputs_kept_class(2)[OF obl2 formed h N' g src] by blast
    have fr: "\<forall>a\<in>schema_variables (decode_finite_schema S) - socket_default_frame Vp Vh S s. h' a = h a"
      using inp by (auto simp: socket_default_frame_def)
    show ?thesis using cl hk fr ag by blast
  qed
  show ?thesis unfolding narrowed_socket_framed_def using narrow first calls mats by blast
qed

lemma narrowed_frame_at_framed:
  assumes dis: "narrowed_declarations_discharged M ND corr" and frames: "narrowed_frames_discharged M ND \<Phi>"
    and socket: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND" and at: "finite_frame_at \<Phi> Vp Vh e S s ch = Some C"
    and formed: "schema_formed (decode_finite_schema S)"
  shows "narrowed_socket_framed M S s keep Vp Vh (declared_narrowing ND e S s) (fset C)"
proof (cases ch)
  case None
  then have C: "C = finite_default_frame Vp Vh S s" using at by (simp add: finite_frame_at_def)
  show ?thesis unfolding C finite_default_frame_correct
    by (rule narrowed_socket_default_framed[OF narrowed_socket[OF dis socket] formed])
next
  case (Some C')
  then have "(e,S,s,C) |\<in>| \<Phi>" using at by (simp add: finite_frame_at_def split: if_splits)
  then show ?thesis using frames socket unfolding narrowed_frames_discharged_def by blast
qed

lemma narrowed_socket_framed_viewed:
  "narrowed_socket_framed M S s keep Vp Vh N C \<Longrightarrow>
    \<forall>d p. (s,d,p) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p \<noteq> None"
  by (simp add: narrowed_socket_framed_def)

lemma narrowed_socket_framed_calls:
  assumes "narrowed_socket_framed M S s keep Vp Vh N C"
  shows "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
    (\<forall>e1 p1 xi yo u y'. (s,e1,p1) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow>
      (e1,u) \<in> M \<longrightarrow> resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow> N y' \<longrightarrow>
      (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'))"
  using assms unfolding narrowed_socket_framed_def by blast

text \<open>A socket with no call premise: its narrowed obligation is R5's, whatever its class.\<close>

lemma narrowed_socket_material_discharged:
  assumes none: "\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S" and obl: "narrowed_socket_discharged M S s keep Vp Vh N"
  shows "socket_discharged M S s keep Vp Vh"
proof -
  have mats: "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>N' g. (s,N') \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N' \<longrightarrow>
        evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N') \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>material_variables N'. h' a = g a)))"
    using obl unfolding narrowed_socket_discharged_def by blast
  show ?thesis unfolding socket_discharged_def using none mats by blast
qed

lemma narrowed_socket_material_framed:
  assumes none: "\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S" and obl: "narrowed_socket_framed M S s keep Vp Vh N C"
  shows "socket_framed M S s keep Vp Vh C"
proof -
  have mats: "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
      (\<forall>N' g. (s,N') \<in> schema_material_premises (decode_finite_schema S) \<longrightarrow> evaluate_material_satisfaction g N' \<longrightarrow>
        evaluate_pattern g (material_source N') = evaluate_pattern h (material_source N') \<longrightarrow>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
          (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
          (\<forall>a\<in>material_variables N'. h' a = g a)))"
    using obl unfolding narrowed_socket_framed_def by blast
  show ?thesis unfolding socket_framed_def using none mats by blast
qed

section \<open>The produced record's truncations\<close>

lemma produced_truncations [simp]:
  "declared_producers (narrowed_declarations.truncate D) = declared_producers D"
  "declared_consumers (narrowed_declarations.truncate D) = declared_consumers D"
  "declared_sockets (narrowed_declarations.truncate D) = declared_sockets D"
  "declared_narrowing (narrowed_declarations.truncate D) = declared_narrowing D"
  "resolution_declarations.truncate (narrowed_declarations.truncate D) = resolution_declarations.truncate D"
  by (simp_all add: narrowed_declarations.truncate_def resolution_declarations.truncate_def)

lemma produced_framed_viewed:
  assumes dis: "narrowed_declarations_discharged M (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged M (narrowed_declarations.truncate D) \<Phi>"
    and t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate D)"
    and at: "finite_frame_at \<Phi> Vp Vh e S s ch = Some C" and formed: "schema_formed (decode_finite_schema S)"
  shows "\<forall>e1 p1. (s,e1,p1) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p1 \<noteq> None"
proof -
  have t': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate D)" using t by simp
  show ?thesis by (rule narrowed_socket_framed_viewed[OF narrowed_frame_at_framed[OF dis frames t' at formed]])
qed

lemma produced_framed_calls:
  assumes dis: "narrowed_declarations_discharged M (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged M (narrowed_declarations.truncate D) \<Phi>"
    and t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate D)"
    and at: "finite_frame_at \<Phi> Vp Vh e S s ch = Some C" and formed: "schema_formed (decode_finite_schema S)"
  shows "\<forall>h. clause_true M (decode_finite_schema S) h \<longrightarrow>
    (\<forall>e1 p1 xi yo u y'. (s,e1,p1) |\<in>| finite_schema_premises S \<longrightarrow> resolution_view_pattern Vp p1 = Some (xi,yo) \<longrightarrow>
      (e1,u) \<in> M \<longrightarrow> resolution_view_term Vp u = Some (evaluate_pattern h (decode_finite_pattern xi),y') \<longrightarrow>
      declared_narrowing D e S s y' \<longrightarrow>
      (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - fset C. h' a = h a) \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = y'))"
proof -
  have t': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate D)" using t by simp
  show ?thesis
    using narrowed_socket_framed_calls[OF narrowed_frame_at_framed[OF dis frames t' at formed]] by simp
qed

section \<open>The sockets whose obligation holds over every answer\<close>

text \<open>
  The record's sockets whose class is every answer, or which hold no call premise (a material socket, whose narrowed
  obligation is R5's): R5's discharge holds of them, and R5's discharges apply at every goal committed there.
\<close>

definition unrestricted_declarations ::
    "('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_declarations" where
  "unrestricted_declarations D = (resolution_declarations.truncate D)\<lparr>declared_sockets := ffilter
    (\<lambda>(e,S,s,keep,Vp,Vh). declared_narrowing D e S s = (\<lambda>_. True) \<or> (\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S))
    (declared_sockets D)\<rparr>"

lemma unrestricted_fields [simp]:
  "declared_producers (unrestricted_declarations D) = declared_producers D"
  "declared_consumers (unrestricted_declarations D) = declared_consumers D"
  "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (unrestricted_declarations D) \<longleftrightarrow> (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<and>
    (declared_narrowing D e S s = (\<lambda>_. True) \<or> (\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S))"
  by (auto simp: unrestricted_declarations_def)

lemma unrestricted_discharged:
  assumes dis: "narrowed_declarations_discharged M (narrowed_declarations.truncate D) corr"
  shows "declarations_discharged M (unrestricted_declarations D) corr"
proof -
  have formed: "declarations_formed (resolution_declarations.truncate D)" using narrowed_formed[OF dis] by simp
  have formed': "declarations_formed (unrestricted_declarations D)"
    using formed unfolding declarations_formed_def by (auto simp: unrestricted_declarations_def)
  have prod: "producer_discharged M d V hs (corr d)" if "(d,V,hs) |\<in>| declared_producers (unrestricted_declarations D)"
    for d V hs using narrowed_producer[OF dis] that by simp
  have cons: "consumer_discharged M e V (corr d i)" if "(d,e,V,i) |\<in>| declared_consumers (unrestricted_declarations D)"
    for d e V i using narrowed_consumer[OF dis] that by simp
  have sock: "socket_discharged M S s keep Vp Vh"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (unrestricted_declarations D)" for e S s keep Vp Vh
  proof -
    have t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate D)" using that by simp
    have ok: "declared_narrowing D e S s = (\<lambda>_. True) \<or> (\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S)"
      using that by simp
    have n: "narrowed_socket_discharged M S s keep Vp Vh (declared_narrowing D e S s)"
      using narrowed_socket[OF dis t] by simp
    show ?thesis using ok
    proof
      assume "declared_narrowing D e S s = (\<lambda>_. True)"
      then show ?thesis using n by (simp add: socket_discharged_narrowed)
    next
      assume "\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S"
      then show ?thesis by (rule narrowed_socket_material_discharged[OF _ n])
    qed
  qed
  show ?thesis unfolding declarations_discharged_def using formed' prod cons sock by blast
qed

lemma unrestricted_frames:
  assumes frames: "narrowed_frames_discharged M (narrowed_declarations.truncate D) \<Phi>"
  shows "frames_discharged M (unrestricted_declarations D) \<Phi>"
  unfolding frames_discharged_def
proof (intro allI impI)
  fix e S s C keep Vp Vh
  assume ph: "(e,S,s,C) |\<in>| \<Phi>" and t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (unrestricted_declarations D)"
  have t0: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate D)" using t by simp
  have ok: "declared_narrowing D e S s = (\<lambda>_. True) \<or> (\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S)" using t by simp
  have n0: "narrowed_socket_framed M S s keep Vp Vh (declared_narrowing (narrowed_declarations.truncate D) e S s) (fset C)"
    using frames ph t0 unfolding narrowed_frames_discharged_def by blast
  have n: "narrowed_socket_framed M S s keep Vp Vh (declared_narrowing D e S s) (fset C)" using n0 by simp
  show "socket_framed M S s keep Vp Vh (fset C)" using ok
  proof
    assume "declared_narrowing D e S s = (\<lambda>_. True)"
    then show ?thesis using n by (simp add: socket_framed_narrowed)
  next
    assume "\<forall>d p. (s,d,p) |\<notin>| finite_schema_premises S"
    then show ?thesis by (rule narrowed_socket_material_framed[OF _ n])
  qed
qed

section \<open>R5's framed test reads the sockets at the goal's parent alone\<close>

lemma socket_kept_framed_sockets:
  assumes kf: "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q Y g"
    and sockets: "\<And>nd keep. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd = butlast q \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D'"
  shows "finite_socket_kept_framed D' \<Phi> Vp Vh ch F st q Y g"
  using kf sockets unfolding finite_socket_kept_framed_def fBex_member_iff by blast

lemma socket_free_framed_sockets:
  assumes kf: "finite_socket_free_framed D \<Phi> Vp Vh ch F st q Y g"
    and sockets: "\<And>nd keep. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd = butlast q \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D'"
  shows "finite_socket_free_framed D' \<Phi> Vp Vh ch F st q Y g"
  using kf sockets unfolding finite_socket_free_framed_def fBex_member_iff by blast

lemma socket_declared_framed_sockets:
  assumes kf: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g"
    and sockets: "\<And>nd keep. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd = butlast q \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D'"
  shows "finite_socket_declared_framed D' \<Phi> Vp Vh ch F st q Y g"
  using kf socket_kept_framed_sockets[OF _ sockets] socket_free_framed_sockets[OF _ sockets]
  unfolding finite_socket_declared_framed_def by blast

lemma socket_declared_framed_views:
  assumes "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g"
  shows "(Vp,Vh) |\<in>| finite_socket_views D"
proof -
  obtain e S s keep where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    using assms unfolding finite_socket_declared_framed_def finite_socket_kept_framed_def
      finite_socket_free_framed_def fBex_member_iff by blast
  then show ?thesis unfolding finite_socket_views_def by (rule rev_fimage_eqI) simp
qed

lemma direct_commitment_sockets:
  assumes producers: "declared_producers D' = declared_producers D"
    and consumers: "declared_consumers D' = declared_consumers D"
  shows "finite_direct_commitment D' F st g = finite_direct_commitment D F st g"
  unfolding finite_direct_commitment_def finite_producer_commits_def finite_output_consumer_def producers consumers ..

lemma socket_declared_framed_position:
  "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g \<Longrightarrow> q \<noteq> []"
  by (auto simp: finite_socket_declared_framed_def finite_socket_kept_framed_def finite_socket_free_framed_def)

context
  fixes D D' :: "('a,'s,'d) resolution_declarations" and st :: "('a,'s,'d,'c) resolution_state"
    and g :: "('a,'s,'d,'c) resolution_goal"
  assumes producers: "declared_producers D' = declared_producers D"
    and consumers: "declared_consumers D' = declared_consumers D"
    and sockets: "\<And>nd keep Vp Vh. nd |\<in>| resolution_nodes st \<Longrightarrow>
      resolution_node_position nd = butlast (resolution_goal_position g) \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last (resolution_goal_position g),keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      (resolution_node_site nd,resolution_node_schema nd,last (resolution_goal_position g),keep,Vp,Vh) |\<in>| declared_sockets D'"
begin

lemma socket_commitment_framed_sockets:
  assumes sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
  shows "finite_socket_commitment_framed D' \<Phi> Vp Vh ch F st g"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  obtain x y where vp: "resolution_view_pattern Vp p = Some (x,y)" and x: "finite_pattern_variables x = {||}"
    and y: "finite_pattern_variables y \<noteq> {||}"
    and decl: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) g"
    using sc Resolution_Call_Goal by (auto simp: finite_socket_commitment_framed_def split: option.splits)
  have decl': "finite_socket_declared_framed D' \<Phi> Vp Vh ch F st q (finite_pattern_variables y) g"
    by (rule socket_declared_framed_sockets[OF decl]) (use sockets Resolution_Call_Goal in simp)
  show ?thesis using vp x y decl' Resolution_Call_Goal by (simp add: finite_socket_commitment_framed_def)
next
  case (Resolution_Material_Goal q r M)
  have c: "finite_canonical_solutions M \<noteq> None" "finite_free_fields M"
    and decl: "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) g"
    using sc Resolution_Material_Goal by (simp_all add: finite_socket_commitment_framed_def)
  have decl': "finite_socket_declared_framed D' \<Phi> Vp Vh ch F st q (finite_material_variables M) g"
    by (rule socket_declared_framed_sockets[OF decl]) (use sockets Resolution_Material_Goal in simp)
  show ?thesis using c decl' Resolution_Material_Goal by (simp add: finite_socket_commitment_framed_def)
qed

lemma call_framed_sockets:
  assumes cn: "finite_call_framed D \<Phi> Vp Vh ch F st g"
  shows "finite_call_framed D' \<Phi> Vp Vh ch F st g"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  have kept: "finite_socket_kept_framed D' \<Phi> Vp Vh ch F st q Y g"
    if "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q Y g" for Y
    by (rule socket_kept_framed_sockets[OF that]) (use sockets Resolution_Call_Goal in simp)
  show ?thesis
  proof (cases "resolution_view_pattern Vp p")
    case None
    then show ?thesis using Resolution_Call_Goal by (simp add: finite_call_framed_def)
  next
    case (Some xy)
    obtain x y where xy: "xy = (x,y)" by (cases xy)
    have "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        (case finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch of
            None \<Rightarrow> False
          | Some C \<Rightarrow> finite_children_framed C st nd (last q)) \<and> finite_premise_only_unshared nd \<and>
        finite_socket_pair Vp q (resolution_node_schema nd) \<and>
        (finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_pattern_variables y) g \<or>
          finite_input_output_apart Vh nd))"
      using cn Resolution_Call_Goal Some xy by (simp add: finite_call_framed_def)
    then have "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        (case finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch of
            None \<Rightarrow> False
          | Some C \<Rightarrow> finite_children_framed C st nd (last q)) \<and> finite_premise_only_unshared nd \<and>
        finite_socket_pair Vp q (resolution_node_schema nd) \<and>
        (finite_socket_kept_framed D' \<Phi> Vp Vh ch F st q (finite_pattern_variables y) g \<or>
          finite_input_output_apart Vh nd))"
      using kept unfolding fBex_member_iff by blast
    then show ?thesis using Resolution_Call_Goal Some xy by (simp add: finite_call_framed_def)
  qed
next
  case (Resolution_Material_Goal q r M)
  then show ?thesis by (simp add: finite_call_framed_def)
qed

lemma material_framed_sockets:
  assumes mn: "finite_material_framed D \<Phi> Vp Vh ch F st g"
  shows "finite_material_framed D' \<Phi> Vp Vh ch F st g"
proof (cases g)
  case (Resolution_Material_Goal q r M)
  have kept: "finite_socket_kept_framed D' \<Phi> Vp Vh ch F st q Y g"
    if "finite_socket_kept_framed D \<Phi> Vp Vh ch F st q Y g" for Y
    by (rule socket_kept_framed_sockets[OF that]) (use sockets Resolution_Material_Goal in simp)
  have "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
      (case finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch of
          None \<Rightarrow> False
        | Some C \<Rightarrow> finite_children_framed C st nd (last q)) \<and> finite_premise_only_unshared nd \<and>
      (finite_socket_kept_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) g \<or>
        finite_input_output_apart Vh nd))"
    using mn Resolution_Material_Goal by (simp add: finite_material_framed_def)
  then have "fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
      (case finite_frame_at \<Phi> Vp Vh (resolution_node_site nd) (resolution_node_schema nd) (last q) ch of
          None \<Rightarrow> False
        | Some C \<Rightarrow> finite_children_framed C st nd (last q)) \<and> finite_premise_only_unshared nd \<and>
      (finite_socket_kept_framed D' \<Phi> Vp Vh ch F st q (finite_material_variables M) g \<or>
        finite_input_output_apart Vh nd))"
    using kept unfolding fBex_member_iff by blast
  then show ?thesis using Resolution_Material_Goal by (simp add: finite_material_framed_def)
next
  case (Resolution_Call_Goal q r e p)
  then show ?thesis by (simp add: finite_material_framed_def)
qed

lemma framed_commitment_call_sockets:
  assumes cc: "commit_call (finite_framed_commitment D \<Phi>) F st g"
  shows "commit_call (finite_framed_commitment D' \<Phi>) F st g"
proof -
  have prem: "finite_goal_premise st g" and alt: "finite_direct_commitment D F st g \<or>
      (resolution_is_call g \<and> fBex (finite_socket_views D) (\<lambda>(Vp,Vh). fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
        finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> finite_call_framed D \<Phi> Vp Vh ch F st g)))"
    using cc by (simp_all add: finite_framed_commitment_def)
  show ?thesis
  proof (cases "finite_direct_commitment D F st g")
    case True
    have "finite_direct_commitment D' F st g"
      using True by (rule iffD2[OF direct_commitment_sockets[OF producers consumers]])
    then show ?thesis using prem by (simp add: finite_framed_commitment_def)
  next
    case False
    then obtain Vp Vh ch where call: "resolution_is_call g" and ch: "ch |\<in>| finite_frame_choices \<Phi>"
      and sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g" and cn: "finite_call_framed D \<Phi> Vp Vh ch F st g"
      using alt unfolding fBex_member_iff by auto
    have sc': "finite_socket_commitment_framed D' \<Phi> Vp Vh ch F st g" by (rule socket_commitment_framed_sockets[OF sc])
    have cn': "finite_call_framed D' \<Phi> Vp Vh ch F st g" by (rule call_framed_sockets[OF cn])
    obtain q r e p where gq: "g = Resolution_Call_Goal q r e p" using call by (cases g) simp_all
    have views: "(Vp,Vh) |\<in>| finite_socket_views D'"
      using sc' gq by (auto simp: finite_socket_commitment_framed_def split: option.splits
        intro: socket_declared_framed_views)
    have "fBex (finite_socket_views D') (\<lambda>(Vp,Vh). fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
        finite_socket_commitment_framed D' \<Phi> Vp Vh ch F st g \<and> finite_call_framed D' \<Phi> Vp Vh ch F st g))"
      using views ch sc' cn' unfolding fBex_member_iff by blast
    then show ?thesis using prem call by (simp add: finite_framed_commitment_def)
  qed
qed

lemma framed_commitment_material_sockets:
  assumes cm: "commit_material (finite_framed_commitment D \<Phi>) F st g"
  shows "commit_material (finite_framed_commitment D' \<Phi>) F st g"
proof -
  have prem: "finite_material_premise st g" and nc: "\<not> resolution_is_call g"
    and alt: "fBex (finite_socket_views D) (\<lambda>(Vp,Vh). fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
      finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> finite_material_framed D \<Phi> Vp Vh ch F st g))"
    using cm by (simp_all add: finite_framed_commitment_def)
  obtain Vp Vh ch where ch: "ch |\<in>| finite_frame_choices \<Phi>"
      and sc: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g" and mn: "finite_material_framed D \<Phi> Vp Vh ch F st g"
    using alt unfolding fBex_member_iff by auto
  have sc': "finite_socket_commitment_framed D' \<Phi> Vp Vh ch F st g" by (rule socket_commitment_framed_sockets[OF sc])
  have mn': "finite_material_framed D' \<Phi> Vp Vh ch F st g" by (rule material_framed_sockets[OF mn])
  obtain q r M where gq: "g = Resolution_Material_Goal q r M" using nc by (cases g) simp_all
  have views: "(Vp,Vh) |\<in>| finite_socket_views D'"
    using sc' gq by (auto simp: finite_socket_commitment_framed_def intro: socket_declared_framed_views)
  have "fBex (finite_socket_views D') (\<lambda>(Vp,Vh). fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
      finite_socket_commitment_framed D' \<Phi> Vp Vh ch F st g \<and> finite_material_framed D' \<Phi> Vp Vh ch F st g))"
    using views ch sc' mn' unfolding fBex_member_iff by blast
  then show ?thesis using prem nc by (simp add: finite_framed_commitment_def)
qed

end

section \<open>The produced state\<close>

text \<open>
  At a production that binds, the produced state is the state under the production's substitution, which binds only
  variables of the goal's pattern, each to a ground term (@{thm [source] finite_production_substitution_ground}). The
  goal stands there at its position with its pattern substituted, the premise of the same parent, unheld where it was
  unheld, and the state is placed where it was placed.
\<close>

lemma produced_goal_premise:
  assumes "finite_goal_premise st g"
  shows "finite_goal_premise (resolution_state_substitute \<sigma> st) (resolution_goal_substitute \<sigma> g)"
  unfolding finite_goal_premise_def resolution_goal_substitute_fields
proof
  assume ne: "resolution_goal_position g \<noteq> []"
  obtain np e0 p0 where np: "np |\<in>| resolution_nodes st" "resolution_node_position np = butlast (resolution_goal_position g)"
      "(last (resolution_goal_position g),e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    using assms ne unfolding finite_goal_premise_def by blast
  have m: "resolution_node_substitute \<sigma> np |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
    using np(1) by (auto simp: resolution_state_substitute_def resolution_fset_simps)
  have f: "resolution_node_position (resolution_node_substitute \<sigma> np) = resolution_node_position np"
    "resolution_node_schema (resolution_node_substitute \<sigma> np) = resolution_node_schema np" by (cases np; simp)+
  show "\<exists>np e0 p0. np |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st) \<and>
      resolution_node_position np = butlast (resolution_goal_position g) \<and>
      (last (resolution_goal_position g),e0,p0) |\<in>| finite_schema_premises (resolution_node_schema np)"
    using m f np by metis
qed

lemma produced_unheld:
  assumes ground: "\<And>z. \<sigma> z = Finite_Variable z \<or> (\<exists>w. \<sigma> z = finite_exact_term_pattern w)"
    and unheld: "\<not> finite_held \<kappa> st g"
  shows "\<not> finite_held \<kappa> (resolution_state_substitute \<sigma> st) (resolution_goal_substitute \<sigma> g)"
proof
  assume "finite_held \<kappa> (resolution_state_substitute \<sigma> st) (resolution_goal_substitute \<sigma> g)"
  then obtain nd' a where nd': "nd' |\<in>| resolution_nodes (resolution_state_substitute \<sigma> st)"
      and a: "a |\<in>| finite_free_registered \<kappa> nd'"
      and x: "((resolution_node_position nd',True),a) |\<in>| resolution_goal_variables (resolution_goal_substitute \<sigma> g)"
    unfolding finite_held_def fBex_member_iff by blast
  obtain nd where nd: "nd |\<in>| resolution_nodes st" and ndeq: "nd' = resolution_node_substitute \<sigma> nd"
    using nd' by (auto simp: resolution_state_substitute_def)
  let ?X = "((resolution_node_position nd,True),a)"
  have f: "resolution_node_position nd' = resolution_node_position nd" "resolution_node_site nd' = resolution_node_site nd"
    "resolution_node_schema nd' = resolution_node_schema nd"
    "resolution_node_bindings nd' = fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) (resolution_node_bindings nd)"
    unfolding ndeq by (cases nd; simp)+
  have ev: "finite_pattern_variables (finite_exact_term_pattern u) = {||}" for u :: finite_factor_term
    by (induction u) auto
  have reg: "a |\<in>| witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd)"
    and b: "(a,Finite_Variable ?X) |\<in>| resolution_node_bindings nd'"
    using a f unfolding finite_free_registered_def by auto
  obtain x0 where x0: "(a,x0) |\<in>| resolution_node_bindings nd" "finite_pattern_substitute \<sigma> x0 = Finite_Variable ?X"
    using b f(4) by auto
  have "x0 = Finite_Variable ?X"
  proof (cases x0)
    case (Finite_Variable w)
    then have sw: "\<sigma> w = Finite_Variable ?X" using x0(2) by simp
    have ne: "finite_exact_term_pattern u \<noteq> Finite_Variable ?X" for u :: finite_factor_term by (cases u) simp_all
    have "\<sigma> w = Finite_Variable w" using ground[of w] sw ne by metis
    then show ?thesis using sw Finite_Variable by simp
  qed (use x0(2) in simp_all)
  then have free: "a |\<in>| finite_free_registered \<kappa> nd" using reg x0(1) unfolding finite_free_registered_def by simp
  obtain w where w: "w |\<in>| resolution_goal_variables g" "?X |\<in>| finite_pattern_variables (\<sigma> w)"
    using x f(1) by (auto elim: resolution_goal_substitute_origin)
  have "w = ?X" using ground[of w] w(2) ev by auto
  then have "?X |\<in>| resolution_goal_variables g" using w(1) by simp
  then have "finite_held \<kappa> st g" using nd free unfolding finite_held_def fBex_member_iff by blast
  with unheld show False by simp
qed

lemma produced_exchange_context:
  assumes ground: "\<And>z. \<sigma> z = Finite_Variable z \<or> (z |\<in>| finite_pattern_variables p \<and> (\<exists>w. \<sigma> z = finite_exact_term_pattern w))"
    and yv: "finite_pattern_substitute \<sigma> y = finite_exact_term_pattern v"
    and ctx: "\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> M \<longrightarrow> N (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
      (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds M \<theta>1 h))"
    and Nv: "N (decode_finite_term v)"
  shows "finite_exchange_context M F q (resolution_state_substitute \<sigma> st) e (finite_pattern_substitute \<sigma> p)"
  unfolding finite_exchange_context_def
proof (intro allI impI)
  fix \<theta>2 assume new: "(e,decode_finite_term (resolution_value \<theta>2 (finite_pattern_substitute \<sigma> p))) \<in> M"
  define \<theta>2' where "\<theta>2' = (\<lambda>z. resolution_value \<theta>2 (\<sigma> z))"
  have ex: "resolution_value \<theta> (finite_exact_term_pattern u) = u" for \<theta> :: "'v \<Rightarrow> finite_factor_term" and u
    by (induction u) (simp_all add: resolution_value_def)
  have ev: "finite_pattern_variables (finite_exact_term_pattern u) = {||}" for u :: finite_factor_term
    by (induction u) auto
  have a1: "(e,decode_finite_term (resolution_value \<theta>2' p)) \<in> M"
    using new unfolding \<theta>2'_def by (simp add: resolution_value_composes)
  have vy: "resolution_value \<theta>2' y = v" unfolding \<theta>2'_def resolution_value_composes[symmetric] yv by (rule ex)
  have a2: "N (decode_finite_term (resolution_value \<theta>2' y))" using Nv vy by simp
  obtain \<theta>1' where t1: "\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1' z = \<theta>2' z"
    and hold: "\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
      finite_goal_holds M \<theta>1' h"
    using mp[OF mp[OF spec[OF ctx, of \<theta>2'] a1] a2] by blast
  define \<theta>1 where "\<theta>1 = (\<lambda>z. if z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) then \<theta>2 z else \<theta>1' z)"
  have key: "resolution_value \<theta>1 (\<sigma> z) = \<theta>1' z" for z
  proof (cases "\<sigma> z = Finite_Variable z")
    case True
    show ?thesis
    proof (cases "z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p)")
      case inp: True
      obtain w where w: "w |\<in>| finite_pattern_variables p" "z |\<in>| finite_pattern_variables (\<sigma> w)"
        using finite_pattern_substitute_origin[OF inp] by blast
      have "w = z" using ground[of w] w(2) ev by auto
      then have zp: "z |\<in>| finite_pattern_variables p" using w(1) by simp
      have "\<theta>1' z = \<theta>2' z" using t1 zp by blast
      also have "\<dots> = \<theta>2 z" by (simp add: \<theta>2'_def True resolution_value_def)
      finally show ?thesis by (simp add: True \<theta>1_def inp resolution_value_def)
    next
      case outp: False
      show ?thesis by (simp add: True \<theta>1_def outp resolution_value_def)
    qed
  next
    case False
    then obtain u where zp: "z |\<in>| finite_pattern_variables p" and su: "\<sigma> z = finite_exact_term_pattern u"
      using ground[of z] by blast
    have "\<theta>1' z = \<theta>2' z" using t1 zp by blast
    also have "\<dots> = u" by (simp add: \<theta>2'_def su ex)
    finally show ?thesis by (simp add: su ex)
  qed
  have eq: "(\<lambda>z. resolution_value \<theta>1 (\<sigma> z)) = \<theta>1'" by (rule ext) (rule key)
  have agree: "\<forall>z. z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) \<longrightarrow> \<theta>1 z = \<theta>2 z"
    by (simp add: \<theta>1_def)
  have holds: "finite_goal_holds M \<theta>1 h"
    if h: "h |\<in>| finite_focus_pending F (resolution_state_substitute \<sigma> st)"
      "\<not> resolution_focused (Some q) (resolution_goal_position h)" for h
  proof -
    have hp: "h |\<in>| resolution_pending (resolution_state_substitute \<sigma> st)" and hf: "resolution_focused F (resolution_goal_position h)"
      using h(1) by (simp_all add: finite_focus_pending_focused)
    obtain h0 where h0: "h0 |\<in>| resolution_pending st" and hh: "h = resolution_goal_substitute \<sigma> h0"
      using hp by (auto simp: resolution_state_substitute_def)
    have pos: "resolution_goal_position h0 = resolution_goal_position h" by (simp add: hh)
    have h0F: "h0 |\<in>| finite_focus_pending F st" using h0 hf pos by (simp add: finite_focus_pending_focused)
    have "finite_goal_holds M \<theta>1' h0" using hold h0F h(2) pos by simp
    then show ?thesis unfolding hh finite_goal_holds_substitute eq .
  qed
  show "\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables (finite_pattern_substitute \<sigma> p) \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
      (\<forall>h. h |\<in>| finite_focus_pending F (resolution_state_substitute \<sigma> st) \<longrightarrow>
        \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow> finite_goal_holds M \<theta>1 h)"
    using agree holds by blast
qed

section \<open>The production's discharge\<close>

text \<open>
  A production declared at a narrowed socket is discharged when its registration stands at the head's output at the
  socket's view, every value it produces is formed and in the socket's class, and every answer at the registration's
  input has one at the produced value (#599's @{const head_registration_produces} and @{const head_registration_answers},
  read of the collection construction of the registration alone at the commitment's bound): the conditions under which
  @{thm [source] registration_complete_at_socket} holds at the socket.
\<close>

definition productions_discharged ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations \<Rightarrow> bool" where
  "productions_discharged M P n D \<longleftrightarrow> (\<forall>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<longrightarrow>
    declared_production D e S s = Some R \<longrightarrow>
    head_registration Vp (registration_schema R) (registration_variable R) \<and>
    head_registration_produces (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
      (registration_variable R) (declared_narrowing D e S s) \<and>
    head_registration_answers M (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
      Vp (registration_variable R))"

lemma productions_discharged_none:
  assumes "\<And>e S s. declared_production D e S s = None"
  shows "productions_discharged M P n D"
  using assms by (simp add: productions_discharged_def)

lemma production_value_class:
  assumes pd: "productions_discharged M P n D" and t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    and R: "declared_production D e S s = Some R" and v: "finite_registration_production P n V R p = Some v"
  shows "finite_term_formed v \<and> declared_narrowing D e S s (decode_finite_term v)"
proof -
  have prod: "head_registration_produces (finite_collection_construction [R] n) P (registration_site R)
      (registration_schema R) (registration_variable R) (declared_narrowing D e S s)"
    using pd t R unfolding productions_discharged_def by blast
  obtain B where rv: "finite_registration_value P n R B = Some v"
    using v by (auto simp: finite_registration_production_def split: option.splits)
  have "witness_value (finite_collection_construction [R] n) P (registration_site R) (registration_schema R) B
      (registration_variable R) = Some v"
    using rv by (simp add: finite_collection_construction_def finite_registration_matches_def)
  then show ?thesis using prod unfolding head_registration_produces_def by blast
qed

section \<open>The exchange at a producing goal\<close>

text \<open>
  A production binds when it is met and its value matches the goal's viewed output.
\<close>

definition finite_production_binds ::
    "('a,'s,'d,'c) resolution_commitment \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_production_binds K F st g \<longleftrightarrow> (case g of
      Resolution_Call_Goal q r e p \<Rightarrow> (case commit_production K F st g of
          Some (V,v) \<Rightarrow> finite_production_substitution V p v \<noteq> None
        | None \<Rightarrow> False)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

theorem finite_narrowed_commitment_exchange:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and I: "resolution_invariant P d t st"
    and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>" and gF: "g |\<in>| finite_focus_pending F st"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and producing: "finite_goal_producing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and only: "finite_registrations_premise_only \<kappa> P" and H: "resolution_registrations_held \<kappa> st"
    and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some (resolution_goal_position g))
      (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))
      (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))"
  shows "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        K P n (Some (resolution_goal_position g))
        (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))
        (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?K = "finite_narrowed_commitment P m D \<Phi>"
  let ?T = "resolution_declarations.truncate D"
  obtain Vv where pr: "commit_production ?K F st g = Some Vv" using producing by (auto simp: finite_goal_producing_def)
  have call: "resolution_is_call g" and nf0: "F \<noteq> Some (resolution_goal_position g)"
    and cc: "commit_call ?K F st g" using producing by (simp_all add: finite_goal_producing_def)
  obtain q r e p VR v where gq: "g = Resolution_Call_Goal q r e p"
      and "commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g"
      and sing: "finite_singleton_option (finite_socket_productions D \<Phi> F st g) = Some VR"
      and "finite_registration_applies (fst VR) (snd VR) e p"
      and rv: "finite_registration_production P m (fst VR) (snd VR) p = Some v" and vv: "Vv = (fst VR,v)"
      and bound: "finite_production_substitution (fst VR) p v \<noteq> None"
    by (rule finite_narrowed_production_some[OF pr[unfolded finite_narrowed_commitment_fields]])
  have VRm: "VR |\<in>| finite_socket_productions D \<Phi> F st g" using sing by (simp add: finite_singleton_option_some)
  obtain q' r' e' p' nd keep Vh ch R where g': "g = Resolution_Call_Goal q' r' e' p'" and qne: "q' \<noteq> []"
      and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q'"
      and tup: "(resolution_node_site nd,resolution_node_schema nd,last q',keep,fst VR,Vh) |\<in>| declared_sockets D"
      and R: "declared_production D (resolution_node_site nd) (resolution_node_schema nd) (last q') = Some R"
        "snd VR = R"
      and sc: "finite_socket_commitment_framed ?T \<Phi> (fst VR) Vh ch F st g"
      and cn: "finite_call_framed ?T \<Phi> (fst VR) Vh ch F st g"
    by (rule finite_socket_productions_member[OF VRm])
  have qq: "q' = q" "p' = p" using g' gq by simp_all
  have formedD: "declarations_formed ?T" using narrowed_formed[OF discharged] by simp
  obtain q2 r2 e2 p2 x y nd2 where gq2: "g = Resolution_Call_Goal q2 r2 e2 p2"
      and vp2: "resolution_view_pattern (fst VR) p2 = Some (x,y)"
      and nd2: "nd2 |\<in>| resolution_nodes st" "resolution_node_position nd2 = butlast q2"
      and ctxN: "\<forall>\<theta>2. (e2,decode_finite_term (resolution_value \<theta>2 p2)) \<in> ?M \<longrightarrow>
        declared_narrowing D (resolution_node_site nd2) (resolution_node_schema nd2) (last q2)
          (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
        (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p2 \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
          (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q2) (resolution_goal_position h) \<longrightarrow>
            finite_goal_holds ?M \<theta>1 h))"
    by (rule finite_framed_socket_class_context[where Nc="declared_narrowing D", OF I sup gF formedD
      produced_framed_viewed[OF discharged frames] produced_framed_calls[OF discharged frames] call sc cn nf0])
  have eqs: "q2 = q" "r2 = r" "e2 = e" "p2 = p" using gq2 gq by simp_all
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have nd2eq: "nd2 = nd"
  proof -
    have "resolution_node_position nd2 = resolution_node_position nd" using nd(2) nd2(2) eqs qq by simp
    then show ?thesis using dist nd2(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  let ?N = "declared_narrowing D (resolution_node_site nd) (resolution_node_schema nd) (last q)"
  have Nv: "finite_term_formed v \<and> ?N (decode_finite_term v)"
    using production_value_class[OF productions tup R(1)] rv R(2) qq by simp
  obtain \<sigma> where \<sigma>: "finite_production_substitution (fst VR) p v = Some \<sigma>" using bound by blast
  have st0: "finite_produced_state ?K F st g = resolution_state_substitute \<sigma> st"
    using pr vv \<sigma> gq by (simp add: finite_produced_state_def)
  have ground: "\<And>z. \<sigma> z = Finite_Variable z \<or> (z |\<in>| finite_pattern_variables p \<and>
      (\<exists>w. finite_term_formed w \<and> \<sigma> z = finite_exact_term_pattern w))"
    by (rule finite_production_substitution_ground[OF \<sigma>])
  have vp: "resolution_view_pattern (fst VR) p = Some (x,y)" using vp2 eqs by simp
  have yv: "finite_pattern_substitute \<sigma> y = finite_exact_term_pattern v"
    using \<sigma> vp by (auto simp: finite_production_substitution_def split: if_splits)
  let ?st0 = "resolution_state_substitute \<sigma> st"
  let ?g0 = "Resolution_Call_Goal q r e (finite_pattern_substitute \<sigma> p)"
  have gpend: "g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have g0: "?g0 |\<in>| resolution_pending ?st0"
    using fimageI[OF gpend, of "resolution_goal_substitute \<sigma>"] gq by (simp add: resolution_state_substitute_def)
  have cc': "commit_call (finite_framed_commitment ?T \<Phi>) F st g" using cc by simp
  have parent0: "finite_goal_premise ?st0 ?g0"
    using produced_goal_premise[OF finite_framed_commitment_premise[OF cc'], of \<sigma>] gq by simp
  have unheld0: "\<not> finite_held \<kappa> ?st0 ?g0"
    using produced_unheld[OF _ unheld, of \<sigma>] ground gq by fastforce
  have I0: "resolution_invariant P d t ?st0" using finite_produced_state_invariant[OF I, of ?K F g] st0 by simp
  have H0: "resolution_registrations_held \<kappa> ?st0" using finite_produced_state_held[OF H, of ?K F g] st0 by simp
  have placed0: "finite_state_placed (\<lambda>_. False) ?st0"
    using finite_substitution_step_placed[OF finite_produced_substitution_step[OF gpend,
      where K="finite_narrowed_commitment P m D \<Phi>" and F=F] resolution_supported_at_placed[OF sup]] st0 by simp
  have ctx: "\<forall>\<theta>2. (e,decode_finite_term (resolution_value \<theta>2 p)) \<in> ?M \<longrightarrow> ?N (decode_finite_term (resolution_value \<theta>2 y)) \<longrightarrow>
      (\<exists>\<theta>1. (\<forall>z. z |\<in>| finite_pattern_variables p \<longrightarrow> \<theta>1 z = \<theta>2 z) \<and>
        (\<forall>h. h |\<in>| finite_focus_pending F st \<longrightarrow> \<not> resolution_focused (Some q) (resolution_goal_position h) \<longrightarrow>
          finite_goal_holds ?M \<theta>1 h))"
    using ctxN eqs nd2eq by simp
  have ctx0: "finite_exchange_context ?M F q ?st0 e (finite_pattern_substitute \<sigma> p)"
    by (rule produced_exchange_context[OF _ yv ctx conjunct2[OF Nv]]) (use ground in blast)
  have s0': "s0 |\<in>| resolution_found (finite_committed_search \<kappa> K P n (Some q) (finite_committed_barring B ?st0) ?st0)"
    using s0 st0 gq by simp
  show ?thesis
    using finite_committed_exchange_placed[OF \<kappa> I0 placed0 g0 parent0 only H0 unheld0 ctx0 s0'] st0 gq by simp
qed

section \<open>The exchanges at the narrowed commitment\<close>

text \<open>
  A material goal's socket holds no call premise, so its narrowed obligation is R5's: its commitment is the framed
  test's at the unrestricted record.
\<close>

lemma material_goal_no_call_premise:
  assumes I: "resolution_invariant P d t st" and prem: "finite_material_premise st g"
    and qne: "resolution_goal_position g \<noteq> []"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
  shows "\<forall>d p. (last (resolution_goal_position g),d,p) |\<notin>| finite_schema_premises (resolution_node_schema nd)"
proof (intro allI notI)
  fix d' p' assume c: "(last (resolution_goal_position g),d',p') |\<in>| finite_schema_premises (resolution_node_schema nd)"
  obtain np z where np: "np |\<in>| resolution_nodes st" "resolution_node_position np = butlast (resolution_goal_position g)"
      and z: "z |\<in>| finite_schema_materials (resolution_node_schema np)" "fst z = last (resolution_goal_position g)"
    using prem qne unfolding finite_material_premise_def fBex_member_iff by blast
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have npnd: "np = nd"
  proof -
    have "resolution_node_position np = resolution_node_position nd" using np(2) nd(2) by simp
    then show ?thesis using dist np(1) nd(1) unfolding resolution_positions_distinct_def by blast
  qed
  have nplaced: "resolution_nodes_placed P d t st" using I by (simp add: resolution_invariant_def)
  have linked: "resolution_node_linked P st nd" using nplaced nd(1) unfolding resolution_nodes_placed_def by blast
  have formed: "schema_formed (decode_finite_schema (resolution_node_schema nd))"
    by (rule finite_linked_schema_formed[OF I linked])
  obtain M0 where zM: "z = (last (resolution_goal_position g),M0)" using z(2) by (cases z) simp
  have call: "(last (resolution_goal_position g),d',decode_finite_pattern p') \<in>
      schema_premises (decode_finite_schema (resolution_node_schema nd))"
    using c by (force simp: decode_finite_call_pattern_def)
  have mat: "(last (resolution_goal_position g),decode_finite_material M0) \<in>
      schema_material_premises (decode_finite_schema (resolution_node_schema nd))"
    using z(1) zM npnd by auto
  have "rel_dom (schema_premises (decode_finite_schema (resolution_node_schema nd))) \<inter>
      rel_dom (schema_material_premises (decode_finite_schema (resolution_node_schema nd))) = {}"
    using formed by (simp add: schema_formed_def)
  then show False using call mat by (auto simp: rel_dom_def)
qed

text \<open>
  The two conditions the correction does not name (q134), each discharged at a record declaring no narrowing and no
  production: a goal the narrowed commitment commits with no production and not at a declared producer stands at a
  socket whose class is every answer, and a production met binds; and the produced state is supported at the goal's
  position under the parent's barring.
\<close>

definition finite_narrowed_committed_apply ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> bool" where
  "finite_narrowed_committed_apply P m D \<Phi> \<longleftrightarrow> (\<forall>d t st F g. resolution_invariant P d t st \<longrightarrow>
    finite_goal_committing (finite_narrowed_commitment P m D \<Phi>) F st g \<longrightarrow>
    (commit_production (finite_narrowed_commitment P m D \<Phi>) F st g = None \<longrightarrow>
      \<not> finite_direct_commitment (resolution_declarations.truncate D) F st g \<longrightarrow>
      (\<forall>nd. nd |\<in>| resolution_nodes st \<longrightarrow> resolution_node_position nd = butlast (resolution_goal_position g) \<longrightarrow>
        declared_narrowing D (resolution_node_site nd) (resolution_node_schema nd) (last (resolution_goal_position g)) =
          (\<lambda>_. True))) \<and>
    (commit_production (finite_narrowed_commitment P m D \<Phi>) F st g \<noteq> None \<longrightarrow>
      finite_production_binds (finite_narrowed_commitment P m D \<Phi>) F st g))"

definition finite_narrowed_productions_supported ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> bool" where
  "finite_narrowed_productions_supported P m D \<Phi> \<longleftrightarrow> (\<forall>d t st F B \<theta> g. resolution_invariant P d t st \<longrightarrow>
    resolution_supported_at (\<lambda>_. False) F B P st \<theta> \<longrightarrow> g |\<in>| finite_focus_pending F st \<longrightarrow>
    finite_goal_producing (finite_narrowed_commitment P m D \<Phi>) F st g \<longrightarrow>
    (\<exists>\<theta>1. resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g))
      (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g)) P
      (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g) \<theta>1))"

text \<open>
  The static premise (task 767, q134): a socket whose class is narrower than every answer declares a production. It is
  vacuous at a record declaring no narrowing.
\<close>

definition narrowed_productions_declared :: "('a,'s,'d,'v) produced_declarations \<Rightarrow> bool" where
  "narrowed_productions_declared D \<longleftrightarrow> (\<forall>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<longrightarrow>
    declared_narrowing D e S s \<noteq> (\<lambda>_. True) \<longrightarrow> declared_production D e S s \<noteq> None)"

lemma narrowed_productions_declared_unnarrowed: "narrowed_productions_declared (unproduced (unnarrowed D))"
  by (simp add: narrowed_productions_declared_def)

text \<open>
  The first condition holds under the static premise: the corrected test commits a goal at a socket declaring a
  production only where the production is defined, so a goal it commits with no production and not at a declared
  producer stands at a socket declaring none, whose class is every answer; and a production defined binds.
\<close>

theorem finite_narrowed_committed_applies:
  assumes declared: "narrowed_productions_declared D"
  shows "finite_narrowed_committed_apply P m D \<Phi>"
  unfolding finite_narrowed_committed_apply_def
proof (intro allI impI conjI)
  fix d t st F g nd
  assume I: "resolution_invariant P d t st"
    and comm: "finite_goal_committing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and none: "commit_production (finite_narrowed_commitment P m D \<Phi>) F st g = None"
    and notdir: "\<not> finite_direct_commitment (resolution_declarations.truncate D) F st g"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast (resolution_goal_position g)"
  let ?T = "resolution_declarations.truncate D"
  have cc0: "commit_call (finite_narrowed_commitment P m D \<Phi>) F st g" and call: "resolution_is_call g"
    using comm by (simp_all add: finite_goal_committing_def)
  have pn: "finite_narrowed_production P m D \<Phi> F st g = None" using none by simp
  have cc: "commit_call (finite_framed_commitment ?T \<Phi>) F st g"
    and met: "finite_socket_productions D \<Phi> F st g = {||}"
    using cc0 pn by simp_all
  obtain Vp Vh ch where ch: "ch |\<in>| finite_frame_choices \<Phi>"
      and sc: "finite_socket_commitment_framed ?T \<Phi> Vp Vh ch F st g" and cn: "finite_call_framed ?T \<Phi> Vp Vh ch F st g"
    using cc notdir unfolding finite_framed_commitment_def fBex_member_iff by auto
  obtain q r e p where gq: "g = Resolution_Call_Goal q r e p" using call by (cases g) simp_all
  obtain x y where decl: "finite_socket_declared_framed ?T \<Phi> Vp Vh ch F st q (finite_pattern_variables y) g"
    using sc gq by (auto simp: finite_socket_commitment_framed_def split: option.splits)
  obtain nd0 keep where qne: "q \<noteq> []" and nd0: "nd0 |\<in>| resolution_nodes st" "resolution_node_position nd0 = butlast q"
      and tup: "(resolution_node_site nd0,resolution_node_schema nd0,last q,keep,Vp,Vh) |\<in>| declared_sockets D"
    using decl unfolding finite_socket_declared_framed_def finite_socket_kept_framed_def finite_socket_free_framed_def
      fBex_member_iff by auto
  have dist: "resolution_positions_distinct st" using I by (simp add: resolution_invariant_def)
  have ndeq: "nd = nd0"
  proof -
    have "resolution_node_position nd = resolution_node_position nd0" using nd(2) nd0(2) gq by simp
    then show ?thesis using dist nd(1) nd0(1) unfolding resolution_positions_distinct_def by blast
  qed
  show "declared_narrowing D (resolution_node_site nd) (resolution_node_schema nd) (last (resolution_goal_position g)) =
      (\<lambda>_. True)"
  proof (rule ccontr)
    assume ne: "declared_narrowing D (resolution_node_site nd) (resolution_node_schema nd)
      (last (resolution_goal_position g)) \<noteq> (\<lambda>_. True)"
    obtain R where R: "declared_production D (resolution_node_site nd0) (resolution_node_schema nd0) (last q) = Some R"
      using declared tup ne ndeq gq unfolding narrowed_productions_declared_def by fastforce
    have "(Vp,R) |\<in>| finite_socket_productions D \<Phi> F st g"
      by (rule finite_socket_productions_memberI[OF gq qne nd0 tup R ch sc cn])
    then show False using met by simp
  qed
next
  fix d t st F g
  assume "resolution_invariant P d t st" and "finite_goal_committing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and pr: "commit_production (finite_narrowed_commitment P m D \<Phi>) F st g \<noteq> None"
  obtain Vv where pv: "finite_narrowed_production P m D \<Phi> F st g = Some Vv" using pr by auto
  obtain q r e p VR v where gq: "g = Resolution_Call_Goal q r e p"
      and "commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g"
      and "finite_singleton_option (finite_socket_productions D \<Phi> F st g) = Some VR"
      and "finite_registration_applies (fst VR) (snd VR) e p"
      and "finite_registration_production P m (fst VR) (snd VR) p = Some v" and vv: "Vv = (fst VR,v)"
      and bound: "finite_production_substitution (fst VR) p v \<noteq> None"
    by (rule finite_narrowed_production_some[OF pv])
  show "finite_production_binds (finite_narrowed_commitment P m D \<Phi>) F st g"
    using pv gq vv bound by (simp add: finite_production_binds_def)
qed

text \<open>
  The second holds at discharged productions: at a producing goal the production applies, so the registration's
  input is the goal's, and its answers give one at the produced value (the production's (iii)); the produced state's
  goal is then true, alone under its position, and every node is barred, so the rank condition is vacuous.
\<close>

theorem finite_narrowed_productions_supports:
  assumes productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
  shows "finite_narrowed_productions_supported P m D \<Phi>"
  unfolding finite_narrowed_productions_supported_def
proof (intro allI impI)
  fix d t st F B \<theta> g
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and producing: "finite_goal_producing (finite_narrowed_commitment P m D \<Phi>) F st g"
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?K = "finite_narrowed_commitment P m D \<Phi>"
  obtain Vv where pv: "finite_narrowed_production P m D \<Phi> F st g = Some Vv"
    using producing by (auto simp: finite_goal_producing_def)
  obtain q r e p VR v where gq: "g = Resolution_Call_Goal q r e p"
      and "commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g"
      and sing: "finite_singleton_option (finite_socket_productions D \<Phi> F st g) = Some VR"
      and applies: "finite_registration_applies (fst VR) (snd VR) e p"
      and rv: "finite_registration_production P m (fst VR) (snd VR) p = Some v" and vv: "Vv = (fst VR,v)"
      and bound: "finite_production_substitution (fst VR) p v \<noteq> None"
    by (rule finite_narrowed_production_some[OF pv])
  have VRm: "VR |\<in>| finite_socket_productions D \<Phi> F st g" using sing by (simp add: finite_singleton_option_some)
  obtain q' r' e' p' nd keep Vh ch R where g': "g = Resolution_Call_Goal q' r' e' p'" and "q' \<noteq> []"
      and "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q'"
      and tup: "(resolution_node_site nd,resolution_node_schema nd,last q',keep,fst VR,Vh) |\<in>| declared_sockets D"
      and R: "declared_production D (resolution_node_site nd) (resolution_node_schema nd) (last q') = Some R"
        "snd VR = R"
      and "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
      and "finite_call_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
    by (rule finite_socket_productions_member[OF VRm])
  obtain q2 r2 e2 p2 x y where g2: "g = Resolution_Call_Goal q2 r2 e2 p2"
      and vp2: "resolution_view_pattern (fst VR) p2 = Some (x,y)" and xg: "finite_pattern_variables x = {||}"
    by (rule finite_socket_productions_ground[OF VRm])
  have vp: "resolution_view_pattern (fst VR) p = Some (x,y)" using vp2 g2 gq by simp
  have hr: "head_registration (fst VR) (registration_schema R) (registration_variable R)"
    and ans: "head_registration_answers ?M (finite_collection_construction [R] m) P (registration_site R)
      (registration_schema R) (fst VR) (registration_variable R)"
    using productions tup R(1) unfolding productions_discharged_def by blast+
  have vf: "view_formed (fst VR)" using hr by (simp add: head_registration_def)
  obtain ci where ci: "resolution_view_pattern (fst VR) (finite_schema_conclusion (registration_schema R)) =
      Some (ci,Finite_Variable (registration_variable R))"
    using hr by (auto simp: head_registration_def)
  let ?B = "finite_matching_bindings ci (finite_residual_term x)"
  have site: "registration_site R = e"
    and inp: "resolution_value (finite_binding_valuation ?B) ci = finite_residual_term x"
    using applies R(2) vp ci by (simp_all add: finite_registration_applies_def)
  have rvB: "finite_registration_value P m R ?B = Some v"
    using rv R(2) vp ci by (simp add: finite_registration_production_def)
  have wvB: "witness_value (finite_collection_construction [R] m) P (registration_site R) (registration_schema R) ?B
      (registration_variable R) = Some v"
    using rvB by (simp add: finite_collection_construction_def finite_registration_matches_def)
  have input: "head_registration_input (fst VR) (registration_schema R) ?B =
      Some (decode_finite_term (finite_residual_term x))"
    using ci inp by (simp add: head_registration_input_def decode_resolution_value[symmetric])
  have true: "(e,decode_finite_term (resolution_value \<theta> p)) \<in> ?M"
    using resolution_supported_at_holds[OF sup gF] gq by (simp add: finite_goal_holds_def)
  have xval: "resolution_value \<theta>' x = finite_residual_term x" for \<theta>'
    by (rule resolution_value_blank) (simp add: xg)
  have vt: "resolution_view_term (fst VR) (decode_finite_term (resolution_value \<theta> p)) =
      Some (decode_finite_term (finite_residual_term x),decode_finite_term (resolution_value \<theta> y))"
    using resolution_view_pattern_evaluate[OF vf vp, of "\<lambda>z. decode_finite_term (\<theta> z)"]
    by (simp add: decode_resolution_value[symmetric] xval)
  obtain t' where t': "(registration_site R,t') \<in> ?M"
      "resolution_view_term (fst VR) t' = Some (decode_finite_term (finite_residual_term x),decode_finite_term v)"
    using ans[unfolded head_registration_answers_def, rule_format, OF wvB input true[folded site] vt] by blast
  obtain \<sigma> where \<sigma>: "finite_production_substitution (fst VR) p v = Some \<sigma>" using bound by blast
  have yv: "finite_pattern_substitute \<sigma> y = finite_exact_term_pattern v"
    using \<sigma> vp by (auto simp: finite_production_substitution_def split: if_splits)
  have st0: "finite_produced_state ?K F st g = resolution_state_substitute \<sigma> st"
    using pv vv \<sigma> gq by (simp add: finite_produced_state_def)
  let ?\<theta>' = "\<lambda>z. resolution_value \<theta> (\<sigma> z)"
  have yv': "resolution_value ?\<theta>' y = v"
    using resolution_value_composes[of \<theta> \<sigma> y] yv resolution_value_ground[of \<theta> v] by simp
  have vt0: "resolution_view_term (fst VR) (decode_finite_term (resolution_value ?\<theta>' p)) =
      Some (decode_finite_term (finite_residual_term x),decode_finite_term v)"
    using resolution_view_pattern_evaluate[OF vf vp, of "\<lambda>z. decode_finite_term (?\<theta>' z)"]
    by (simp add: decode_resolution_value[symmetric] xval yv')
  obtain w1 w2 w3 where V3: "fst VR = (w1,w2,w3)" by (cases "fst VR") auto
  have vf3: "view_formed (w1,w2,w3)" using vf V3 by simp
  have eqt: "decode_finite_term (resolution_value ?\<theta>' p) = t'"
    by (rule resolution_view_injective[OF vf3 vt0[unfolded V3] t'(2)[unfolded V3]])
  have val0: "resolution_value \<theta> (finite_pattern_substitute \<sigma> p) = resolution_value ?\<theta>' p"
    by (rule resolution_value_composes)
  let ?st0 = "resolution_state_substitute \<sigma> st"
  let ?g0 = "Resolution_Call_Goal q r e (finite_pattern_substitute \<sigma> p)"
  have gpend: "g |\<in>| resolution_pending st" using gF by (simp add: finite_focus_pending_focused)
  have g0: "?g0 |\<in>| resolution_pending ?st0"
    using fimageI[OF gpend, of "resolution_goal_substitute \<sigma>"] gq by (simp add: resolution_state_substitute_def)
  have I0: "resolution_invariant P d t ?st0" using finite_produced_state_invariant[OF I, of ?K F g] st0 by simp
  have alone: "finite_focus_pending (Some q) ?st0 = {|?g0|}"
    using finite_committed_goal_alone[OF I0 g0] by simp
  have placed0: "finite_state_placed (\<lambda>_. False) ?st0"
    using finite_substitution_step_placed[OF finite_produced_substitution_step[OF gpend,
      where K="finite_narrowed_commitment P m D \<Phi>" and F=F] resolution_supported_at_placed[OF sup]] st0 by simp
  have holds: "finite_goal_holds ?M \<theta> h"
    if h: "h |\<in>| resolution_pending ?st0" "resolution_focused (Some q) (resolution_goal_position h)" for h
  proof -
    have "h |\<in>| finite_focus_pending (Some q) ?st0" using h by (simp add: finite_focus_pending_focused)
    then have "h = ?g0" using alone by simp
    then show ?thesis using site t'(1) eqt val0 by (simp add: finite_goal_holds_def)
  qed
  have "resolution_supported_at (\<lambda>_. False) (Some q) (fimage resolution_node_position (resolution_nodes ?st0)) P ?st0 \<theta>"
    by (rule resolution_supported_at_barred_allI[OF holds placed0])
  then have "resolution_supported_at (\<lambda>_. False) (Some q) (finite_committed_barring B ?st0) P ?st0 \<theta>"
    by (rule resolution_supported_at_barred_mono) (auto simp: finite_committed_barring_def)
  then show "\<exists>\<theta>1. resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g))
      (finite_committed_barring B (finite_produced_state ?K F st g)) P (finite_produced_state ?K F st g) \<theta>1"
    using st0 gq by auto
qed

lemma finite_narrowed_conditions_unproduced:
  "finite_narrowed_committed_apply P m (unproduced (unnarrowed D)) \<Phi>"
  "finite_narrowed_productions_supported P m (unproduced (unnarrowed D)) \<Phi>"
proof -
  have none: "finite_narrowed_production P m (unproduced (unnarrowed D)) \<Phi> F st g = None"
    for F st g by (rule finite_narrowed_production_none) simp
  show "finite_narrowed_committed_apply P m (unproduced (unnarrowed D)) \<Phi>"
    unfolding finite_narrowed_committed_apply_def by (simp add: none)
  show "finite_narrowed_productions_supported P m (unproduced (unnarrowed D)) \<Phi>"
    unfolding finite_narrowed_productions_supported_def by (simp add: finite_goal_producing_def none)
qed

theorem finite_narrowed_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P"
proof -
  have applies: "finite_narrowed_committed_apply P m D \<Phi>" by (rule finite_narrowed_committed_applies[OF declared])
  have supported: "finite_narrowed_productions_supported P m D \<Phi>"
    by (rule finite_narrowed_productions_supports[OF productions])
  show ?thesis
  unfolding finite_commitment_exchanges_def
proof (intro allI impI conjI)
  fix n F B st \<theta> g d t s0 B0 \<theta>0
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and committed: "finite_goal_committed (finite_narrowed_commitment P m D \<Phi>) F st g"
    and H: "resolution_registrations_held \<kappa> st" and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n
      (Some (resolution_goal_position g)) B st)"
    and "resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
  let ?T = "resolution_declarations.truncate D"
  let ?U = "unrestricted_declarations D"
  have cc: "commit_call (finite_framed_commitment ?T \<Phi>) F st g"
    and nf0: "F \<noteq> Some (resolution_goal_position g)"
    and none: "commit_production (finite_narrowed_commitment P m D \<Phi>) F st g = None"
    using committed by (simp_all add: finite_goal_committed_def)
  have disU: "declarations_discharged (positive_meaning (decode_finite_system P)) ?U corr"
    by (rule unrestricted_discharged[OF discharged])
  have framesU: "frames_discharged (positive_meaning (decode_finite_system P)) ?U \<Phi>"
    by (rule unrestricted_frames[OF frames])
  have dU: "finite_direct_commitment ?U F st g = finite_direct_commitment ?T F st g"
    by (rule direct_commitment_sockets) simp_all
  show "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        (finite_narrowed_commitment P m D \<Phi>) P n (Some (resolution_goal_position g)) B st)) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
  proof (cases "finite_direct_commitment ?T F st g")
    case True
    have dirU: "finite_direct_commitment ?U F st g" using True dU by simp
    show ?thesis by (rule finite_direct_exchange[OF \<kappa> I sup gF disU dirU finite_framed_commitment_premise[OF cc]
      only H unheld s0])
  next
    case False
    have comm: "finite_goal_committing (finite_narrowed_commitment P m D \<Phi>) F st g"
      using committed finite_goal_committing_parts by blast
    have top: "\<And>nd. nd |\<in>| resolution_nodes st \<Longrightarrow> resolution_node_position nd = butlast (resolution_goal_position g) \<Longrightarrow>
        declared_narrowing D (resolution_node_site nd) (resolution_node_schema nd) (last (resolution_goal_position g)) =
          (\<lambda>_. True)"
      using applies I comm none False unfolding finite_narrowed_committed_apply_def by blast
    have ccU: "commit_call (finite_framed_commitment ?U \<Phi>) F st g"
      by (rule framed_commitment_call_sockets[OF _ _ _ cc]) (use top in auto)
    have notdirU: "\<not> finite_direct_commitment ?U F st g" using False dU by simp
    show ?thesis by (rule finite_framed_socket_exchange[OF \<kappa> I sup gF disU framesU ccU nf0 notdirU only H unheld s0])
  qed
next
  fix n F B st \<theta> g d t q r M Ws
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st" and gq: "g = Resolution_Material_Goal q r M"
    and Ws: "finite_canonical_solutions M = Some Ws"
    and cm: "commit_material (finite_narrowed_commitment P m D \<Phi>) F st g"
  let ?T = "resolution_declarations.truncate D"
  let ?U = "unrestricted_declarations D"
  have cmT: "commit_material (finite_framed_commitment ?T \<Phi>) F st g" using cm by simp
  obtain Vp Vh ch where sc: "finite_socket_commitment_framed ?T \<Phi> Vp Vh ch F st g"
    using cmT unfolding finite_framed_commitment_def fBex_member_iff by auto
  have qne: "resolution_goal_position g \<noteq> []"
    using sc gq by (auto simp: finite_socket_commitment_framed_def dest: socket_declared_framed_position)
  have prem: "finite_material_premise st g" using cmT by (simp add: finite_framed_commitment_def)
  have cmU: "commit_material (finite_framed_commitment ?U \<Phi>) F st g"
    by (rule framed_commitment_material_sockets[OF _ _ _ cmT])
      (use material_goal_no_call_premise[OF I prem qne] in auto)
  show "\<exists>st' \<theta>'. st' |\<in>| finite_solution_successors st q r M Ws \<and>
      resolution_supported_at (\<lambda>_. False) F (finite_committed_barring B st) P st' \<theta>'"
    by (rule finite_framed_material_commitment_exchanges[OF unrestricted_discharged[OF discharged]
      unrestricted_frames[OF frames] I sup gF gq Ws cmU])
next
  fix n F B st \<theta> g d t
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and producing: "finite_goal_producing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and "resolution_registrations_held \<kappa> st" and "\<not> finite_held \<kappa> st g"
  show "\<exists>\<theta>1. resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g))
      (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g)) P
      (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g) \<theta>1"
    using supported I sup gF producing unfolding finite_narrowed_productions_supported_def by blast
next
  fix n F B st \<theta> g d t s0 B0 \<theta>0
  assume I: "resolution_invariant P d t st" and sup: "resolution_supported_at (\<lambda>_. False) F B P st \<theta>"
    and gF: "g |\<in>| finite_focus_pending F st"
    and producing: "finite_goal_producing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and H: "resolution_registrations_held \<kappa> st" and unheld: "\<not> finite_held \<kappa> st g"
    and s0: "s0 |\<in>| resolution_found (finite_committed_search \<kappa> (finite_narrowed_commitment P m D \<Phi>) P n
      (Some (resolution_goal_position g))
      (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))
      (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))"
    and "resolution_supported_at (\<lambda>_. False) (Some (resolution_goal_position g)) B0 P s0 \<theta>0"
  have comm: "finite_goal_committing (finite_narrowed_commitment P m D \<Phi>) F st g"
    and pr: "commit_production (finite_narrowed_commitment P m D \<Phi>) F st g \<noteq> None"
    using producing by (simp_all add: finite_goal_producing_def finite_goal_committing_def)
  show "\<exists>s \<theta>'. s |\<in>| finite_kept (resolution_goal_position g) (resolution_found (finite_committed_search \<kappa>
        (finite_narrowed_commitment P m D \<Phi>) P n (Some (resolution_goal_position g))
        (finite_committed_barring B (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))
        (finite_produced_state (finite_narrowed_commitment P m D \<Phi>) F st g))) \<and>
      resolution_supported_at (\<lambda>_. False) F (fimage resolution_node_position (resolution_nodes s)) P s \<theta>'"
    by (rule finite_narrowed_commitment_exchange[OF \<kappa> I sup gF discharged frames productions producing
      only H unheld s0])
qed
qed

text \<open>At a record declaring no narrowing and no production, the exchanges follow from R5's discharges alone.\<close>

corollary finite_unproduced_commitment_exchanges:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa>
    (finite_narrowed_commitment P m (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations) \<Phi>) P"
proof (rule finite_narrowed_commitment_exchanges[OF \<kappa> _ _ _ narrowed_productions_declared_unnarrowed only])
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations)) corr"
    using discharged by (simp add: declarations_discharged_unnarrowed)
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations)) \<Phi>"
    using frames by (simp add: frames_discharged_unnarrowed)
  show "productions_discharged (positive_meaning (decode_finite_system P)) P m
      (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations)"
    by (rule productions_discharged_none) simp
qed

section \<open>The committed forms exact at narrowed sockets with productions\<close>

theorem finite_narrowed_refutation_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and refutes: "finite_resolution_refutes (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_resolution_refutation_exact[OF \<kappa> finite_narrowed_commitment_exchanges[OF \<kappa> discharged
    frames productions declared only] constructions refutes])

theorem finite_narrowed_verdict_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and verdict: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) P d t n) =
      Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_committed_verdict_exact[OF \<kappa> finite_narrowed_commitment_exchanges[OF \<kappa> discharged
    frames productions declared only] constructions verdict])

theorem finite_narrowed_demand_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "finite_committed_demand \<kappa> (finite_narrowed_commitment P m D \<Phi>) P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_committed_demand_exact[OF \<kappa> finite_narrowed_commitment_exchanges[OF \<kappa> discharged
    frames productions declared only] constructions result] by blast+

theorem native_narrowed_resolution_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "native_committed_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_committed_resolution_exact[OF \<kappa> finite_narrowed_commitment_exchanges[OF \<kappa> discharged
    frames productions declared only] constructions result] by blast+

lemmas finite_narrowed_forms_exact = finite_narrowed_refutation_exact finite_narrowed_verdict_exact
  finite_narrowed_demand_exact native_narrowed_resolution_exact

text \<open>
  At a record declaring no narrowing and no production the forms are B2b's framed forms (review 737's follow-up 2):
  the narrowed commitment there is the framed commitment (@{thm [source] finite_unproduced_commitment}), and B2b's
  discharges of the declarations and the frames are all it takes.
\<close>

corollary finite_unproduced_refutation_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and refutes: "finite_resolution_refutes (finite_committed_resolution \<kappa>
      (finite_narrowed_commitment P m (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations) \<Phi>) P d t n)"
  shows "(d,decode_finite_term t) \<notin> positive_meaning (decode_finite_system P)"
  by (rule finite_framed_refutation_exact[OF \<kappa> discharged frames only constructions
    refutes[unfolded finite_unproduced_commitment narrowed_truncate]])

corollary finite_unproduced_verdict_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and verdict: "finite_resolution_verdict (finite_committed_resolution \<kappa>
      (finite_narrowed_commitment P m (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations) \<Phi>) P d t n) = Some b"
  shows "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
  by (rule finite_framed_verdict_exact[OF \<kappa> discharged frames only constructions
    verdict[unfolded finite_unproduced_commitment narrowed_truncate]])

corollary finite_unproduced_demand_exact:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "finite_committed_demand \<kappa>
      (finite_narrowed_commitment P m (unproduced (unnarrowed D) :: ('a,'s,'d,'v) produced_declarations) \<Phi>) P Q n = Some A"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A = {q\<in>fset Q. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using finite_framed_demand_exact[OF \<kappa> discharged frames only constructions
    result[unfolded finite_unproduced_commitment narrowed_truncate]] by blast+

corollary native_unproduced_resolution_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and frames: "frames_discharged (positive_meaning (decode_finite_system P)) D \<Phi>"
    and only: "finite_registrations_premise_only \<kappa> P"
    and constructions: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and result: "native_committed_resolution \<kappa> (finite_narrowed_commitment P m (unproduced (unnarrowed D)) \<Phi>) P R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and> fBall C (\<lambda>p. finite_checks_schema_proof P p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow>
      decode_finite_call_term q \<notin> positive_meaning (decode_finite_system P)"
    and "A = Some B \<Longrightarrow> schema_system_formed (decode_finite_system P) \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning (decode_finite_system P)}"
  using native_framed_resolution_exact[OF \<kappa> discharged frames only constructions
    result[unfolded finite_unproduced_commitment narrowed_truncate]] by blast+

section \<open>The narrowed frames carried by relocation and by agreement\<close>

text \<open>
  The narrowed obligation at a frame reads the clause's callees only through the meaning at them, as R5's framed
  obligation does (@{thm [source] socket_framed_callees}): a clause whose premises are the source's with their callees
  mapped, its conclusion, material premises and variables the source's, and whose truth is the source's, keeps the
  obligation at every class and frame (task 774, review 737's follow-up 1 (c)).
\<close>

lemma narrowed_socket_framed_callees:
  assumes src: "narrowed_socket_framed M S s keep Vp Vh N C"
    and prem: "\<And>q e p. (q,e,p) |\<in>| finite_schema_premises R \<longleftrightarrow>
      (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e = g d)"
    and conc: "finite_schema_conclusion R = finite_schema_conclusion S"
    and mat: "schema_material_premises (decode_finite_schema R) = schema_material_premises (decode_finite_schema S)"
    and ct: "\<And>h. clause_true M' (decode_finite_schema R) h \<longleftrightarrow> clause_true M (decode_finite_schema S) h"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and vars: "schema_variables (decode_finite_schema R) = schema_variables (decode_finite_schema S)"
  shows "narrowed_socket_framed M' R s keep Vp Vh N C"
proof -
  have hk: "head_kept keep Vh R h h' \<longleftrightarrow> head_kept keep Vh S h h'" for h h' unfolding head_kept_def conc ..
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)" if "(q,d,p) |\<in>| finite_schema_premises S" for q d p
    by (rule schema_dependencies_premise[of q d "decode_finite_pattern p"]) (use that in \<open>auto simp: finite_premise_decoded\<close>)
  note src' = src[unfolded narrowed_socket_framed_def socket_narrowing_def]
  note S2 = mp[OF spec[OF conjunct2[OF conjunct2[OF src']]]]
  show ?thesis unfolding narrowed_socket_framed_def socket_narrowing_def vars
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
        "\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h2 a = h a"
        "evaluate_pattern h2 (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi)"
        "evaluate_pattern h2 (decode_finite_pattern yo) = y'"
      using conjunct1[OF S2[OF hS], rule_format, OF p0 v a0 vt n] by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
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
        "\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h2 a = h a" "\<forall>a\<in>material_variables N'. h2 a = v a"
      using conjunct2[OF S2[OF hS], rule_format, OF mS sat se] by blast
    then show "\<exists>h'. clause_true M' (decode_finite_schema R) h' \<and> head_kept keep Vh R h h' \<and>
        (\<forall>a\<in>schema_variables (decode_finite_schema S) - C. h' a = h a) \<and>
        (\<forall>a\<in>material_variables N'. h' a = v a)"
      using ct hk by blast
  qed
qed

lemma narrowed_socket_framed_relocated:
  assumes src: "narrowed_socket_framed M S s keep Vp Vh N C"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "narrowed_socket_framed M' (finite_rename_schema id id g S) s keep Vp Vh N C"
proof (rule narrowed_socket_framed_callees[OF src _ _ _ _ eq])
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
  show "schema_variables (decode_finite_schema ?R) = schema_variables (decode_finite_schema S)"
    by (simp add: finite_rename_schema_correct renamed_schema_variables)
qed

text \<open>
  The narrowed frames relocate with the declarations as B2b's frames do (@{thm [source] frames_relocated_at}), each
  socket's class given at its relocated site as the narrowed discharge gives it
  (@{thm [source] narrowed_declarations_relocated_discharged}).
\<close>

theorem narrowed_frames_relocated_at:
  assumes at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate ND) \<Longrightarrow> (g d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and injective: "inj_on g (declared_sites (resolution_declarations.truncate ND) \<union> frame_sites \<Phi>)"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing ND e S s"
    and frames: "narrowed_frames_discharged M ND \<Phi>"
  shows "narrowed_frames_discharged M' (narrowed (declarations_relocated g (resolution_declarations.truncate ND)) \<nu>)
    (frames_relocated g \<Phi>)"
  unfolding narrowed_frames_discharged_def
proof (intro allI impI)
  let ?D = "resolution_declarations.truncate ND"
  fix e' S' s C keep Vp Vh
  assume fr: "(e',S',s,C) |\<in>| frames_relocated g \<Phi>"
    and so: "(e',S',s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed (declarations_relocated g ?D) \<nu>)"
  obtain e1 S1 where f1: "(e1,S1,s,C) |\<in>| \<Phi>" "e' = g e1" "S' = finite_rename_schema id id g S1"
    using fr by (auto simp: frames_relocated_def)
  obtain e2 S2 where s2: "(e2,S2,s,keep,Vp,Vh) |\<in>| declared_sockets ?D" "e' = g e2"
      "S' = finite_rename_schema id id g S2"
    using so by (auto simp: declarations_relocated_def)
  have sites1: "e1 \<in> frame_sites \<Phi>" "schema_dependencies (decode_finite_schema S1) \<subseteq> frame_sites \<Phi>"
    using f1(1) by (force simp: frame_sites_def)+
  have sub: "schema_dependencies (decode_finite_schema S2) \<subseteq> declared_sites ?D"
    by (rule declared_sites_members(5)[OF s2(1)])
  have "g e1 = g e2" using f1(2) s2(2) by simp
  then have e: "e1 = e2"
    by (rule inj_onD[OF injective]) (use sites1(1) declared_sites_members(4)[OF s2(1)] in blast)+
  have S: "S1 = S2"
    by (rule finite_rename_schema_callees_inj[OF _ inj_on_subset[OF injective]])
      (use f1(3) s2(3) sites1(2) sub in auto)
  have s2N: "(e2,S2,s,keep,Vp,Vh) |\<in>| declared_sockets ND" using s2(1) by simp
  have "(e2,S2,s,C) |\<in>| \<Phi>" using f1(1) e S by simp
  then have src: "narrowed_socket_framed M S2 s keep Vp Vh (declared_narrowing ND e2 S2 s) (fset C)"
    by (rule frames[unfolded narrowed_frames_discharged_def, rule_format, OF _ s2N])
  have "narrowed_socket_framed M' (finite_rename_schema id id g S2) s keep Vp Vh (declared_narrowing ND e2 S2 s) (fset C)"
    by (rule narrowed_socket_framed_relocated[OF src at]) (use sub in blast)
  then show "narrowed_socket_framed M' S' s keep Vp Vh
      (declared_narrowing (narrowed (declarations_relocated g ?D) \<nu>) e' S' s) (fset C)"
    using relocates[OF s2N] s2(2,3) by simp
qed

theorem narrowed_frames_relocated_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (system_definitions (decode_finite_system P) \<union>
      declared_sites (resolution_declarations.truncate ND) \<union> frame_sites \<Phi>)"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND \<Longrightarrow>
      \<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing ND e S s"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P)) ND \<Phi>"
  shows "narrowed_frames_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
    (narrowed (declarations_relocated g (resolution_declarations.truncate ND)) \<nu>) (frames_relocated g \<Phi>)"
proof -
  have inj: "inj_on g (system_definitions (decode_finite_system P) \<union> declared_sites (resolution_declarations.truncate ND))"
    by (rule inj_on_subset[OF injective]) blast
  show ?thesis
  proof (rule narrowed_frames_relocated_at[OF _ _ relocates frames])
    show "(g d,x) \<in> positive_meaning (decode_finite_system (finite_rename_system g P)) \<longleftrightarrow>
        (d,x) \<in> positive_meaning (decode_finite_system P)"
      if "d \<in> declared_sites (resolution_declarations.truncate ND)" for d x
      using relocated_meaning_at[OF Pf inj that] by simp
    show "inj_on g (declared_sites (resolution_declarations.truncate ND) \<union> frame_sites \<Phi>)"
      by (rule inj_on_subset[OF injective]) blast
  qed
qed

text \<open>
  By agreement the narrowed frames carry as the narrowed discharge does
  (@{thm [source] narrowed_declarations_agree_discharged}): every callee a socket's obligation reads is a declared
  site, where the two meanings agree.
\<close>

theorem narrowed_frames_agree_discharged:
  assumes Pf: "schema_system_formed P" and Qf: "schema_system_formed Q"
    and agree: "systems_agree_on P Q V" and closed: "system_dependency_closed P V"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> V"
    and frames: "narrowed_frames_discharged (positive_meaning P) ND \<Phi>"
  shows "narrowed_frames_discharged (positive_meaning Q) ND \<Phi>"
  unfolding narrowed_frames_discharged_def
proof (intro allI impI)
  fix e S s C keep Vp Vh assume f: "(e,S,s,C) |\<in>| \<Phi>" and m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ND"
  have m': "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate ND)" using m by simp
  have src: "narrowed_socket_framed (positive_meaning P) S s keep Vp Vh (declared_narrowing ND e S s) (fset C)"
    by (rule frames[unfolded narrowed_frames_discharged_def, rule_format, OF f m])
  have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites (resolution_declarations.truncate ND)"
    by (rule declared_sites_members(5)[OF m'])
  have eqQ: "(id d,x) \<in> positive_meaning Q \<longleftrightarrow> (d,x) \<in> positive_meaning P"
    if "d \<in> schema_dependencies (decode_finite_schema S)" for d x
    using positive_meaning_dependency_locality[OF Pf Qf agree closed subsetD[OF sites subsetD[OF sub that]], of x]
    by simp
  show "narrowed_socket_framed (positive_meaning Q) S s keep Vp Vh (declared_narrowing ND e S s) (fset C)"
  proof (rule narrowed_socket_framed_callees[OF src _ _ _ _ eqQ])
    show "(q,e',p) |\<in>| finite_schema_premises S \<longleftrightarrow> (\<exists>d. (q,d,p) |\<in>| finite_schema_premises S \<and> e' = id d)"
      for q e' p by simp
    show "clause_true (positive_meaning Q) (decode_finite_schema S) h \<longleftrightarrow>
        clause_true (positive_meaning P) (decode_finite_schema S) h" for h
      using clause_true_relocated[of "decode_finite_schema S" id "positive_meaning Q" "positive_meaning P" h, OF eqQ]
      by simp
  qed simp_all
qed

section \<open>The transfer at productions\<close>

text \<open>
  By relocation: the narrowed discharge is carried by #599's @{thm [source] narrowed_declarations_relocated_discharged},
  its classes given at the relocated sites, and the narrowed frames, relocated with the declarations, by
  @{thm [source] narrowed_frames_relocated_discharged} (task 774). By agreement: the narrowed discharge and the
  narrowed frames are carried at the declared sites (@{thm [source] narrowed_declarations_agree_discharged},
  @{thm [source] narrowed_frames_agree_discharged}), the frames the source's. Two premises of the other side remain.
  Its productions' discharge: a production's value is W2's registration value computed by the resolution search in
  the program the committed step searches, and neither the search's equivariance under a site relocation nor its
  locality under agreement is stated (q138). Its static premise at a relocated record: the relocated record's
  productions are its own data. The verdicts are then carried as R5's are
  (@{thm [source] finite_committed_relocation_transfer}, @{thm [source] finite_committed_agreement_transfer}).
\<close>

corollary finite_narrowed_relocation_transfer:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
    and D :: "('a,'s,'d,'v) produced_declarations" and D' :: "('a,'s,'e,'w) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and relocated: "narrowed_declarations.truncate D' =
      narrowed (declarations_relocated g (resolution_declarations.truncate D)) \<nu>"
    and relocates: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      \<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing D e S s"
    and productions': "productions_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
      (finite_rename_system g P) m' D'"
    and declared': "narrowed_productions_declared D'"
    and only': "finite_registrations_premise_only \<kappa>' (finite_rename_system g P)"
    and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' (finite_rename_system g P)"
    and Pf: "schema_system_formed (decode_finite_system P)"
    and injective: "inj_on g (insert d (system_definitions (decode_finite_system P) \<union>
      declared_sites (resolution_declarations.truncate D) \<union> frame_sites \<Phi>))"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>'
      (finite_narrowed_commitment (finite_rename_system g P) m' D' (frames_relocated g \<Phi>)) (finite_rename_system g P)
      (g d) t n') = Some b'"
  shows "b = b'"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P"
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa> discharged frames productions declared only])
  have inj0: "inj_on g (system_definitions (decode_finite_system P) \<union>
      declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate D)))"
    by (rule inj_on_subset[OF injective]) auto
  have rel0: "\<nu> (g e) (finite_rename_schema id id g S) s = declared_narrowing (narrowed_declarations.truncate D) e S s"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate D)" for e S s keep Vp Vh
    using relocates[of e S s keep Vp Vh] that by simp
  have dR: "narrowed_declarations_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
      (narrowed_declarations.truncate D') (corr \<circ> inv_into (declared_sites (resolution_declarations.truncate D)) g)"
    using narrowed_declarations_relocated_discharged[OF Pf inj0 discharged rel0] relocated by simp
  have fR: "narrowed_frames_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
      (narrowed_declarations.truncate D') (frames_relocated g \<Phi>)"
  proof -
    have "narrowed_frames_discharged (positive_meaning (decode_finite_system (finite_rename_system g P)))
        (narrowed (declarations_relocated g (resolution_declarations.truncate (narrowed_declarations.truncate D))) \<nu>)
        (frames_relocated g \<Phi>)"
      by (rule narrowed_frames_relocated_discharged[OF Pf _ rel0 frames]) (rule inj_on_subset[OF injective], auto)
    then show ?thesis using relocated by simp
  qed
  have ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>'
      (finite_narrowed_commitment (finite_rename_system g P) m' D' (frames_relocated g \<Phi>)) (finite_rename_system g P)"
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa>' dR fR productions' declared' only'])
  have inj: "inj_on g (insert d (system_definitions (decode_finite_system P)))"
    by (rule inj_on_subset[OF injective]) blast
  show ?thesis by (rule finite_committed_relocation_transfer[OF \<kappa> ex cl \<kappa>' ex' cl' Pf inj v v'])
qed

corollary finite_narrowed_agreement_transfer:
  fixes P Q :: "('a,'s::linorder,'d,'c) finite_schema_system" and D :: "('a,'s,'d,'v) produced_declarations"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) corr"
    and frames: "narrowed_frames_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate D) \<Phi>"
    and productions: "productions_discharged (positive_meaning (decode_finite_system P)) P m D"
    and declared: "narrowed_productions_declared D"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and productions': "productions_discharged (positive_meaning (decode_finite_system Q)) Q m' D"
    and only': "finite_registrations_premise_only \<kappa>' Q" and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' Q"
    and Pf: "schema_system_formed (decode_finite_system P)" and Qf: "schema_system_formed (decode_finite_system Q)"
    and agree: "systems_agree_on (decode_finite_system P) (decode_finite_system Q) V"
    and closed: "system_dependency_closed (decode_finite_system P) V" and dV: "d \<in> V"
    and sites: "declared_sites (resolution_declarations.truncate D) \<subseteq> V"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_narrowed_commitment P m D \<Phi>) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' (finite_narrowed_commitment Q m' D \<Phi>) Q d t n') =
      Some b'"
  shows "b = b'"
proof -
  have ex: "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_narrowed_commitment P m D \<Phi>) P"
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa> discharged frames productions declared only])
  have sites0: "declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate D)) \<subseteq> V"
    using sites by simp
  have dQ: "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate D) corr"
    by (rule narrowed_declarations_agree_discharged[OF Pf Qf agree closed sites0 discharged])
  have fQ: "narrowed_frames_discharged (positive_meaning (decode_finite_system Q)) (narrowed_declarations.truncate D) \<Phi>"
    by (rule narrowed_frames_agree_discharged[OF Pf Qf agree closed sites0 frames])
  have ex': "finite_commitment_exchanges (\<lambda>_. False) \<kappa>' (finite_narrowed_commitment Q m' D \<Phi>) Q"
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa>' dQ fQ productions' declared only'])
  show ?thesis by (rule finite_committed_agreement_transfer[OF \<kappa> ex cl \<kappa>' ex' cl' Pf Qf agree closed dV v v'])
qed

end
