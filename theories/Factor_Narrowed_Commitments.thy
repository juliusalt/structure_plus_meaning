theory Factor_Narrowed_Commitments
  imports Factor_Narrowed_Sockets
begin

text \<open>
  The production at a narrowed socket (R5f1 of DECISIONS.md "The native evaluator constructs the missing witnesses by
  resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", the correction
  closing it, task 725). The narrowed socket's record holds, beside its class N, its production: a registration at a
  clause of the socket's callee site whose variable stands at the head's output at the socket's premise view, or none
  (@{text produced_declarations}, an extension of @{text narrowed_declarations}, keyed by site, schema and socket as the
  narrowing is). The registration is held by the record, not by the witness construction, whose registrations stay
  premise-only. The narrowed commitment is the framed commitment of the record's truncation (the search and its tests
  read the truncation, unchanged), and its production at a call goal it commits at a narrowed socket declaring a
  registration R is W2's registration value of R at the search's bound, at the ground bindings of R's clause head at
  the view's input matched against the goal's pattern. The value is read by the committed step
  (@{const finite_produced_state}) and checked there by the given's clauses; no checker produces it. At a record
  declaring no production the narrowed commitment is the framed commitment of its truncation.

  Corrected by task 767 (q134): the production is defined only where it applies — its registration stands at the
  goal's callee, the registered head's input at the matched bindings is the goal's input, its value is defined at the
  bound and the goal's viewed output matches it (@{const finite_production_substitution}) — and the call test commits a
  goal meeting a declared production only where the production is defined. Elsewhere at such a socket the goal is not
  committed: it is searched plainly, unresolved at the bound, never refuted. At a goal meeting no production the test
  is the framed test.
\<close>

section \<open>The production field\<close>

record ('a,'s,'d,'v) produced_declarations = "('a,'s,'d) narrowed_declarations" +
  declared_production :: "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> ('a,'s,'d,'v) collection_registration option"

definition produced ::
    "('a,'s,'d) narrowed_declarations \<Rightarrow>
      ('d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> ('a,'s,'d,'v) collection_registration option) \<Rightarrow>
      ('a,'s,'d,'v) produced_declarations" where
  "produced ND \<rho> = \<lparr>declared_producers = declared_producers ND, declared_consumers = declared_consumers ND,
    declared_sockets = declared_sockets ND, declared_narrowing = declared_narrowing ND, declared_production = \<rho>\<rparr>"

lemma produced_fields [simp]:
  "declared_producers (produced ND \<rho>) = declared_producers ND"
  "declared_consumers (produced ND \<rho>) = declared_consumers ND"
  "declared_sockets (produced ND \<rho>) = declared_sockets ND"
  "declared_narrowing (produced ND \<rho>) = declared_narrowing ND"
  "declared_production (produced ND \<rho>) = \<rho>"
  by (simp_all add: produced_def)

lemma produced_truncate [simp]: "narrowed_declarations.truncate (produced ND \<rho>) = ND"
  by (cases ND) (simp add: produced_def narrowed_declarations.truncate_def)

lemma produced_resolution_truncate [simp]:
  "resolution_declarations.truncate (produced ND \<rho>) = resolution_declarations.truncate ND"
  by (simp add: produced_def resolution_declarations.truncate_def)

text \<open>A record declares no production when every socket's production is none: #599's narrowed record.\<close>

abbreviation unproduced :: "('a,'s,'d) narrowed_declarations \<Rightarrow> ('a,'s,'d,'v) produced_declarations" where
  "unproduced ND \<equiv> produced ND (\<lambda>_ _ _. None)"

section \<open>The narrowed commitment\<close>

text \<open>
  The productions a call goal meets: at a declared socket whose site, clause and premise are the goal's parent node's
  and the goal's own socket, and at whose views the framed test of the record's truncation commits the goal at some
  frame choice (the socket disjunct, never a declared direct producer alone), a declared production, with the socket's
  premise view. The goal's input at that view is then ground (@{text finite_socket_productions_ground}). The narrowed
  commitment produces where exactly one is met.
\<close>

definition finite_socket_productions ::
    "('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow> 's list option \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      (nat resolution_view \<times> ('a,'s,'d,'v) collection_registration) fset" where
  "finite_socket_productions D \<Phi> F st g = (case g of
      Resolution_Call_Goal q r e p \<Rightarrow>
        (\<lambda>(e',S,s,keep,Vp,Vh). (Vp,the (declared_production D e' S s))) |`|
          ffilter (\<lambda>(e',S,s,keep,Vp,Vh). q \<noteq> [] \<and> s = last q \<and> declared_production D e' S s \<noteq> None \<and>
            fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
              resolution_node_site nd = e' \<and> resolution_node_schema nd = S) \<and>
            fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
              finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g \<and>
              finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g)) (declared_sockets D)
    | Resolution_Material_Goal q r M \<Rightarrow> {||})"

text \<open>
  A production met stands at a call goal and at a declared socket of the goal's parent node: its site, clause and
  key are the node's and the goal's, its view is the socket's premise view, its registration is the one the record
  declares there, and at those views the goal is committed as at a socket at some frame choice. A material goal meets
  none.
\<close>

lemma finite_socket_productions_member:
  assumes m: "VR |\<in>| finite_socket_productions D \<Phi> F st g"
  obtains q r e p nd keep Vh ch R where "g = Resolution_Call_Goal q r e p" "q \<noteq> []"
    "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q"
    "(resolution_node_site nd,resolution_node_schema nd,last q,keep,fst VR,Vh) |\<in>| declared_sockets D"
    "declared_production D (resolution_node_site nd) (resolution_node_schema nd) (last q) = Some R" "snd VR = R"
    "ch |\<in>| finite_frame_choices \<Phi>"
    "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
    "finite_call_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  \<comment> \<open>The call case: the filter's conditions at the tuple the production was read from.\<close>
  obtain e' S s keep Vp Vh nd ch where t: "(e',S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
      and VR: "VR = (Vp,the (declared_production D e' S s))" and q: "q \<noteq> []" and s: "s = last q"
      and pr: "declared_production D e' S s \<noteq> None"
      and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q"
        "resolution_node_site nd = e'" "resolution_node_schema nd = S"
      and ch: "ch |\<in>| finite_frame_choices \<Phi>"
        "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g"
        "finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g"
    using m unfolding Resolution_Call_Goal finite_socket_productions_def fBex_member_iff
    by (auto split: prod.splits; blast)
  obtain R where R: "declared_production D e' S s = Some R" using pr by blast
  show thesis
    by (rule that[of q r e p nd keep Vh R ch]) (use Resolution_Call_Goal q nd t s R VR ch in simp_all)
next
  case (Resolution_Material_Goal q r M)
  \<comment> \<open>The material case: the productions are empty.\<close>
  then show thesis using m by (simp add: finite_socket_productions_def)
qed

text \<open>A production met is one at whose views the goal is committed as at a socket, and so a call goal.\<close>

text \<open>A declared production at the goal's parent socket at whose views the framed test commits is met.\<close>

lemma finite_socket_productions_memberI:
  assumes g: "g = Resolution_Call_Goal q r e p" and qne: "q \<noteq> []"
    and nd: "nd |\<in>| resolution_nodes st" "resolution_node_position nd = butlast q"
    and tup: "(resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh) |\<in>| declared_sockets D"
    and R: "declared_production D (resolution_node_site nd) (resolution_node_schema nd) (last q) = Some R"
    and ch: "ch |\<in>| finite_frame_choices \<Phi>"
    and sc: "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g"
    and cn: "finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g"
  shows "(Vp,R) |\<in>| finite_socket_productions D \<Phi> F st g"
proof -
  let ?t = "(resolution_node_site nd,resolution_node_schema nd,last q,keep,Vp,Vh)"
  have "fBex (resolution_nodes st) (\<lambda>nd'. resolution_node_position nd' = butlast q \<and>
      resolution_node_site nd' = resolution_node_site nd \<and> resolution_node_schema nd' = resolution_node_schema nd)"
    using nd unfolding fBex_member_iff by blast
  moreover have "fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
      finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g \<and>
      finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g)"
    using ch sc cn unfolding fBex_member_iff by blast
  ultimately have "?t |\<in>| ffilter (\<lambda>(e',S,s,keep,Vp,Vh). q \<noteq> [] \<and> s = last q \<and> declared_production D e' S s \<noteq> None \<and>
      fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
        resolution_node_site nd = e' \<and> resolution_node_schema nd = S) \<and>
      fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
        finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g \<and>
        finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g)) (declared_sockets D)"
    using tup qne R by simp
  then have "(\<lambda>(e',S,s,keep,Vp,Vh). (Vp,the (declared_production D e' S s))) ?t |\<in>|
      (\<lambda>(e',S,s,keep,Vp,Vh). (Vp,the (declared_production D e' S s))) |`| ffilter (\<lambda>(e',S,s,keep,Vp,Vh). q \<noteq> [] \<and>
        s = last q \<and> declared_production D e' S s \<noteq> None \<and>
        fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
          resolution_node_site nd = e' \<and> resolution_node_schema nd = S) \<and>
        fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
          finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g \<and>
          finite_call_framed (resolution_declarations.truncate D) \<Phi> Vp Vh ch F st g)) (declared_sockets D)"
    by (rule fimageI)
  then show ?thesis using R by (simp add: finite_socket_productions_def g)
qed

lemma finite_socket_productions_committed:
  assumes "VR |\<in>| finite_socket_productions D \<Phi> F st g"
  shows "resolution_is_call g \<and> (\<exists>Vh ch. ch |\<in>| finite_frame_choices \<Phi> \<and>
    finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g \<and>
    finite_call_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g)"
proof -
  obtain q r e p nd keep Vh ch R where g: "g = Resolution_Call_Goal q r e p"
      and ch: "ch |\<in>| finite_frame_choices \<Phi>"
      and sc: "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
      and cn: "finite_call_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
    by (rule finite_socket_productions_member[OF assms])
  have "resolution_is_call g" using g by simp
  then show ?thesis using ch sc cn by blast
qed

text \<open>At a production met, the goal's input read at the production's view is ground and its output is not.\<close>

lemma finite_socket_productions_ground:
  assumes m: "VR |\<in>| finite_socket_productions D \<Phi> F st g"
  obtains q r e p x y where "g = Resolution_Call_Goal q r e p" "resolution_view_pattern (fst VR) p = Some (x,y)"
    "finite_pattern_variables x = {||}" "finite_pattern_variables y \<noteq> {||}"
proof -
  obtain Vh ch where c: "finite_socket_commitment_framed (resolution_declarations.truncate D) \<Phi> (fst VR) Vh ch F st g"
    and call: "resolution_is_call g"
    using finite_socket_productions_committed[OF m] by blast
  show thesis by (rule finite_socket_commitment_framed_view[OF c call]) (rule that)
qed

text \<open>
  The value of a registration at a goal's pattern: the registered clause's head read at the view, its input matched
  against the goal's input read at the same view (ground at every production met,
  @{thm [source] finite_socket_productions_ground}), and W2's registration value at those bindings and the bound.
\<close>

definition finite_registration_production ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> nat resolution_view \<Rightarrow>
      ('a,'s,'d,'v) collection_registration \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      finite_factor_term option" where
  "finite_registration_production P n V R p = (case resolution_view_pattern V p of None \<Rightarrow> None
    | Some xy \<Rightarrow> (case resolution_view_pattern V (finite_schema_conclusion (registration_schema R)) of None \<Rightarrow> None
      | Some cc \<Rightarrow> finite_registration_value P n R (finite_matching_bindings (fst cc) (finite_residual_term (fst xy)))))"

text \<open>
  A registration applies at a call goal (task 767) when it stands at the goal's callee and the registered head's input
  at the view, read at the bindings matched against the goal's viewed input, is that input.
\<close>

definition finite_registration_applies ::
    "nat resolution_view \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow> 'd \<Rightarrow>
      ('s,'a) resolution_variable finite_term_pattern \<Rightarrow> bool" where
  "finite_registration_applies V R e p \<longleftrightarrow> registration_site R = e \<and> (case resolution_view_pattern V p of None \<Rightarrow> False
    | Some xy \<Rightarrow> (case resolution_view_pattern V (finite_schema_conclusion (registration_schema R)) of None \<Rightarrow> False
      | Some cc \<Rightarrow> resolution_value (finite_binding_valuation (finite_matching_bindings (fst cc) (finite_residual_term (fst xy))))
          (fst cc) = finite_residual_term (fst xy)))"

definition finite_narrowed_production ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> (nat resolution_view \<times> finite_factor_term) option" where
  "finite_narrowed_production P n D \<Phi> F st g = (case g of
      Resolution_Call_Goal q r e p \<Rightarrow>
        if commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g then
          (case finite_singleton_option (finite_socket_productions D \<Phi> F st g) of None \<Rightarrow> None
          | Some VR \<Rightarrow> if finite_registration_applies (fst VR) (snd VR) e p then
              (case finite_registration_production P n (fst VR) (snd VR) p of None \<Rightarrow> None
              | Some v \<Rightarrow> if finite_production_substitution (fst VR) p v = None then None else Some (fst VR,v))
            else None)
        else None
    | Resolution_Material_Goal q r M \<Rightarrow> None)"

definition finite_narrowed_commitment ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d,'c) resolution_commitment" where
  "finite_narrowed_commitment P n D \<Phi> = (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>)
    \<lparr>commit_call := (\<lambda>F st g. commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g \<and>
       (finite_socket_productions D \<Phi> F st g = {||} \<or> finite_narrowed_production P n D \<Phi> F st g \<noteq> None)),
     commit_production := finite_narrowed_production P n D \<Phi>\<rparr>"

lemma finite_narrowed_commitment_fields [simp]:
  "commit_call (finite_narrowed_commitment P n D \<Phi>) = (\<lambda>F st g.
    commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g \<and>
    (finite_socket_productions D \<Phi> F st g = {||} \<or> finite_narrowed_production P n D \<Phi> F st g \<noteq> None))"
  "commit_material (finite_narrowed_commitment P n D \<Phi>) =
    commit_material (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>)"
  "commit_production (finite_narrowed_commitment P n D \<Phi>) = finite_narrowed_production P n D \<Phi>"
  by (simp_all add: finite_narrowed_commitment_def)

text \<open>The narrowed commitment produces only at a goal its call test commits.\<close>

lemma finite_narrowed_production_committed:
  assumes "finite_narrowed_production P n D \<Phi> F st g \<noteq> None"
  shows "commit_call (finite_narrowed_commitment P n D \<Phi>) F st g" "resolution_is_call g"
  using assms by (auto simp: finite_narrowed_production_def split: resolution_goal.splits if_splits)

text \<open>
  Where the production is defined it applies: the goal is a call the framed test commits, the production met is one,
  its registration applies at the goal, its value is defined at the bound and the goal's viewed output matches it.
\<close>

lemma finite_narrowed_production_some:
  assumes "finite_narrowed_production P n D \<Phi> F st g = Some Vv"
  obtains q r e p VR v where "g = Resolution_Call_Goal q r e p"
    "commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g"
    "finite_singleton_option (finite_socket_productions D \<Phi> F st g) = Some VR"
    "finite_registration_applies (fst VR) (snd VR) e p"
    "finite_registration_production P n (fst VR) (snd VR) p = Some v" "Vv = (fst VR,v)"
    "finite_production_substitution (fst VR) p v \<noteq> None"
proof (cases g)
  case (Resolution_Call_Goal q r e p)
  show thesis
  proof (cases "finite_singleton_option (finite_socket_productions D \<Phi> F st g)")
    case None
    then show thesis using assms Resolution_Call_Goal by (simp add: finite_narrowed_production_def split: if_splits)
  next
    case (Some VR)
    show thesis
    proof (cases "finite_registration_production P n (fst VR) (snd VR) p")
      case None
      then show thesis using assms Resolution_Call_Goal Some
        by (simp add: finite_narrowed_production_def split: if_splits)
    next
      case (Some v)
      have "commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g"
        "finite_registration_applies (fst VR) (snd VR) e p" "Vv = (fst VR,v)"
        "finite_production_substitution (fst VR) p v \<noteq> None"
        using assms Resolution_Call_Goal \<open>finite_singleton_option _ = Some VR\<close> Some
        by (simp_all add: finite_narrowed_production_def split: if_splits)
      then show thesis using that Resolution_Call_Goal \<open>finite_singleton_option _ = Some VR\<close> Some by blast
    qed
  qed
next
  case (Resolution_Material_Goal q r M)
  then show thesis using assms by (simp add: finite_narrowed_production_def)
qed

section \<open>At a record declaring no production\<close>

lemma finite_socket_productions_none:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_socket_productions D \<Phi> F st g = {||}"
proof -
  have "x |\<notin>| finite_socket_productions D \<Phi> F st g" for x
    by (cases g) (auto simp: finite_socket_productions_def none)
  then show ?thesis by (simp add: fset_eq_iff)
qed

lemma finite_narrowed_production_none:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_narrowed_production P n D \<Phi> F st g = None"
proof -
  have e: "finite_singleton_option (finite_socket_productions D \<Phi> F' st' g') = None" for F' st' g'
    unfolding finite_socket_productions_none[OF none] finite_singleton_option_def set_singleton_option_def by simp
  show ?thesis by (simp add: finite_narrowed_production_def e split: resolution_goal.split)
qed

theorem finite_narrowed_commitment_unproduced:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_narrowed_commitment P n D \<Phi> = finite_framed_commitment (resolution_declarations.truncate D) \<Phi>"
proof -
  have prod: "finite_narrowed_production P n D \<Phi> = (\<lambda>F st g. None)"
    by (intro ext) (rule finite_narrowed_production_none[OF none])
  show ?thesis
    by (simp add: finite_narrowed_commitment_def finite_framed_commitment_def prod finite_socket_productions_none[OF none])
qed

corollary finite_unproduced_commitment:
  "finite_narrowed_commitment P n (unproduced ND) \<Phi> = finite_framed_commitment (resolution_declarations.truncate ND) \<Phi>"
  by (simp add: finite_narrowed_commitment_unproduced)

end
