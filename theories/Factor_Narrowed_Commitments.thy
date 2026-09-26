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
  and the goal's own socket, a declared production, with the socket's premise view. The narrowed commitment produces
  where exactly one is met.
\<close>

definition finite_socket_productions ::
    "('a,'s,'d,'v) produced_declarations \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow>
      (nat resolution_view \<times> ('a,'s,'d,'v) collection_registration) fset" where
  "finite_socket_productions D st g = (case g of
      Resolution_Call_Goal q r e p \<Rightarrow>
        (\<lambda>(e',S,s,keep,Vp,Vh). (Vp,the (declared_production D e' S s))) |`|
          ffilter (\<lambda>(e',S,s,keep,Vp,Vh). q \<noteq> [] \<and> s = last q \<and> declared_production D e' S s \<noteq> None \<and>
            fBex (resolution_nodes st) (\<lambda>nd. resolution_node_position nd = butlast q \<and>
              resolution_node_site nd = e' \<and> resolution_node_schema nd = S)) (declared_sockets D)
    | Resolution_Material_Goal q r M \<Rightarrow> {||})"

text \<open>
  The value of a registration at a goal's pattern: the registered clause's head read at the view, its input matched
  against the goal's input read at the same view (ground where the commitment commits,
  @{thm [source] finite_framed_commitment_input_ground}), and W2's registration value at those bindings and the bound.
\<close>

definition finite_registration_production ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> nat resolution_view \<Rightarrow>
      ('a,'s,'d,'v) collection_registration \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      finite_factor_term option" where
  "finite_registration_production P n V R p = (case resolution_view_pattern V p of None \<Rightarrow> None
    | Some xy \<Rightarrow> (case resolution_view_pattern V (finite_schema_conclusion (registration_schema R)) of None \<Rightarrow> None
      | Some cc \<Rightarrow> finite_registration_value P n R (finite_matching_bindings (fst cc) (finite_residual_term (fst xy)))))"

definition finite_narrowed_production ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> (nat resolution_view \<times> finite_factor_term) option" where
  "finite_narrowed_production P n D \<Phi> F st g = (case g of
      Resolution_Call_Goal q r e p \<Rightarrow>
        if commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) F st g then
          (case finite_singleton_option (finite_socket_productions D st g) of None \<Rightarrow> None
          | Some VR \<Rightarrow> map_option (\<lambda>v. (fst VR,v)) (finite_registration_production P n (fst VR) (snd VR) p))
        else None
    | Resolution_Material_Goal q r M \<Rightarrow> None)"

definition finite_narrowed_commitment ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
      ('a,'s,'d) resolution_frames \<Rightarrow> ('a,'s,'d,'c) resolution_commitment" where
  "finite_narrowed_commitment P n D \<Phi> = (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>)
    \<lparr>commit_production := finite_narrowed_production P n D \<Phi>\<rparr>"

lemma finite_narrowed_commitment_fields [simp]:
  "commit_call (finite_narrowed_commitment P n D \<Phi>) = commit_call (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>)"
  "commit_material (finite_narrowed_commitment P n D \<Phi>) =
    commit_material (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>)"
  "commit_production (finite_narrowed_commitment P n D \<Phi>) = finite_narrowed_production P n D \<Phi>"
  by (simp_all add: finite_narrowed_commitment_def)

text \<open>The narrowed commitment produces only at a goal its call test commits.\<close>

lemma finite_narrowed_production_committed:
  assumes "finite_narrowed_production P n D \<Phi> F st g \<noteq> None"
  shows "commit_call (finite_narrowed_commitment P n D \<Phi>) F st g" "resolution_is_call g"
  using assms by (auto simp: finite_narrowed_production_def split: resolution_goal.splits if_splits)

section \<open>At a record declaring no production\<close>

lemma finite_socket_productions_none:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_socket_productions D st g = {||}"
proof -
  have "x |\<notin>| finite_socket_productions D st g" for x
    by (cases g) (auto simp: finite_socket_productions_def none)
  then show ?thesis by (simp add: fset_eq_iff)
qed

lemma finite_narrowed_production_none:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_narrowed_production P n D \<Phi> F st g = None"
proof -
  have e: "finite_singleton_option (finite_socket_productions D st g') = None" for g'
    unfolding finite_socket_productions_none[OF none] finite_singleton_option_def set_singleton_option_def by simp
  show ?thesis by (simp add: finite_narrowed_production_def e split: resolution_goal.split)
qed

theorem finite_narrowed_commitment_unproduced:
  assumes none: "\<And>e S s. declared_production D e S s = None"
  shows "finite_narrowed_commitment P n D \<Phi> = finite_framed_commitment (resolution_declarations.truncate D) \<Phi>"
proof -
  have prod: "finite_narrowed_production P n D \<Phi> = (\<lambda>F st g. None)"
    by (intro ext) (rule finite_narrowed_production_none[OF none])
  show ?thesis by (simp add: finite_narrowed_commitment_def finite_framed_commitment_def prod)
qed

corollary finite_unproduced_commitment:
  "finite_narrowed_commitment P n (unproduced ND) \<Phi> = finite_framed_commitment (resolution_declarations.truncate ND) \<Phi>"
  by (simp add: finite_narrowed_commitment_unproduced)

end
