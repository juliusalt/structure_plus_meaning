theory Factor_Framed_Commitment_Index
  imports Factor_Narrowed_Commitments Tree_Map_Indexes
begin

text \<open>
  The framed commitment (@{const finite_framed_commitment}) tests a goal against every pair of socket views of the
  record and every choice of frame, though only those at the goal's own raising socket can hold: the socket's declared
  test (@{const finite_socket_declared_framed}) asks for a declared socket at the last position of the goal and, for a
  chosen frame, a frame at that socket (@{const finite_frame_at}). The views and choices at a socket are indexed once
  per record and frames, keyed by the socket, through the tree's index (@{text Tree_Map_Indexes}); the test at a goal
  reads the entry at its raising socket alone. The equation is a code equation proved equal to the definition at every
  record and frames; no statement changes.
\<close>

section \<open>The views and frame choices at a socket\<close>

definition framed_sockets :: "('a,'s,'d) resolution_declarations \<Rightarrow> 's fset" where
  "framed_sockets D = (\<lambda>(e,S,s,keep,Vp,Vh). s) |`| declared_sockets D"

definition framed_views_at ::
    "('a,'s,'d) resolution_declarations \<Rightarrow> 's \<Rightarrow> (nat resolution_view \<times> nat resolution_view) fset" where
  "framed_views_at D s = (\<lambda>(e,S,s',keep,Vp,Vh). (Vp,Vh)) |`|
    ffilter (\<lambda>(e,S,s',keep,Vp,Vh). s' = s) (declared_sockets D)"

definition framed_choices_at :: "('a,'s,'d) resolution_frames \<Rightarrow> 's \<Rightarrow> 'a fset option fset" where
  "framed_choices_at \<Phi> s = finsert None ((\<lambda>(e,S,s',C). Some C) |`| ffilter (\<lambda>(e,S,s',C). s' = s) \<Phi>)"

lemma framed_views_at_subset: "framed_views_at D s |\<subseteq>| finite_socket_views D"
  unfolding framed_views_at_def finite_socket_views_def by (rule fimage_mono) auto

lemma framed_choices_at_subset: "framed_choices_at \<Phi> s |\<subseteq>| finite_frame_choices \<Phi>"
  unfolding framed_choices_at_def finite_frame_choices_def by (rule finsert_mono, rule fimage_mono) auto

lemma framed_views_at_socket:
  assumes declared: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
  shows "(Vp,Vh) |\<in>| framed_views_at D s \<and> s |\<in>| framed_sockets D"
proof
  have "(e,S,s,keep,Vp,Vh) |\<in>| ffilter (\<lambda>(e,S,s',keep,Vp,Vh). s' = s) (declared_sockets D)"
    using declared by simp
  then show "(Vp,Vh) |\<in>| framed_views_at D s" unfolding framed_views_at_def by (rule rev_fimage_eqI) simp
  show "s |\<in>| framed_sockets D" unfolding framed_sockets_def using declared by (rule rev_fimage_eqI) simp
qed

lemma framed_choices_at_frame:
  assumes frame: "finite_frame_at \<Phi> Vp Vh e S s ch \<noteq> None"
  shows "ch |\<in>| framed_choices_at \<Phi> s"
proof (cases ch)
  case None
  then show ?thesis by (simp add: framed_choices_at_def)
next
  case (Some C)
  then have member: "(e,S,s,C) |\<in>| \<Phi>" using frame by (simp add: finite_frame_at_def split: if_splits)
  have "(e,S,s,C) |\<in>| ffilter (\<lambda>(e,S,s',C). s' = s) \<Phi>" using member by simp
  then have "Some C |\<in>| (\<lambda>(e,S,s',C). Some C) |`| ffilter (\<lambda>(e,S,s',C). s' = s) \<Phi>"
    by (rule rev_fimage_eqI) simp
  then show ?thesis unfolding framed_choices_at_def Some by simp
qed

text \<open>A goal passing the socket's declared test stands at a declared socket, under a view and a choice found there.\<close>

lemma framed_declared_socket:
  assumes "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g"
  shows "q \<noteq> [] \<and> (Vp,Vh) |\<in>| framed_views_at D (last q) \<and> last q |\<in>| framed_sockets D \<and>
    ch |\<in>| framed_choices_at \<Phi> (last q)"
proof -
  obtain e S keep where q: "q \<noteq> []" and declared: "(e,S,last q,keep,Vp,Vh) |\<in>| declared_sockets D"
    and frame: "finite_frame_at \<Phi> Vp Vh e S (last q) ch \<noteq> None"
    using assms unfolding finite_socket_declared_framed_def finite_socket_kept_framed_def
      finite_socket_free_framed_def
    by (auto split: option.splits)
  show ?thesis using q framed_views_at_socket[OF declared] framed_choices_at_frame[OF frame] by simp
qed

lemma framed_socket_commitment:
  assumes test: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g"
  shows "resolution_goal_position g \<noteq> [] \<and> (Vp,Vh) |\<in>| framed_views_at D (last (resolution_goal_position g)) \<and>
    last (resolution_goal_position g) |\<in>| framed_sockets D \<and>
    ch |\<in>| framed_choices_at \<Phi> (last (resolution_goal_position g))"
proof (cases g)
  case (Resolution_Call_Goal q r d p)
  then have "\<exists>Y. finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g"
    using test by (auto simp: finite_socket_commitment_framed_def split: option.splits prod.splits)
  then obtain Y where "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q Y g" by blast
  from framed_declared_socket[OF this] show ?thesis using Resolution_Call_Goal by simp
next
  case (Resolution_Material_Goal q r M)
  then have "finite_socket_declared_framed D \<Phi> Vp Vh ch F st q (finite_material_variables M) g"
    using test by (simp add: finite_socket_commitment_framed_def)
  from framed_declared_socket[OF this] show ?thesis using Resolution_Material_Goal by simp
qed

section \<open>The index, keyed by the socket\<close>

text \<open>
  The rows are the record's sockets, each with its views and frame choices; the socket is the key, and distinct
  sockets are the tree's only obligation (its formation), discharged by the ordered listing of the socket set.
\<close>

definition framed_socket_rows :: "('a,'s::linorder,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow>
    ('s \<times> (nat resolution_view \<times> nat resolution_view) fset \<times> 'a fset option fset) list" where
  "framed_socket_rows D \<Phi> =
    map (\<lambda>s. (s,framed_views_at D s,framed_choices_at \<Phi> s)) (sorted_list_of_fset (framed_sockets D))"

definition framed_socket_index :: "('a,'s::linorder,'d) resolution_declarations \<Rightarrow> ('a,'s,'d) resolution_frames \<Rightarrow>
    ('s,(nat resolution_view \<times> nat resolution_view) fset \<times> 'a fset option fset) rbt" where
  "framed_socket_index D \<Phi> = RBT.bulkload (framed_socket_rows D \<Phi>)"

lemma framed_socket_index_search:
  "RBT.lookup (framed_socket_index D \<Phi>) s = Some v \<longleftrightarrow>
    s |\<in>| framed_sockets D \<and> v = (framed_views_at D s,framed_choices_at \<Phi> s)"
proof -
  have formed: "distinct (map fst (framed_socket_rows D \<Phi>))"
    by (simp add: framed_socket_rows_def comp_def sorted_list_of_fset_def)
  have "RBT.lookup (framed_socket_index D \<Phi>) s = Some v \<longleftrightarrow> (s,v) \<in> set (framed_socket_rows D \<Phi>)"
    using tree_map_index.query_search[OF formed UNIV_I, of s v] by (simp add: framed_socket_index_def)
  then show ?thesis by (auto simp: framed_socket_rows_def)
qed

definition framed_socket_test ::
    "('s::linorder,(nat resolution_view \<times> nat resolution_view) fset \<times> 'a fset option fset) rbt \<Rightarrow>
      (nat resolution_view \<Rightarrow> nat resolution_view \<Rightarrow> 'a fset option \<Rightarrow> bool) \<Rightarrow> 's list \<Rightarrow> bool" where
  "framed_socket_test T R q \<longleftrightarrow> q \<noteq> [] \<and> (case RBT.lookup T (last q) of None \<Rightarrow> False
    | Some (Vs,Cs) \<Rightarrow> fBex Vs (\<lambda>(Vp,Vh). fBex Cs (\<lambda>ch. R Vp Vh ch)))"

text \<open>
  A test that asks the socket's declared test holds at a view and a choice of the whole record exactly when it holds
  at a view and a choice of the entry at the goal's raising socket. A goal at the root raises no socket, and its
  position is read before its last socket is.
\<close>

theorem framed_socket_test_exact:
  "fBex (finite_socket_views D) (\<lambda>(Vp,Vh). fBex (finite_frame_choices \<Phi>) (\<lambda>ch.
      finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> R Vp Vh ch)) \<longleftrightarrow>
    framed_socket_test (framed_socket_index D \<Phi>) (\<lambda>Vp Vh ch.
      finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> R Vp Vh ch) (resolution_goal_position g)"
  (is "?whole \<longleftrightarrow> ?indexed")
proof
  assume ?whole
  then obtain Vp Vh ch where test: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g" and holds: "R Vp Vh ch"
    by auto
  note at = framed_socket_commitment[OF test]
  let ?s = "last (resolution_goal_position g)"
  have found: "RBT.lookup (framed_socket_index D \<Phi>) ?s = Some (framed_views_at D ?s,framed_choices_at \<Phi> ?s)"
    using at by (simp add: framed_socket_index_search)
  have "fBex (framed_views_at D ?s) (\<lambda>(Vp,Vh). fBex (framed_choices_at \<Phi> ?s) (\<lambda>ch.
      finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> R Vp Vh ch))"
    using at test holds by (intro rev_fBexI[where x="(Vp,Vh)"]) (auto intro: rev_fBexI[where x=ch])
  then show ?indexed unfolding framed_socket_test_def found using at by simp
next
  assume ?indexed
  then obtain Vs Cs where found: "RBT.lookup (framed_socket_index D \<Phi>) (last (resolution_goal_position g)) = Some (Vs,Cs)"
    by (auto simp: framed_socket_test_def split: option.splits)
  have holds: "fBex Vs (\<lambda>(Vp,Vh). fBex Cs (\<lambda>ch. finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and> R Vp Vh ch))"
    using \<open>?indexed\<close> by (simp add: framed_socket_test_def found)
  have views: "Vs = framed_views_at D (last (resolution_goal_position g))"
    and choices: "Cs = framed_choices_at \<Phi> (last (resolution_goal_position g))"
    using found by (simp_all add: framed_socket_index_search)
  from holds obtain Vp Vh ch where view: "(Vp,Vh) |\<in>| Vs" and choice: "ch |\<in>| Cs"
    and test: "finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g" and at: "R Vp Vh ch" by auto
  have "(Vp,Vh) |\<in>| finite_socket_views D" using view unfolding views
    by (rule rev_fsubsetD[OF _ framed_views_at_subset])
  moreover have "ch |\<in>| finite_frame_choices \<Phi>" using choice unfolding choices
    by (rule rev_fsubsetD[OF _ framed_choices_at_subset])
  ultimately show ?whole using test at
    by (intro rev_fBexI[where x="(Vp,Vh)"]) (auto intro: rev_fBexI[where x=ch])
qed

section \<open>The code equations\<close>

text \<open>
  The index is built once where the commitment is: every test the commitment makes reads it. The narrowed commitment
  (@{const finite_narrowed_commitment}) reads the framed commitment in its call test and in its production at every
  goal; its equation binds the framed commitment once, so that its index too is built once per record and frames.
\<close>

lemma finite_framed_commitment_indexed [code]:
  "finite_framed_commitment D \<Phi> = (let T = framed_socket_index D \<Phi> in
    \<lparr>commit_call=(\<lambda>F st g. finite_goal_premise st g \<and> (finite_direct_commitment D F st g \<or>
      (resolution_is_call g \<and> framed_socket_test T (\<lambda>Vp Vh ch. finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and>
        finite_call_framed D \<Phi> Vp Vh ch F st g) (resolution_goal_position g)))),
     commit_material=(\<lambda>F st g. finite_material_premise st g \<and> \<not> resolution_is_call g \<and>
      framed_socket_test T (\<lambda>Vp Vh ch. finite_socket_commitment_framed D \<Phi> Vp Vh ch F st g \<and>
        finite_material_framed D \<Phi> Vp Vh ch F st g) (resolution_goal_position g)),
     commit_production=(\<lambda>F st g. None)\<rparr>)"
  by (simp only: finite_framed_commitment_def Let_def framed_socket_test_exact)

definition narrowed_production_under :: "('a,'s,'d,'c) resolution_commitment \<Rightarrow>
    ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'v) produced_declarations \<Rightarrow>
    ('a,'s,'d) resolution_frames \<Rightarrow> 's list option \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
    ('a,'s,'d,'c) resolution_goal \<Rightarrow> (nat resolution_view \<times> finite_factor_term) option" where
  "narrowed_production_under K P n D \<Phi> F st g = (case g of
      Resolution_Call_Goal q r e p \<Rightarrow>
        if commit_call K F st g then
          (case finite_singleton_option (finite_socket_productions D \<Phi> F st g) of None \<Rightarrow> None
          | Some VR \<Rightarrow> if finite_registration_applies (fst VR) (snd VR) e p then
              (case finite_registration_production P n (fst VR) (snd VR) p of None \<Rightarrow> None
              | Some v \<Rightarrow> if finite_production_substitution (fst VR) p v = None then None else Some (fst VR,v))
            else None)
        else None
    | Resolution_Material_Goal q r M \<Rightarrow> None)"

lemma finite_narrowed_production_under:
  "finite_narrowed_production P n D \<Phi> =
    narrowed_production_under (finite_framed_commitment (resolution_declarations.truncate D) \<Phi>) P n D \<Phi>"
  by (intro ext) (simp only: finite_narrowed_production_def narrowed_production_under_def)

lemma finite_narrowed_commitment_under [code]:
  "finite_narrowed_commitment P n D \<Phi> = (let K = finite_framed_commitment (resolution_declarations.truncate D) \<Phi> in
    K\<lparr>commit_call := (\<lambda>F st g. commit_call K F st g \<and>
       (finite_socket_productions D \<Phi> F st g = {||} \<or> narrowed_production_under K P n D \<Phi> F st g \<noteq> None)),
     commit_production := narrowed_production_under K P n D \<Phi>\<rparr>)"
  by (simp only: finite_narrowed_commitment_def finite_narrowed_production_under Let_def)

export_code finite_framed_commitment finite_narrowed_commitment checking SML

end
