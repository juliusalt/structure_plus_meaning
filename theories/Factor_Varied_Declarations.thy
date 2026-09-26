theory Factor_Varied_Declarations
  imports Factor_Finite_Schema_Matching Factor_Resolution_Views Factor_Resolution_Carriers Finite_Set_Composition
begin

text \<open>
  V2a of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an installed
  package by matching its clauses against the placed ones" (task 642). A record of declarations over a program P is
  carried to a program N whose clauses at the same sites are alpha variants of P's: producers and consumers are kept,
  sites not being renamed; a socket declared at a clause S of P at site e and socket s, with its keep flag and its two
  views, is carried to every clause T of N at e that the clause match (@{const finite_schema_match}) sends S to by
  binder and socket maps (f, h), at socket h s, its flag and views kept. A clause of N no clause of P matches keeps no
  commitment and is searched plainly; a declaration at a key where no premise of S stands declares nothing and is
  carried nowhere. Carriers are not declared: they discharge a socket at its clause (@{const socket_carried}), and the
  discharged socket is carried. The record is discharged at N wherever the two programs mean the same at its sites
  (at alpha variants always, @{thm [source] system_alpha_positive_meaning}): a socket's obligation along the match,
  producers, consumers and carriers by the meaning. No clause key is read or mapped and no clause changes.
\<close>

section \<open>A clause and its readings along a renaming\<close>

lemma evaluate_rename_pattern: "evaluate_pattern v (rename_pattern f p) = evaluate_pattern (v \<circ> f) p"
  by (induction p) simp_all

lemma evaluate_rename_material:
  "evaluate_material_satisfaction v (rename_material_pattern f M) \<longleftrightarrow> evaluate_material_satisfaction (v \<circ> f) M"
  by (simp add: rename_material_pattern_def evaluate_rename_pattern)

lemma evaluate_map_finite_pattern:
  "evaluate_pattern v (decode_finite_pattern (map_finite_term_pattern f p)) = evaluate_pattern (v \<circ> f) (decode_finite_pattern p)"
  by (simp add: decode_finite_pattern_map evaluate_rename_pattern)

text \<open>A clause's truth reads a valuation at the clause's variables alone.\<close>

lemma clause_true_cong:
  assumes agree: "\<And>a. a \<in> schema_variables S \<Longrightarrow> u a = v a"
  shows "clause_true M S u \<longleftrightarrow> clause_true M S v"
proof -
  have pv: "evaluate_pattern u p = evaluate_pattern v p" if "(q,d,p) \<in> schema_premises S" for q d p
  proof (rule evaluate_pattern_cong)
    fix a assume "a \<in> pattern_variables p"
    then have "a \<in> schema_variables S" using that by (force simp: schema_variables_def)
    then show "u a = v a" by (rule agree)
  qed
  have mv: "evaluate_material_satisfaction u N \<longleftrightarrow> evaluate_material_satisfaction v N"
    if "(q,N) \<in> schema_material_premises S" for q N
  proof (rule evaluate_material_satisfaction_cong)
    fix a assume "a \<in> material_variables N"
    then have "a \<in> schema_variables S" using that by (force simp: schema_variables_def)
    then show "u a = v a" by (rule agree)
  qed
  have fv: "(\<forall>a\<in>schema_variables S. term_formed (u a)) \<longleftrightarrow> (\<forall>a\<in>schema_variables S. term_formed (v a))"
    using agree by simp
  have calls: "(\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern u p) \<in> M) \<longleftrightarrow>
      (\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern v p) \<in> M)"
    using pv by metis
  have mats: "(\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction u N) \<longleftrightarrow>
      (\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction v N)"
    using mv by metis
  show ?thesis unfolding clause_true_def by (simp only: fv calls mats)
qed

text \<open>
  A clause renamed by binder and socket maps, its callees kept, is true at a valuation exactly when the source is
  true at the valuation composed with the binder map, the two meanings agreeing at the callees.
\<close>

lemma clause_true_renamed:
  assumes eq: "\<And>d x. d \<in> schema_dependencies S \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "clause_true M' (rename_schema f h id S) v \<longleftrightarrow> clause_true M S (v \<circ> f)"
proof -
  let ?R = "rename_schema f h id S"
  have fv: "(\<forall>a\<in>schema_variables ?R. term_formed (v a)) \<longleftrightarrow> (\<forall>a\<in>schema_variables S. term_formed ((v \<circ> f) a))"
    by (simp add: renamed_schema_variables)
  have prem: "(q,e,p') \<in> schema_premises ?R \<longleftrightarrow>
      (\<exists>s d p. (s,d,p) \<in> schema_premises S \<and> q = h s \<and> e = d \<and> p' = rename_pattern f p)" for q e p'
    by (simp add: rename_schema_def map_socket_graph_member)
  have mat: "(q,N') \<in> schema_material_premises ?R \<longleftrightarrow>
      (\<exists>s N. (s,N) \<in> schema_material_premises S \<and> q = h s \<and> N' = rename_material_pattern f N)" for q N'
    by (force simp: rename_schema_def)
  have calls: "(\<forall>q e p'. (q,e,p') \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern v p') \<in> M') \<longleftrightarrow>
      (\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern (v \<circ> f) p) \<in> M)"
  proof
    assume A: "\<forall>q e p'. (q,e,p') \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern v p') \<in> M'"
    show "\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern (v \<circ> f) p) \<in> M"
    proof (intro allI impI)
      fix q d p assume qd: "(q,d,p) \<in> schema_premises S"
      have "(h q,d,rename_pattern f p) \<in> schema_premises ?R" using qd prem by blast
      then have "(d,evaluate_pattern v (rename_pattern f p)) \<in> M'" using A by blast
      then show "(d,evaluate_pattern (v \<circ> f) p) \<in> M"
        using eq[OF schema_dependencies_premise[OF qd]] by (simp add: evaluate_rename_pattern)
    qed
  next
    assume B: "\<forall>q d p. (q,d,p) \<in> schema_premises S \<longrightarrow> (d,evaluate_pattern (v \<circ> f) p) \<in> M"
    show "\<forall>q e p'. (q,e,p') \<in> schema_premises ?R \<longrightarrow> (e,evaluate_pattern v p') \<in> M'"
    proof (intro allI impI)
      fix q e p' assume "(q,e,p') \<in> schema_premises ?R"
      then obtain s p where sp: "(s,e,p) \<in> schema_premises S" and p': "p' = rename_pattern f p" using prem by blast
      have "(e,evaluate_pattern (v \<circ> f) p) \<in> M" using B sp by blast
      then show "(e,evaluate_pattern v p') \<in> M'"
        using eq[OF schema_dependencies_premise[OF sp]] p' by (simp add: evaluate_rename_pattern)
    qed
  qed
  have mats: "(\<forall>q N'. (q,N') \<in> schema_material_premises ?R \<longrightarrow> evaluate_material_satisfaction v N') \<longleftrightarrow>
      (\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction (v \<circ> f) N)"
  proof
    assume A: "\<forall>q N'. (q,N') \<in> schema_material_premises ?R \<longrightarrow> evaluate_material_satisfaction v N'"
    show "\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction (v \<circ> f) N"
    proof (intro allI impI)
      fix q N assume "(q,N) \<in> schema_material_premises S"
      then have "(h q,rename_material_pattern f N) \<in> schema_material_premises ?R" using mat by blast
      then show "evaluate_material_satisfaction (v \<circ> f) N" using A evaluate_rename_material by blast
    qed
  next
    assume B: "\<forall>q N. (q,N) \<in> schema_material_premises S \<longrightarrow> evaluate_material_satisfaction (v \<circ> f) N"
    show "\<forall>q N'. (q,N') \<in> schema_material_premises ?R \<longrightarrow> evaluate_material_satisfaction v N'"
    proof (intro allI impI)
      fix q N' assume "(q,N') \<in> schema_material_premises ?R"
      then obtain s N where "(s,N) \<in> schema_material_premises S" "N' = rename_material_pattern f N" using mat by blast
      then show "evaluate_material_satisfaction v N'" using B evaluate_rename_material by blast
    qed
  qed
  show ?thesis unfolding clause_true_def by (simp only: fv calls mats)
qed

text \<open>A view reads a pattern renamed by a binder map as the renaming of its reading.\<close>

lemma finite_pattern_substitute_variable_map:
  "finite_pattern_substitute (\<lambda>a. Finite_Variable (f a)) c = map_finite_term_pattern f c"
  by (induction c) simp_all

lemma resolution_view_pattern_map:
  assumes "resolution_view_pattern V c = Some (ci,co)"
  shows "resolution_view_pattern V (map_finite_term_pattern f c) =
    Some (map_finite_term_pattern f ci,map_finite_term_pattern f co)"
  using resolution_view_pattern_substitute[OF assms, of "\<lambda>a. Finite_Variable (f a)"]
  by (simp only: finite_pattern_substitute_variable_map)

lemma resolution_view_parts_variables:
  assumes formed: "view_formed V" and viewed: "resolution_view_pattern V c = Some (ci,co)"
  shows "fset (finite_pattern_variables ci) \<subseteq> fset (finite_pattern_variables c)"
    and "fset (finite_pattern_variables co) \<subseteq> fset (finite_pattern_variables c)"
  using resolution_view_pattern_variables[OF formed viewed] by auto

lemma decoded_pattern_variables: "pattern_variables (decode_finite_pattern p) = fset (finite_pattern_variables p)"
  by (metis finite_pattern_variables_correct)

section \<open>A socket's obligation along the match\<close>

context finite_schema_matched
begin

lemma clause_true_along:
  assumes eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "clause_true M' (decode_finite_schema T) v \<longleftrightarrow> clause_true M (decode_finite_schema S) (v \<circ> f)"
  unfolding decoded by (rule clause_true_renamed[OF eq])

lemma inverse_agrees: "a \<in> schema_variables (decode_finite_schema S) \<Longrightarrow> ((u \<circ> binder_inverse) \<circ> f) a = u a"
  by (simp add: binder_inverse_def inv_into_f_f[OF binders])

lemma clause_true_back:
  assumes eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and true: "clause_true M (decode_finite_schema S) u"
  shows "clause_true M' (decode_finite_schema T) (u \<circ> binder_inverse)"
proof -
  have "clause_true M (decode_finite_schema S) ((u \<circ> binder_inverse) \<circ> f)"
    using clause_true_cong[of "decode_finite_schema S" "(u \<circ> binder_inverse) \<circ> f" u M] inverse_agrees true by blast
  then show ?thesis using clause_true_along[OF eq] by blast
qed

lemma evaluate_back:
  assumes "fset (finite_pattern_variables q) \<subseteq> schema_variables (decode_finite_schema S)"
  shows "evaluate_pattern ((u \<circ> binder_inverse) \<circ> f) (decode_finite_pattern q) = evaluate_pattern u (decode_finite_pattern q)"
proof (rule evaluate_pattern_cong)
  fix a assume "a \<in> pattern_variables (decode_finite_pattern q)"
  then have "a \<in> schema_variables (decode_finite_schema S)" using assms by (auto simp: decoded_pattern_variables)
  then show "((u \<circ> binder_inverse) \<circ> f) a = u a" by (rule inverse_agrees)
qed

lemma conclusion_back: "finite_schema_conclusion S = map_finite_term_pattern binder_inverse (finite_schema_conclusion T)"
  using arg_cong[OF inverse, of finite_schema_conclusion] by (simp add: finite_rename_schema_def)

lemma head_kept_along:
  assumes kept: "head_kept keep Vh S (v \<circ> f) u" and formed: "view_formed Vh"
  shows "head_kept keep Vh T v (u \<circ> binder_inverse)"
proof (cases "resolution_view_pattern Vh (finite_schema_conclusion S)")
  case None
  have NT: "resolution_view_pattern Vh (finite_schema_conclusion T) = None"
  proof (rule ccontr)
    assume "resolution_view_pattern Vh (finite_schema_conclusion T) \<noteq> None"
    then obtain x y where "resolution_view_pattern Vh (finite_schema_conclusion T) = Some (x,y)" by auto
    from resolution_view_pattern_map[OF this, of binder_inverse] show False using None by (simp add: conclusion_back[symmetric])
  qed
  have "evaluate_pattern u (decode_finite_pattern (finite_schema_conclusion S)) =
      evaluate_pattern (v \<circ> f) (decode_finite_pattern (finite_schema_conclusion S))"
    using kept None by (simp add: head_kept_def)
  then show ?thesis
    unfolding head_kept_def NT by (simp add: conclusion evaluate_map_finite_pattern evaluate_back[OF head_scope])
next
  case (Some cc)
  obtain ci co where cc: "cc = (ci,co)" by (cases cc)
  have vS: "resolution_view_pattern Vh (finite_schema_conclusion S) = Some (ci,co)" using Some cc by simp
  have vT: "resolution_view_pattern Vh (finite_schema_conclusion T) =
      Some (map_finite_term_pattern f ci,map_finite_term_pattern f co)"
    unfolding conclusion by (rule resolution_view_pattern_map[OF vS])
  have ci: "fset (finite_pattern_variables ci) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(1)[OF formed vS] head_scope by blast
  have co: "fset (finite_pattern_variables co) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(2)[OF formed vS] head_scope by blast
  from kept vS have "evaluate_pattern u (decode_finite_pattern ci) = evaluate_pattern (v \<circ> f) (decode_finite_pattern ci)"
      "keep \<longrightarrow> evaluate_pattern u (decode_finite_pattern co) = evaluate_pattern (v \<circ> f) (decode_finite_pattern co)"
    by (simp_all add: head_kept_def)
  then show ?thesis
    unfolding head_kept_def vT by (simp add: evaluate_map_finite_pattern evaluate_back[OF ci] evaluate_back[OF co])
qed

lemma premise_at_image:
  assumes sock: "s \<in> schema_sockets (decode_finite_schema S)" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
  obtains p0 where "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
proof -
  obtain s' p0 where o: "(s',d,p0) |\<in>| finite_schema_premises S" "h s = h s'" "p = map_finite_term_pattern f p0"
    using call_origin[OF at] by blast
  have "s = s'" by (rule inj_onD[OF sockets o(2) sock source_socket(1)[OF o(1)]])
  then show ?thesis using that o by blast
qed

lemma material_at_image:
  assumes sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and at: "(h s,N) \<in> schema_material_premises (decode_finite_schema T)"
  obtains N0 where "(s,N0) \<in> schema_material_premises (decode_finite_schema S)" "N = rename_material_pattern f N0"
proof -
  have "(h s,N) \<in> (\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises (decode_finite_schema S)"
    using at by (simp add: decoded rename_schema_def)
  then obtain s' N0 where o: "(s',N0) \<in> schema_material_premises (decode_finite_schema S)" "h s = h s'"
      "N = rename_material_pattern f N0" by force
  have "s' \<in> schema_sockets (decode_finite_schema S)" using o(1) by (force simp: schema_sockets_def rel_dom_def)
  then have "s = s'" by (rule inj_onD[OF sockets o(2) sock])
  then show ?thesis using that o by blast
qed

text \<open>
  A socket's obligation at S carries to T at the image of its socket, its flag and views kept, wherever the two
  meanings agree at S's callees: an instance of T is read back through the binder map, the source's obligation gives
  its new instance, and that instance is carried forward through the binder map's inverse on S's scope, the premise's
  and the head's views read at the renamed patterns.
\<close>

theorem socket_discharged_matched:
  assumes src: "socket_discharged M S s keep Vp Vh"
    and sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and Vpf: "view_formed Vp" and Vhf: "view_formed Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "socket_discharged M' T (h s) keep Vp Vh"
  unfolding socket_discharged_def
proof (intro conjI allI impI)
  fix d p assume at: "(h s,d,p) |\<in>| finite_schema_premises T"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding socket_discharged_def by fastforce
  show "resolution_view_pattern Vp p \<noteq> None" using resolution_view_pattern_map[OF v0, of f] p0(2) by simp
next
  fix v d p xi yo t y'
  assume vT: "clause_true M' (decode_finite_schema T) v" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
    and vp: "resolution_view_pattern Vp p = Some (xi,yo)" and dt: "(d,t) \<in> M'"
    and vt: "resolution_view_term Vp t = Some (evaluate_pattern v (decode_finite_pattern xi),y')"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding socket_discharged_def by fastforce
  have xy: "xi = map_finite_term_pattern f xi0" "yo = map_finite_term_pattern f yo0"
    using resolution_view_pattern_map[OF v0, of f] vp p0(2) by simp_all
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)"
    by (rule schema_dependencies_premise[of s d "decode_finite_pattern p0"]) (use p0(1) in \<open>auto simp: finite_premise_decoded\<close>)
  have dt0: "(d,t) \<in> M" using dt eq[OF dep] by simp
  have vS: "clause_true M (decode_finite_schema S) (v \<circ> f)" using vT clause_true_along[OF eq] by blast
  have vt0: "resolution_view_term Vp t = Some (evaluate_pattern (v \<circ> f) (decode_finite_pattern xi0),y')"
    using vt by (simp add: xy evaluate_map_finite_pattern)
  obtain h2 where h2: "clause_true M (decode_finite_schema S) h2" "head_kept keep Vh S (v \<circ> f) h2"
      "evaluate_pattern h2 (decode_finite_pattern xi0) = evaluate_pattern (v \<circ> f) (decode_finite_pattern xi0)"
      "evaluate_pattern h2 (decode_finite_pattern yo0) = y'"
    using src vS p0(1) v0 dt0 vt0 unfolding socket_discharged_def by blast
  have pv: "fset (finite_pattern_variables p0) \<subseteq> schema_variables (decode_finite_schema S)" by (rule call_scope[OF p0(1)])
  have xv: "fset (finite_pattern_variables xi0) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(1)[OF Vpf v0] pv by blast
  have yv: "fset (finite_pattern_variables yo0) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(2)[OF Vpf v0] pv by blast
  show "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T v h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern v (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = y'"
  proof (intro exI conjI)
    show "clause_true M' (decode_finite_schema T) (h2 \<circ> binder_inverse)" by (rule clause_true_back[OF eq h2(1)])
    show "head_kept keep Vh T v (h2 \<circ> binder_inverse)" by (rule head_kept_along[OF h2(2) Vhf])
    show "evaluate_pattern (h2 \<circ> binder_inverse) (decode_finite_pattern xi) = evaluate_pattern v (decode_finite_pattern xi)"
      using h2(3) by (simp add: xy evaluate_map_finite_pattern evaluate_back[OF xv])
    show "evaluate_pattern (h2 \<circ> binder_inverse) (decode_finite_pattern yo) = y'"
      using h2(4) by (simp add: xy evaluate_map_finite_pattern evaluate_back[OF yv])
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
      "\<forall>a\<in>material_variables N0. h2 a = (g \<circ> f) a"
    using src vS N0(1) sat0 se0 unfolding socket_discharged_def by blast
  have mv: "material_variables N0 \<subseteq> schema_variables (decode_finite_schema S)"
    using N0(1) by (force simp: schema_variables_def)
  show "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T v h' \<and>
      (\<forall>a\<in>material_variables N. h' a = g a)"
  proof (intro exI conjI ballI)
    show "clause_true M' (decode_finite_schema T) (h2 \<circ> binder_inverse)" by (rule clause_true_back[OF eq h2(1)])
    show "head_kept keep Vh T v (h2 \<circ> binder_inverse)" by (rule head_kept_along[OF h2(2) Vhf])
  next
    fix b assume "b \<in> material_variables N"
    then obtain a where a: "a \<in> material_variables N0" "b = f a" using N0(2) by (auto simp: renamed_material_variables)
    have "(h2 \<circ> binder_inverse) b = ((h2 \<circ> binder_inverse) \<circ> f) a" using a(2) by simp
    also have "\<dots> = h2 a" using inverse_agrees[of a h2] a(1) mv by blast
    also have "\<dots> = g b" using h2(3) a by simp
    finally show "(h2 \<circ> binder_inverse) b = g b" .
  qed
qed

end

section \<open>The varied record\<close>

text \<open>
  The sockets a socket declaration is carried to: where its clause is one of P's at its site and its key a socket of
  the clause, every clause of N at that site the match reaches, at the image of the socket.
\<close>

definition varied_sockets ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      'd \<times> ('a,'s,'d) finite_factor_schema \<times> 's \<times> bool \<times> nat resolution_view \<times> nat resolution_view \<Rightarrow>
      ('d \<times> ('b,'t,'d) finite_factor_schema \<times> 't \<times> bool \<times> nat resolution_view \<times> nat resolution_view) fset" where
  "varied_sockets P N z = (case z of (e,S,s,keep,Vp,Vh) \<Rightarrow>
    if (\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S) then
      ffUnion (fimage (\<lambda>((e',c'),T). if e' = e then (case finite_schema_match S T of None \<Rightarrow> {||}
        | Some (f,h) \<Rightarrow> {|(e,T,h s,keep,Vp,Vh)|}) else {||}) (finite_system_clauses N))
    else {||})"

text \<open>
  Producers and consumers are kept; each socket declaration is replaced by the sockets it is carried to. The binder
  and socket types change with the programs', so the record is written with its fields, as a relocation's is.
\<close>

definition declarations_varied ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d) resolution_declarations \<Rightarrow> ('b,'t,'d) resolution_declarations" where
  "declarations_varied P N D = \<lparr>declared_producers = declared_producers D,
    declared_consumers = declared_consumers D,
    declared_sockets = ffUnion (fimage (varied_sockets P N) (declared_sockets D))\<rparr>"

lemma declarations_varied_sockets:
  "declared_sockets (declarations_varied P N D) = ffUnion (fimage (varied_sockets P N) (declared_sockets D))"
  by (simp add: declarations_varied_def)

lemma declarations_varied_kept [simp]:
  "declared_producers (declarations_varied P N D) = declared_producers D"
  "declared_consumers (declarations_varied P N D) = declared_consumers D"
  by (simp_all add: declarations_varied_def)

lemma varied_sockets_member:
  "y |\<in>| varied_sockets P N (e,S,s,keep,Vp,Vh) \<longleftrightarrow> (\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and>
    s \<in> schema_sockets (decode_finite_schema S) \<and>
    (\<exists>c' T f h. ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and>
      y = (e,T,h s,keep,Vp,Vh))"
proof
  assume y: "y |\<in>| varied_sockets P N (e,S,s,keep,Vp,Vh)"
  have guard: "(\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S)"
  proof (rule ccontr)
    assume ng: "\<not> ((\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S))"
    have "varied_sockets P N (e,S,s,keep,Vp,Vh) = {||}" by (simp only: varied_sockets_def prod.case if_not_P[OF ng])
    then show False using y by simp
  qed
  let ?F = "\<lambda>((e',c'),T). if e' = e then
      (case finite_schema_match S T of None \<Rightarrow> {||} | Some (f,h) \<Rightarrow> {|(e,T,h s,keep,Vp,Vh)|}) else {||}"
  have yU: "y |\<in>| ffUnion (fimage ?F (finite_system_clauses N))"
    using y by (simp only: varied_sockets_def prod.case if_P[OF guard])
  obtain w where w: "w |\<in>| finite_system_clauses N" "y |\<in>| ?F w"
    using iffD1[OF finite_union_image_member yU] by (elim exE conjE)
  obtain ec T where ws0: "w = (ec,T)" by (cases w)
  obtain e' c' where ec: "ec = (e',c')" by (cases ec)
  have ws: "w = ((e',c'),T)" by (simp only: ws0 ec)
  have e': "e' = e"
  proof (rule ccontr)
    assume "e' \<noteq> e"
    then show False using w(2) unfolding ws by simp
  qed
  obtain f h where fh: "finite_schema_match S T = Some (f,h)" and yv: "y = (e,T,h s,keep,Vp,Vh)"
  proof (cases "finite_schema_match S T")
    case None
    then show ?thesis using w(2) unfolding ws by (simp add: e')
  next
    case (Some fh')
    obtain f h where fh': "fh' = (f,h)" by (cases fh')
    show ?thesis by (rule that[of f h]) (use Some fh' w(2) in \<open>simp_all add: ws e'\<close>)
  qed
  show "(\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
      (\<exists>c' T f h. ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and>
        y = (e,T,h s,keep,Vp,Vh))" using guard w(1) ws e' fh yv by blast
next
  assume "(\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
    (\<exists>c' T f h. ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and>
      y = (e,T,h s,keep,Vp,Vh))"
  then obtain c' T f h where guard: "(\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S)"
    and T: "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "y = (e,T,h s,keep,Vp,Vh)"
    by blast
  let ?F = "\<lambda>((e',c'),T). if e' = e then
      (case finite_schema_match S T of None \<Rightarrow> {||} | Some (f,h) \<Rightarrow> {|(e,T,h s,keep,Vp,Vh)|}) else {||}"
  have yF: "y |\<in>| ?F ((e,c'),T)" using T(2,3) by simp
  have "y |\<in>| ffUnion (fimage ?F (finite_system_clauses N))"
    by (rule iffD2[OF finite_union_image_member], rule exI[of _ "((e,c'),T)"], rule conjI[OF T(1) yF])
  then show "y |\<in>| varied_sockets P N (e,S,s,keep,Vp,Vh)" by (simp only: varied_sockets_def prod.case if_P[OF guard])
qed

lemma declarations_varied_sockets_member:
  "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N D) \<longleftrightarrow>
    (\<exists>S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<and> ((e,c),S) |\<in>| finite_system_clauses P \<and>
      s \<in> schema_sockets (decode_finite_schema S) \<and> ((e,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match S T = Some (f,h) \<and> t = h s)"
proof
  assume "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N D)"
  then obtain z where z: "z |\<in>| declared_sockets D" "(e,T,t,keep,Vp,Vh) |\<in>| varied_sockets P N z"
    unfolding declarations_varied_sockets finite_union_image_member by blast
  obtain e0 S s keep0 Vp0 Vh0 where zs: "z = (e0,S,s,keep0,Vp0,Vh0)" by (metis prod_cases6)
  show "\<exists>S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<and> ((e,c),S) |\<in>| finite_system_clauses P \<and>
      s \<in> schema_sockets (decode_finite_schema S) \<and> ((e,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match S T = Some (f,h) \<and> t = h s"
    using z unfolding zs varied_sockets_member by blast
next
  assume "\<exists>S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<and> ((e,c),S) |\<in>| finite_system_clauses P \<and>
      s \<in> schema_sockets (decode_finite_schema S) \<and> ((e,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match S T = Some (f,h) \<and> t = h s"
  then obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" "((e,c),S) |\<in>| finite_system_clauses P"
      "s \<in> schema_sockets (decode_finite_schema S)" "((e,c'),T) |\<in>| finite_system_clauses N"
      "finite_schema_match S T = Some (f,h)" "t = h s" by blast
  have "(e,T,t,keep,Vp,Vh) |\<in>| varied_sockets P N (e,S,s,keep,Vp,Vh)"
    unfolding varied_sockets_member using m by blast
  then show "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N D)"
    unfolding declarations_varied_sockets finite_union_image_member using m(1) by blast
qed

lemma declarations_formed_varied:
  assumes "declarations_formed D"
  shows "declarations_formed (declarations_varied P N D)"
proof -
  have sockets: "view_formed Vp \<and> view_formed Vh" if m: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N D)"
    for e T t keep Vp Vh
  proof -
    obtain S s where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
      using m[unfolded declarations_varied_sockets_member] by blast
    moreover have "fBall (declared_sockets D) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
      using assms by (simp add: declarations_formed_def)
    ultimately show ?thesis by (auto dest: fbspec)
  qed
  show ?thesis unfolding declarations_formed_def declarations_varied_kept
  proof (intro conjI)
    show "fBall (declared_producers D) (\<lambda>(d,V,hs). view_formed V)" using assms by (simp add: declarations_formed_def)
    show "fBall (declared_consumers D) (\<lambda>(d,e,V,i). view_formed V)" using assms by (simp add: declarations_formed_def)
    show "fBall (declared_sockets (declarations_varied P N D)) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
    proof (rule fBallI)
      fix z assume z: "z |\<in>| declared_sockets (declarations_varied P N D)"
      obtain e T t keep Vp Vh where zs: "z = (e,T,t,keep,Vp,Vh)" by (metis prod_cases6)
      show "case z of (e,S,s,keep,Vp,Vh) \<Rightarrow> view_formed Vp \<and> view_formed Vh"
        using sockets[of e T t keep Vp Vh] z unfolding zs by simp
    qed
  qed
qed

lemma finite_system_clause_formed:
  assumes "finite_system_formed P" "((e,c),S) |\<in>| finite_system_clauses P"
  shows "finite_schema_formed S"
  using fbspec[OF assms(1)[unfolded finite_system_formed_def, THEN conjunct2, THEN conjunct2, THEN conjunct2] assms(2)]
  by simp

section \<open>The varied record discharged\<close>

text \<open>
  A record discharged at P's meaning is, varied, discharged at N's wherever the two mean the same at the record's
  sites: producers and consumers by the meaning at their sites, each carried socket by its obligation along the match
  (@{text socket_discharged_matched}), its callees among the record's sites.
\<close>

theorem declarations_varied_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites D \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "declarations_discharged (positive_meaning (decode_finite_system N)) (declarations_varied P N D) corr"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?M' = "positive_meaning (decode_finite_system N)"
  have Df: "declarations_formed D" using discharged by (simp add: declarations_discharged_def)
  show ?thesis unfolding declarations_discharged_def
  proof (intro conjI allI impI)
    show "declarations_formed (declarations_varied P N D)" by (rule declarations_formed_varied[OF Df])
  next
    fix d W hs assume "(d,W,hs) |\<in>| declared_producers (declarations_varied P N D)"
    then have d: "(d,W,hs) |\<in>| declared_producers D" by simp
    have "producer_discharged ?M d W hs (corr d)" using discharged d unfolding declarations_discharged_def by blast
    then show "producer_discharged ?M' d W hs (corr d)"
      unfolding producer_discharged_def at[OF declared_sites_members(1)[OF d]] .
  next
    fix d e W i assume "(d,e,W,i) |\<in>| declared_consumers (declarations_varied P N D)"
    then have de: "(d,e,W,i) |\<in>| declared_consumers D" by simp
    have "consumer_discharged ?M e W (corr d i)" using discharged de unfolding declarations_discharged_def by blast
    then show "consumer_discharged ?M' e W (corr d i)"
      unfolding consumer_discharged_def at[OF declared_sites_members(3)[OF de]] .
  next
    fix e T t keep Vp Vh assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N D)"
    obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" "((e,c),S) |\<in>| finite_system_clauses P"
        "s \<in> schema_sockets (decode_finite_schema S)" "((e,c'),T) |\<in>| finite_system_clauses N"
        "finite_schema_match S T = Some (f,h)" "t = h s"
      using mem[unfolded declarations_varied_sockets_member] by blast
    interpret matched: finite_schema_matched S T f h
      by unfold_locales (rule finite_system_clause_formed[OF Pf m(2)], rule finite_system_clause_formed[OF Nf m(4)], rule m(5))
    have src: "socket_discharged ?M S s keep Vp Vh" using discharged m(1) unfolding declarations_discharged_def by blast
    have "fBall (declared_sockets D) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
      using Df by (simp add: declarations_formed_def)
    from fbspec[OF this m(1)] have views: "view_formed Vp" "view_formed Vh" by simp_all
    have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites D" by (rule declared_sites_members(5)[OF m(1)])
    show "socket_discharged ?M' T t keep Vp Vh" unfolding m(6)
      by (rule matched.socket_discharged_matched[OF src m(3) views]) (use at sub in blast)
  qed
qed

text \<open>At alpha variants the two programs mean the same everywhere, and both are formed.\<close>

corollary declarations_varied_discharged_variant:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "declarations_discharged (positive_meaning (decode_finite_system N)) (declarations_varied P N D) corr"
proof -
  have Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  show ?thesis
    by (rule declarations_varied_discharged[OF Pf Nf _ discharged]) (simp add: system_alpha_positive_meaning[OF alpha])
qed

text \<open>A carrier's obligation reads the meaning at its site alone.\<close>

lemma carrier_discharged_agree:
  assumes "\<And>x. (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "carrier_discharged M' d V cin cout \<longleftrightarrow> carrier_discharged M d V cin cout"
  unfolding carrier_discharged_def assms ..

section \<open>The committed forms at the varied program\<close>

text \<open>
  The exchange premise at N is derived from the carried discharge (@{text finite_declared_commitment_exchanges}), never
  transferred: the forms under discharged declarations at views (@{text finite_declared_forms_exact}) hold at N with the
  varied declarations, at a construction whose registrations are premise-only at N and whose lifts hold there.
\<close>

theorem finite_commitment_exchanges_varied:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites D \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> N"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa> (finite_declared_commitment (declarations_varied P N D)) N"
  by (rule finite_declared_commitment_exchanges[OF \<kappa> declarations_varied_discharged[OF Pf Nf at discharged] only])

lemmas finite_varied_refutation_exact = finite_declared_refutation_exact[OF _ declarations_varied_discharged]
lemmas finite_varied_verdict_exact = finite_declared_verdict_exact[OF _ declarations_varied_discharged]
lemmas finite_varied_demand_exact = finite_declared_demand_exact[OF _ declarations_varied_discharged]
lemmas native_varied_declared_resolution_exact = native_declared_resolution_exact[OF _ declarations_varied_discharged]

text \<open>The four forms as one fact, for the route's consumers; at alpha variants they take the variance alone.\<close>

lemmas finite_varied_forms_exact = finite_varied_refutation_exact finite_varied_verdict_exact
  finite_varied_demand_exact native_varied_declared_resolution_exact

lemmas finite_variant_forms_exact =
  finite_declared_refutation_exact[OF _ declarations_varied_discharged_variant]
  finite_declared_verdict_exact[OF _ declarations_varied_discharged_variant]
  finite_declared_demand_exact[OF _ declarations_varied_discharged_variant]
  native_declared_resolution_exact[OF _ declarations_varied_discharged_variant]

section \<open>The transfer to a varied presentation\<close>

text \<open>
  A program and its varied presentation give the same committed verdict where both give one: each verdict is the
  call's meaning in its own program (the forms at views, the exchange at N derived from the carried discharge), and
  alpha variants mean the same. Beside @{text finite_committed_relocation_transfer} and
  @{text finite_committed_agreement_transfer}, not a restatement of either.
\<close>

corollary finite_committed_variant_transfer:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
    and only: "finite_registrations_premise_only \<kappa> P" and cl: "finite_construction_lifts (\<lambda>_. False) \<kappa> P"
    and \<kappa>': "finite_witness_construction_formed \<kappa>'"
    and only': "finite_registrations_premise_only \<kappa>' N" and cl': "finite_construction_lifts (\<lambda>_. False) \<kappa>' N"
    and alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and v: "finite_resolution_verdict (finite_committed_resolution \<kappa> (finite_declared_commitment D) P d t n) = Some b"
    and v': "finite_resolution_verdict (finite_committed_resolution \<kappa>' (finite_declared_commitment (declarations_varied P N D))
      N d t m) = Some b'"
  shows "b = b'"
proof -
  have "b \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
    by (rule finite_declared_verdict_exact[OF \<kappa> discharged only cl v])
  moreover have "b' \<longleftrightarrow> (d,decode_finite_term t) \<in> positive_meaning (decode_finite_system N)"
    by (rule finite_declared_verdict_exact[OF \<kappa>' declarations_varied_discharged_variant[OF alpha discharged] only' cl' v'])
  ultimately show ?thesis using system_alpha_positive_meaning[OF alpha] by simp
qed

text \<open>
  After #595's relocation: a record discharged at the numbered program, relocated by a placement injective on its
  definitions and the record's sites (@{text declarations_relocated_discharged}), and varied to an alpha variant of
  the placed program, is discharged there. Relocation comes first, as the installation places the numbered program
  before its package is read; the variation then names the installed clauses as they stand.
\<close>

theorem declarations_relocated_varied_discharged:
  fixes Q :: "('a,'s::linorder,'d,'c) finite_schema_system" and g :: "'d \<Rightarrow> 'e"
    and N :: "('b,'t::linorder,'e,'f) finite_schema_system"
  assumes Qf: "schema_system_formed (decode_finite_system Q)"
    and injective: "inj_on g (system_definitions (decode_finite_system Q) \<union> declared_sites D)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system Q)) D corr"
    and alpha: "system_alpha_variant (decode_finite_system (finite_rename_system g Q)) (decode_finite_system N)"
  shows "declarations_discharged (positive_meaning (decode_finite_system N))
    (declarations_varied (finite_rename_system g Q) N (declarations_relocated g D)) (corr \<circ> inv_into (declared_sites D) g)"
  by (rule declarations_varied_discharged_variant[OF alpha declarations_relocated_discharged[OF Qf injective discharged]])

end
