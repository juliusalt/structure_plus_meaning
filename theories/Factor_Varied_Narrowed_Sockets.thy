theory Factor_Varied_Narrowed_Sockets
  imports Factor_Varied_Declarations Factor_Varied_Constructions Factor_Narrowed_Commitments
begin

text \<open>
  V2b of DECISIONS.md "A checker does not produce", its addition "Registrations and declarations reach an installed
  package by matching its clauses against the placed ones" (task 642), its (1) and (2), with the whole-record discharge
  (task 725's line for it). R5e's narrowed record (@{text narrowed_declarations}) and R5f1's production field
  (@{text produced_declarations}) are carried along the clause match (@{const finite_schema_match}) beside V2a's record:
  the truncation is V2a's @{const declarations_varied}, as it stands; the class at a carried socket (e, T, t) is the
  class the sources the match sends to T at t declare, agreeing where several do (their conjunction, each source's
  where they agree); the production is the source's registration carried to the clause of the callee site its clause
  matches, its variable the image of the head variable under that match's binder map, a production only where every
  source's carries to that one. A narrowed socket's obligation carries as V2a's socket obligation does, through V2a's
  locale facts; the completeness at a narrowed socket (@{thm [source] registration_complete_at_socket}) carries with
  the production, the head's input read at the matched clause as at the source at the bindings carried back, wherever
  the target's values at the carried production are the source's. No clause key is read or mapped and no clause
  changes; a clause no match reaches keeps no narrowing and no production.
\<close>

section \<open>Bindings carried back read the same values\<close>

lemma carried_fibre_member: "t |\<in>| fimage snd (ffilter (\<lambda>r. fst r = k) X) \<longleftrightarrow> (k,t) |\<in>| X"
  by (force simp: fimage.rep_eq ffilter.rep_eq)

lemma carried_back_valuation:
  assumes "y |\<in>| X"
  shows "finite_binding_valuation (finite_bindings_carried_back f X B) y = finite_binding_valuation B (f y)"
proof -
  have "fimage snd (ffilter (\<lambda>r. fst r = y) (finite_bindings_carried_back f X B)) =
      fimage snd (ffilter (\<lambda>r. fst r = f y) B)"
    unfolding fset_eq_iff carried_fibre_member finite_bindings_carried_back_member using assms by simp
  then show ?thesis by (simp only: finite_binding_valuation_def finite_relation_option_def)
qed

section \<open>A narrowed socket and a head registration along the match\<close>

context finite_schema_matched
begin

text \<open>
  A narrowed socket's obligation at S carries to T at the image of its socket, its flag, views and class kept,
  wherever the two meanings agree at S's callees: the narrowing reads a true instance of T back through the binder
  map, and the obligation over the class is V2a's socket obligation read at the answers in the class.
\<close>

theorem narrowed_socket_discharged_matched:
  assumes src: "narrowed_socket_discharged M S s keep Vp Vh K"
    and sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and Vpf: "view_formed Vp" and Vhf: "view_formed Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "narrowed_socket_discharged M' T (h s) keep Vp Vh K"
  unfolding narrowed_socket_discharged_def socket_narrowing_def
proof (intro conjI allI impI)
  fix v d p xi yo
  assume vT: "clause_true M' (decode_finite_schema T) v" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
    and vp: "resolution_view_pattern Vp p = Some (xi,yo)"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_discharged_def by fastforce
  have xy: "xi = map_finite_term_pattern f xi0" "yo = map_finite_term_pattern f yo0"
    using resolution_view_pattern_map[OF v0, of f] vp p0(2) by simp_all
  have vS: "clause_true M (decode_finite_schema S) (v \<circ> f)" using vT clause_true_along[OF eq] by blast
  have "K (evaluate_pattern (v \<circ> f) (decode_finite_pattern yo0))"
    using src vS p0(1) v0 unfolding narrowed_socket_discharged_def socket_narrowing_def by blast
  then show "K (evaluate_pattern v (decode_finite_pattern yo))" by (simp add: xy evaluate_map_finite_pattern)
next
  fix d p assume at: "(h s,d,p) |\<in>| finite_schema_premises T"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_discharged_def by fastforce
  show "resolution_view_pattern Vp p \<noteq> None" using resolution_view_pattern_map[OF v0, of f] p0(2) by simp
next
  fix v d p xi yo t y'
  assume vT: "clause_true M' (decode_finite_schema T) v" and at: "(h s,d,p) |\<in>| finite_schema_premises T"
    and vp: "resolution_view_pattern Vp p = Some (xi,yo)" and dt: "(d,t) \<in> M'"
    and vt: "resolution_view_term Vp t = Some (evaluate_pattern v (decode_finite_pattern xi),y')" and n: "K y'"
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using premise_at_image[OF sock at] .
  obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)"
    using src p0(1) unfolding narrowed_socket_discharged_def by fastforce
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
    using src vS p0(1) v0 dt0 vt0 n unfolding narrowed_socket_discharged_def by blast
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
    using src vS N0(1) sat0 se0 unfolding narrowed_socket_discharged_def by blast
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

text \<open>
  A head registration's input is read at T at bindings B as at S at B carried back over S's scope: the view reads
  the renamed conclusion as the renaming of its reading, and the carried bindings give each variable of S's scope
  the value B gives its image.
\<close>

lemma head_registration_input_matched:
  assumes formed: "view_formed Vc"
  shows "head_registration_input Vc T B =
    head_registration_input Vc S (finite_bindings_carried_back f (finite_schema_variables S) B)"
proof (cases "resolution_view_pattern Vc (finite_schema_conclusion S)")
  case None
  have NT: "resolution_view_pattern Vc (finite_schema_conclusion T) = None"
  proof (rule ccontr)
    assume "resolution_view_pattern Vc (finite_schema_conclusion T) \<noteq> None"
    then obtain x y where "resolution_view_pattern Vc (finite_schema_conclusion T) = Some (x,y)" by auto
    from resolution_view_pattern_map[OF this, of binder_inverse] show False using None by (simp add: conclusion_back[symmetric])
  qed
  show ?thesis by (simp add: head_registration_input_def None NT)
next
  case (Some cc)
  obtain ci co where cc: "cc = (ci,co)" by (cases cc)
  have vS: "resolution_view_pattern Vc (finite_schema_conclusion S) = Some (ci,co)" using Some cc by simp
  have vT: "resolution_view_pattern Vc (finite_schema_conclusion T) =
      Some (map_finite_term_pattern f ci,map_finite_term_pattern f co)"
    unfolding conclusion by (rule resolution_view_pattern_map[OF vS])
  have ci: "fset (finite_pattern_variables ci) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(1)[OF formed vS] head_scope by blast
  have "evaluate_pattern (\<lambda>x. decode_finite_term (finite_binding_valuation B x))
        (decode_finite_pattern (map_finite_term_pattern f ci)) =
      evaluate_pattern (\<lambda>x. decode_finite_term (finite_binding_valuation
        (finite_bindings_carried_back f (finite_schema_variables S) B) x)) (decode_finite_pattern ci)"
    unfolding evaluate_map_finite_pattern
  proof (rule evaluate_pattern_cong)
    fix a assume "a \<in> pattern_variables (decode_finite_pattern ci)"
    then have "a \<in> schema_variables (decode_finite_schema S)" using ci by (auto simp: decoded_pattern_variables)
    then have aX: "a |\<in>| finite_schema_variables S" by (simp add: finite_schema_variables_correct)
    show "((\<lambda>x. decode_finite_term (finite_binding_valuation B x)) \<circ> f) a =
        decode_finite_term (finite_binding_valuation (finite_bindings_carried_back f (finite_schema_variables S) B) a)"
      by (simp add: carried_back_valuation[OF aX])
  qed
  then show ?thesis by (simp add: head_registration_input_def vS vT)
qed

text \<open>A head registration at S is one at T, at the image of its variable.\<close>

lemma head_registration_matched:
  assumes reg: "head_registration Vc S a"
  shows "head_registration Vc T (f a)"
proof -
  obtain ci where vf: "view_formed Vc"
      and vS: "resolution_view_pattern Vc (finite_schema_conclusion S) = Some (ci,Finite_Variable a)"
      and na: "a |\<notin>| finite_pattern_variables ci"
    using reg unfolding head_registration_def by blast
  have vT: "resolution_view_pattern Vc (finite_schema_conclusion T) =
      Some (map_finite_term_pattern f ci,Finite_Variable (f a))"
    using resolution_view_pattern_map[OF vS, of f] by (simp add: conclusion)
  have ci: "fset (finite_pattern_variables ci) \<subseteq> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(1)[OF vf vS] head_scope by blast
  have aS: "a \<in> schema_variables (decode_finite_schema S)"
    using resolution_view_parts_variables(2)[OF vf vS] head_scope by auto
  have mv: "fset (finite_pattern_variables (map_finite_term_pattern f ci)) = f ` fset (finite_pattern_variables ci)"
    by (simp add: decoded_pattern_variables[symmetric] decode_finite_pattern_map rename_pattern_variables)
  have "f a |\<notin>| finite_pattern_variables (map_finite_term_pattern f ci)"
  proof
    assume "f a |\<in>| finite_pattern_variables (map_finite_term_pattern f ci)"
    then have "f a \<in> f ` fset (finite_pattern_variables ci)" using mv by simp
    then obtain y where y: "y \<in> fset (finite_pattern_variables ci)" "f y = f a" by auto
    have "y = a" by (rule inj_onD[OF binders y(2)]) (use y(1) ci aS in auto)
    then show False using y(1) na by simp
  qed
  then show ?thesis unfolding head_registration_def using vf vT by blast
qed

end

section \<open>The carried production\<close>

text \<open>
  A registration's families read the registered clause's variables in their queries' equations; carried to a matched
  clause they read the images, every other field kept.
\<close>

definition map_collection_query :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'d,'v) collection_query \<Rightarrow> ('b,'d,'v) collection_query" where
  "map_collection_query f q = \<lparr>query_equations = map (\<lambda>(a,p). (f a,p)) (query_equations q),
    query_site = query_site q, query_goal = query_goal q, query_element = query_element q\<rparr>"

definition map_collection_family :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'d,'v) collection_family \<Rightarrow> ('b,'d,'v) collection_family" where
  "map_collection_family f F = \<lparr>family_base = map (map_collection_query f) (family_base F),
    family_step = map_option (\<lambda>(q,p). (map_collection_query f q,p)) (family_step F),
    family_key = family_key F, family_identity = family_identity F\<rparr>"

fun map_registration_families ::
    "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'d,'v) registration_families \<Rightarrow> ('b,'d,'v) registration_families" where
  "map_registration_families f (Single_Family F) = Single_Family (map_collection_family f F)"
| "map_registration_families f (Paired_Families F G) =
    Paired_Families (map_collection_family f F) (map_collection_family f G)"

definition registration_varied ::
    "('a \<Rightarrow> 'b) \<Rightarrow> ('b,'t,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow>
      ('b,'t,'d,'v) collection_registration" where
  "registration_varied f T R = \<lparr>registration_site = registration_site R, registration_schema = T,
    registration_variable = f (registration_variable R),
    registration_families = map_registration_families f (registration_families R)\<rparr>"

lemma registration_varied_fields [simp]:
  "registration_site (registration_varied f T R) = registration_site R"
  "registration_schema (registration_varied f T R) = T"
  "registration_variable (registration_varied f T R) = f (registration_variable R)"
  "registration_families (registration_varied f T R) = map_registration_families f (registration_families R)"
  by (simp_all add: registration_varied_def)

text \<open>
  A registration at a clause of P at its site is carried, as V1 carries a construction's registrations, to every
  clause of N at that site the match reaches.
\<close>

definition registration_clause_varied ::
    "('a,'s::linorder,'d,'v) collection_registration \<Rightarrow> ('d \<times> 'e) \<times> ('b,'t::linorder,'d) finite_factor_schema \<Rightarrow>
      ('b,'t,'d,'v) collection_registration fset" where
  "registration_clause_varied R z = (case z of ((d,c'),T) \<Rightarrow> if d = registration_site R then
    (case finite_schema_match (registration_schema R) T of None \<Rightarrow> {||}
      | Some (f,h) \<Rightarrow> {|registration_varied f T R|}) else {||})"

lemma registration_clause_varied_member:
  "R' |\<in>| registration_clause_varied R ((d,c'),T) \<longleftrightarrow> d = registration_site R \<and>
    (\<exists>f h. finite_schema_match (registration_schema R) T = Some (f,h) \<and> R' = registration_varied f T R)"
  by (auto simp: registration_clause_varied_def split: option.splits)

definition registrations_varied ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'v) collection_registration \<Rightarrow> ('b,'t,'d,'v) collection_registration fset" where
  "registrations_varied P N R = (if \<exists>c. ((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses P
    then ffUnion (fimage (registration_clause_varied R) (finite_system_clauses N)) else {||})"

lemma registrations_varied_member:
  "R' |\<in>| registrations_varied P N R \<longleftrightarrow>
    (\<exists>c. ((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses P) \<and>
    (\<exists>c' T f h. ((registration_site R,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match (registration_schema R) T = Some (f,h) \<and> R' = registration_varied f T R)"
proof (cases "\<exists>c. ((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses P")
  case False
  then show ?thesis by (simp add: registrations_varied_def)
next
  case True
  have "R' |\<in>| registrations_varied P N R \<longleftrightarrow>
      (\<exists>z. z |\<in>| finite_system_clauses N \<and> R' |\<in>| registration_clause_varied R z)"
    unfolding registrations_varied_def if_P[OF True] finite_union_image_member by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>c' T f h. ((registration_site R,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match (registration_schema R) T = Some (f,h) \<and> R' = registration_varied f T R)"
  proof
    assume "\<exists>z. z |\<in>| finite_system_clauses N \<and> R' |\<in>| registration_clause_varied R z"
    then obtain z where z: "z |\<in>| finite_system_clauses N" "R' |\<in>| registration_clause_varied R z" by blast
    obtain d c' T where zs: "z = ((d,c'),T)" by (metis prod.collapse)
    show "\<exists>c' T f h. ((registration_site R,c'),T) |\<in>| finite_system_clauses N \<and>
        finite_schema_match (registration_schema R) T = Some (f,h) \<and> R' = registration_varied f T R"
      using z unfolding zs registration_clause_varied_member by blast
  next
    assume "\<exists>c' T f h. ((registration_site R,c'),T) |\<in>| finite_system_clauses N \<and>
        finite_schema_match (registration_schema R) T = Some (f,h) \<and> R' = registration_varied f T R"
    then obtain c' T f h where m: "((registration_site R,c'),T) |\<in>| finite_system_clauses N"
        "finite_schema_match (registration_schema R) T = Some (f,h)" "R' = registration_varied f T R" by blast
    have "R' |\<in>| registration_clause_varied R ((registration_site R,c'),T)"
      unfolding registration_clause_varied_member using m(2,3) by blast
    then show "\<exists>z. z |\<in>| finite_system_clauses N \<and> R' |\<in>| registration_clause_varied R z" using m(1) by blast
  qed
  finally show ?thesis using True by simp
qed

section \<open>The narrowed record varied\<close>

text \<open>
  The sources of a carried key (e, T, t): the clauses S of P at e with a socket s declared there that the match sends
  to T at t.
\<close>

definition varied_socket_source ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      'd \<Rightarrow> ('b,'t,'d) finite_factor_schema \<Rightarrow> 't \<Rightarrow>
      'd \<times> ('a,'s,'d) finite_factor_schema \<times> 's \<times> bool \<times> nat resolution_view \<times> nat resolution_view \<Rightarrow>
      (('a,'s,'d) finite_factor_schema \<times> 's) fset" where
  "varied_socket_source P N e T t z = (case z of (e',S,s,keep,Vp,Vh) \<Rightarrow>
    if e' = e \<and> (\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
      (\<exists>c'. ((e,c'),T) |\<in>| finite_system_clauses N) then
      (case finite_schema_match S T of None \<Rightarrow> {||} | Some (f,h) \<Rightarrow> if h s = t then {|(S,s)|} else {||})
    else {||})"

lemma varied_socket_source_member:
  "y |\<in>| varied_socket_source P N e T t (e',S,s,keep,Vp,Vh) \<longleftrightarrow> e' = e \<and>
    (\<exists>c. ((e,c),S) |\<in>| finite_system_clauses P) \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
    (\<exists>c'. ((e,c'),T) |\<in>| finite_system_clauses N) \<and>
    (\<exists>f h. finite_schema_match S T = Some (f,h) \<and> h s = t) \<and> y = (S,s)"
  by (auto simp: varied_socket_source_def split: option.splits)

definition varied_socket_sources ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('d \<times> ('a,'s,'d) finite_factor_schema \<times> 's \<times> bool \<times> nat resolution_view \<times> nat resolution_view) fset \<Rightarrow>
      'd \<Rightarrow> ('b,'t,'d) finite_factor_schema \<Rightarrow> 't \<Rightarrow> (('a,'s,'d) finite_factor_schema \<times> 's) fset" where
  "varied_socket_sources P N Z e T t = ffUnion (fimage (varied_socket_source P N e T t) Z)"

lemma varied_socket_sources_member:
  "(S,s) |\<in>| varied_socket_sources P N Z e T t \<longleftrightarrow> (\<exists>keep Vp Vh c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| Z \<and>
    ((e,c),S) |\<in>| finite_system_clauses P \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
    ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and> t = h s)"
proof
  assume "(S,s) |\<in>| varied_socket_sources P N Z e T t"
  then obtain z where z: "z |\<in>| Z" "(S,s) |\<in>| varied_socket_source P N e T t z"
    unfolding varied_socket_sources_def finite_union_image_member by blast
  obtain e' S0 s0 keep Vp Vh where zs: "z = (e',S0,s0,keep,Vp,Vh)" by (metis prod_cases6)
  show "\<exists>keep Vp Vh c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| Z \<and>
      ((e,c),S) |\<in>| finite_system_clauses P \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
      ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and> t = h s"
    using z unfolding zs varied_socket_source_member prod.inject by fastforce
next
  assume "\<exists>keep Vp Vh c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| Z \<and>
      ((e,c),S) |\<in>| finite_system_clauses P \<and> s \<in> schema_sockets (decode_finite_schema S) \<and>
      ((e,c'),T) |\<in>| finite_system_clauses N \<and> finite_schema_match S T = Some (f,h) \<and> t = h s"
  then obtain keep Vp Vh c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| Z" "((e,c),S) |\<in>| finite_system_clauses P"
      "s \<in> schema_sockets (decode_finite_schema S)" "((e,c'),T) |\<in>| finite_system_clauses N"
      "finite_schema_match S T = Some (f,h)" "t = h s" by blast
  have "(S,s) |\<in>| varied_socket_source P N e T t (e,S,s,keep,Vp,Vh)"
    unfolding varied_socket_source_member using m(2-6) by blast
  then show "(S,s) |\<in>| varied_socket_sources P N Z e T t"
    unfolding varied_socket_sources_def finite_union_image_member using m(1) by blast
qed

text \<open>
  The class at a carried key holds where every source's class holds: at a key whose sources agree it is their class
  (@{text narrowing_varied_source}). Where they disagree, the conjunction need not be dischargeable, since each
  source's narrowing holds at its own premise view alone: the discharge asks that the sources agree
  (@{text varied_narrowings_agree}), which holds at records declaring no narrowing and at programs where no two
  clauses of P at a site match one clause of N (@{text varied_narrowings_agree_unique}).
\<close>

definition narrowing_varied where
  "narrowing_varied P N ND e T t y \<longleftrightarrow>
    fBall (varied_socket_sources P N (declared_sockets ND) e T t) (\<lambda>(S,s). declared_narrowing ND e S s y)"

definition varied_narrowings_agree where
  "varied_narrowings_agree P N ND \<longleftrightarrow> (\<forall>e T t S s S' s'.
    (S,s) |\<in>| varied_socket_sources P N (declared_sockets ND) e T t \<longrightarrow>
    (S',s') |\<in>| varied_socket_sources P N (declared_sockets ND) e T t \<longrightarrow>
    declared_narrowing ND e S s = declared_narrowing ND e S' s')"

lemma narrowing_varied_source:
  assumes agree: "varied_narrowings_agree P N ND"
    and src: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
  shows "narrowing_varied P N ND e T t = declared_narrowing ND e S s"
proof (rule ext)
  fix y
  have eqs: "declared_narrowing ND e S' s' = declared_narrowing ND e S s"
    if "(S',s') |\<in>| varied_socket_sources P N (declared_sockets ND) e T t" for S' s'
    using agree that src unfolding varied_narrowings_agree_def by blast
  show "narrowing_varied P N ND e T t y = declared_narrowing ND e S s y"
  proof
    assume a: "narrowing_varied P N ND e T t y"
    have "(\<lambda>(S,s). declared_narrowing ND e S s y) (S,s)" by (rule fbspec[OF a[unfolded narrowing_varied_def] src])
    then show "declared_narrowing ND e S s y" by simp
  next
    assume n: "declared_narrowing ND e S s y"
    show "narrowing_varied P N ND e T t y" unfolding narrowing_varied_def
    proof (rule fBallI)
      fix z assume z: "z |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
      obtain S' s' where zs: "z = (S',s')" by (cases z)
      show "case z of (S,s) \<Rightarrow> declared_narrowing ND e S s y" using eqs[of S' s'] z n unfolding zs by simp
    qed
  qed
qed

lemma narrowing_varied_top:
  assumes top: "\<And>e S s. declared_narrowing ND e S s = (\<lambda>_. True)"
  shows "narrowing_varied P N ND = (\<lambda>_ _ _ _. True)"
  by (auto simp: narrowing_varied_def top fun_eq_iff intro!: fBallI)

definition finite_varied_sources_unique ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow> bool" where
  "finite_varied_sources_unique P N \<longleftrightarrow> (\<forall>e c S c' S' c'' T f h f' h'. ((e,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
    ((e,c'),S') |\<in>| finite_system_clauses P \<longrightarrow> ((e,c''),T) |\<in>| finite_system_clauses N \<longrightarrow>
    finite_schema_match S T = Some (f,h) \<longrightarrow> finite_schema_match S' T = Some (f',h') \<longrightarrow> S = S')"

lemma varied_narrowings_agree_unique:
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and unique: "finite_varied_sources_unique P N"
  shows "varied_narrowings_agree P N ND"
  unfolding varied_narrowings_agree_def
proof (intro allI impI)
  fix e T t S s S' s'
  assume a: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
    and b: "(S',s') |\<in>| varied_socket_sources P N (declared_sockets ND) e T t"
  obtain c c' f h where ma: "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
    using a unfolding varied_socket_sources_member by blast
  obtain c1 c1' f' h' where mb: "((e,c1),S') |\<in>| finite_system_clauses P" "s' \<in> schema_sockets (decode_finite_schema S')"
      "((e,c1'),T) |\<in>| finite_system_clauses N" "finite_schema_match S' T = Some (f',h')" "t = h' s'"
    using b unfolding varied_socket_sources_member by blast
  have SS: "S' = S" using unique ma(1,3,4) mb(1,4) unfolding finite_varied_sources_unique_def by blast
  interpret matched: finite_schema_matched S T f h
    by (rule finite_schema_matched.intro[OF finite_system_clause_formed[OF Pf ma(1)]
      finite_system_clause_formed[OF Nf ma(3)] ma(4)])
  have hh: "h' = h" using mb(4) ma(4) SS by simp
  have "s' = s" by (rule inj_onD[OF matched.sockets]) (use ma mb SS hh in auto)
  then show "declared_narrowing ND e S s = declared_narrowing ND e S' s'" using SS by simp
qed

lemma varied_narrowings_agree_top:
  assumes top: "\<And>e S s. declared_narrowing ND e S s = (\<lambda>_. True)"
  shows "varied_narrowings_agree P N ND"
  by (simp add: varied_narrowings_agree_def top)

text \<open>
  The production at a carried key: each source's registration carried to its matched clause, a production only where
  every source's carries to exactly one registration and all to the same one, as V1's values do.
\<close>

definition production_carried ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'v) collection_registration option \<Rightarrow> ('b,'t,'d,'v) collection_registration option" where
  "production_carried P N \<rho> = (case \<rho> of None \<Rightarrow> None | Some R \<Rightarrow>
    (let Rs = registrations_varied P N R in if Rs = {|fthe_elem Rs|} then Some (fthe_elem Rs) else None))"

text \<open>A value where one is determined: the singleton's element, and none otherwise.\<close>

lemma singleton_some_iff:
  "(if X = {|fthe_elem X|} then Some (fthe_elem X) else None) = Some y \<longleftrightarrow> X = {|y|}"
proof
  assume a: "(if X = {|fthe_elem X|} then Some (fthe_elem X) else None) = Some y"
  have single: "X = {|fthe_elem X|}"
  proof (rule ccontr)
    assume "X \<noteq> {|fthe_elem X|}"
    then show False using a by simp
  qed
  have "fthe_elem X = y" using a[unfolded if_P[OF single]] by simp
  then show "X = {|y|}" using single by metis
next
  assume "X = {|y|}"
  then show "(if X = {|fthe_elem X|} then Some (fthe_elem X) else None) = Some y" by (simp add: fthe_felem_eq)
qed

lemma singleton_option_iff:
  "(if X = {|fthe_elem X|} then fthe_elem X else None) = Some y \<longleftrightarrow> X = {|Some y|}"
proof
  assume a: "(if X = {|fthe_elem X|} then fthe_elem X else None) = Some y"
  have single: "X = {|fthe_elem X|}"
  proof (rule ccontr)
    assume "X \<noteq> {|fthe_elem X|}"
    then show False using a by simp
  qed
  have "fthe_elem X = Some y" using a[unfolded if_P[OF single]] .
  then show "X = {|Some y|}" using single by metis
next
  assume "X = {|Some y|}"
  then show "(if X = {|fthe_elem X|} then fthe_elem X else None) = Some y" by (simp add: fthe_felem_eq)
qed

lemma production_carried_some:
  "production_carried P N \<rho> = Some R' \<longleftrightarrow> (\<exists>R. \<rho> = Some R \<and> registrations_varied P N R = {|R'|})"
  by (cases \<rho>) (simp_all add: production_carried_def Let_def singleton_some_iff)

definition production_varied where
  "production_varied P N PD e T t = (let Os = fimage (\<lambda>(S,s). production_carried P N (declared_production PD e S s))
      (varied_socket_sources P N (declared_sockets PD) e T t) in if Os = {|fthe_elem Os|} then fthe_elem Os else None)"

lemma production_varied_source:
  assumes prod: "production_varied P N PD e T t = Some R'"
    and src: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
  shows "\<exists>R. declared_production PD e S s = Some R \<and> registrations_varied P N R = {|R'|}"
proof -
  let ?Os = "fimage (\<lambda>(S,s). production_carried P N (declared_production PD e S s))
    (varied_socket_sources P N (declared_sockets PD) e T t)"
  have single: "?Os = {|Some R'|}"
    using prod by (simp add: production_varied_def Let_def singleton_option_iff)
  have "(\<lambda>(S,s). production_carried P N (declared_production PD e S s)) (S,s) |\<in>| ?Os" by (rule fimageI[OF src])
  then have "production_carried P N (declared_production PD e S s) |\<in>| ?Os" by simp
  then have "production_carried P N (declared_production PD e S s) = Some R'" using single by simp
  then show ?thesis by (simp add: production_carried_some)
qed

text \<open>
  The varied narrowed record: V2a's truncation, as it stands, with the carried class; the varied record with
  productions adds the carried production. The binder and socket types change with the programs'.
\<close>

definition narrowed_declarations_varied where
  "narrowed_declarations_varied P N ND =
    narrowed (declarations_varied P N (resolution_declarations.truncate ND)) (narrowing_varied P N ND)"

definition produced_declarations_varied where
  "produced_declarations_varied P N PD = produced (narrowed_declarations_varied P N PD) (production_varied P N PD)"

lemma narrowed_truncate_fields [simp]:
  "declared_producers (narrowed_declarations.truncate X) = declared_producers X"
  "declared_consumers (narrowed_declarations.truncate X) = declared_consumers X"
  "declared_sockets (narrowed_declarations.truncate X) = declared_sockets X"
  "declared_narrowing (narrowed_declarations.truncate X) = declared_narrowing X"
  "resolution_declarations.truncate (narrowed_declarations.truncate X) = resolution_declarations.truncate X"
  by (simp_all add: narrowed_declarations.truncate_def resolution_declarations.truncate_def)

lemma narrowed_declarations_varied_truncate:
  "resolution_declarations.truncate (narrowed_declarations_varied P N ND) =
    declarations_varied P N (resolution_declarations.truncate ND)"
  by (simp add: narrowed_declarations_varied_def)

lemma produced_declarations_varied_truncate:
  "narrowed_declarations.truncate (produced_declarations_varied P N PD) = narrowed_declarations_varied P N PD"
  by (simp add: produced_declarations_varied_def)

lemma produced_declarations_varied_fields:
  "declared_producers (produced_declarations_varied P N PD) = declared_producers PD"
  "declared_consumers (produced_declarations_varied P N PD) = declared_consumers PD"
  "declared_sockets (produced_declarations_varied P N PD) =
    declared_sockets (declarations_varied P N (resolution_declarations.truncate PD))"
  "declared_narrowing (produced_declarations_varied P N PD) = narrowing_varied P N PD"
  "declared_production (produced_declarations_varied P N PD) = production_varied P N PD"
  by (simp_all add: produced_declarations_varied_def narrowed_declarations_varied_def)

section \<open>Completeness at a narrowed socket, carried with the production\<close>

text \<open>
  The completeness a production gives at a narrowed socket (@{thm [source] registration_complete_at_socket}), read at
  the production's own site, clause and variable: every true instance of the caller clause whose input the head
  reads extends to one through the construction's value there, which is formed and in the class.
\<close>

definition production_complete_at ::
    "('d \<times> factor_term) set \<Rightarrow> ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d) finite_factor_schema \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> nat resolution_view \<Rightarrow> nat resolution_view \<Rightarrow>
      (factor_term \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'v) collection_registration \<Rightarrow> bool" where
  "production_complete_at M \<kappa> P C s keep Vp Vh K R \<longleftrightarrow> (\<forall>d p xi yo h B v. (s,d,p) |\<in>| finite_schema_premises C \<longrightarrow>
    resolution_view_pattern Vp p = Some (xi,yo) \<longrightarrow> clause_true M (decode_finite_schema C) h \<longrightarrow>
    head_registration_input Vp (registration_schema R) B = Some (evaluate_pattern h (decode_finite_pattern xi)) \<longrightarrow>
    witness_value \<kappa> P (registration_site R) (registration_schema R) B (registration_variable R) = Some v \<longrightarrow>
    finite_term_formed v \<and> K (decode_finite_term v) \<and>
    (\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v))"

lemma production_complete_at_socket:
  assumes narrowed: "narrowed_socket_discharged M C s keep Vp Vh K" and vp: "view_formed Vp"
    and site: "\<And>d p. (s,d,p) |\<in>| finite_schema_premises C \<Longrightarrow> registration_site R = d"
    and produces: "head_registration_produces \<kappa> P (registration_site R) (registration_schema R) (registration_variable R) K"
    and answers: "head_registration_answers M \<kappa> P (registration_site R) (registration_schema R) Vp (registration_variable R)"
  shows "production_complete_at M \<kappa> P C s keep Vp Vh K R"
  unfolding production_complete_at_def
proof (intro allI impI)
  fix d p xi yo g B v
  assume premise: "(s,d,p) |\<in>| finite_schema_premises C" and viewed: "resolution_view_pattern Vp p = Some (xi,yo)"
    and true: "clause_true M (decode_finite_schema C) g"
    and input: "head_registration_input Vp (registration_schema R) B = Some (evaluate_pattern g (decode_finite_pattern xi))"
    and valued: "witness_value \<kappa> P (registration_site R) (registration_schema R) B (registration_variable R) = Some v"
  have d: "registration_site R = d" by (rule site[OF premise])
  note completed = registration_complete_at_socket[OF narrowed vp premise viewed produces[unfolded d]
    answers[unfolded d] true input valued[unfolded d]]
  show "finite_term_formed v \<and> K (decode_finite_term v) \<and>
      (\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C g h' \<and>
        evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern g (decode_finite_pattern xi) \<and>
        evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v)"
    using completed by blast
qed

text \<open>
  The target's values at a carried production are the source's: at every clause of the target at the production's
  site the match reaches, a value at the image of the head variable is the source's value at the bindings carried
  back over the source clause's scope, as V1's values are.
\<close>

definition production_values_carried ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow>
      ('b,'t,'d,'e) finite_witness_construction \<Rightarrow> ('b,'t::linorder,'d,'e) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'v) collection_registration \<Rightarrow> bool" where
  "production_values_carried \<kappa> P \<kappa>' Q R \<longleftrightarrow> (\<forall>c' T f h B v. ((registration_site R,c'),T) |\<in>| finite_system_clauses Q \<longrightarrow>
    finite_schema_match (registration_schema R) T = Some (f,h) \<longrightarrow>
    witness_value \<kappa>' Q (registration_site R) T B (f (registration_variable R)) = Some v \<longrightarrow>
    witness_value \<kappa> P (registration_site R) (registration_schema R)
      (finite_bindings_carried_back f (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v)"

lemma head_registration_produces_varied:
  assumes produces: "head_registration_produces \<kappa> P d S a K"
    and carried_values: "\<And>B v. witness_value \<kappa>' Q d T B b = Some v \<Longrightarrow> witness_value \<kappa> P d S (G B) a = Some v"
  shows "head_registration_produces \<kappa>' Q d T b K"
  using produces carried_values unfolding head_registration_produces_def by blast

lemma head_registration_answers_varied:
  assumes producer: "finite_schema_matched (registration_schema R) TR fR hR" and Vcf: "view_formed Vc"
    and answers: "head_registration_answers M \<kappa> P d (registration_schema R) Vc (registration_variable R)"
    and eqd: "\<And>x. (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and carried_values: "\<And>B v. witness_value \<kappa>' Q d TR B (fR (registration_variable R)) = Some v \<Longrightarrow>
      witness_value \<kappa> P d (registration_schema R)
        (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
  shows "head_registration_answers M' \<kappa>' Q d TR Vc (fR (registration_variable R))"
  unfolding head_registration_answers_def
proof (intro allI impI)
  fix B v x t y
  assume val: "witness_value \<kappa>' Q d TR B (fR (registration_variable R)) = Some v"
    and inp: "head_registration_input Vc TR B = Some x" and dt: "(d,t) \<in> M'"
    and vt: "resolution_view_term Vc t = Some (x,y)"
  have inp0: "head_registration_input Vc (registration_schema R)
      (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) = Some x"
    using inp by (simp add: finite_schema_matched.head_registration_input_matched[OF producer Vcf])
  have dt0: "(d,t) \<in> M" using dt eqd by blast
  obtain t' where "(d,t') \<in> M" "resolution_view_term Vc t' = Some (x,decode_finite_term v)"
    using answers[unfolded head_registration_answers_def, rule_format, OF carried_values[OF val] inp0 dt0 vt] by blast
  then show "\<exists>t'. (d,t') \<in> M' \<and> resolution_view_term Vc t' = Some (x,decode_finite_term v)" using eqd by blast
qed

text \<open>
  The completeness at a narrowed socket carries to the carried socket and the carried production: an instance of the
  target caller read back through its binder map is one of the source, the head's input read at the matched producer
  clause is the source's at the bindings carried back, the source's value gives the source's new instance, and that
  instance is carried forward through the inverse on the source's scope.
\<close>

theorem production_complete_matched:
  assumes caller: "finite_schema_matched S T f h"
    and producer: "finite_schema_matched (registration_schema R) TR fR hR"
    and src: "production_complete_at M \<kappa> P S s keep Vp Vh K R"
    and views: "\<And>d p. (s,d,p) |\<in>| finite_schema_premises S \<Longrightarrow> resolution_view_pattern Vp p \<noteq> None"
    and sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and Vpf: "view_formed Vp" and Vhf: "view_formed Vh"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and carried_values: "\<And>B v. witness_value \<kappa>' Q (registration_site R) TR B (fR (registration_variable R)) = Some v \<Longrightarrow>
      witness_value \<kappa> P (registration_site R) (registration_schema R)
        (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
  shows "production_complete_at M' \<kappa>' Q T (h s) keep Vp Vh K (registration_varied fR TR R)"
proof -
  interpret C: finite_schema_matched S T f h by (rule caller)
  interpret Pr: finite_schema_matched "registration_schema R" TR fR hR by (rule producer)
  show ?thesis unfolding production_complete_at_def registration_varied_fields
  proof (intro allI impI)
    fix d p xi yo g B v
    assume at: "(h s,d,p) |\<in>| finite_schema_premises T" and vp: "resolution_view_pattern Vp p = Some (xi,yo)"
      and vT: "clause_true M' (decode_finite_schema T) g"
      and input: "head_registration_input Vp TR B = Some (evaluate_pattern g (decode_finite_pattern xi))"
      and valued: "witness_value \<kappa>' Q (registration_site R) TR B (fR (registration_variable R)) = Some v"
    obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
      using C.premise_at_image[OF sock at] .
    obtain xi0 yo0 where v0: "resolution_view_pattern Vp p0 = Some (xi0,yo0)" using views[OF p0(1)] by auto
    have xy: "xi = map_finite_term_pattern f xi0" "yo = map_finite_term_pattern f yo0"
      using resolution_view_pattern_map[OF v0, of f] vp p0(2) by simp_all
    have vS: "clause_true M (decode_finite_schema S) (g \<circ> f)" using vT C.clause_true_along[OF eq] by blast
    have input0: "head_registration_input Vp (registration_schema R)
        (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) =
      Some (evaluate_pattern (g \<circ> f) (decode_finite_pattern xi0))"
      using input by (simp add: Pr.head_registration_input_matched[OF Vpf] xy evaluate_map_finite_pattern)
    have srcv: "finite_term_formed v \<and> K (decode_finite_term v) \<and>
        (\<exists>h'. clause_true M (decode_finite_schema S) h' \<and> head_kept keep Vh S (g \<circ> f) h' \<and>
          evaluate_pattern h' (decode_finite_pattern xi0) = evaluate_pattern (g \<circ> f) (decode_finite_pattern xi0) \<and>
          evaluate_pattern h' (decode_finite_pattern yo0) = decode_finite_term v)"
      by (rule src[unfolded production_complete_at_def, rule_format, OF p0(1) v0 vS input0 carried_values[OF valued]])
    obtain h3 where h3: "clause_true M (decode_finite_schema S) h3" "head_kept keep Vh S (g \<circ> f) h3"
        "evaluate_pattern h3 (decode_finite_pattern xi0) = evaluate_pattern (g \<circ> f) (decode_finite_pattern xi0)"
        "evaluate_pattern h3 (decode_finite_pattern yo0) = decode_finite_term v"
      using srcv by blast
    have pv: "fset (finite_pattern_variables p0) \<subseteq> schema_variables (decode_finite_schema S)" by (rule C.call_scope[OF p0(1)])
    have xv: "fset (finite_pattern_variables xi0) \<subseteq> schema_variables (decode_finite_schema S)"
      using resolution_view_parts_variables(1)[OF Vpf v0] pv by blast
    have yv: "fset (finite_pattern_variables yo0) \<subseteq> schema_variables (decode_finite_schema S)"
      using resolution_view_parts_variables(2)[OF Vpf v0] pv by blast
    show "finite_term_formed v \<and> K (decode_finite_term v) \<and>
        (\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T g h' \<and>
          evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern g (decode_finite_pattern xi) \<and>
          evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v)"
    proof (intro conjI exI)
      show "finite_term_formed v" using srcv by blast
      show "K (decode_finite_term v)" using srcv by blast
      show "clause_true M' (decode_finite_schema T) (h3 \<circ> C.binder_inverse)" by (rule C.clause_true_back[OF eq h3(1)])
      show "head_kept keep Vh T g (h3 \<circ> C.binder_inverse)" by (rule C.head_kept_along[OF h3(2) Vhf])
      show "evaluate_pattern (h3 \<circ> C.binder_inverse) (decode_finite_pattern xi) = evaluate_pattern g (decode_finite_pattern xi)"
        using h3(3) by (simp add: xy evaluate_map_finite_pattern C.evaluate_back[OF xv])
      show "evaluate_pattern (h3 \<circ> C.binder_inverse) (decode_finite_pattern yo) = decode_finite_term v"
        using h3(4) by (simp add: xy evaluate_map_finite_pattern C.evaluate_back[OF yv])
    qed
  qed
qed

text \<open>
  (2): @{thm [source] registration_complete_at_socket} for a production at a narrowed socket of P gives it for the
  carried production at the matched clause of N and the carried socket, the class kept and the values the same: the
  narrowed obligation, the production and the answers are each carried, and the completeness is the theorem itself
  at N.
\<close>

theorem varied_registration_complete_at_socket:
  fixes \<kappa>' :: "('b,'t::linorder,'d,'e) finite_witness_construction"
  assumes caller: "finite_schema_matched S T f h"
    and producer: "finite_schema_matched (registration_schema R) TR fR hR"
    and narrowed: "narrowed_socket_discharged M S s keep Vp Vh K" and sock: "s \<in> schema_sockets (decode_finite_schema S)"
    and Vpf: "view_formed Vp" and Vhf: "view_formed Vh"
    and site: "\<And>d p. (s,d,p) |\<in>| finite_schema_premises S \<Longrightarrow> registration_site R = d"
    and produces: "head_registration_produces \<kappa> P (registration_site R) (registration_schema R) (registration_variable R) K"
    and answers: "head_registration_answers M \<kappa> P (registration_site R) (registration_schema R) Vp (registration_variable R)"
    and eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
    and carried_values: "\<And>B v. witness_value \<kappa>' Q (registration_site R) TR B (fR (registration_variable R)) = Some v \<Longrightarrow>
      witness_value \<kappa> P (registration_site R) (registration_schema R)
        (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
    and premise: "(h s,d,p) |\<in>| finite_schema_premises T" and viewed: "resolution_view_pattern Vp p = Some (xi,yo)"
    and true: "clause_true M' (decode_finite_schema T) g"
    and input: "head_registration_input Vp (registration_schema (registration_varied fR TR R)) B =
      Some (evaluate_pattern g (decode_finite_pattern xi))"
    and valued: "witness_value \<kappa>' Q (registration_site (registration_varied fR TR R))
      (registration_schema (registration_varied fR TR R)) B (registration_variable (registration_varied fR TR R)) = Some v"
  shows "finite_term_formed v" "K (decode_finite_term v)"
    "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T g h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern g (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
proof -
  interpret C: finite_schema_matched S T f h by (rule caller)
  obtain p0 where p0: "(s,d,p0) |\<in>| finite_schema_premises S" "p = map_finite_term_pattern f p0"
    using C.premise_at_image[OF sock premise] .
  have d: "registration_site R = d" by (rule site[OF p0(1)])
  have dep: "d \<in> schema_dependencies (decode_finite_schema S)"
    by (rule schema_dependencies_premise[of s d "decode_finite_pattern p0"]) (use p0(1) in \<open>auto simp: finite_premise_decoded\<close>)
  have eqd: "\<And>x. (registration_site R,x) \<in> M' \<longleftrightarrow> (registration_site R,x) \<in> M" using eq[OF dep] d by simp
  have nT: "narrowed_socket_discharged M' T (h s) keep Vp Vh K"
    by (rule C.narrowed_socket_discharged_matched[OF narrowed sock Vpf Vhf eq])
  have prod': "head_registration_produces \<kappa>' Q d TR (fR (registration_variable R)) K"
    using head_registration_produces_varied[OF produces carried_values] d by simp
  have ans': "head_registration_answers M' \<kappa>' Q d TR Vp (fR (registration_variable R))"
    using head_registration_answers_varied[OF producer Vpf answers eqd carried_values] d by simp
  have input': "head_registration_input Vp TR B = Some (evaluate_pattern g (decode_finite_pattern xi))"
    using input by simp
  have valued': "witness_value \<kappa>' Q d TR B (fR (registration_variable R)) = Some v" using valued d by simp
  note completed = registration_complete_at_socket[OF nT Vpf premise viewed prod' ans' true input' valued']
  show "finite_term_formed v" by (rule completed(1))
  show "K (decode_finite_term v)" by (rule completed(2))
  show "\<exists>h'. clause_true M' (decode_finite_schema T) h' \<and> head_kept keep Vh T g h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern g (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
    by (rule completed(3))
qed

section \<open>The whole record with productions discharged at the varied program\<close>

definition productions_complete where
  "productions_complete M \<kappa> P PD \<longleftrightarrow> (\<forall>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<longrightarrow>
    declared_production PD e S s = Some R \<longrightarrow>
    production_complete_at M \<kappa> P S s keep Vp Vh (declared_narrowing PD e S s) R)"

text \<open>
  (3): a record with narrowed sockets and productions discharged at P's meaning is, varied, discharged at N's wherever
  the two mean the same at the record's sites and the sources' classes agree: producers and consumers by the meaning
  at their sites, each carried socket's narrowed obligation along the match (@{text narrowed_socket_discharged_matched})
  at its source's class, and each carried production's completeness along the two matches
  (@{text production_complete_matched}) wherever N's values at the carried production are P's.
\<close>

theorem declarations_varied_narrowed_discharged:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites (resolution_declarations.truncate PD) \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and complete: "productions_complete (positive_meaning (decode_finite_system P)) \<kappa> P PD"
    and carried_values: "\<And>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> production_values_carried \<kappa> P \<kappa>' N R"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    and "productions_complete (positive_meaning (decode_finite_system N)) \<kappa>' N (produced_declarations_varied P N PD)"
proof -
  let ?M = "positive_meaning (decode_finite_system P)"
  let ?M' = "positive_meaning (decode_finite_system N)"
  let ?D = "resolution_declarations.truncate PD"
  have Df: "declarations_formed ?D" using narrowed_formed[OF discharged] by simp
  have carried: "\<exists>S s c c' f h. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<and> ((e,c),S) |\<in>| finite_system_clauses P \<and>
      s \<in> schema_sockets (decode_finite_schema S) \<and> ((e,c'),T) |\<in>| finite_system_clauses N \<and>
      finite_schema_match S T = Some (f,h) \<and> t = h s \<and>
      (S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t \<and>
      narrowed_socket_discharged ?M S s keep Vp Vh (declared_narrowing PD e S s) \<and>
      view_formed Vp \<and> view_formed Vh \<and> schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
    if mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N ?D)" for e T t keep Vp Vh
  proof -
    obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?D" "((e,c),S) |\<in>| finite_system_clauses P"
        "s \<in> schema_sockets (decode_finite_schema S)" "((e,c'),T) |\<in>| finite_system_clauses N"
        "finite_schema_match S T = Some (f,h)" "t = h s"
      using mem[unfolded declarations_varied_sockets_member] by blast
    have mPD: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" using m(1) by simp
    have mND: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations.truncate PD)" using m(1) by simp
    have src: "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
      unfolding varied_socket_sources_member using mPD m(2-6) by blast
    have nd: "narrowed_socket_discharged ?M S s keep Vp Vh (declared_narrowing PD e S s)"
      using narrowed_socket[OF discharged mND] by simp
    have "fBall (declared_sockets ?D) (\<lambda>(e,S,s,keep,Vp,Vh). view_formed Vp \<and> view_formed Vh)"
      using Df by (simp add: declarations_formed_def)
    from fbspec[OF this m(1)] have views: "view_formed Vp" "view_formed Vh" by simp_all
    have sub: "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
      by (rule declared_sites_members(5)[OF m(1)])
    show ?thesis using mPD m(2-6) src nd views sub by blast
  qed
  have sockets: "narrowed_socket_discharged ?M' T t keep Vp Vh (narrowing_varied P N PD e T t)"
    if mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N ?D)" for e T t keep Vp Vh
  proof -
    obtain S s c c' f h where m: "((e,c),S) |\<in>| finite_system_clauses P" "s \<in> schema_sockets (decode_finite_schema S)"
        "((e,c'),T) |\<in>| finite_system_clauses N" "finite_schema_match S T = Some (f,h)" "t = h s"
        "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
        "narrowed_socket_discharged ?M S s keep Vp Vh (declared_narrowing PD e S s)"
        "view_formed Vp" "view_formed Vh" "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
      using carried[OF mem] by blast
    interpret matched: finite_schema_matched S T f h
      by (rule finite_schema_matched.intro[OF finite_system_clause_formed[OF Pf m(1)]
        finite_system_clause_formed[OF Nf m(3)] m(4)])
    have "narrowed_socket_discharged ?M' T (h s) keep Vp Vh (declared_narrowing PD e S s)"
      by (rule matched.narrowed_socket_discharged_matched[OF m(7) m(2) m(8) m(9)]) (use at m(10) in blast)
    then show ?thesis using narrowing_varied_source[OF agree m(6)] m(5) by simp
  qed
  show "narrowed_declarations_discharged ?M' (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    unfolding produced_declarations_varied_truncate narrowed_declarations_discharged_def
  proof (intro conjI allI impI)
    show "declarations_formed (resolution_declarations.truncate (narrowed_declarations_varied P N PD))"
      unfolding narrowed_declarations_varied_truncate by (rule declarations_formed_varied[OF Df])
  next
    fix d W hs assume "(d,W,hs) |\<in>| declared_producers (narrowed_declarations_varied P N PD)"
    then have d: "(d,W,hs) |\<in>| declared_producers ?D" by (simp add: narrowed_declarations_varied_def)
    have "producer_discharged ?M d W hs (corr d)" using narrowed_producer[OF discharged] d by simp
    then show "producer_discharged ?M' d W hs (corr d)"
      unfolding producer_discharged_def at[OF declared_sites_members(1)[OF d]] .
  next
    fix d e W i assume "(d,e,W,i) |\<in>| declared_consumers (narrowed_declarations_varied P N PD)"
    then have de: "(d,e,W,i) |\<in>| declared_consumers ?D" by (simp add: narrowed_declarations_varied_def)
    have "consumer_discharged ?M e W (corr d i)" using narrowed_consumer[OF discharged] de by simp
    then show "consumer_discharged ?M' e W (corr d i)"
      unfolding consumer_discharged_def at[OF declared_sites_members(3)[OF de]] .
  next
    fix e T t keep Vp Vh assume "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (narrowed_declarations_varied P N PD)"
    then show "narrowed_socket_discharged ?M' T t keep Vp Vh (declared_narrowing (narrowed_declarations_varied P N PD) e T t)"
      using sockets by (simp add: narrowed_declarations_varied_def)
  qed
  show "productions_complete ?M' \<kappa>' N (produced_declarations_varied P N PD)"
    unfolding productions_complete_def
  proof (intro allI impI)
    fix e T t keep Vp Vh R'
    assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied P N PD)"
      and prod: "declared_production (produced_declarations_varied P N PD) e T t = Some R'"
    have mem': "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (declarations_varied P N ?D)"
      using mem by (simp add: produced_declarations_varied_fields)
    have prod': "production_varied P N PD e T t = Some R'" using prod by (simp add: produced_declarations_varied_fields)
    obtain S s c c' f h where m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "((e,c),S) |\<in>| finite_system_clauses P"
        "s \<in> schema_sockets (decode_finite_schema S)" "((e,c'),T) |\<in>| finite_system_clauses N"
        "finite_schema_match S T = Some (f,h)" "t = h s"
        "(S,s) |\<in>| varied_socket_sources P N (declared_sockets PD) e T t"
        "narrowed_socket_discharged ?M S s keep Vp Vh (declared_narrowing PD e S s)"
        "view_formed Vp" "view_formed Vh" "schema_dependencies (decode_finite_schema S) \<subseteq> declared_sites ?D"
      using carried[OF mem'] by blast
    obtain R where R: "declared_production PD e S s = Some R" "registrations_varied P N R = {|R'|}"
      using production_varied_source[OF prod' m(7)] by blast
    have "R' |\<in>| registrations_varied P N R" using R(2) by simp
    then obtain c0 c1 TR fR hR where r: "((registration_site R,c0),registration_schema R) |\<in>| finite_system_clauses P"
        "((registration_site R,c1),TR) |\<in>| finite_system_clauses N"
        "finite_schema_match (registration_schema R) TR = Some (fR,hR)" "R' = registration_varied fR TR R"
      unfolding registrations_varied_member by blast
    have caller: "finite_schema_matched S T f h"
      by (rule finite_schema_matched.intro[OF finite_system_clause_formed[OF Pf m(2)]
        finite_system_clause_formed[OF Nf m(4)] m(5)])
    have producer: "finite_schema_matched (registration_schema R) TR fR hR"
      by (rule finite_schema_matched.intro[OF finite_system_clause_formed[OF Pf r(1)]
        finite_system_clause_formed[OF Nf r(2)] r(3)])
    have pc: "production_complete_at ?M \<kappa> P S s keep Vp Vh (declared_narrowing PD e S s) R"
      using complete m(1) R(1) unfolding productions_complete_def by blast
    have views: "\<And>d p. (s,d,p) |\<in>| finite_schema_premises S \<Longrightarrow> resolution_view_pattern Vp p \<noteq> None"
      using m(8) unfolding narrowed_socket_discharged_def by blast
    have eq: "\<And>d x. d \<in> schema_dependencies (decode_finite_schema S) \<Longrightarrow> (d,x) \<in> ?M' \<longleftrightarrow> (d,x) \<in> ?M"
      using at m(11) by blast
    have vals: "\<And>B v. witness_value \<kappa>' N (registration_site R) TR B (fR (registration_variable R)) = Some v \<Longrightarrow>
        witness_value \<kappa> P (registration_site R) (registration_schema R)
          (finite_bindings_carried_back fR (finite_schema_variables (registration_schema R)) B) (registration_variable R) = Some v"
      using carried_values[OF m(1) R(1)] r(2,3) unfolding production_values_carried_def by blast
    have "production_complete_at ?M' \<kappa>' N T (h s) keep Vp Vh (declared_narrowing PD e S s) (registration_varied fR TR R)"
      by (rule production_complete_matched[OF caller producer pc views m(3) m(9) m(10) eq vals])
    then show "production_complete_at ?M' \<kappa>' N T t keep Vp Vh
        (declared_narrowing (produced_declarations_varied P N PD) e T t) R'"
      using narrowing_varied_source[OF agree m(7)] m(6) r(4) by (simp add: produced_declarations_varied_fields)
  qed
qed

text \<open>At alpha variants the two programs mean the same everywhere, and both are formed.\<close>

corollary declarations_varied_narrowed_discharged_variant:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
    and PD :: "('a,'s,'d,'v) produced_declarations"
  assumes alpha: "system_alpha_variant (decode_finite_system P) (decode_finite_system N)"
    and agree: "varied_narrowings_agree P N PD"
    and discharged: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    and complete: "productions_complete (positive_meaning (decode_finite_system P)) \<kappa> P PD"
    and carried_values: "\<And>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD \<Longrightarrow>
      declared_production PD e S s = Some R \<Longrightarrow> production_values_carried \<kappa> P \<kappa>' N R"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    and "productions_complete (positive_meaning (decode_finite_system N)) \<kappa>' N (produced_declarations_varied P N PD)"
proof -
  have Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    using alpha by (simp_all add: system_alpha_variant_def finite_system_formed_correct)
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    by (rule declarations_varied_narrowed_discharged(1)[OF Pf Nf _ agree discharged complete carried_values])
      (simp add: system_alpha_positive_meaning[OF alpha])
  show "productions_complete (positive_meaning (decode_finite_system N)) \<kappa>' N (produced_declarations_varied P N PD)"
    by (rule declarations_varied_narrowed_discharged(2)[OF Pf Nf _ agree discharged complete carried_values])
      (simp add: system_alpha_positive_meaning[OF alpha])
qed

text \<open>
  V2a's discharge is the instance at a record declaring no narrowing and no production: its sources' classes agree
  (every term), the production part is empty, and the narrowed discharge at every term is R5's.
\<close>

corollary declarations_varied_discharged_unnarrowed:
  fixes P :: "('a,'s::linorder,'d,'c) finite_schema_system" and N :: "('b,'t::linorder,'d,'e) finite_schema_system"
  assumes Pf: "finite_system_formed P" and Nf: "finite_system_formed N"
    and at: "\<And>d x. d \<in> declared_sites D \<Longrightarrow>
      (d,x) \<in> positive_meaning (decode_finite_system N) \<longleftrightarrow> (d,x) \<in> positive_meaning (decode_finite_system P)"
    and discharged: "declarations_discharged (positive_meaning (decode_finite_system P)) D corr"
  shows "declarations_discharged (positive_meaning (decode_finite_system N)) (declarations_varied P N D) corr"
proof -
  define PD :: "('a,'s,'d,unit) produced_declarations" where "PD = unproduced (unnarrowed D)"
  define \<kappa> :: "('a,'s,'d,'c) finite_witness_construction" where "\<kappa> = undefined"
  define \<kappa>' :: "('b,'t,'d,'e) finite_witness_construction" where "\<kappa>' = undefined"
  have none: "declared_production PD e S s = None" for e S s by (simp add: PD_def)
  have trD: "resolution_declarations.truncate PD = D" by (simp add: PD_def)
  have top: "\<And>e S s. declared_narrowing PD e S s = (\<lambda>_. True)" by (simp add: PD_def)
  have dis: "narrowed_declarations_discharged (positive_meaning (decode_finite_system P))
      (narrowed_declarations.truncate PD) corr"
    using discharged by (simp add: PD_def declarations_discharged_unnarrowed)
  have complete: "productions_complete (positive_meaning (decode_finite_system P)) \<kappa> P PD"
    by (simp add: productions_complete_def none)
  have carried_values: "production_values_carried \<kappa> P \<kappa>' N R"
    if "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets PD" "declared_production PD e S s = Some R" for e S s keep Vp Vh R
    using that(2) by (simp add: none)
  have eqr: "narrowed_declarations.truncate (produced_declarations_varied P N PD) = unnarrowed (declarations_varied P N D)"
    by (simp add: produced_declarations_varied_truncate narrowed_declarations_varied_def trD narrowing_varied_top[OF top])
  have "narrowed_declarations_discharged (positive_meaning (decode_finite_system N))
      (narrowed_declarations.truncate (produced_declarations_varied P N PD)) corr"
    by (rule declarations_varied_narrowed_discharged(1)[OF Pf Nf _ varied_narrowings_agree_top[OF top] dis complete carried_values])
      (simp add: trD at)
  then show ?thesis by (simp add: eqr declarations_discharged_unnarrowed)
qed

end
