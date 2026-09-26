theory Factor_Input_Productions
  imports Factor_Varied_Narrowed_Transfer Factor_Artifact_Citation_Declarations
begin

text \<open>
  The input production (I2 of correction (13) of DECISIONS.md, task 495's entry, "Committed choice, for refusals"): a
  producer d whose clause S reads its head at a view Vc as (ci, a), the variable a not in ci
  (@{const head_registration}), produces its input as its output's value: the registration at site d, clause S,
  variable a, whose families are the determined value of ci (@{const Determined_Value}, I1's). At a goal it applies at,
  its value is the goal's viewed input itself; it reads neither the program nor the bound. At a socket of class every
  answer its completeness is discharged once, for every input registration, by its producer's reflexivity at the view
  (@{text producer_reflexive}): every answer read (x,y) has an answer read (x,x). The value is read by R5's committed
  step alone (@{const finite_registration_production}); no checker, test or discharge's hypothesis reads it.
\<close>

section \<open>The input registration and a producer's reflexivity\<close>

definition input_registration ::
    "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> nat resolution_view \<Rightarrow> 'a \<Rightarrow> ('a,'s,'d,'v) collection_registration" where
  "input_registration d S Vc a = \<lparr>registration_site = d, registration_schema = S, registration_variable = a,
    registration_families = Determined_Value (fst (the (resolution_view_pattern Vc (finite_schema_conclusion S))))\<rparr>"

definition producer_reflexive :: "('d \<times> factor_term) set \<Rightarrow> 'd \<Rightarrow> nat resolution_view \<Rightarrow> bool" where
  "producer_reflexive M d Vc \<longleftrightarrow> (\<forall>t x y. (d,t) \<in> M \<longrightarrow> resolution_view_term Vc t = Some (x,y) \<longrightarrow>
    (\<exists>t'. (d,t') \<in> M \<and> resolution_view_term Vc t' = Some (x,x)))"

lemma input_registration_fields [simp]:
  "registration_site (input_registration d S Vc a) = d" "registration_schema (input_registration d S Vc a) = S"
  "registration_variable (input_registration d S Vc a) = a"
  by (simp_all add: input_registration_def)

lemma input_registration_head:
  assumes "head_registration Vc S a"
  obtains ci where "resolution_view_pattern Vc (finite_schema_conclusion S) = Some (ci,Finite_Variable a)"
    "a |\<notin>| finite_pattern_variables ci" "registration_families (input_registration d S Vc a) = Determined_Value ci"
  using assms unfolding head_registration_def by (auto simp: input_registration_def)

text \<open>
  An input registration's value at its own site and clause is the determined value of the head's viewed input: at
  every program and bound.
\<close>

lemma input_registration_value:
  "witness_value (finite_collection_construction [input_registration d S Vc a] n) P d S B a =
    finite_determined_value (fst (the (resolution_view_pattern Vc (finite_schema_conclusion S)))) B"
  by (simp add: finite_collection_construction_def finite_registration_matches_def input_registration_def
      finite_registration_value_def)

section \<open>Production and answers, from the value alone\<close>

text \<open>
  Stated once for any construction whose value at the site and clause is the determined value of the head's viewed
  input: the input registration's own construction and its relocation are the instances below.
\<close>

lemma determined_input_produces:
  assumes computed: "\<And>B. witness_value \<kappa> P e T B a =
      finite_determined_value (fst (the (resolution_view_pattern Vc (finite_schema_conclusion T)))) B"
  shows "head_registration_produces \<kappa> P e T a (\<lambda>_. True)"
  unfolding head_registration_produces_def by (auto simp: computed intro: finite_determined_value_formed)

lemma determined_input_answers:
  assumes computed: "\<And>B. witness_value \<kappa> P e T B a =
      finite_determined_value (fst (the (resolution_view_pattern Vc (finite_schema_conclusion T)))) B"
    and reflexive: "producer_reflexive M e Vc"
  shows "head_registration_answers M \<kappa> P e T Vc a"
  unfolding head_registration_answers_def
proof (intro allI impI)
  fix B v x t y
  assume val: "witness_value \<kappa> P e T B a = Some v" and inp: "head_registration_input Vc T B = Some x"
    and et: "(e,t) \<in> M" and vt: "resolution_view_term Vc t = Some (x,y)"
  obtain ci co where vc: "resolution_view_pattern Vc (finite_schema_conclusion T) = Some (ci,co)"
    using inp by (auto simp: head_registration_input_def split: option.splits)
  have x: "x = evaluate_pattern (\<lambda>z. decode_finite_term (finite_binding_valuation B z)) (decode_finite_pattern ci)"
    using inp by (simp add: head_registration_input_def vc)
  have "finite_determined_value ci B = Some v" using val computed[of B] by (simp add: vc)
  then have xv: "decode_finite_term v = x" using finite_determined_value_decoded x by simp
  obtain t' where "(e,t') \<in> M" "resolution_view_term Vc t' = Some (x,x)"
    using reflexive et vt unfolding producer_reflexive_def by blast
  then show "\<exists>t'. (e,t') \<in> M \<and> resolution_view_term Vc t' = Some (x,decode_finite_term v)" using xv by blast
qed

theorem input_registration_produces:
  "head_registration_produces (finite_collection_construction [input_registration d S Vc a] n) P d S a (\<lambda>_. True)"
  by (rule determined_input_produces[OF input_registration_value])

theorem input_registration_answers:
  assumes reflexive: "producer_reflexive M d Vc"
  shows "head_registration_answers M (finite_collection_construction [input_registration d S Vc a] n) P d S Vc a"
  by (rule determined_input_answers[OF input_registration_value reflexive])

section \<open>Completeness at a socket of class every answer\<close>

text \<open>
  #599's @{thm [source] registration_complete_at_socket} at the input registration: a socket discharged over every
  answer (R5's @{const socket_discharged}, @{thm [source] socket_discharged_narrowed}) whose premise calls a producer
  reflexive at the socket's view. Every true instance of the clause extends to one whose output is the input.
\<close>

theorem input_registration_complete_at_socket:
  assumes socket: "socket_discharged M C s keep Vp Vh" and vp: "view_formed Vp"
    and premise: "(s,d,p) |\<in>| finite_schema_premises C" and viewed: "resolution_view_pattern Vp p = Some (xi,yo)"
    and reflexive: "producer_reflexive M d Vp" and h: "clause_true M (decode_finite_schema C) h"
    and input: "head_registration_input Vp S B = Some (evaluate_pattern h (decode_finite_pattern xi))"
    and valued: "witness_value (finite_collection_construction [input_registration d S Vp a] n) P d S B a = Some v"
  shows "finite_term_formed v"
    "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
proof -
  note n = socket[unfolded socket_discharged_narrowed]
  show "finite_term_formed v"
    by (rule registration_complete_at_socket(1)[OF n vp premise viewed input_registration_produces
        input_registration_answers[OF reflexive] h input valued])
  show "\<exists>h'. clause_true M (decode_finite_schema C) h' \<and> head_kept keep Vh C h h' \<and>
      evaluate_pattern h' (decode_finite_pattern xi) = evaluate_pattern h (decode_finite_pattern xi) \<and>
      evaluate_pattern h' (decode_finite_pattern yo) = decode_finite_term v"
    by (rule registration_complete_at_socket(3)[OF n vp premise viewed input_registration_produces
        input_registration_answers[OF reflexive] h input valued])
qed

text \<open>
  A record's productions discharged (R5f2's @{const productions_discharged}) where each is an input registration of a
  producer reflexive at its socket's view, at a socket of class every answer, or a production discharged as R5f2
  states: the two kinds side by side in one record.
\<close>

theorem input_productions_discharged:
  fixes D :: "('a,'s::linorder,'d,'v) produced_declarations"
  assumes each: "\<And>e S s keep Vp Vh R. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      declared_production D e S s = Some R \<Longrightarrow>
      (R = input_registration (registration_site R) (registration_schema R) Vp (registration_variable R) \<and>
        head_registration Vp (registration_schema R) (registration_variable R) \<and>
        producer_reflexive M (registration_site R) Vp \<and> (\<forall>x. declared_narrowing D e S s x)) \<or>
      (head_registration Vp (registration_schema R) (registration_variable R) \<and>
        head_registration_produces (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
          (registration_variable R) (declared_narrowing D e S s) \<and>
        head_registration_answers M (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
          Vp (registration_variable R))"
  shows "productions_discharged M P n D"
  unfolding productions_discharged_def
proof (intro allI impI)
  fix e S s keep Vp Vh R
  assume t: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D" and r: "declared_production D e S s = Some R"
  show "head_registration Vp (registration_schema R) (registration_variable R) \<and>
      head_registration_produces (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
        (registration_variable R) (declared_narrowing D e S s) \<and>
      head_registration_answers M (finite_collection_construction [R] n) P (registration_site R) (registration_schema R)
        Vp (registration_variable R)"
    using each[OF t r]
  proof
    assume i: "R = input_registration (registration_site R) (registration_schema R) Vp (registration_variable R) \<and>
      head_registration Vp (registration_schema R) (registration_variable R) \<and>
      producer_reflexive M (registration_site R) Vp \<and> (\<forall>x. declared_narrowing D e S s x)"
    then have eq: "input_registration (registration_site R) (registration_schema R) Vp (registration_variable R) = R"
      and reflexive: "producer_reflexive M (registration_site R) Vp" and top: "\<forall>x. declared_narrowing D e S s x"
      by simp_all
    have p: "head_registration_produces (finite_collection_construction [R] n)
        P (registration_site R) (registration_schema R) (registration_variable R) (\<lambda>_. True)"
      by (rule subst[OF eq, where P = "\<lambda>R'. head_registration_produces (finite_collection_construction [R'] n)
          P (registration_site R) (registration_schema R) (registration_variable R) (\<lambda>_. True)"])
        (rule input_registration_produces)
    have a: "head_registration_answers M (finite_collection_construction [R] n)
        P (registration_site R) (registration_schema R) Vp (registration_variable R)"
      by (rule subst[OF eq, where P = "\<lambda>R'. head_registration_answers M (finite_collection_construction [R'] n)
          P (registration_site R) (registration_schema R) Vp (registration_variable R)"])
        (rule input_registration_answers[OF reflexive])
    show ?thesis using i p a top unfolding head_registration_produces_def by auto
  qed
qed

section \<open>Transfers, reading no search\<close>

text \<open>
  The value reads neither the program nor the bound, so no transfer asks the search's equivariance. By agreement: the
  answers read the meaning at the registration's site alone (@{thm [source] head_registration_answers_agree}), and so
  does reflexivity.
\<close>

lemma producer_reflexive_agree:
  assumes "\<And>x. (d,x) \<in> M' \<longleftrightarrow> (d,x) \<in> M"
  shows "producer_reflexive M' d Vc \<longleftrightarrow> producer_reflexive M d Vc"
  unfolding producer_reflexive_def by (simp add: assms)

text \<open>
  By relocation, the site mapped as the records': the relocated construction's value at the relocated clause is the
  determined value of the source clause's input (I1's @{thm [source] finite_relocated_determined_value}), and the head
  reads the same input there.
\<close>

lemma input_registration_relocated_value:
  assumes R: "R = input_registration d S Vc a" and clause: "((d,c),S) |\<in>| finite_system_clauses P"
  shows "witness_value (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g d) (finite_rename_schema id id g S) B a =
    finite_determined_value (fst (the (resolution_view_pattern Vc
      (finite_schema_conclusion (finite_rename_schema id id g S))))) B"
proof -
  have "witness_value (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g (registration_site R)) (finite_rename_schema id id g (registration_schema R)) B (registration_variable R) =
    finite_determined_value (fst (the (resolution_view_pattern Vc (finite_schema_conclusion S)))) B"
    by (rule finite_relocated_determined_value[where g=g and P=P and n=n and Q=Q and B=B and R=R and c=c])
      (use clause in \<open>simp_all add: R input_registration_def\<close>)
  then show ?thesis by (simp add: R finite_rename_schema_def finite_term_pattern.map_id)
qed

theorem input_registration_relocated:
  assumes R: "R = input_registration d S Vc a" and clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and reflexive: "producer_reflexive M' (g d) Vc"
  shows "head_registration_produces (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g d) (finite_rename_schema id id g S) a (\<lambda>_. True)"
    "head_registration_answers M' (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g d) (finite_rename_schema id id g S) Vc a"
proof -
  note computed = input_registration_relocated_value[OF R clause, where g=g and n=n and Q=Q]
  show "head_registration_produces (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g d) (finite_rename_schema id id g S) a (\<lambda>_. True)"
    by (rule determined_input_produces[OF computed])
  show "head_registration_answers M' (finite_relocated_construction g P (finite_collection_construction [R] n))
      Q (g d) (finite_rename_schema id id g S) Vc a"
    by (rule determined_input_answers[OF computed reflexive])
qed

text \<open>
  Along the clause match: the varied registration is the input registration of the matched clause at the mapped
  variable, and V2b's value carrying holds of an input registration outright (I1's
  @{thm [source] determined_values_carried}).
\<close>

lemma finite_conclusion_variables_scope:
  "finite_pattern_variables (finite_schema_conclusion S) |\<subseteq>| finite_schema_variables S"
  by (auto simp: finite_schema_variables_def)

theorem input_registration_values_carried:
  assumes reg: "head_registration Vc S a"
  shows "registration_values_carried P m N m' (input_registration d S Vc a)"
proof -
  obtain ci where vS: "resolution_view_pattern Vc (finite_schema_conclusion S) = Some (ci,Finite_Variable a)"
      and vf: "view_formed Vc"
    using reg unfolding head_registration_def by blast
  have "fset (finite_pattern_variables ci) \<subseteq> fset (finite_pattern_variables (finite_schema_conclusion S))"
    by (rule resolution_view_parts_variables(1)[OF vf vS])
  then have sub: "finite_pattern_variables ci |\<subseteq>| finite_schema_variables S"
    using finite_conclusion_variables_scope[of S] by (auto simp: less_eq_fset.rep_eq)
  show ?thesis
    by (rule determined_values_carried[where p=ci]) (use vS sub in \<open>simp_all add: input_registration_def\<close>)
qed

context finite_schema_matched
begin

theorem input_registration_varied:
  assumes reg: "head_registration Vc S a"
  shows "registration_varied f T (input_registration d S Vc a) = input_registration d T Vc (f a)"
proof -
  obtain ci where vS: "resolution_view_pattern Vc (finite_schema_conclusion S) = Some (ci,Finite_Variable a)"
    using input_registration_head[OF reg] by blast
  have vT: "resolution_view_pattern Vc (finite_schema_conclusion T) =
      Some (map_finite_term_pattern f ci,Finite_Variable (f a))"
    using resolution_view_pattern_map[OF vS, of f] by (simp add: conclusion)
  show ?thesis by (simp add: registration_varied_def input_registration_def vS vT)
qed

end

section \<open>12's instance: artifact identity produces its input at 37.0/2\<close>

text \<open>
  12's clause (@{const identity_socket_schema}) reads its head at @{const view_identity} as (x0, x1): the input
  registration of 12 is at variable 1, its value x0's term. Artifact identity is reflexive on the artifacts it admits,
  from @{thm [source] artifact_identity_exact} alone; nothing of the given's readers is refined, restated or added.
\<close>

definition identity_input_registration :: "(nat,nat,nat,nat) collection_registration" where
  "identity_input_registration = input_registration 12 identity_socket_schema view_identity 1"

lemma identity_input_registration_head: "head_registration view_identity identity_socket_schema 1"
  by (simp add: head_registration_def view_identity_formed view_identity_pattern identity_socket_schema_def)

lemma identity_input_registration_fields:
  "registration_site identity_input_registration = 12"
  "registration_schema identity_input_registration = identity_socket_schema"
  "registration_variable identity_input_registration = 1"
  "registration_families identity_input_registration = Determined_Value (Finite_Variable 0)"
  by (simp_all add: identity_input_registration_def input_registration_def view_identity_pattern
      identity_socket_schema_def)

theorem artifact_identity_reflexive: "producer_reflexive (positive_meaning artifact_identity_system) 12 view_identity"
  unfolding producer_reflexive_def view_identity_term
proof (intro allI impI)
  fix t x y
  assume m: "(12,t) \<in> positive_meaning artifact_identity_system" and v: "pair_view t = Some (x,y)"
  obtain R x0 y0 where t: "t = Pair_Term x0 y0" and r: "artifact_value_presents R x0" "artifact_value_presents R y0"
    using m artifact_identity_exact by blast
  have x: "x = x0" using v t by (simp add: pair_view_some)
  have "(12,Pair_Term x0 x0) \<in> positive_meaning artifact_identity_system"
    using artifact_identity_exact r(1) by blast
  then show "\<exists>t'. (12,t') \<in> positive_meaning artifact_identity_system \<and> pair_view t' = Some (x,x)"
    using x by (auto simp: pair_view_some)
qed

theorem identity_input_complete_at_lookup:
  assumes h: "clause_true (positive_meaning artifact_lookup_system) (decode_finite_schema lookup_socket_schema) h"
    and input: "head_registration_input view_identity identity_socket_schema B = Some (h 4)"
    and valued: "witness_value (finite_collection_construction [identity_input_registration] n) P 12
      identity_socket_schema B 1 = Some v"
  shows "finite_term_formed v"
    "\<exists>h'. clause_true (positive_meaning artifact_lookup_system) (decode_finite_schema lookup_socket_schema) h' \<and>
      head_kept False lookup_view lookup_socket_schema h h' \<and> h' 4 = h 4 \<and> h' 3 = decode_finite_term v"
proof -
  have eq: "\<And>x. (12,x) \<in> positive_meaning artifact_lookup_system \<longleftrightarrow> (12,x) \<in> positive_meaning artifact_identity_system"
    by (simp add: artifact_lookup_components artifact_identity_exact)
  have reflexive: "producer_reflexive (positive_meaning artifact_lookup_system) 12 view_identity"
    using artifact_identity_reflexive producer_reflexive_agree[OF eq] by simp
  have premise: "(2,12,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 3)) |\<in>| finite_schema_premises lookup_socket_schema"
    by (simp add: lookup_socket_schema_def)
  have viewed: "resolution_view_pattern view_identity (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 3)) =
      Some (Finite_Variable 4,Finite_Variable 3)"
    by (simp add: view_identity_pattern)
  note complete = input_registration_complete_at_socket[OF lookup_socket_discharged view_identity_formed premise viewed
      reflexive h, of identity_socket_schema B 1 n P v]
  show "finite_term_formed v" using complete(1) input valued by (simp add: identity_input_registration_def)
  show "\<exists>h'. clause_true (positive_meaning artifact_lookup_system) (decode_finite_schema lookup_socket_schema) h' \<and>
      head_kept False lookup_view lookup_socket_schema h h' \<and> h' 4 = h 4 \<and> h' 3 = decode_finite_term v"
    using complete(2) input valued by (simp add: identity_input_registration_def)
qed

end
