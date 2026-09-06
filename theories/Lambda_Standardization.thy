theory Lambda_Standardization
  imports Lambda_Applications
begin

section \<open>Standardization of the existing beta relation\<close>

declare listrel_mono [mono_set]

inductive lambda_standard :: "lambda_term \<Rightarrow> lambda_term \<Rightarrow> bool" where
  variable: "listrelp lambda_standard ps qs \<Longrightarrow>
    lambda_standard (lambda_apps (Lambda_Variable n) ps) (lambda_apps (Lambda_Variable n) qs)"
| abstraction: "lambda_standard p q \<Longrightarrow> listrelp lambda_standard ps qs \<Longrightarrow>
    lambda_standard (lambda_apps (Lambda_Abstraction p) ps) (lambda_apps (Lambda_Abstraction q) qs)"
| beta: "lambda_standard (lambda_apps (lambda_substitute p q 0) ps) r \<Longrightarrow>
    lambda_standard (lambda_apps (Lambda_Application (Lambda_Abstraction p) q) ps) r"

lemma lambda_listrel_conj_left:
  "listrelp (\<lambda>x y. R x y \<and> S x y) xs ys \<Longrightarrow> listrelp R xs ys"
  by (induction rule: listrelp.induct) (auto intro: listrelp.intros)

lemma lambda_listrel_conj_right:
  "listrelp (\<lambda>x y. R x y \<and> S x y) xs ys \<Longrightarrow> listrelp S xs ys"
  by (induction rule: listrelp.induct) (auto intro: listrelp.intros)

lemma lambda_listrel_append:
  assumes "listrelp R xs ys" "listrelp R xs' ys'"
  shows "listrelp R (xs@xs') (ys@ys')"
  using assms by (induction arbitrary: xs' ys' rule: listrelp.induct)
    (auto intro: listrelp.intros)

lemma lambda_standard_application:
  assumes head: "lambda_standard p p'" and argument: "lambda_standard q q'"
  shows "lambda_standard (Lambda_Application p q) (Lambda_Application p' q')"
  using head
proof (induction rule: lambda_standard.induct)
  case (variable ps ps' n)
  then have "listrelp lambda_standard ps ps'" by (rule lambda_listrel_conj_left)
  moreover have "listrelp lambda_standard [q] [q']"
    by (auto intro: argument listrelp.intros)
  ultimately have "listrelp lambda_standard (ps@[q]) (ps'@[q'])"
    by (rule lambda_listrel_append)
  then have "lambda_standard (lambda_apps (Lambda_Variable n) (ps@[q]))
    (lambda_apps (Lambda_Variable n) (ps'@[q']))" by (rule lambda_standard.variable)
  then show ?case by (simp only: lambda_apps_last)
next
  case (abstraction p p' ps ps')
  from abstraction(3) have "listrelp lambda_standard ps ps'"
    by (rule lambda_listrel_conj_left)
  moreover have "listrelp lambda_standard [q] [q']"
    by (auto intro: argument listrelp.intros)
  ultimately have "listrelp lambda_standard (ps@[q]) (ps'@[q'])"
    by (rule lambda_listrel_append)
  with abstraction(1) have "lambda_standard (lambda_apps (Lambda_Abstraction p) (ps@[q]))
    (lambda_apps (Lambda_Abstraction p') (ps'@[q']))" by (rule lambda_standard.abstraction)
  then show ?case by (simp only: lambda_apps_last)
next
  case (beta p u ps r)
  then have "lambda_standard (lambda_apps (lambda_substitute p u 0) (ps@[q]))
    (Lambda_Application r q')" by (simp only: lambda_apps_last)
  then have "lambda_standard
    (lambda_apps (Lambda_Application (Lambda_Abstraction p) u) (ps@[q]))
    (Lambda_Application r q')" by (rule lambda_standard.beta)
  then show ?case by (simp only: lambda_apps_last)
qed

lemma lambda_standard_refl: "lambda_standard p p"
proof (induction p)
  case (Lambda_Variable n)
  have "lambda_standard (lambda_apps (Lambda_Variable n) []) (lambda_apps (Lambda_Variable n) [])"
    by (rule lambda_standard.variable, rule listrelp.Nil)
  then show ?case by simp
next
  case (Lambda_Application p q)
  then show ?case by (rule lambda_standard_application)
next
  case (Lambda_Abstraction p)
  have "lambda_standard (lambda_apps (Lambda_Abstraction p) [])
    (lambda_apps (Lambda_Abstraction p) [])"
    by (rule lambda_standard.abstraction[OF Lambda_Abstraction.IH listrelp.Nil])
  then show ?case by simp
qed

lemma lambda_standard_apps:
  assumes "listrelp lambda_standard ps qs" "lambda_standard p q"
  shows "lambda_standard (lambda_apps p ps) (lambda_apps q qs)"
  using assms by (induction arbitrary: p q rule: listrelp.induct)
    (auto intro: lambda_standard_application)

lemma lambda_listrel_reduces_apps:
  assumes "listrelp lambda_reduces ps qs" "lambda_reduces p q"
  shows "lambda_reduces (lambda_apps p ps) (lambda_apps q qs)"
  using assms by (induction arbitrary: p q rule: listrelp.induct)
    (auto intro: lambda_reduces_application)

theorem lambda_standard_sound:
  assumes "lambda_standard p q"
  shows "lambda_reduces p q"
  using assms by (induction rule: lambda_standard.induct)
    (auto dest: lambda_listrel_conj_right intro: lambda_listrel_reduces_apps
      lambda_apps_beta lambda_reduces_under converse_rtranclp_into_rtranclp)

lemma lambda_standard_lift:
  assumes "lambda_standard p q"
  shows "lambda_standard (lambda_lift p k) (lambda_lift q k)"
  using assms
proof (induction arbitrary: k rule: lambda_standard.induct)
  case (variable ps qs n)
  then have "listrelp lambda_standard (map (\<lambda>p. lambda_lift p k) ps)
    (map (\<lambda>p. lambda_lift p k) qs)"
    by (induction rule: listrelp.induct) (auto intro: listrelp.intros)
  then show ?case by (cases "n<k") (auto intro: lambda_standard.variable)
next
  case (abstraction p q ps qs)
  from abstraction(3) have "listrelp lambda_standard (map (\<lambda>p. lambda_lift p k) ps)
    (map (\<lambda>p. lambda_lift p k) qs)"
    by (induction rule: listrelp.induct) (auto intro: listrelp.intros)
  then show ?case by (auto intro: lambda_standard.abstraction abstraction)
next
  case (beta p q ps r)
  then show ?case by (auto intro: lambda_standard.beta)
qed

lemma lambda_standard_substitute:
  assumes "lambda_standard p p'" "lambda_standard q q'"
  shows "lambda_standard (lambda_substitute p q k) (lambda_substitute p' q' k)"
  using assms
proof (induction arbitrary: q q' k rule: lambda_standard.induct)
  case (variable ps ps' n)
  then have "listrelp lambda_standard (map (\<lambda>p. lambda_substitute p q k) ps)
    (map (\<lambda>p. lambda_substitute p q' k) ps')"
    by (induction rule: listrelp.induct) (auto intro: listrelp.intros variable)
  moreover have "lambda_standard (lambda_substitute (Lambda_Variable n) q k)
    (lambda_substitute (Lambda_Variable n) q' k)"
    using variable.prems by (auto simp: lambda_substitute.simps(1) intro: lambda_standard_refl)
  ultimately show ?case by simp (rule lambda_standard_apps)
next
  case (abstraction p p' ps ps')
  from abstraction.prems have "lambda_standard (lambda_lift q 0) (lambda_lift q' 0)"
    by (rule lambda_standard_lift)
  then have "lambda_standard (lambda_substitute p (lambda_lift q 0) (Suc k))
    (lambda_substitute p' (lambda_lift q' 0) (Suc k))" by (rule abstraction.IH(1))
  moreover from abstraction(3) have
    "listrelp lambda_standard (map (\<lambda>p. lambda_substitute p q k) ps)
      (map (\<lambda>p. lambda_substitute p q' k) ps')"
    by (induction rule: listrelp.induct) (auto intro: listrelp.intros abstraction)
  ultimately show ?case by simp (rule lambda_standard.abstraction)
next
  case (beta p u ps r)
  then show ?case by (auto simp: lambda_substitution_composition intro: lambda_standard.beta)
qed

lemma lambda_standard_list_after_beta:
  assumes "listrelp (\<lambda>p q. lambda_standard p q \<and>
    (\<forall>r. lambda_beta q r \<longrightarrow> lambda_standard p r)) ps qs"
    "lambda_list_beta qs rs"
  shows "listrelp lambda_standard ps rs"
  using assms
proof (induction arbitrary: rs rule: listrelp.induct)
  case Nil
  then show ?case by simp
next
  case (Cons p q ps qs)
  note source = Cons
  show ?case
  proof (cases rs)
    case Nil
    with source show ?thesis by simp
  next
    case (Cons r rs')
    with source have "(lambda_beta q r \<and> qs=rs') \<or>
      (q=r \<and> lambda_list_beta qs rs')" by simp
    then have "listrelp lambda_standard (p#ps) (r#rs')"
    proof
      assume head: "lambda_beta q r \<and> qs=rs'"
      with source have "lambda_standard p r" by blast
      moreover from source have "listrelp lambda_standard ps qs"
        by (iprover dest: lambda_listrel_conj_left)
      ultimately show ?thesis using head by (auto intro: listrelp.Cons)
    next
      assume tail: "q=r \<and> lambda_list_beta qs rs'"
      with source have "lambda_standard p r" by blast
      moreover from tail have "listrelp lambda_standard ps rs'" by (blast intro: source)
      ultimately show ?thesis by (rule listrelp.Cons)
    qed
    with Cons show ?thesis by simp
  qed
qed

lemma lambda_standard_after_beta:
  assumes "lambda_standard p q" "lambda_beta q r"
  shows "lambda_standard p r"
  using assms
proof (induction arbitrary: r rule: lambda_standard.induct)
  case (variable ps qs n)
  then obtain rs where step: "lambda_list_beta qs rs"
    and result: "r=lambda_apps (Lambda_Variable n) rs"
    by (blast dest: lambda_variable_apps_beta)
  from variable(1) step have "listrelp lambda_standard ps rs"
    by (rule lambda_standard_list_after_beta)
  then show ?case unfolding result by (rule lambda_standard.variable)
next
  case (abstraction p q ps qs)
  from abstraction.prems show ?case
  proof (rule lambda_apps_beta_cases)
    fix q'
    assume step: "lambda_beta (Lambda_Abstraction q) q'"
      and result: "r=lambda_apps q' qs"
    from step obtain b where body: "q'=Lambda_Abstraction b" "lambda_beta q b" by auto
    from body have "lambda_standard p b" by (blast intro: abstraction)
    moreover from abstraction have "listrelp lambda_standard ps qs"
      by (iprover dest: lambda_listrel_conj_left)
    ultimately show "lambda_standard (lambda_apps (Lambda_Abstraction p) ps) r"
      unfolding result body(1) by (rule lambda_standard.abstraction)
  next
    fix rs
    assume step: "lambda_list_beta qs rs"
      and result: "r=lambda_apps (Lambda_Abstraction q) rs"
    from abstraction(3) step have "listrelp lambda_standard ps rs"
      by (rule lambda_standard_list_after_beta)
    with abstraction(1) show "lambda_standard (lambda_apps (Lambda_Abstraction p) ps) r"
      unfolding result by (rule lambda_standard.abstraction)
  next
    fix b a as
    assume body: "Lambda_Abstraction q=Lambda_Abstraction b"
      and arguments: "qs=a#as" and result: "r=lambda_apps (lambda_substitute b a 0) as"
    from abstraction(3) have related: "listrelp lambda_standard ps qs"
      by (rule lambda_listrel_conj_left)
    from related arguments obtain u us where source: "ps=u#us"
      and head: "lambda_standard u a" and tail: "listrelp lambda_standard us as"
      by (cases rule: listrelp.cases) auto
    have "lambda_standard (lambda_substitute p u 0) (lambda_substitute q a 0)"
      using abstraction(1) head by (rule lambda_standard_substitute)
    with tail have "lambda_standard (lambda_apps (lambda_substitute p u 0) us)
      (lambda_apps (lambda_substitute q a 0) as)" by (rule lambda_standard_apps)
    then have "lambda_standard (lambda_apps (Lambda_Application (Lambda_Abstraction p) u) us)
      (lambda_apps (lambda_substitute q a 0) as)" by (rule lambda_standard.beta)
    then show "lambda_standard (lambda_apps (Lambda_Abstraction p) ps) r"
      using source body result by simp
  qed
next
  case (beta p q ps s)
  show ?case by (rule lambda_standard.beta) (rule beta)+
qed

theorem lambda_reduction_standard:
  assumes "lambda_reduces p q"
  shows "lambda_standard p q"
  using assms by (induction rule: rtranclp_induct)
    (iprover intro: lambda_standard_refl lambda_standard_after_beta)+

theorem lambda_standard_iff_reduction:
  "lambda_standard p q \<longleftrightarrow> lambda_reduces p q"
  using lambda_standard_sound lambda_reduction_standard by blast

text \<open>
  Standard reduction organizes a finite beta derivation by its application
  spine. It is equivalent to the existing reflexive transitive beta relation,
  including for open terms. Application compatibility permits reflexivity to
  follow from ordinary term induction. Substitution compatibility and closure
  under one further beta step give the reverse inclusion.

  The argument adapts Stefan Berghofer's HOL/Proofs/Lambda/Standardization
  development (2005, TU Muenchen), based on Ralph Matthes's lecture notes and
  Ralph Loader's proof idea. Every proof here is checked over this repository's
  source syntax and substitution; no external lambda datatype is imported.
\<close>

end
