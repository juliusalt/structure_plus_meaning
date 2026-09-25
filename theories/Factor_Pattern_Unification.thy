theory Factor_Pattern_Unification
  imports Factor_Finite_Schema_Renaming Factor_Finite_Exact_Patterns
begin

section \<open>Substitution of finite patterns\<close>

text \<open>
  A substitution replaces every variable of a finite pattern by a pattern and keeps its leaves and
  pairs. Decoded, it is the existing substitution of patterns (@{text decode_finite_pattern_substitute}),
  so what is proved of it here is proved of @{const pattern_substitute}.
\<close>

fun finite_pattern_substitute ::
    "('a \<Rightarrow> 'b finite_term_pattern) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'b finite_term_pattern" where
  "finite_pattern_substitute s (Finite_Variable a) = s a"
| "finite_pattern_substitute s (Finite_Pattern_Target t) = Finite_Pattern_Target t"
| "finite_pattern_substitute s (Finite_Pattern_Payload v) = Finite_Pattern_Payload v"
| "finite_pattern_substitute s (Finite_Pattern_Pair p q) =
    Finite_Pattern_Pair (finite_pattern_substitute s p) (finite_pattern_substitute s q)"

lemma decode_finite_pattern_substitute:
  "decode_finite_pattern (finite_pattern_substitute s p) =
    pattern_substitute (decode_finite_pattern \<circ> s) (decode_finite_pattern p)"
  by (induction p) simp_all

lemma finite_pattern_substitute_composes:
  "finite_pattern_substitute t (finite_pattern_substitute s p) =
    finite_pattern_substitute (\<lambda>a. finite_pattern_substitute t (s a)) p"
  by (induction p) simp_all

lemma finite_pattern_substitute_identity [simp]:
  "finite_pattern_substitute Finite_Variable p = p"
  by (induction p) simp_all

lemma finite_pattern_substitute_cong:
  assumes "\<And>a. a |\<in>| finite_pattern_variables p \<Longrightarrow> s a = t a"
  shows "finite_pattern_substitute s p = finite_pattern_substitute t p"
  using assms by (induction p) auto

lemma finite_pattern_substitute_factor:
  assumes "\<And>b. finite_pattern_substitute \<theta> (\<sigma> b) = \<theta> b"
  shows "finite_pattern_substitute \<theta> (finite_pattern_substitute \<sigma> p) = finite_pattern_substitute \<theta> p"
  by (simp add: finite_pattern_substitute_composes assms)

text \<open>
  The eliminator of a variable by a pattern sends the variable to the pattern and every other
  variable to itself. It is a constant of its own, so that a proof reads it applied and never as an
  expanded function.
\<close>

definition finite_eliminator :: "'a \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'a \<Rightarrow> 'a finite_term_pattern" where
  "finite_eliminator a q b = (if b = a then q else Finite_Variable b)"

lemma finite_eliminator_apply [simp]:
  "finite_eliminator a q b = (if b = a then q else Finite_Variable b)"
  by (simp add: finite_eliminator_def)

lemma finite_pattern_substitute_fresh:
  assumes "a \<notin> fset (finite_pattern_variables p)"
  shows "finite_pattern_substitute (finite_eliminator a q) p = p"
  using assms by (induction p) auto

lemma finite_pattern_eliminate_variables:
  assumes "a \<notin> fset (finite_pattern_variables q)"
  shows "fset (finite_pattern_variables (finite_pattern_substitute (finite_eliminator a q) p)) \<subseteq>
    (fset (finite_pattern_variables p) - {a}) \<union> fset (finite_pattern_variables q)"
  using assms by (induction p) auto

lemma finite_pattern_substitute_rename:
  assumes "\<And>b. \<tau> (f b) = map_finite_term_pattern f (\<sigma> b)"
  shows "finite_pattern_substitute \<tau> (map_finite_term_pattern f p) =
    map_finite_term_pattern f (finite_pattern_substitute \<sigma> p)"
  using assms by (induction p) simp_all

lemma finite_pattern_variables_map:
  "finite_pattern_variables (map_finite_term_pattern f p) = f |`| finite_pattern_variables p"
  by (induction p) (simp_all add: fimage_funion)

section \<open>Equations between finite patterns and their unifiers\<close>

type_synonym 'a finite_pattern_pairs = "('a finite_term_pattern \<times> 'a finite_term_pattern) list"

definition finite_unifies :: "('a \<Rightarrow> 'b finite_term_pattern) \<Rightarrow> 'a finite_pattern_pairs \<Rightarrow> bool" where
  "finite_unifies \<theta> E \<longleftrightarrow>
    (\<forall>x\<in>set E. finite_pattern_substitute \<theta> (fst x) = finite_pattern_substitute \<theta> (snd x))"

lemma finite_unifies_Nil [simp]: "finite_unifies \<theta> []"
  by (simp add: finite_unifies_def)

lemma finite_unifies_Cons [simp]:
  "finite_unifies \<theta> (x # E) \<longleftrightarrow>
    finite_pattern_substitute \<theta> (fst x) = finite_pattern_substitute \<theta> (snd x) \<and> finite_unifies \<theta> E"
  by (simp add: finite_unifies_def)

lemma finite_unifies_compose:
  assumes "finite_unifies \<sigma> E"
  shows "finite_unifies (\<lambda>b. finite_pattern_substitute \<rho> (\<sigma> b)) E"
  using assms by (auto simp: finite_unifies_def finite_pattern_substitute_composes[symmetric])

definition finite_pairs_substitute ::
    "('a \<Rightarrow> 'b finite_term_pattern) \<Rightarrow> 'a finite_pattern_pairs \<Rightarrow> 'b finite_pattern_pairs" where
  "finite_pairs_substitute s E =
    map (\<lambda>x. (finite_pattern_substitute s (fst x), finite_pattern_substitute s (snd x))) E"

lemma finite_pairs_substitute_simps [simp]:
  "finite_pairs_substitute s [] = []"
  "finite_pairs_substitute s (x # E) =
    (finite_pattern_substitute s (fst x), finite_pattern_substitute s (snd x)) # finite_pairs_substitute s E"
  by (simp_all add: finite_pairs_substitute_def)

definition finite_pairs_variables :: "'a finite_pattern_pairs \<Rightarrow> 'a set" where
  "finite_pairs_variables E =
    (\<Union>x\<in>set E. fset (finite_pattern_variables (fst x)) \<union> fset (finite_pattern_variables (snd x)))"

lemma finite_pairs_variables_simps [simp]:
  "finite_pairs_variables [] = {}"
  "finite_pairs_variables (x # E) =
    fset (finite_pattern_variables (fst x)) \<union> fset (finite_pattern_variables (snd x)) \<union> finite_pairs_variables E"
  by (auto simp: finite_pairs_variables_def)

lemma finite_pairs_variables_finite [simp]: "finite (finite_pairs_variables E)"
  by (induction E) auto

text \<open>
  A variable's equation with a pattern that does not hold it is eliminated by substituting that
  pattern for the variable in the remaining equations: exactly the unifiers that send the variable to
  the pattern's image unify the remaining equations before and after, and the variable leaves them.
\<close>

lemma finite_pattern_substitute_eliminate:
  assumes "\<theta> a = finite_pattern_substitute \<theta> q"
  shows "finite_pattern_substitute \<theta> (finite_pattern_substitute (finite_eliminator a q) p) =
    finite_pattern_substitute \<theta> p"
proof -
  have "(\<lambda>b. finite_pattern_substitute \<theta> ((finite_eliminator a q) b)) = \<theta>"
    using assms by (auto simp: fun_eq_iff)
  then show ?thesis by (simp add: finite_pattern_substitute_composes)
qed

lemma finite_unifies_eliminate_iff:
  assumes "\<theta> a = finite_pattern_substitute \<theta> q"
  shows "finite_unifies \<theta> (finite_pairs_substitute (finite_eliminator a q) E) \<longleftrightarrow> finite_unifies \<theta> E"
  by (induction E) (simp_all only: finite_unifies_Nil finite_unifies_Cons finite_pairs_substitute_simps
      fst_conv snd_conv finite_pattern_substitute_eliminate[OF assms])

lemma finite_eliminated_substitution:
  "finite_pattern_substitute (\<sigma>(a := finite_pattern_substitute \<sigma> q)) p =
    finite_pattern_substitute \<sigma> (finite_pattern_substitute (finite_eliminator a q) p)"
proof -
  have "\<sigma>(a := finite_pattern_substitute \<sigma> q) =
      (\<lambda>b. finite_pattern_substitute \<sigma> ((finite_eliminator a q) b))"
    by (auto simp: fun_eq_iff)
  then show ?thesis by (simp add: finite_pattern_substitute_composes)
qed

lemma finite_unifies_eliminated:
  assumes fresh: "a \<notin> fset (finite_pattern_variables q)"
    and unified: "finite_unifies \<sigma> (finite_pairs_substitute (finite_eliminator a q) E)"
  shows "finite_unifies (\<sigma>(a := finite_pattern_substitute \<sigma> q)) ((Finite_Variable a, q) # E)"
proof -
  have unchanged: "finite_pattern_substitute (finite_eliminator a q) q = q"
    using fresh by (rule finite_pattern_substitute_fresh)
  have "finite_unifies (\<sigma>(a := finite_pattern_substitute \<sigma> q)) E"
    using unified by (induction E) (simp_all add: finite_eliminated_substitution)
  then show ?thesis by (simp add: finite_eliminated_substitution unchanged)
qed

section \<open>The most general unifier\<close>

text \<open>
  The unifier solves a list of equations as a system of transformations of Robinson's algorithm in
  the formulation of Martelli and Montanari: an equation of a variable with itself or of two equal
  leaves is dropped, a pair of pairs is decomposed into its two components' equations, an equation
  whose variable stands on the right is turned around, and a variable's equation with a pattern that
  does not hold it (the occurs check) is eliminated; any other equation has no unifier. Leaves are
  compared for equality as they are, a payload as its octets and a target as its exact artifact, as
  matching compares them. The same contract is stated by Krauss's @{text "HOL/ex/Unification.thy"} of
  the Isabelle distribution for its nested formulation over its own terms; the list of equations here
  gives the list form at once and a lexicographic measure, the variables of the equations, their
  weight and the orientation of the first equation, instead of a proof in the function's domain.

  The unifier is returned as a list of bindings, read by lookup (@{text finite_binding_substitution}):
  the first binding of a variable is its image, a variable without one stands for itself.
\<close>

definition finite_binding_substitution ::
    "('a \<times> 'a finite_term_pattern) list \<Rightarrow> 'a \<Rightarrow> 'a finite_term_pattern" where
  "finite_binding_substitution s a = (case map_of s a of None \<Rightarrow> Finite_Variable a | Some p \<Rightarrow> p)"

lemma finite_binding_substitution_Nil [simp]: "finite_binding_substitution [] = Finite_Variable"
  by (simp add: fun_eq_iff finite_binding_substitution_def)

lemma finite_binding_substitution_Cons [simp]:
  "finite_binding_substitution (x # s) = (finite_binding_substitution s)(fst x := snd x)"
  by (auto simp: fun_eq_iff finite_binding_substitution_def)

fun finite_pattern_weight :: "'a finite_term_pattern \<Rightarrow> nat" where
  "finite_pattern_weight (Finite_Pattern_Pair p q) = Suc (finite_pattern_weight p + finite_pattern_weight q)"
| "finite_pattern_weight p = 1"

lemma finite_pattern_weight_positive [simp]: "0 < finite_pattern_weight p"
  by (cases p) simp_all

lemma finite_pattern_weight_variable_le:
  assumes "a |\<in>| finite_pattern_variables q"
  shows "finite_pattern_weight (s a) \<le> finite_pattern_weight (finite_pattern_substitute s q)"
  using assms by (induction q) auto

text \<open>The occurs check: a variable held strictly inside a pattern is no unifier's image of it.\<close>

lemma finite_pattern_occurs_weight:
  assumes "a |\<in>| finite_pattern_variables q" "q \<noteq> Finite_Variable a"
  shows "finite_pattern_weight (s a) < finite_pattern_weight (finite_pattern_substitute s q)"
proof (cases q)
  case (Finite_Pattern_Pair p p')
  from assms(1) Finite_Pattern_Pair
  have "a |\<in>| finite_pattern_variables p \<or> a |\<in>| finite_pattern_variables p'" by simp
  then show ?thesis
  proof
    assume "a |\<in>| finite_pattern_variables p"
    then have "finite_pattern_weight (s a) \<le> finite_pattern_weight (finite_pattern_substitute s p)"
      by (rule finite_pattern_weight_variable_le)
    with Finite_Pattern_Pair show ?thesis by simp
  next
    assume "a |\<in>| finite_pattern_variables p'"
    then have "finite_pattern_weight (s a) \<le> finite_pattern_weight (finite_pattern_substitute s p')"
      by (rule finite_pattern_weight_variable_le)
    with Finite_Pattern_Pair show ?thesis by simp
  qed
qed (use assms in simp_all)

definition finite_pairs_weight :: "'a finite_pattern_pairs \<Rightarrow> nat" where
  "finite_pairs_weight E = sum_list (map (\<lambda>x. finite_pattern_weight (fst x) + finite_pattern_weight (snd x)) E)"

lemma finite_pairs_weight_simps [simp]:
  "finite_pairs_weight [] = 0"
  "finite_pairs_weight (x # E) =
    finite_pattern_weight (fst x) + finite_pattern_weight (snd x) + finite_pairs_weight E"
  by (simp_all add: finite_pairs_weight_def)

fun finite_pairs_unoriented :: "'a finite_pattern_pairs \<Rightarrow> nat" where
  "finite_pairs_unoriented ((Finite_Variable a, q) # E) = 0"
| "finite_pairs_unoriented E = 1"

abbreviation finite_unify_order :: "('a finite_pattern_pairs \<times> 'a finite_pattern_pairs) set" where
  "finite_unify_order \<equiv>
    measures [\<lambda>E. card (finite_pairs_variables E), finite_pairs_weight, finite_pairs_unoriented]"

lemma finite_unify_drop: "(E, x # E) \<in> finite_unify_order"
proof -
  have "card (finite_pairs_variables E) \<le> card (finite_pairs_variables (x # E))"
    by (rule card_mono) auto
  moreover have "finite_pairs_weight E < finite_pairs_weight (x # E)"
    using finite_pattern_weight_positive[of "fst x"] by simp
  ultimately show ?thesis by (auto simp: le_less)
qed

lemma finite_unify_pair:
  "((p,p') # (q,q') # E, (Finite_Pattern_Pair p q, Finite_Pattern_Pair p' q') # E) \<in> finite_unify_order"
proof -
  have c: "card (finite_pairs_variables ((p,p') # (q,q') # E)) =
      card (finite_pairs_variables ((Finite_Pattern_Pair p q, Finite_Pattern_Pair p' q') # E))"
    by (rule arg_cong[where f=card]) auto
  have w: "finite_pairs_weight ((p,p') # (q,q') # E) <
      finite_pairs_weight ((Finite_Pattern_Pair p q, Finite_Pattern_Pair p' q') # E)"
    by simp
  show ?thesis using c w by simp
qed

lemma finite_unify_swap:
  assumes "finite_pairs_unoriented ((p, Finite_Variable a) # E) = 1"
  shows "((Finite_Variable a, p) # E, (p, Finite_Variable a) # E) \<in> finite_unify_order"
proof -
  have c: "card (finite_pairs_variables ((Finite_Variable a, p) # E)) =
      card (finite_pairs_variables ((p, Finite_Variable a) # E))"
    by (rule arg_cong[where f=card]) auto
  have w: "finite_pairs_weight ((Finite_Variable a, p) # E) = finite_pairs_weight ((p, Finite_Variable a) # E)"
    by simp
  show ?thesis using c w assms by simp
qed

lemma finite_pairs_eliminate_variables:
  assumes fresh: "a \<notin> fset (finite_pattern_variables q)"
  shows "finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E) \<subseteq>
    finite_pairs_variables ((Finite_Variable a, q) # E) - {a}"
proof
  fix c assume "c \<in> finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E)"
  then show "c \<in> finite_pairs_variables ((Finite_Variable a, q) # E) - {a}"
    using fresh by (induction E) (auto dest: finite_pattern_eliminate_variables[OF fresh, THEN subsetD])
qed

lemma finite_unify_eliminate:
  assumes fresh: "a \<notin> fset (finite_pattern_variables q)"
  shows "(finite_pairs_substitute (finite_eliminator a q) E, (Finite_Variable a, q) # E) \<in> finite_unify_order"
proof -
  have "finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E) \<subseteq>
      finite_pairs_variables ((Finite_Variable a, q) # E) - {a}"
    by (rule finite_pairs_eliminate_variables[OF fresh])
  also have "\<dots> \<subset> finite_pairs_variables ((Finite_Variable a, q) # E)"
    by auto
  finally have "card (finite_pairs_variables (finite_pairs_substitute (finite_eliminator a q) E)) <
      card (finite_pairs_variables ((Finite_Variable a, q) # E))"
    by (rule psubset_card_mono[rotated]) simp
  then show ?thesis by simp
qed

function (sequential) finite_unify_pairs ::
    "'a finite_pattern_pairs \<Rightarrow> ('a \<times> 'a finite_term_pattern) list option" where
  "finite_unify_pairs [] = Some []"
| "finite_unify_pairs ((Finite_Variable a, q) # E) =
    (if q = Finite_Variable a then finite_unify_pairs E
     else if a |\<in>| finite_pattern_variables q then None
     else map_option (\<lambda>s. (a, finite_pattern_substitute (finite_binding_substitution s) q) # s)
       (finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E)))"
| "finite_unify_pairs ((Finite_Pattern_Pair p q, Finite_Pattern_Pair p' q') # E) =
    finite_unify_pairs ((p,p') # (q,q') # E)"
| "finite_unify_pairs ((Finite_Pattern_Target x, Finite_Pattern_Target y) # E) =
    (if x = y then finite_unify_pairs E else None)"
| "finite_unify_pairs ((Finite_Pattern_Payload v, Finite_Pattern_Payload w) # E) =
    (if v = w then finite_unify_pairs E else None)"
| "finite_unify_pairs ((p, Finite_Variable a) # E) = finite_unify_pairs ((Finite_Variable a, p) # E)"
| "finite_unify_pairs ((p, q) # E) = None"
  by pat_completeness auto

termination
  by (relation finite_unify_order)
    (auto simp del: in_measures intro: finite_unify_drop finite_unify_pair finite_unify_swap finite_unify_eliminate)

theorem finite_unify_pairs_sound:
  assumes "finite_unify_pairs E = Some s"
  shows "finite_unifies (finite_binding_substitution s) E"
  using assms
proof (induction E arbitrary: s rule: finite_unify_pairs.induct)
  case (2 a q E s)
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1) "2.prems" show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False "2.prems" show ?thesis by simp
    next
      case fresh: False
      from "2.prems" False fresh obtain s' where
        rec: "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = Some s'" and
        s: "s = (a, finite_pattern_substitute (finite_binding_substitution s') q) # s'"
        by auto
      have "finite_unifies ((finite_binding_substitution s')(a :=
          finite_pattern_substitute (finite_binding_substitution s') q)) ((Finite_Variable a, q) # E)"
        by (rule finite_unifies_eliminated[OF fresh "2.IH"(2)[OF False fresh rec]])
      then show ?thesis by (simp only: s finite_binding_substitution_Cons fst_conv snd_conv)
    qed
  qed
qed (auto split: if_splits)

theorem finite_unify_pairs_most_general:
  assumes "finite_unify_pairs E = Some s" "finite_unifies \<theta> E"
  shows "finite_pattern_substitute \<theta> (finite_binding_substitution s b) = \<theta> b"
  using assms
proof (induction E arbitrary: s b rule: finite_unify_pairs.induct)
  case (2 a q E s b)
  from "2.prems"(2) have head: "\<theta> a = finite_pattern_substitute \<theta> q" and tail: "finite_unifies \<theta> E"
    by simp_all
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1) "2.prems"(1) tail show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False "2.prems"(1) show ?thesis by simp
    next
      case fresh: False
      from "2.prems"(1) False fresh obtain s' where
        rec: "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = Some s'" and
        s: "s = (a, finite_pattern_substitute (finite_binding_substitution s') q) # s'"
        by auto
      have unified: "finite_unifies \<theta> (finite_pairs_substitute (finite_eliminator a q) E)"
        using tail by (simp add: finite_unifies_eliminate_iff[OF head])
      have factors: "\<And>c. finite_pattern_substitute \<theta> (finite_binding_substitution s' c) = \<theta> c"
        by (rule "2.IH"(2)[OF False fresh rec unified])
      show ?thesis
        using head by (simp add: s finite_pattern_substitute_factor[OF factors] factors)
    qed
  qed
qed auto

theorem finite_unify_pairs_none:
  assumes "finite_unify_pairs E = None"
  shows "\<not> finite_unifies \<theta> E"
  using assms
proof (induction E rule: finite_unify_pairs.induct)
  case (2 a q E)
  show ?case
  proof
    assume "finite_unifies \<theta> ((Finite_Variable a, q) # E)"
    then have head: "\<theta> a = finite_pattern_substitute \<theta> q" and tail: "finite_unifies \<theta> E"
      by simp_all
    show False
    proof (cases "q = Finite_Variable a")
      case True
      with "2.IH"(1) "2.prems" tail show False by simp
    next
      case False
      show False
      proof (cases "a |\<in>| finite_pattern_variables q")
        case True
        have "finite_pattern_weight (\<theta> a) < finite_pattern_weight (finite_pattern_substitute \<theta> q)"
          by (rule finite_pattern_occurs_weight[OF True False])
        with head show False by simp
      next
        case fresh: False
        from "2.prems" False fresh
        have "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = None"
          by simp
        from "2.IH"(2)[OF False fresh this] tail show False
          by (simp add: finite_unifies_eliminate_iff[OF head])
      qed
    qed
  qed
qed auto

text \<open>
  The contract of the unifier: it returns a substitution exactly when the equations have a unifier
  of any variable type, and then its substitution unifies them, every unifier is its instance, it is
  idempotent, and it binds only variables of the equations to patterns over them.
\<close>

corollary finite_unify_pairs_none_iff:
  "finite_unify_pairs E = None \<longleftrightarrow> (\<forall>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. \<not> finite_unifies \<theta> E)"
proof
  assume "finite_unify_pairs E = None"
  then show "\<forall>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. \<not> finite_unifies \<theta> E"
    using finite_unify_pairs_none by blast
next
  assume none: "\<forall>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. \<not> finite_unifies \<theta> E"
  show "finite_unify_pairs E = None"
  proof (rule ccontr)
    assume "finite_unify_pairs E \<noteq> None"
    then obtain s where "finite_unify_pairs E = Some s" by auto
    then have "finite_unifies (finite_binding_substitution s) E" by (rule finite_unify_pairs_sound)
    then have "finite_unifies (\<lambda>b. finite_pattern_substitute
        (\<lambda>_. Finite_Pattern_Payload [] :: 'b finite_term_pattern) (finite_binding_substitution s b)) E"
      by (rule finite_unifies_compose)
    with none show False by blast
  qed
qed

theorem finite_unify_pairs_unifiers:
  assumes "finite_unify_pairs E = Some s"
  shows "finite_unifies \<theta> E \<longleftrightarrow>
    (\<exists>\<delta>. \<theta> = (\<lambda>b. finite_pattern_substitute \<delta> (finite_binding_substitution s b)))"
proof
  assume unified: "finite_unifies \<theta> E"
  have "\<theta> = (\<lambda>b. finite_pattern_substitute \<theta> (finite_binding_substitution s b))"
    using finite_unify_pairs_most_general[OF assms unified] by (simp add: fun_eq_iff)
  then show "\<exists>\<delta>. \<theta> = (\<lambda>b. finite_pattern_substitute \<delta> (finite_binding_substitution s b))" by blast
next
  assume "\<exists>\<delta>. \<theta> = (\<lambda>b. finite_pattern_substitute \<delta> (finite_binding_substitution s b))"
  then show "finite_unifies \<theta> E"
    using finite_unifies_compose[OF finite_unify_pairs_sound[OF assms]] by blast
qed

corollary finite_unify_pairs_idempotent:
  assumes "finite_unify_pairs E = Some s"
  shows "finite_pattern_substitute (finite_binding_substitution s) (finite_binding_substitution s b) =
    finite_binding_substitution s b"
  by (rule finite_unify_pairs_most_general[OF assms finite_unify_pairs_sound[OF assms]])

corollary finite_unify_pairs_idempotent_pattern:
  assumes "finite_unify_pairs E = Some s"
  shows "finite_pattern_substitute (finite_binding_substitution s)
      (finite_pattern_substitute (finite_binding_substitution s) p) =
    finite_pattern_substitute (finite_binding_substitution s) p"
  by (rule finite_pattern_substitute_factor[OF finite_unify_pairs_idempotent[OF assms]])

corollary decode_finite_unify_pairs_sound:
  assumes "finite_unify_pairs E = Some s" "x \<in> set E"
  shows "pattern_substitute (decode_finite_pattern \<circ> finite_binding_substitution s) (decode_finite_pattern (fst x)) =
    pattern_substitute (decode_finite_pattern \<circ> finite_binding_substitution s) (decode_finite_pattern (snd x))"
  using finite_unify_pairs_sound[OF assms(1)] assms(2)
  unfolding decode_finite_pattern_substitute[symmetric] finite_unifies_def by simp

lemma finite_binding_substitution_variables:
  "fset (finite_pattern_variables (finite_pattern_substitute (finite_binding_substitution s) p)) \<subseteq>
    fset (finite_pattern_variables p) \<union> (\<Union>x\<in>set s. fset (finite_pattern_variables (snd x)))"
proof (induction p)
  case (Finite_Variable b)
  show ?case
  proof (cases "map_of s b")
    case (Some t)
    then have "(b,t) \<in> set s" by (rule map_of_SomeD)
    with Some show ?thesis by (force simp: finite_binding_substitution_def)
  qed (simp add: finite_binding_substitution_def)
qed auto

theorem finite_unify_pairs_variables:
  assumes "finite_unify_pairs E = Some s"
  shows "\<forall>x\<in>set s. fst x \<in> finite_pairs_variables E \<and>
    fset (finite_pattern_variables (snd x)) \<subseteq> finite_pairs_variables E"
  using assms
proof (induction E arbitrary: s rule: finite_unify_pairs.induct)
  case (2 a q E s)
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1)[OF True] "2.prems" show ?thesis by fastforce
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False "2.prems" show ?thesis by simp
    next
      case fresh: False
      from "2.prems" False fresh obtain s' where
        rec: "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E) = Some s'" and
        s: "s = (a, finite_pattern_substitute (finite_binding_substitution s') q) # s'"
        by auto
      have image: "fset (finite_pattern_variables (finite_pattern_substitute (finite_binding_substitution s') q)) \<subseteq>
          fset (finite_pattern_variables q) \<union> (\<Union>x\<in>set s'. fset (finite_pattern_variables (snd x)))"
        by (rule finite_binding_substitution_variables)
      from "2.IH"(2)[OF False fresh rec] finite_pairs_eliminate_variables[OF fresh, of E] image
      show ?thesis by (simp add: s) blast
    qed
  qed
qed (auto split: if_splits)

corollary finite_unify_pairs_outside:
  assumes "finite_unify_pairs E = Some s" "b \<notin> finite_pairs_variables E"
  shows "finite_binding_substitution s b = Finite_Variable b"
proof -
  from finite_unify_pairs_variables[OF assms(1)] assms(2) have "b \<notin> fst ` set s" by auto
  then have "map_of s b = None" by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: finite_binding_substitution_def)
qed

text \<open>Two patterns are unified as the list of their one equation.\<close>

definition finite_unify_patterns ::
    "'a finite_term_pattern \<Rightarrow> 'a finite_term_pattern \<Rightarrow> ('a \<times> 'a finite_term_pattern) list option" where
  "finite_unify_patterns p q = finite_unify_pairs [(p,q)]"

corollary finite_unify_patterns_contract:
  assumes "finite_unify_patterns p q = Some s"
  shows "finite_pattern_substitute (finite_binding_substitution s) p =
      finite_pattern_substitute (finite_binding_substitution s) q"
    and "finite_pattern_substitute \<theta> p = finite_pattern_substitute \<theta> q \<Longrightarrow>
      finite_pattern_substitute \<theta> (finite_binding_substitution s b) = \<theta> b"
  using finite_unify_pairs_sound[of "[(p,q)]" s] finite_unify_pairs_most_general[of "[(p,q)]" s \<theta> b] assms
  by (simp_all add: finite_unify_patterns_def)

corollary finite_unify_patterns_none_iff:
  "finite_unify_patterns p q = None \<longleftrightarrow>
    (\<forall>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. finite_pattern_substitute \<theta> p \<noteq> finite_pattern_substitute \<theta> q)"
  using finite_unify_pairs_none_iff[of "[(p,q)]"] by (simp add: finite_unify_patterns_def)

section \<open>The unifier does not depend on the names of variables\<close>

text \<open>
  Variables are compared for equality and nothing else: renaming them injectively renames the
  unifier's equations and its bindings alike, so no result depends on which variables were chosen.
\<close>

definition finite_pairs_rename :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a finite_pattern_pairs \<Rightarrow> 'b finite_pattern_pairs" where
  "finite_pairs_rename f E =
    map (\<lambda>x. (map_finite_term_pattern f (fst x), map_finite_term_pattern f (snd x))) E"

lemma finite_pairs_rename_simps [simp]:
  "finite_pairs_rename f [] = []"
  "finite_pairs_rename f (x # E) =
    (map_finite_term_pattern f (fst x), map_finite_term_pattern f (snd x)) # finite_pairs_rename f E"
  by (simp_all add: finite_pairs_rename_def)

definition finite_rename_bindings ::
    "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a finite_term_pattern) list \<Rightarrow> ('b \<times> 'b finite_term_pattern) list" where
  "finite_rename_bindings f s = map (\<lambda>x. (f (fst x), map_finite_term_pattern f (snd x))) s"

lemma finite_rename_bindings_simps [simp]:
  "finite_rename_bindings f [] = []"
  "finite_rename_bindings f (x # s) = (f (fst x), map_finite_term_pattern f (snd x)) # finite_rename_bindings f s"
  by (simp_all add: finite_rename_bindings_def)

lemma finite_rename_binding_substitution:
  assumes "inj f"
  shows "finite_binding_substitution (finite_rename_bindings f s) (f b) =
    map_finite_term_pattern f (finite_binding_substitution s b)"
  by (induction s) (simp_all add: inj_eq[OF assms])

lemma finite_pairs_substitute_rename:
  assumes "\<And>b. \<tau> (f b) = map_finite_term_pattern f (\<sigma> b)"
  shows "finite_pairs_substitute \<tau> (finite_pairs_rename f E) =
    finite_pairs_rename f (finite_pairs_substitute \<sigma> E)"
  by (induction E) (simp_all add: finite_pattern_substitute_rename[where \<tau>=\<tau> and f=f and \<sigma>=\<sigma>, OF assms])

lemma finite_rename_substitution:
  assumes "inj f"
  shows "finite_pattern_substitute (finite_binding_substitution (finite_rename_bindings f s))
      (map_finite_term_pattern f p) =
    map_finite_term_pattern f (finite_pattern_substitute (finite_binding_substitution s) p)"
  by (rule finite_pattern_substitute_rename) (rule finite_rename_binding_substitution[OF assms])

theorem finite_unify_pairs_rename:
  assumes "inj f"
  shows "finite_unify_pairs (finite_pairs_rename f E) =
    map_option (finite_rename_bindings f) (finite_unify_pairs E)"
proof (induction E rule: finite_unify_pairs.induct)
  case (2 a q E)
  have var: "map_finite_term_pattern f q = Finite_Variable (f a) \<longleftrightarrow> q = Finite_Variable a"
    by (cases q) (simp_all add: inj_eq[OF assms])
  have occurs: "f a |\<in>| finite_pattern_variables (map_finite_term_pattern f q) \<longleftrightarrow>
      a |\<in>| finite_pattern_variables q"
    by (simp add: finite_pattern_variables_map fimage.rep_eq inj_image_mem_iff[OF assms])
  have eliminate: "finite_pairs_substitute (finite_eliminator (f a) (map_finite_term_pattern f q))
      (finite_pairs_rename f E) = finite_pairs_rename f (finite_pairs_substitute (finite_eliminator a q) E)"
    by (rule finite_pairs_substitute_rename) (simp add: inj_eq[OF assms])
  show ?case
  proof (cases "q = Finite_Variable a")
    case True
    with "2.IH"(1) show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "a |\<in>| finite_pattern_variables q")
      case True
      with False var occurs show ?thesis by simp
    next
      case fresh: False
      show ?thesis
        by (cases "finite_unify_pairs (finite_pairs_substitute (finite_eliminator a q) E)")
          (simp_all add: False fresh var occurs eliminate "2.IH"(2)[OF False fresh]
            finite_rename_substitution[OF assms])
    qed
  qed
qed simp_all

section \<open>Renaming apart by derivation position\<close>

text \<open>
  A clause's variables at a derivation position @{term w} become the pair of the position and the
  variable. The renaming is injective, patterns renamed at distinct positions share no variable, and
  by the equivariance above the unifier of renamed equations is the renamed unifier. The type of
  positions is a parameter, chosen by the evaluator that renames.
\<close>

definition finite_rename_apart :: "'w \<Rightarrow> 'a finite_term_pattern \<Rightarrow> ('w \<times> 'a) finite_term_pattern" where
  "finite_rename_apart w = map_finite_term_pattern (Pair w)"

lemma finite_rename_apart_inj: "inj (finite_rename_apart w)"
  unfolding finite_rename_apart_def by (rule finite_term_pattern.inj_map) (simp add: inj_def)

lemma finite_rename_apart_variables:
  "finite_pattern_variables (finite_rename_apart w p) = Pair w |`| finite_pattern_variables p"
  by (simp add: finite_rename_apart_def finite_pattern_variables_map)

lemma finite_rename_apart_disjoint:
  assumes "w \<noteq> w'"
  shows "fset (finite_pattern_variables (finite_rename_apart w p)) \<inter>
    fset (finite_pattern_variables (finite_rename_apart w' q)) = {}"
  using assms by (auto simp: finite_rename_apart_variables fimage.rep_eq)

lemma decode_finite_rename_apart:
  "decode_finite_pattern (finite_rename_apart w p) = rename_pattern (Pair w) (decode_finite_pattern p)"
  by (simp add: finite_rename_apart_def decode_finite_pattern_map)

corollary finite_unify_pairs_rename_apart:
  "finite_unify_pairs (finite_pairs_rename (Pair w) E) =
    map_option (finite_rename_bindings (Pair w)) (finite_unify_pairs E)"
  by (rule finite_unify_pairs_rename) (simp add: inj_def)

section \<open>A ground substitution presents bindings\<close>

text \<open>
  A substitution whose images are ground is a map of variables to terms. Its graph over a set of
  variables is a binding table, formed where its terms are, and under it a pattern whose variables it
  covers has as its instance exactly the term its substitution presents: the lemma by which a
  certificate's bindings are read from a ground unifier.
\<close>

lemma finite_exact_term_pattern_eq_iff [simp]:
  "finite_exact_term_pattern t = finite_exact_term_pattern u \<longleftrightarrow> t = u"
  by (induction t arbitrary: u; case_tac u; simp)

lemma finite_exact_term_pattern_variables [simp]:
  "finite_pattern_variables (finite_exact_term_pattern t) = {||}"
  by (induction t) simp_all

lemma finite_ground_pattern:
  "finite_pattern_variables q = {||} \<longleftrightarrow> (\<exists>t. q = finite_exact_term_pattern t)"
proof
  assume "finite_pattern_variables q = {||}"
  then show "\<exists>t. q = finite_exact_term_pattern t"
  proof (induction q)
    case (Finite_Pattern_Target x)
    have "Finite_Pattern_Target x = finite_exact_term_pattern (Finite_Target x)" by simp
    then show ?case by blast
  next
    case (Finite_Pattern_Payload v)
    have "Finite_Pattern_Payload v = finite_exact_term_pattern (Finite_Payload v)" by simp
    then show ?case by blast
  next
    case (Finite_Pattern_Pair p q)
    then obtain t u where "p = finite_exact_term_pattern t" "q = finite_exact_term_pattern u" by auto
    then have "Finite_Pattern_Pair p q = finite_exact_term_pattern (Finite_Pair t u)" by simp
    then show ?case by blast
  qed simp
next
  assume "\<exists>t. q = finite_exact_term_pattern t"
  then show "finite_pattern_variables q = {||}" by auto
qed

definition finite_ground_bindings ::
    "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a fset \<Rightarrow> ('a \<times> finite_factor_term) fset" where
  "finite_ground_bindings \<tau> B = (\<lambda>a. (a, \<tau> a)) |`| B"

lemma finite_ground_bindings_member [simp]:
  "(a,t) |\<in>| finite_ground_bindings \<tau> B \<longleftrightarrow> a |\<in>| B \<and> t = \<tau> a"
  by (auto simp: finite_ground_bindings_def fimage.rep_eq)

lemma finite_ground_bindings_formed:
  assumes "\<And>a. a |\<in>| B \<Longrightarrow> finite_term_formed (\<tau> a)"
  shows "finite_term_bindings_formed B (finite_ground_bindings \<tau> B)"
  using assms by (auto simp: finite_term_bindings_formed_def finite_relation_functional_def
      finite_ground_bindings_def fimage.rep_eq fset.map_comp comp_def)

theorem finite_ground_substitution_instance:
  assumes "fset (finite_pattern_variables p) \<subseteq> fset B"
  shows "finite_pattern_instance (finite_ground_bindings \<tau> B) p t \<longleftrightarrow>
    finite_pattern_formed p \<and>
    finite_exact_term_pattern t = finite_pattern_substitute (finite_exact_term_pattern \<circ> \<tau>) p"
  using assms
proof (induction p arbitrary: t)
  case (Finite_Variable a)
  then show ?case by auto
next
  case (Finite_Pattern_Target x)
  then show ?case by (cases t) auto
next
  case (Finite_Pattern_Payload v)
  then show ?case by (cases t) auto
next
  case (Finite_Pattern_Pair p q)
  from Finite_Pattern_Pair.prems have "fset (finite_pattern_variables p) \<subseteq> fset B"
    "fset (finite_pattern_variables q) \<subseteq> fset B" by auto
  with Finite_Pattern_Pair.IH show ?case by (cases t) auto
qed

corollary finite_ground_substitution_pattern_instance:
  assumes "fset (finite_pattern_variables p) \<subseteq> fset B"
  shows "pattern_instance (decode_finite_term_bindings (finite_ground_bindings \<tau> B))
      (decode_finite_pattern p) (decode_finite_term t) \<longleftrightarrow>
    finite_pattern_formed p \<and>
    finite_exact_term_pattern t = finite_pattern_substitute (finite_exact_term_pattern \<circ> \<tau>) p"
  by (simp add: finite_pattern_instance_correct[symmetric] finite_ground_substitution_instance[OF assms])

end
