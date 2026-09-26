theory Factor_Shared_Patterns
  imports Factor_Pattern_Unification Shared_Term_Tables
begin

section \<open>Patterns whose ground subterms are references into a shared-term table\<close>

text \<open>
  Build F2a of DECISIONS.md, task 495's entry, its addition "The resolver at the given's size". A search's
  patterns are clause-sized skeletons of variables and pairs, and their size is in their ground subterms,
  the environment values they hold. A \emph{shared pattern} is such a skeleton whose every ground subterm
  it marks as ground is a reference into a shared-term table (@{text Shared_Term_Tables}), and whose every
  pair caches its variable set. It is \emph{formed} over a table when its references are the table's and
  every cache is what it caches, and its \emph{projection} decodes its references to their exact patterns
  and forgets its caches. Formation is established by the constructors that make a shared pattern and kept
  by substitution and unification; it is never checked again.

  Every operation here is a refinement: equal over the projection to the operation of
  @{text Factor_Pattern_Unification} (R2). Substitution reads the caches and returns unchanged a subterm
  none of whose variables it binds; unification compares two references as numbers, which the table's
  canonicity makes exact (@{thm [source] shared_canonical_equality}), and descends a reference against a
  pair through the table's view (@{thm [source] shared_view_decode}); it reads the table and never
  changes it. The table is extended as ground terms are made (@{text share_pattern}, @{text share_node}),
  by the table's own first-occurrence step, and every earlier reference decodes as before
  (@{thm [source] share_term_preserves}). No reference is presented or compared across two tables.
\<close>

datatype 'a shared_pattern =
  Shared_Variable 'a
| Shared_Ground nat
| Shared_Node "'a fset" "'a shared_pattern" "'a shared_pattern"

fun shared_pattern_variables :: "'a shared_pattern \<Rightarrow> 'a fset" where
  "shared_pattern_variables (Shared_Variable a) = {|a|}"
| "shared_pattern_variables (Shared_Ground i) = {||}"
| "shared_pattern_variables (Shared_Node A p q) = A"

definition shared_node :: "'a shared_pattern \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "shared_node p q = Shared_Node (shared_pattern_variables p |\<union>| shared_pattern_variables q) p q"

fun shared_pattern_formed :: "shape list \<Rightarrow> 'a shared_pattern \<Rightarrow> bool" where
  "shared_pattern_formed T (Shared_Variable a) \<longleftrightarrow> True"
| "shared_pattern_formed T (Shared_Ground i) \<longleftrightarrow> i < length T"
| "shared_pattern_formed T (Shared_Node A p q) \<longleftrightarrow>
    A = shared_pattern_variables p |\<union>| shared_pattern_variables q \<and>
    shared_pattern_formed T p \<and> shared_pattern_formed T q"

fun shared_pattern_project :: "shape list \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a finite_term_pattern" where
  "shared_pattern_project T (Shared_Variable a) = Finite_Variable a"
| "shared_pattern_project T (Shared_Ground i) =
    (case reference_term T i of Some t \<Rightarrow> finite_exact_term_pattern t | None \<Rightarrow> Finite_Pattern_Payload [])"
| "shared_pattern_project T (Shared_Node A p q) =
    Finite_Pattern_Pair (shared_pattern_project T p) (shared_pattern_project T q)"

text \<open>A ground reference is a canonical shared term of the table, and so decodes over a formed table.\<close>

lemma shared_ground_canonical:
  "shared_pattern_formed T (Shared_Ground i) \<longleftrightarrow> shared_canonical T (Shared_Reference i)"
  by simp

lemma finite_exact_term_pattern_not_variable [simp]: "finite_exact_term_pattern t \<noteq> Finite_Variable a"
  by (cases t) simp_all

lemma shared_pattern_variables_project:
  "shared_pattern_formed T p \<Longrightarrow> shared_pattern_variables p = finite_pattern_variables (shared_pattern_project T p)"
  by (induction p) (auto split: option.splits)

lemma shared_pattern_project_variable [simp]:
  "shared_pattern_project T q = Finite_Variable a \<longleftrightarrow> q = Shared_Variable a"
  by (cases q) (auto split: option.splits)

lemma shared_node_fields [simp]:
  "shared_pattern_variables (shared_node p q) = shared_pattern_variables p |\<union>| shared_pattern_variables q"
  "shared_pattern_project T (shared_node p q) =
    Finite_Pattern_Pair (shared_pattern_project T p) (shared_pattern_project T q)"
  "shared_pattern_formed T (shared_node p q) \<longleftrightarrow> shared_pattern_formed T p \<and> shared_pattern_formed T q"
  by (simp_all add: shared_node_def)

section \<open>Substitution stops at what it does not bind\<close>

text \<open>
  A substitution is given with a finite set of variables outside which it is the identity. It returns a
  pair whose cached variables it does not bind as it stands, reading only the cache.
\<close>

fun shared_substitute ::
    "('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "shared_substitute \<sigma> D (Shared_Variable a) = \<sigma> a"
| "shared_substitute \<sigma> D (Shared_Ground i) = Shared_Ground i"
| "shared_substitute \<sigma> D (Shared_Node A p q) =
    (if A |\<inter>| D = {||} then Shared_Node A p q
     else shared_node (shared_substitute \<sigma> D p) (shared_substitute \<sigma> D q))"

lemma shared_substitute_formed:
  assumes "shared_pattern_formed T p" "\<And>a. shared_pattern_formed T (\<sigma> a)"
  shows "shared_pattern_formed T (shared_substitute \<sigma> D p)"
  using assms by (induction p) auto

theorem shared_substitute_project:
  assumes formed: "shared_pattern_formed T p" and outside: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_pattern_project T (shared_substitute \<sigma> D p) =
    finite_pattern_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_pattern_project T p)"
  using formed
proof (induction p)
  case (Shared_Variable a)
  then show ?case by simp
next
  case (Shared_Ground i)
  have "finite_pattern_substitute s (finite_exact_term_pattern t) = finite_exact_term_pattern t"
    for s :: "'a \<Rightarrow> 'a finite_term_pattern" and t by (induction t) simp_all
  then show ?case by (simp split: option.splits)
next
  case (Shared_Node A p q)
  show ?case
  proof (cases "A |\<inter>| D = {||}")
    case True
    have kept: "finite_pattern_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_pattern_project T r) =
        shared_pattern_project T r"
      if formed_r: "shared_pattern_formed T r" and inside: "\<And>a. a |\<in>| shared_pattern_variables r \<Longrightarrow> a |\<in>| A"
      for r
    proof -
      have "finite_pattern_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_pattern_project T r) =
          finite_pattern_substitute Finite_Variable (shared_pattern_project T r)"
      proof (rule finite_pattern_substitute_cong)
        fix a
        assume "a |\<in>| finite_pattern_variables (shared_pattern_project T r)"
        then have "a |\<in>| A" using inside shared_pattern_variables_project[OF formed_r] by simp
        then have "a |\<notin>| D" using True by (metis finter_iff fempty_iff)
        then show "shared_pattern_project T (\<sigma> a) = Finite_Variable a" using outside by simp
      qed
      then show ?thesis by simp
    qed
    have "A = shared_pattern_variables p |\<union>| shared_pattern_variables q" using Shared_Node.prems by simp
    then show ?thesis using True Shared_Node.prems kept[of p] kept[of q] by auto
  next
    case False
    then show ?thesis using Shared_Node by simp
  qed
qed

subsection \<open>Substitution by a list of bindings\<close>

definition shared_binding_substitution :: "('a \<times> 'a shared_pattern) list \<Rightarrow> 'a \<Rightarrow> 'a shared_pattern" where
  "shared_binding_substitution s a = (case map_of s a of None \<Rightarrow> Shared_Variable a | Some p \<Rightarrow> p)"

definition shared_binding_domain :: "('a \<times> 'a shared_pattern) list \<Rightarrow> 'a fset" where
  "shared_binding_domain s = fset_of_list (map fst s)"

definition shared_bindings_project ::
    "shape list \<Rightarrow> ('a \<times> 'a shared_pattern) list \<Rightarrow> ('a \<times> 'a finite_term_pattern) list" where
  "shared_bindings_project T s = map (\<lambda>(a,p). (a, shared_pattern_project T p)) s"

definition shared_bindings_formed :: "shape list \<Rightarrow> ('a \<times> 'a shared_pattern) list \<Rightarrow> bool" where
  "shared_bindings_formed T s \<longleftrightarrow> (\<forall>x\<in>set s. shared_pattern_formed T (snd x))"

lemma shared_bindings_simps [simp]:
  "shared_bindings_project T [] = []"
  "shared_bindings_project T ((a,p) # s) = (a, shared_pattern_project T p) # shared_bindings_project T s"
  "shared_bindings_formed T []"
  "shared_bindings_formed T ((a,p) # s) \<longleftrightarrow> shared_pattern_formed T p \<and> shared_bindings_formed T s"
  by (simp_all add: shared_bindings_project_def shared_bindings_formed_def)

lemma shared_binding_substitution_outside:
  "a |\<notin>| shared_binding_domain s \<Longrightarrow> shared_binding_substitution s a = Shared_Variable a"
  by (cases "map_of s a")
    (force simp: shared_binding_domain_def shared_binding_substitution_def fset_of_list.rep_eq dest: map_of_SomeD)+

lemma shared_binding_substitution_formed:
  "shared_bindings_formed T s \<Longrightarrow> shared_pattern_formed T (shared_binding_substitution s a)"
  by (fastforce simp: shared_bindings_formed_def shared_binding_substitution_def split: option.splits
      dest: map_of_SomeD)

lemma shared_binding_substitution_project:
  "shared_pattern_project T (shared_binding_substitution s a) =
    finite_binding_substitution (shared_bindings_project T s) a"
  by (simp add: shared_binding_substitution_def finite_binding_substitution_def shared_bindings_project_def
      map_of_map split: option.splits)

subsection \<open>Equations and the eliminator\<close>

type_synonym 'a shared_pattern_pairs = "('a shared_pattern \<times> 'a shared_pattern) list"

definition shared_pairs_project :: "shape list \<Rightarrow> 'a shared_pattern_pairs \<Rightarrow> 'a finite_pattern_pairs" where
  "shared_pairs_project T E =
    map (\<lambda>x. (shared_pattern_project T (fst x), shared_pattern_project T (snd x))) E"

definition shared_pairs_substitute ::
    "('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow> 'a shared_pattern_pairs \<Rightarrow> 'a shared_pattern_pairs" where
  "shared_pairs_substitute \<sigma> D E =
    map (\<lambda>x. (shared_substitute \<sigma> D (fst x), shared_substitute \<sigma> D (snd x))) E"

definition shared_pairs_formed :: "shape list \<Rightarrow> 'a shared_pattern_pairs \<Rightarrow> bool" where
  "shared_pairs_formed T E \<longleftrightarrow> (\<forall>x\<in>set E. shared_pattern_formed T (fst x) \<and> shared_pattern_formed T (snd x))"

lemma shared_pairs_simps [simp]:
  "shared_pairs_project T [] = []"
  "shared_pairs_project T (x # E) =
    (shared_pattern_project T (fst x), shared_pattern_project T (snd x)) # shared_pairs_project T E"
  "shared_pairs_formed T []"
  "shared_pairs_formed T (x # E) \<longleftrightarrow>
    shared_pattern_formed T (fst x) \<and> shared_pattern_formed T (snd x) \<and> shared_pairs_formed T E"
  by (simp_all add: shared_pairs_project_def shared_pairs_formed_def)

lemma shared_pairs_substitute_project:
  assumes "shared_pairs_formed T E" and outside: "\<And>a. a |\<notin>| D \<Longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_pairs_project T (shared_pairs_substitute \<sigma> D E) =
    finite_pairs_substitute (\<lambda>a. shared_pattern_project T (\<sigma> a)) (shared_pairs_project T E)"
  using assms(1) by (induction E) (simp_all add: shared_pairs_substitute_def shared_substitute_project[OF _ outside])

lemma shared_pairs_substitute_formed:
  assumes "shared_pairs_formed T E" "\<And>a. shared_pattern_formed T (\<sigma> a)"
  shows "shared_pairs_formed T (shared_pairs_substitute \<sigma> D E)"
  using assms by (induction E) (simp_all add: shared_pairs_substitute_def shared_substitute_formed)

definition shared_eliminator :: "'a \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a \<Rightarrow> 'a shared_pattern" where
  "shared_eliminator a q b = (if b = a then q else Shared_Variable b)"

lemma shared_eliminator_project:
  "(\<lambda>b. shared_pattern_project T (shared_eliminator a q b)) = finite_eliminator a (shared_pattern_project T q)"
  by (auto simp: fun_eq_iff shared_eliminator_def)

section \<open>Unification descends a reference through the table's view\<close>

text \<open>
  A reference against a pair is read one level through the view of the table: the references of its two
  components, which stand at smaller positions.
\<close>

definition shared_ground_view :: "shape list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "shared_ground_view T i = (case shared_view T (Shared_Reference i) of
    Some (Pair_View (Shared_Reference j) (Shared_Reference k)) \<Rightarrow> Some (j, k) | _ \<Rightarrow> None)"

lemma shared_ground_view_pair:
  assumes decoded: "reference_term T i = Some (Finite_Pair u v)"
  obtains j k where "shared_ground_view T i = Some (j, k)" "reference_term T j = Some u" "reference_term T k = Some v"
proof -
  have "shared_decode T (Shared_Reference i) = Some (Finite_Pair u v)" using decoded by simp
  from shared_view_decode[OF this] obtain a b x y where view: "shared_view T (Shared_Reference i) = Some (Pair_View a b)"
      and ax: "shared_decode T a = Some x" and bx: "shared_decode T b = Some y" and xy: "Finite_Pair u v = Finite_Pair x y"
    by (auto simp del: shared_view.simps simp: leaf_term_not_pair)
  from view obtain j k where "a = Shared_Reference j" "b = Shared_Reference k"
    by (auto split: option.splits shape.splits)
  with view ax bx xy show ?thesis using that by (simp add: shared_ground_view_def)
qed

lemma shared_ground_view_leaf:
  assumes "reference_term T i = Some (leaf_term l)"
  shows "shared_ground_view T i = None"
  using reference_factor_leaf_read[OF assms] by (simp add: shared_ground_view_def)

text \<open>
  The unifier follows R2's transformations on the skeleton: an equation of two references is dropped when
  they are equal and fails otherwise, whatever the terms they hold; a reference against a pair descends one
  level; the occurs check reads the cache. Its recursion is R2's, so it is stated as a partial function
  whose equation holds unconditionally, and its equality to R2 over the projection shows it returns on
  every formed input.
\<close>

partial_function (option) shared_unify_pairs ::
    "shape list \<Rightarrow> 'a shared_pattern_pairs \<Rightarrow> ('a \<times> 'a shared_pattern) list option" where
  "shared_unify_pairs T E = (case E of
    [] \<Rightarrow> Some []
  | x # F \<Rightarrow> (case x of (p, q) \<Rightarrow> (case p of
      Shared_Variable a \<Rightarrow>
        (if q = Shared_Variable a then shared_unify_pairs T F
         else if a |\<in>| shared_pattern_variables q then None
         else Option.bind (shared_unify_pairs T (shared_pairs_substitute (shared_eliminator a q) {|a|} F))
           (\<lambda>s. Some ((a, shared_substitute (shared_binding_substitution s) (shared_binding_domain s) q) # s)))
    | Shared_Ground i \<Rightarrow> (case q of
        Shared_Variable b \<Rightarrow> shared_unify_pairs T ((Shared_Variable b, p) # F)
      | Shared_Ground j \<Rightarrow> (if i = j then shared_unify_pairs T F else None)
      | Shared_Node B p' q' \<Rightarrow> (case shared_ground_view T i of None \<Rightarrow> None
          | Some (j, k) \<Rightarrow> shared_unify_pairs T ((Shared_Ground j, p') # (Shared_Ground k, q') # F)))
    | Shared_Node A p1 q1 \<Rightarrow> (case q of
        Shared_Variable b \<Rightarrow> shared_unify_pairs T ((Shared_Variable b, p) # F)
      | Shared_Ground j \<Rightarrow> (case shared_ground_view T j of None \<Rightarrow> None
          | Some (k, l) \<Rightarrow> shared_unify_pairs T ((p1, Shared_Ground k) # (q1, Shared_Ground l) # F))
      | Shared_Node B p' q' \<Rightarrow> shared_unify_pairs T ((p1, p') # (q1, q') # F)))))"

subsection \<open>R2 at ground patterns\<close>

text \<open>
  R2 decomposes two exact patterns to their leaves: equal terms leave the remaining equations as they
  were, and different terms have no unifier. A pattern that is not a variable is turned around.
\<close>

lemma finite_unify_pairs_exact_equal:
  "finite_unify_pairs ((finite_exact_term_pattern t, finite_exact_term_pattern t) # E) = finite_unify_pairs E"
  by (induction t arbitrary: E) simp_all

lemma finite_unify_pairs_exact_differ:
  assumes "t \<noteq> u"
  shows "finite_unify_pairs ((finite_exact_term_pattern t, finite_exact_term_pattern u) # E) = None"
proof -
  have fixed: "finite_pattern_substitute \<theta> (finite_exact_term_pattern w) = finite_exact_term_pattern w"
    for \<theta> :: "'a \<Rightarrow> 'a finite_term_pattern" and w by (induction w) simp_all
  show ?thesis using assms by (simp add: finite_unify_pairs_none_iff[where 'b='a] fixed)
qed

lemma finite_unify_pairs_turn:
  assumes "\<And>b. p \<noteq> Finite_Variable b"
  shows "finite_unify_pairs ((p, Finite_Variable a) # E) = finite_unify_pairs ((Finite_Variable a, p) # E) \<and>
    finite_pairs_unoriented ((p, Finite_Variable a) # E) = 1"
  using assms by (cases p) auto

subsection \<open>The unifier is R2's over the projection\<close>

theorem shared_unify_pairs_exact:
  fixes E :: "'a shared_pattern_pairs"
  assumes table: "table_formed T" and formed: "shared_pairs_formed T E"
  shows "map_option (shared_bindings_project T) (shared_unify_pairs T E) =
      finite_unify_pairs (shared_pairs_project T E) \<and>
    (\<forall>s. shared_unify_pairs T E = Some s \<longrightarrow> shared_bindings_formed T s)"
proof -
  define R where "R = inv_image (finite_unify_order :: ('a finite_pattern_pairs \<times> 'a finite_pattern_pairs) set)
    (shared_pairs_project T)"
  define Q where "Q F \<longleftrightarrow> map_option (shared_bindings_project T) (shared_unify_pairs T F) =
      finite_unify_pairs (shared_pairs_project T F) \<and>
    (\<forall>s. shared_unify_pairs T F = Some s \<longrightarrow> shared_bindings_formed T s)" for F :: "'a shared_pattern_pairs"
  have wf: "wf R" unfolding R_def by (rule wf_inv_image) (rule wf_measures)
  have "Q E" using formed
  proof (induction E rule: wf_induct_rule[OF wf])
    fix E :: "'a shared_pattern_pairs"
    assume IH0: "\<And>F. (F, E) \<in> R \<Longrightarrow> shared_pairs_formed T F \<Longrightarrow> Q F"
      and prems: "shared_pairs_formed T E"
    have IH: "Q F" if "shared_pairs_formed T F"
      "(shared_pairs_project T F, shared_pairs_project T E) \<in> finite_unify_order" for F
      using IH0[of F] that by (simp add: R_def)
    have same: "Q E" if "shared_unify_pairs T E = shared_unify_pairs T F"
      "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T F)" "Q F" for F
      using that by (simp add: Q_def)
    have fails: "Q E" if "shared_unify_pairs T E = None" "finite_unify_pairs (shared_pairs_project T E) = None"
      using that by (simp add: Q_def)
    show "Q E"
    proof (cases E)
      case Nil
      have "shared_unify_pairs T E = Some []" by (rule trans[OF shared_unify_pairs.simps]) (simp add: Nil)
      then show ?thesis by (simp add: Q_def Nil)
    next
      case (Cons x E')
      obtain p q where x: "x = (p, q)" by (cases x)
      have fp: "shared_pattern_formed T p" and fq: "shared_pattern_formed T q" and fE': "shared_pairs_formed T E'"
        using prems Cons x by simp_all
      have drop: "(shared_pairs_project T E', shared_pairs_project T E) \<in> finite_unify_order"
        by (simp only: Cons x shared_pairs_simps(2)) (rule finite_unify_drop)
      show ?thesis
      proof (cases p)
        case (Shared_Variable a)
        note pv = Shared_Variable
        show ?thesis
        proof (cases "q = Shared_Variable a")
          case True
          show ?thesis
          proof (rule same[of E'])
            show "shared_unify_pairs T E = shared_unify_pairs T E'"
              by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pv True)
            show "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T E')"
              by (simp add: Cons x pv True)
            show "Q E'" by (rule IH[OF fE' drop])
          qed
        next
          case False
          have pq: "shared_pattern_project T q \<noteq> Finite_Variable a" using False by simp
          have vq: "shared_pattern_variables q = finite_pattern_variables (shared_pattern_project T q)"
            by (rule shared_pattern_variables_project[OF fq])
          show ?thesis
          proof (cases "a |\<in>| shared_pattern_variables q")
            case True
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pv False True)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                using True pq by (simp add: Cons x pv vq)
            qed
          next
            case fresh: False
            define E'' where "E'' = shared_pairs_substitute (shared_eliminator a q) {|a|} E'"
            have fresh': "a |\<notin>| finite_pattern_variables (shared_pattern_project T q)" using fresh vq by simp
            have outside: "\<And>b. b |\<notin>| {|a|} \<Longrightarrow> shared_eliminator a q b = Shared_Variable b"
              by (simp add: shared_eliminator_def)
            have pE'': "shared_pairs_project T E'' =
                finite_pairs_substitute (finite_eliminator a (shared_pattern_project T q)) (shared_pairs_project T E')"
              using shared_pairs_substitute_project[OF fE' outside] unfolding E''_def shared_eliminator_project .
            have fE'': "shared_pairs_formed T E''"
              unfolding E''_def by (rule shared_pairs_substitute_formed[OF fE']) (simp add: shared_eliminator_def fq)
            have QE'': "Q E''"
            proof (rule IH[OF fE''])
              show "(shared_pairs_project T E'', shared_pairs_project T E) \<in> finite_unify_order"
                using finite_unify_eliminate[OF fresh', of "shared_pairs_project T E'"]
                by (simp add: pE'' Cons x pv del: in_measures)
            qed
            have eq: "shared_unify_pairs T E = Option.bind (shared_unify_pairs T E'')
                (\<lambda>s. Some ((a, shared_substitute (shared_binding_substitution s) (shared_binding_domain s) q) # s))"
              by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pv False fresh E''_def)
            have req: "finite_unify_pairs (shared_pairs_project T E) =
                map_option (\<lambda>s. (a, finite_pattern_substitute (finite_binding_substitution s)
                  (shared_pattern_project T q)) # s) (finite_unify_pairs (shared_pairs_project T E''))"
              using pq fresh' by (simp add: Cons x pv pE'')
            show ?thesis
            proof (cases "shared_unify_pairs T E''")
              case None
              then show ?thesis using QE'' by (simp add: Q_def eq req)
            next
              case (Some s)
              have ps: "finite_unify_pairs (shared_pairs_project T E'') = Some (shared_bindings_project T s)"
                and fs: "shared_bindings_formed T s" using QE'' Some by (simp_all add: Q_def)
              have sub: "shared_pattern_project T
                  (shared_substitute (shared_binding_substitution s) (shared_binding_domain s) q) =
                finite_pattern_substitute (finite_binding_substitution (shared_bindings_project T s))
                  (shared_pattern_project T q)"
                using shared_substitute_project[OF fq shared_binding_substitution_outside]
                by (simp add: shared_binding_substitution_project)
              have fsub: "shared_pattern_formed T
                  (shared_substitute (shared_binding_substitution s) (shared_binding_domain s) q)"
                by (rule shared_substitute_formed[OF fq shared_binding_substitution_formed[OF fs]])
              show ?thesis using Some ps fs sub fsub by (simp add: Q_def eq req)
            qed
          qed
        qed
      next
        case (Shared_Ground i)
        note pg = Shared_Ground
        obtain t where ti: "reference_term T i = Some t"
          using table_formed_decodes[OF table] fp pg by auto
        have pt: "shared_pattern_project T p = finite_exact_term_pattern t" using ti pg by simp
        show ?thesis
        proof (cases q)
          case (Shared_Variable b)
          have turn: "finite_unify_pairs ((finite_exact_term_pattern t, Finite_Variable b) # shared_pairs_project T E') =
              finite_unify_pairs ((Finite_Variable b, finite_exact_term_pattern t) # shared_pairs_project T E') \<and>
            finite_pairs_unoriented ((finite_exact_term_pattern t, Finite_Variable b) # shared_pairs_project T E') = 1"
            by (rule finite_unify_pairs_turn) simp
          show ?thesis
          proof (rule same[of "(Shared_Variable b, p) # E'"])
            show "shared_unify_pairs T E = shared_unify_pairs T ((Shared_Variable b, p) # E')"
              by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg Shared_Variable)
            show "finite_unify_pairs (shared_pairs_project T E) =
                finite_unify_pairs (shared_pairs_project T ((Shared_Variable b, p) # E'))"
              using turn by (simp add: Cons x Shared_Variable pt)
            show "Q ((Shared_Variable b, p) # E')"
            proof (rule IH)
              show "shared_pairs_formed T ((Shared_Variable b, p) # E')" using fp fE' by simp
              show "(shared_pairs_project T ((Shared_Variable b, p) # E'), shared_pairs_project T E) \<in> finite_unify_order"
                using finite_unify_swap[of "finite_exact_term_pattern t" b "shared_pairs_project T E'"] turn
                by (simp add: Cons x Shared_Variable pt del: in_measures)
            qed
          qed
        next
          case (Shared_Ground j)
          note qg = Shared_Ground
          obtain u where uj: "reference_term T j = Some u"
            using table_formed_decodes[OF table] fq qg by auto
          have iff: "i = j \<longleftrightarrow> t = u" using reference_term_injective[OF table, of i t j] ti uj by auto
          show ?thesis
          proof (cases "i = j")
            case True
            show ?thesis
            proof (rule same[of E'])
              show "shared_unify_pairs T E = shared_unify_pairs T E'"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg qg True)
              show "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T E')"
                using True iff ti uj by (simp add: Cons x pg qg finite_unify_pairs_exact_equal)
              show "Q E'" by (rule IH[OF fE' drop])
            qed
          next
            case False
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg qg False)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                using False iff ti uj by (simp add: Cons x pg qg finite_unify_pairs_exact_differ)
            qed
          qed
        next
          case (Shared_Node B p' q')
          note qn = Shared_Node
          have fp': "shared_pattern_formed T p'" and fq': "shared_pattern_formed T q'" using fq qn by simp_all
          show ?thesis
          proof (cases t)
            case (Finite_Pair u v)
            obtain j k where view: "shared_ground_view T i = Some (j, k)"
                and uj: "reference_term T j = Some u" and vk: "reference_term T k = Some v"
              using shared_ground_view_pair[of T i u v] ti Finite_Pair by blast
            define F' where "F' = (Shared_Ground j, p') # (Shared_Ground k, q') # E'"
            show ?thesis
            proof (rule same[of F'])
              show "shared_unify_pairs T E = shared_unify_pairs T F'"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg qn view F'_def)
              show "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T F')"
                by (simp add: Cons x pg qn ti uj vk Finite_Pair F'_def)
              show "Q F'"
              proof (rule IH)
                show "shared_pairs_formed T F'"
                  using fp' fq' fE' reference_term_bound[OF uj] reference_term_bound[OF vk] by (simp add: F'_def)
                show "(shared_pairs_project T F', shared_pairs_project T E) \<in> finite_unify_order"
                  using finite_unify_pair[of "finite_exact_term_pattern u" "shared_pattern_project T p'"
                      "finite_exact_term_pattern v" "shared_pattern_project T q'" "shared_pairs_project T E'"]
                  by (simp add: Cons x pg qn ti uj vk Finite_Pair F'_def del: in_measures)
              qed
            qed
          next
            case (Finite_Target y)
            have view: "shared_ground_view T i = None"
              by (rule shared_ground_view_leaf[of T i "Target_Leaf y"]) (simp add: ti Finite_Target)
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg qn view)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                by (simp add: Cons x pg qn ti Finite_Target)
            qed
          next
            case (Finite_Payload y)
            have view: "shared_ground_view T i = None"
              by (rule shared_ground_view_leaf[of T i "Payload_Leaf y"]) (simp add: ti Finite_Payload)
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pg qn view)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                by (simp add: Cons x pg qn ti Finite_Payload)
            qed
          qed
        qed
      next
        case (Shared_Node A p1 q1)
        note pn = Shared_Node
        have fp1: "shared_pattern_formed T p1" and fq1: "shared_pattern_formed T q1" using fp pn by simp_all
        show ?thesis
        proof (cases q)
          case (Shared_Variable b)
          have turn: "finite_unify_pairs ((shared_pattern_project T p, Finite_Variable b) # shared_pairs_project T E') =
              finite_unify_pairs ((Finite_Variable b, shared_pattern_project T p) # shared_pairs_project T E') \<and>
            finite_pairs_unoriented ((shared_pattern_project T p, Finite_Variable b) # shared_pairs_project T E') = 1"
            by (rule finite_unify_pairs_turn) (simp add: pn)
          show ?thesis
          proof (rule same[of "(Shared_Variable b, p) # E'"])
            show "shared_unify_pairs T E = shared_unify_pairs T ((Shared_Variable b, p) # E')"
              by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pn Shared_Variable)
            show "finite_unify_pairs (shared_pairs_project T E) =
                finite_unify_pairs (shared_pairs_project T ((Shared_Variable b, p) # E'))"
              using turn by (simp add: Cons x Shared_Variable)
            show "Q ((Shared_Variable b, p) # E')"
            proof (rule IH)
              show "shared_pairs_formed T ((Shared_Variable b, p) # E')" using fp fE' by simp
              show "(shared_pairs_project T ((Shared_Variable b, p) # E'), shared_pairs_project T E) \<in> finite_unify_order"
                using finite_unify_swap[of "shared_pattern_project T p" b "shared_pairs_project T E'"] turn
                by (simp add: Cons x Shared_Variable del: in_measures)
            qed
          qed
        next
          case (Shared_Ground j)
          note qg = Shared_Ground
          obtain u where uj: "reference_term T j = Some u"
            using table_formed_decodes[OF table] fq qg by auto
          show ?thesis
          proof (cases u)
            case (Finite_Pair u1 u2)
            obtain k l where view: "shared_ground_view T j = Some (k, l)"
                and uk: "reference_term T k = Some u1" and ul: "reference_term T l = Some u2"
              using shared_ground_view_pair[of T j u1 u2] uj Finite_Pair by blast
            define F' where "F' = (p1, Shared_Ground k) # (q1, Shared_Ground l) # E'"
            show ?thesis
            proof (rule same[of F'])
              show "shared_unify_pairs T E = shared_unify_pairs T F'"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pn qg view F'_def)
              show "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T F')"
                by (simp add: Cons x pn qg uj uk ul Finite_Pair F'_def)
              show "Q F'"
              proof (rule IH)
                show "shared_pairs_formed T F'"
                  using fp1 fq1 fE' reference_term_bound[OF uk] reference_term_bound[OF ul] by (simp add: F'_def)
                show "(shared_pairs_project T F', shared_pairs_project T E) \<in> finite_unify_order"
                  using finite_unify_pair[of "shared_pattern_project T p1" "finite_exact_term_pattern u1"
                      "shared_pattern_project T q1" "finite_exact_term_pattern u2" "shared_pairs_project T E'"]
                  by (simp add: Cons x pn qg uj uk ul Finite_Pair F'_def del: in_measures)
              qed
            qed
          next
            case (Finite_Target y)
            have view: "shared_ground_view T j = None"
              by (rule shared_ground_view_leaf[of T j "Target_Leaf y"]) (simp add: uj Finite_Target)
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pn qg view)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                by (simp add: Cons x pn qg uj Finite_Target)
            qed
          next
            case (Finite_Payload y)
            have view: "shared_ground_view T j = None"
              by (rule shared_ground_view_leaf[of T j "Payload_Leaf y"]) (simp add: uj Finite_Payload)
            show ?thesis
            proof (rule fails)
              show "shared_unify_pairs T E = None"
                by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pn qg view)
              show "finite_unify_pairs (shared_pairs_project T E) = None"
                by (simp add: Cons x pn qg uj Finite_Payload)
            qed
          qed
        next
          case (Shared_Node B p' q')
          note qn = Shared_Node
          have fp': "shared_pattern_formed T p'" and fq': "shared_pattern_formed T q'" using fq qn by simp_all
          define F' where "F' = (p1, p') # (q1, q') # E'"
          show ?thesis
          proof (rule same[of F'])
            show "shared_unify_pairs T E = shared_unify_pairs T F'"
              by (rule trans[OF shared_unify_pairs.simps]) (simp add: Cons x pn qn F'_def)
            show "finite_unify_pairs (shared_pairs_project T E) = finite_unify_pairs (shared_pairs_project T F')"
              by (simp add: Cons x pn qn F'_def)
            show "Q F'"
            proof (rule IH)
              show "shared_pairs_formed T F'" using fp1 fq1 fp' fq' fE' by (simp add: F'_def)
              show "(shared_pairs_project T F', shared_pairs_project T E) \<in> finite_unify_order"
                using finite_unify_pair[of "shared_pattern_project T p1" "shared_pattern_project T p'"
                    "shared_pattern_project T q1" "shared_pattern_project T q'" "shared_pairs_project T E'"]
                by (simp add: Cons x pn qn F'_def del: in_measures)
            qed
          qed
        qed
      qed
    qed
  qed
  then show ?thesis by (simp add: Q_def)
qed

corollary shared_unify_pairs_project:
  assumes "table_formed T" "shared_pairs_formed T E"
  shows "map_option (shared_bindings_project T) (shared_unify_pairs T E) = finite_unify_pairs (shared_pairs_project T E)"
  using shared_unify_pairs_exact[OF assms] by simp

corollary shared_unify_pairs_formed:
  assumes "table_formed T" "shared_pairs_formed T E" "shared_unify_pairs T E = Some s"
  shows "shared_bindings_formed T s"
  using shared_unify_pairs_exact[OF assms(1,2)] assms(3) by simp

corollary shared_unify_pairs_none_iff:
  assumes "table_formed T" "shared_pairs_formed T E"
  shows "shared_unify_pairs T E = None \<longleftrightarrow> finite_unify_pairs (shared_pairs_project T E) = None"
  using shared_unify_pairs_project[OF assms, symmetric] by simp

text \<open>Two patterns are unified as the list of their one equation, as R2 unifies them.\<close>

definition shared_unify_patterns ::
    "shape list \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a shared_pattern \<Rightarrow> ('a \<times> 'a shared_pattern) list option" where
  "shared_unify_patterns T p q = shared_unify_pairs T [(p, q)]"

corollary shared_unify_patterns_project:
  assumes "table_formed T" "shared_pattern_formed T p" "shared_pattern_formed T q"
  shows "map_option (shared_bindings_project T) (shared_unify_patterns T p q) =
    finite_unify_patterns (shared_pattern_project T p) (shared_pattern_project T q)"
  using shared_unify_pairs_project[OF assms(1), of "[(p, q)]"] assms(2,3)
  by (simp add: shared_unify_patterns_def finite_unify_patterns_def)

section \<open>The table extended as ground terms are made\<close>

text \<open>
  Whatever keeps every decoded reference keeps every shared pattern formed and its projection unchanged;
  the table's sharing is such an extension (@{thm [source] share_term_preserves}). Two ground references
  of a formed table are equal exactly when their projections are: they are canonical shared terms.
\<close>

lemma shared_pattern_extended:
  assumes table: "table_formed T" and formed: "shared_pattern_formed T p"
    and decodes: "\<And>i u. reference_term T i = Some u \<Longrightarrow> reference_term T' i = Some u"
  shows "shared_pattern_formed T' p \<and> shared_pattern_project T' p = shared_pattern_project T p"
  using formed
proof (induction p)
  case (Shared_Ground i)
  obtain t where t: "reference_term T i = Some t" using table_formed_decodes[OF table] Shared_Ground by auto
  have t': "reference_term T' i = Some t" by (rule decodes[OF t])
  show ?case using t t' reference_term_bound[OF t'] by simp
qed auto

theorem shared_pattern_share_term:
  assumes "table_formed T" "shared_pattern_formed T p"
  shows "shared_pattern_formed (snd (share_term t T)) p \<and>
    shared_pattern_project (snd (share_term t T)) p = shared_pattern_project T p"
  by (rule shared_pattern_extended[OF assms share_term_preserves])

theorem shared_ground_equality:
  assumes table: "table_formed T"
    and i: "shared_pattern_formed T (Shared_Ground i)" and j: "shared_pattern_formed T (Shared_Ground j)"
  shows "i = j \<longleftrightarrow> shared_pattern_project T (Shared_Ground i) = shared_pattern_project T (Shared_Ground j)"
proof -
  have canonical: "Shared_Reference i = Shared_Reference j \<longleftrightarrow>
      shared_decode T (Shared_Reference i) = shared_decode T (Shared_Reference j)"
    by (rule shared_canonical_equality[OF table]) (use i j in simp_all)
  obtain t u where "reference_term T i = Some t" "reference_term T j = Some u"
    using table_formed_decodes[OF table] i j by fastforce
  then show ?thesis using canonical by simp
qed

subsection \<open>Making ground terms\<close>

text \<open>
  Two ground references make a ground pair by the table's first-occurrence step: the pair's reference
  where the table holds its shape, else the shape appended. Any other two patterns make a node. A plain
  pattern is shared by making its leaves and pairs so, and a ground pattern is exactly the table's sharing
  of its term (@{text share_pattern_exact_term}).
\<close>

fun share_node :: "'a shared_pattern \<Rightarrow> 'a shared_pattern \<Rightarrow> shape list \<Rightarrow> 'a shared_pattern \<times> shape list" where
  "share_node (Shared_Ground i) (Shared_Ground j) T =
    (case value_reference_step (Pair_Shape i j) T of (k, T') \<Rightarrow> (Shared_Ground k, T'))"
| "share_node p q T = (shared_node p q, T)"

lemma share_node_exact:
  assumes table: "table_formed T" and p: "shared_pattern_formed T p" and q: "shared_pattern_formed T q"
  shows "table_formed (snd (share_node p q T)) \<and>
    shared_pattern_formed (snd (share_node p q T)) (fst (share_node p q T)) \<and>
    shared_pattern_project (snd (share_node p q T)) (fst (share_node p q T)) =
      Finite_Pattern_Pair (shared_pattern_project T p) (shared_pattern_project T q) \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term (snd (share_node p q T)) i = Some u)"
proof (cases "\<exists>i j. p = Shared_Ground i \<and> q = Shared_Ground j")
  case True
  then obtain i j where pi: "p = Shared_Ground i" and qj: "q = Shared_Ground j" by blast
  obtain u where u: "reference_term T i = Some u" using table_formed_decodes[OF table] p pi by auto
  obtain v where v: "reference_term T j = Some v" using table_formed_decodes[OF table] q qj by auto
  obtain k T' where step: "value_reference_step (Pair_Shape i j) T = (k, T')"
    by (cases "value_reference_step (Pair_Shape i j) T")
  have f': "table_formed T'"
    using share_step_formed[OF table, of "Pair_Shape i j"] p q pi qj step by simp
  have read: "value_reference_read T' k = Some (Pair_Shape i j)"
    using value_reference_step_exact[of "Pair_Shape i j" T] step by simp
  have ordered: "i < k" "j < k" using f' read by (auto simp: table_formed_def)
  have reads: "value_reference_read T' n = Some s" if "value_reference_read T n = Some s" for n s
    using value_reference_step_preserves[OF that, of "Pair_Shape i j"] step by simp
  have keep: "reference_term T' n = Some w" if "reference_term T n = Some w" for n w
    by (rule reference_term_preserved[OF reads that])
  have k: "reference_term T' k = Some (Finite_Pair u v)"
    using reference_term_pair[OF read ordered] keep[OF u] keep[OF v] by (simp add: pair_decoded_def)
  show ?thesis using f' k keep reference_term_bound[OF k] u v by (simp add: pi qj step)
next
  case False
  then have "share_node p q T = (shared_node p q, T)" by (cases p; cases q) auto
  then show ?thesis using table p q by simp
qed

fun share_pattern :: "'a finite_term_pattern \<Rightarrow> shape list \<Rightarrow> 'a shared_pattern \<times> shape list" where
  "share_pattern (Finite_Variable a) T = (Shared_Variable a, T)"
| "share_pattern (Finite_Pattern_Target t) T =
    (case share_term (Finite_Target t) T of (i, T') \<Rightarrow> (Shared_Ground i, T'))"
| "share_pattern (Finite_Pattern_Payload v) T =
    (case share_term (Finite_Payload v) T of (i, T') \<Rightarrow> (Shared_Ground i, T'))"
| "share_pattern (Finite_Pattern_Pair p q) T = (case share_pattern p T of (p', T1) \<Rightarrow>
    (case share_pattern q T1 of (q', T2) \<Rightarrow> share_node p' q' T2))"

lemma share_leaf_pattern:
  assumes table: "table_formed T" and leaf: "l = Finite_Target t \<or> l = Finite_Payload v"
  shows "table_formed (snd (share_term l T)) \<and>
    shared_pattern_formed (snd (share_term l T)) (Shared_Ground (fst (share_term l T)) :: 'a shared_pattern) \<and>
    (shared_pattern_project (snd (share_term l T)) (Shared_Ground (fst (share_term l T))) :: 'a finite_term_pattern) =
      finite_exact_term_pattern l \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term (snd (share_term l T)) i = Some u)"
proof -
  have exact: "table_formed (snd (share_term l T))" "reference_term (snd (share_term l T)) (fst (share_term l T)) = Some l"
    using share_term_exact[OF table, of l] by simp_all
  show ?thesis using exact reference_term_bound[OF exact(2)] share_term_preserves[of T _ _ l] by simp
qed

theorem share_pattern_exact:
  "table_formed T \<Longrightarrow> table_formed (snd (share_pattern p T)) \<and>
    shared_pattern_formed (snd (share_pattern p T)) (fst (share_pattern p T)) \<and>
    shared_pattern_project (snd (share_pattern p T)) (fst (share_pattern p T)) = p \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term (snd (share_pattern p T)) i = Some u)"
proof (induction p arbitrary: T)
  case (Finite_Variable a)
  then show ?case by simp
next
  case (Finite_Pattern_Target t)
  show ?case using share_leaf_pattern[OF Finite_Pattern_Target.prems, of "Finite_Target t" t "[]", where 'a='a]
    by (simp add: case_prod_unfold)
next
  case (Finite_Pattern_Payload v)
  show ?case using share_leaf_pattern[OF Finite_Pattern_Payload.prems, of "Finite_Payload v" undefined v, where 'a='a]
    by (simp add: case_prod_unfold)
next
  case (Finite_Pattern_Pair p q)
  obtain p' T1 where s1: "share_pattern p T = (p', T1)" by (cases "share_pattern p T")
  obtain q' T2 where s2: "share_pattern q T1 = (q', T2)" by (cases "share_pattern q T1")
  obtain r T3 where s3: "share_node p' q' T2 = (r, T3)" by (cases "share_node p' q' T2")
  have f1: "table_formed T1" and fp1: "shared_pattern_formed T1 p'" and pp: "shared_pattern_project T1 p' = p"
    and k1: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T1 i = Some u"
    using Finite_Pattern_Pair.IH(1)[OF Finite_Pattern_Pair.prems] s1 by simp_all
  have f2: "table_formed T2" and fq2: "shared_pattern_formed T2 q'" and pq: "shared_pattern_project T2 q' = q"
    and k2: "\<forall>i u. reference_term T1 i = Some u \<longrightarrow> reference_term T2 i = Some u"
    using Finite_Pattern_Pair.IH(2)[OF f1] s2 by simp_all
  have ext: "shared_pattern_formed T2 p' \<and> shared_pattern_project T2 p' = shared_pattern_project T1 p'"
    by (rule shared_pattern_extended[OF f1 fp1]) (use k2 in blast)
  have n: "table_formed T3 \<and> shared_pattern_formed T3 r \<and>
      shared_pattern_project T3 r = Finite_Pattern_Pair (shared_pattern_project T2 p') (shared_pattern_project T2 q') \<and>
      (\<forall>i u. reference_term T2 i = Some u \<longrightarrow> reference_term T3 i = Some u)"
    using share_node_exact[OF f2 ext[THEN conjunct1] fq2] s3 by simp
  have k: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T3 i = Some u" using k1 k2 n by blast
  show ?case using n ext pp pq k by (simp add: s1 s2 s3)
qed

lemma share_pattern_exact_term:
  "share_pattern (finite_exact_term_pattern t) T = (Shared_Ground (fst (share_term t T)), snd (share_term t T))"
proof (induction t arbitrary: T)
  case (Finite_Pair t u)
  obtain i T1 where s1: "share_term t T = (i, T1)" by (cases "share_term t T")
  obtain j T2 where s2: "share_term u T1 = (j, T2)" by (cases "share_term u T1")
  obtain k T3 where s3: "value_reference_step (Pair_Shape i j) T2 = (k, T3)"
    by (cases "value_reference_step (Pair_Shape i j) T2")
  show ?case using Finite_Pair.IH(1)[of T] Finite_Pair.IH(2)[of T1] by (simp add: s1 s2 s3)
qed (simp_all add: case_prod_unfold)

end
