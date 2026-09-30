theory Shared_Binding_Stores
  imports Factor_Shared_Patterns
begin

section \<open>A substitution kept factored in a store and resolved where read\<close>

text \<open>
  Build D1a of DECISIONS.md, task 495's entry, its addition "The step at the given's depth". A search that
  substitutes every pattern holding a variable its unifier binds walks each such pattern whole at every
  step. A \emph{binding store} keeps the substitutions instead, factored: a finite functional relation
  from variables to shared patterns (@{text Factor_Shared_Patterns}), each binding with the rank at which
  it was recorded. A pattern is \emph{resolved} where it is read: each bound variable replaced by the
  resolution of its binding, well founded by the rank, since a binding's pattern holds no variable bound
  at its own rank or below. Recording a unifier (@{text store_bind}) walks no pattern the store keeps.

  The store is formed over a table when every binding is a formed, collapsed pattern of the table and
  every variable of a binding's pattern is unbound or bound at a greater rank. Formation is established by
  the constructors (the empty store, @{text store_bind}, @{text store_compress}) and kept by them, never
  checked again. The laws are stated once: resolution at the empty store is the identity, and a pattern
  holding no bound variable is its own resolution; resolution after a bind is F2a's substitution of the
  unifier applied to the resolution before (@{text store_bind_resolve}); a resolution projects to R2's
  substitution of the projection (@{text binding_resolve_project}), by which the bind law meets the keyed
  substitution's contract (@{text keyed_substitute_exact}) where a search composes them; the variables of
  a resolution after a bind are those before outside the unifier's domain and those of its bindings at
  the members of the domain the resolution held (@{text store_bind_variables}); and a binding replaced by
  a resolution of it leaves the projection of every resolution as it was (@{text store_compress_resolve}),
  so a ground resolution is memoized as its reference and the ancestors of a closed tail resolve in total
  time linear in the chain. The keyed resolution builds through the keyed constructor, so a resolved
  collapsed pattern stays collapsed and the table only extends; it is the collapse of the resolution
  (@{text keyed_binding_resolve_exact}). The store's code reads it through a red-black tree at a key
  injective on its variables, an instance of the index notion (@{text Carrier_Indexes}).
\<close>

record 'a binding_store =
  binding_next_rank :: nat
  binding_map :: "'a \<Rightarrow> (nat \<times> 'a shared_pattern) option"

definition binding_store_empty :: "'a binding_store" where
  "binding_store_empty = \<lparr>binding_next_rank = 0, binding_map = (\<lambda>a. None)\<rparr>"

definition ranked_bindings :: "nat \<Rightarrow> shape list \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow> bool" where
  "ranked_bindings n T M \<longleftrightarrow> (\<forall>a r p. M a = Some (r, p) \<longrightarrow> r < n \<and> shared_pattern_formed T p \<and>
    (\<forall>b r' p'. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = Some (r', p') \<longrightarrow> r < r'))"

definition binding_store_formed :: "shape list \<Rightarrow> 'a binding_store \<Rightarrow> bool" where
  "binding_store_formed T S \<longleftrightarrow> finite (dom (binding_map S)) \<and>
    ranked_bindings (binding_next_rank S) T (binding_map S) \<and>
    (\<forall>a r p. binding_map S a = Some (r, p) \<longrightarrow> shared_collapsed p)"

lemma binding_store_formedD:
  assumes "binding_store_formed T S"
  shows "finite (dom (binding_map S))" "ranked_bindings (binding_next_rank S) T (binding_map S)"
    "\<forall>b r' u. binding_map S b = Some (r', u) \<longrightarrow> shared_pattern_formed T u \<and> shared_collapsed u"
  using assms unfolding binding_store_formed_def ranked_bindings_def by blast+

theorem binding_store_empty_formed: "binding_store_formed T binding_store_empty"
  by (simp add: binding_store_formed_def binding_store_empty_def ranked_bindings_def)

text \<open>
  A store formed over a table stays formed over every table that decodes each of its references as it does: every
  binding stays a formed pattern, its rank and its collapse as they were (review 900's follow-up 1).
\<close>

theorem binding_store_formed_extended:
  assumes S: "binding_store_formed T S" and table: "table_formed T"
    and ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
  shows "binding_store_formed T' S"
proof -
  have "shared_pattern_formed T' p" if "shared_pattern_formed T p" for p
    using shared_pattern_extended[OF table that ext[rule_format]] by blast
  then show ?thesis using S unfolding binding_store_formed_def ranked_bindings_def by blast
qed


lemma option_eq_by_Some: "(\<And>v. x = Some v \<longleftrightarrow> y = Some v) \<Longrightarrow> x = y"
  by (cases x; cases y) auto

definition binding_store_domain :: "'a binding_store \<Rightarrow> 'a fset" where
  "binding_store_domain S = Abs_fset (dom (binding_map S))"

lemma binding_store_domain_member:
  assumes "binding_store_formed T S"
  shows "a |\<in>| binding_store_domain S \<longleftrightarrow> binding_map S a \<noteq> None"
  using assms by (simp add: binding_store_domain_def binding_store_formed_def Abs_fset_inverse domIff)

subsection \<open>Resolution, well founded by the rank\<close>

text \<open>
  Resolution from a rank follows a binding only when its rank is at least that rank and below the
  store's next rank, and resolves the binding's pattern from the rank above it; so it terminates on every
  input, and on a formed store it follows every binding a pattern reaches. A node none of whose cached
  variables the store binds is returned as it stands, read through its cache alone.
\<close>

function binding_resolve_from :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow>
    'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "binding_resolve_from n r M (Shared_Variable a) = (case M a of
      Some (r', q) \<Rightarrow> (if r \<le> r' \<and> r' < n then binding_resolve_from n (Suc r') M q else Shared_Variable a)
    | None \<Rightarrow> Shared_Variable a)"
| "binding_resolve_from n r M (Shared_Ground i) = Shared_Ground i"
| "binding_resolve_from n r M (Shared_Node A p q) = (if fBall A (\<lambda>a. M a = None) then Shared_Node A p q
    else shared_node (binding_resolve_from n r M p) (binding_resolve_from n r M q))"
  by pat_completeness auto
termination by (relation "measures [\<lambda>(n, r, M, p). n - r, \<lambda>(n, r, M, p). size p]") auto

function keyed_resolve_from :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow>
    'a shared_pattern \<Rightarrow> share_state \<Rightarrow> 'a shared_pattern \<times> share_state" where
  "keyed_resolve_from n r M (Shared_Variable a) st = (case M a of
      Some (r', q) \<Rightarrow> (if r \<le> r' \<and> r' < n then keyed_resolve_from n (Suc r') M q st else (Shared_Variable a, st))
    | None \<Rightarrow> (Shared_Variable a, st))"
| "keyed_resolve_from n r M (Shared_Ground i) st = (Shared_Ground i, st)"
| "keyed_resolve_from n r M (Shared_Node A p q) st = (if fBall A (\<lambda>a. M a = None) then (Shared_Node A p q, st)
    else (case keyed_resolve_from n r M p st of (p', st1) \<Rightarrow>
      (case keyed_resolve_from n r M q st1 of (q', st2) \<Rightarrow> keyed_share_node p' q' st2)))"
  by pat_completeness auto
termination by (relation "measures [\<lambda>(n, r, M, p, st). n - r, \<lambda>(n, r, M, p, st). size p]") auto

lemma binding_resolve_from_followed:
  "M a = Some (r', u) \<Longrightarrow> r \<le> r' \<Longrightarrow> r' < n \<Longrightarrow>
    binding_resolve_from n r M (Shared_Variable a) = binding_resolve_from n (Suc r') M u"
  by simp

lemma binding_resolve_from_unfollowed:
  "\<not> (\<exists>r' u. M a = Some (r', u) \<and> r \<le> r' \<and> r' < n) \<Longrightarrow>
    binding_resolve_from n r M (Shared_Variable a) = Shared_Variable a"
  by (auto split: option.splits prod.splits)

lemma keyed_resolve_from_followed:
  "M a = Some (r', u) \<Longrightarrow> r \<le> r' \<Longrightarrow> r' < n \<Longrightarrow>
    keyed_resolve_from n r M (Shared_Variable a) st = keyed_resolve_from n (Suc r') M u st"
  by simp

lemma keyed_resolve_from_unfollowed:
  "\<not> (\<exists>r' u. M a = Some (r', u) \<and> r \<le> r' \<and> r' < n) \<Longrightarrow>
    keyed_resolve_from n r M (Shared_Variable a) st = (Shared_Variable a, st)"
  by (auto split: option.splits prod.splits)

lemma binding_resolve_from_node:
  "\<not> fBall A (\<lambda>a. M a = None) \<Longrightarrow>
    binding_resolve_from n r M (Shared_Node A p q) = shared_node (binding_resolve_from n r M p) (binding_resolve_from n r M q)"
  by (simp only: binding_resolve_from.simps(3) if_not_P if_False)

lemma binding_resolve_from_kept:
  "fBall A (\<lambda>a. M a = None) \<Longrightarrow> binding_resolve_from n r M (Shared_Node A p q) = Shared_Node A p q"
  by (simp only: binding_resolve_from.simps(3) if_P if_True)

lemma keyed_resolve_from_node:
  "\<not> fBall A (\<lambda>a. M a = None) \<Longrightarrow>
    keyed_resolve_from n r M (Shared_Node A p q) st = (case keyed_resolve_from n r M p st of (p', st1) \<Rightarrow>
      (case keyed_resolve_from n r M q st1 of (q', st2) \<Rightarrow> keyed_share_node p' q' st2))"
  by (simp only: keyed_resolve_from.simps(3) if_not_P if_False)

lemma keyed_resolve_from_kept:
  "fBall A (\<lambda>a. M a = None) \<Longrightarrow> keyed_resolve_from n r M (Shared_Node A p q) st = (Shared_Node A p q, st)"
  by (simp only: keyed_resolve_from.simps(3) if_P if_True)

lemma binding_resolve_from_induct [case_names bound unbound ground node]:
  assumes bound: "\<And>n r M a r' u. M a = Some (r', u) \<Longrightarrow> r \<le> r' \<Longrightarrow> r' < n \<Longrightarrow> P n (Suc r') M u \<Longrightarrow>
      P n r M (Shared_Variable a)"
    and unbound: "\<And>n r M a. \<not> (\<exists>r' u. M a = Some (r', u) \<and> r \<le> r' \<and> r' < n) \<Longrightarrow> P n r M (Shared_Variable a)"
    and ground: "\<And>n r M i. P n r M (Shared_Ground i)"
    and node: "\<And>n r M A p q. (\<not> fBall A (\<lambda>a. M a = None) \<Longrightarrow> P n r M p) \<Longrightarrow>
      (\<not> fBall A (\<lambda>a. M a = None) \<Longrightarrow> P n r M q) \<Longrightarrow> P n r M (Shared_Node A p q)"
  shows "P n r M p"
proof (induction n r M p rule: binding_resolve_from.induct)
  case (1 n r M a)
  show ?case
  proof (cases "\<exists>r' u. M a = Some (r', u) \<and> r \<le> r' \<and> r' < n")
    case True
    then obtain r' u where b: "M a = Some (r', u)" "r \<le> r'" "r' < n" by blast
    have "P n (Suc r') M u" using "1" b by blast
    then show ?thesis by (rule bound[of M a r' u r n, OF b])
  next
    case False
    then show ?thesis by (rule unbound)
  qed
next
  case (2 n r M i)
  show ?case by (rule ground)
next
  case (3 n r M A p q)
  then show ?case by (rule node)
qed

lemma binding_resolve_from_unbound:
  "\<forall>b. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = None \<Longrightarrow> binding_resolve_from n r M p = p"
  by (cases p) auto

lemma binding_resolve_from_rank:
  "shared_pattern_formed T p \<Longrightarrow> \<forall>b r' u. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = Some (r', u) \<longrightarrow> r \<le> r' \<Longrightarrow>
    binding_resolve_from n r M p = binding_resolve_from n 0 M p"
proof (induction p)
  case (Shared_Variable a)
  then show ?case by (auto split: option.splits prod.splits)
next
  case (Shared_Node A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q" using Shared_Node.prems(1) by simp
  have "binding_resolve_from n r M p = binding_resolve_from n 0 M p"
    by (rule Shared_Node.IH(1)) (use Shared_Node.prems A in auto)
  moreover have "binding_resolve_from n r M q = binding_resolve_from n 0 M q"
    by (rule Shared_Node.IH(2)) (use Shared_Node.prems A in auto)
  ultimately show ?case by simp
qed simp

lemma binding_resolve_from_formed:
  "\<forall>b r' u. M b = Some (r', u) \<longrightarrow> shared_pattern_formed T u \<Longrightarrow> shared_pattern_formed T p \<Longrightarrow>
    shared_pattern_formed T (binding_resolve_from n r M p)"
proof (induction n r M p rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  have "shared_pattern_formed T u" using bound.prems(1) bound.hyps(1) by blast
  then show ?case using bound.IH[OF bound.prems(1)] bound.hyps by simp
next
  case (unbound n r M a)
  then show ?case using binding_resolve_from_unfollowed[of M a r n, OF unbound.hyps] by simp
next
  case (ground n r M i)
  then show ?case by simp
next
  case (node n r M A p q)
  show ?case
  proof (cases "fBall A (\<lambda>a. M a = None)")
    case True
    then show ?thesis using node.prems(2) by simp
  next
    case False
    then show ?thesis using node.IH(1)[OF False node.prems(1)] node.IH(2)[OF False node.prems(1)] node.prems(2)
      by simp
  qed
qed

lemma binding_resolve_from_variables:
  "ranked_bindings n T M \<Longrightarrow> shared_pattern_formed T p \<Longrightarrow>
    \<forall>b r' u. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = Some (r', u) \<longrightarrow> r \<le> r' \<Longrightarrow>
    c |\<in>| shared_pattern_variables (binding_resolve_from n r M p) \<Longrightarrow> M c = None"
proof (induction n r M p rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  have u: "shared_pattern_formed T u"
    "\<forall>b r'' u'. b |\<in>| shared_pattern_variables u \<longrightarrow> M b = Some (r'', u') \<longrightarrow> Suc r' \<le> r''"
    using bound.prems(1) bound.hyps(1) unfolding ranked_bindings_def by (blast, fastforce)
  have "c |\<in>| shared_pattern_variables (binding_resolve_from n (Suc r') M u)"
    using bound.prems(4) bound.hyps by simp
  then show ?case by (rule bound.IH[OF bound.prems(1) u])
next
  case (unbound n r M a)
  have "M a = None"
  proof (rule ccontr)
    assume "M a \<noteq> None"
    then obtain r' u where a: "M a = Some (r', u)" by (metis not_None_eq surj_pair)
    have "r \<le> r'" using unbound.prems(3) a by auto
    moreover have "r' < n" using unbound.prems(1) a unfolding ranked_bindings_def by blast
    ultimately show False using unbound.hyps a by blast
  qed
  then show ?case using unbound.prems(4) binding_resolve_from_unfollowed[of M a r n, OF unbound.hyps] by simp
next
  case (ground n r M i)
  then show ?case by simp
next
  case (node n r M A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q"
    and f: "shared_pattern_formed T p" "shared_pattern_formed T q" using node.prems(2) by simp_all
  show ?case
  proof (cases "fBall A (\<lambda>a. M a = None)")
    case True
    then show ?thesis using node.prems(4) by simp
  next
    case False
    have "c |\<in>| shared_pattern_variables (binding_resolve_from n r M p) \<or>
        c |\<in>| shared_pattern_variables (binding_resolve_from n r M q)"
      using node.prems(4) False by simp
    then show ?thesis
      using node.IH(1)[OF False node.prems(1) f(1)] node.IH(2)[OF False node.prems(1) f(2)] node.prems(3) A
      by auto
  qed
qed

subsection \<open>The resolution of a store and its first laws\<close>

definition binding_resolve :: "'a binding_store \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a shared_pattern" where
  "binding_resolve S = binding_resolve_from (binding_next_rank S) 0 (binding_map S)"

definition binding_substitution :: "'a binding_store \<Rightarrow> 'a \<Rightarrow> 'a shared_pattern" where
  "binding_substitution S a = binding_resolve S (Shared_Variable a)"

theorem binding_resolve_empty: "binding_resolve binding_store_empty p = p"
  unfolding binding_resolve_def binding_store_empty_def by (rule binding_resolve_from_unbound) simp

theorem binding_resolve_unbound:
  assumes "\<forall>b. b |\<in>| shared_pattern_variables p \<longrightarrow> binding_map S b = None"
  shows "binding_resolve S p = p"
  using assms unfolding binding_resolve_def by (rule binding_resolve_from_unbound)

lemma binding_substitution_outside:
  assumes "binding_store_formed T S" "a |\<notin>| binding_store_domain S"
  shows "binding_substitution S a = Shared_Variable a"
  using assms binding_store_domain_member[OF assms(1)]
  by (auto simp: binding_substitution_def binding_resolve_def split: option.splits)

text \<open>A resolution is the substitution the store denotes, applied through F2a's substitution.\<close>

theorem binding_resolve_substitute:
  assumes S: "binding_store_formed T S"
  shows "binding_resolve S p = shared_substitute (binding_substitution S) (binding_store_domain S) p"
proof (induction p)
  case (Shared_Variable a)
  show ?case by (simp add: binding_substitution_def)
next
  case (Shared_Ground i)
  show ?case by (simp add: binding_resolve_def)
next
  case (Shared_Node A p q)
  have test: "fBall A (\<lambda>a. binding_map S a = None) \<longleftrightarrow> A |\<inter>| binding_store_domain S = {||}"
    unfolding fset_eq_iff finter_iff fempty_iff using binding_store_domain_member[OF S] by blast
  show ?case using Shared_Node.IH test by (simp add: binding_resolve_def)
qed

theorem binding_resolve_formed:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
  shows "shared_pattern_formed T (binding_resolve S p)"
  unfolding binding_resolve_def
  by (rule binding_resolve_from_formed[OF _ p]) (use binding_store_formedD(3)[OF S] in blast)

theorem binding_resolve_project:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
  shows "shared_pattern_project T (binding_resolve S p) =
    finite_pattern_substitute (\<lambda>a. shared_pattern_project T (binding_substitution S a)) (shared_pattern_project T p)"
  unfolding binding_resolve_substitute[OF S]
  by (rule shared_substitute_project[OF p binding_substitution_outside[OF S]])

theorem binding_resolve_variables:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
    and c: "c |\<in>| shared_pattern_variables (binding_resolve S p)"
  shows "binding_map S c = None"
  using binding_resolve_from_variables[OF binding_store_formedD(2)[OF S] p _ c[unfolded binding_resolve_def]]
  by simp

subsection \<open>Recording a unifier\<close>

text \<open>
  A unifier is given as F2a's substitution is, a function and the finite set outside which it is the
  identity. It is ready for a store when its domain and the variables of its images are unbound in the
  store, it is idempotent (no image holds a variable of the domain), and its images are formed, collapsed
  patterns of the table. It is recorded at the store's next rank; no kept pattern is walked.
\<close>

definition unifier_ready :: "shape list \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow> ('a \<Rightarrow> 'a shared_pattern) \<Rightarrow>
    'a fset \<Rightarrow> bool" where
  "unifier_ready T M \<sigma> D \<longleftrightarrow> (\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a) \<and>
    (\<forall>a. a |\<in>| D \<longrightarrow> M a = None \<and> shared_pattern_formed T (\<sigma> a) \<and> shared_collapsed (\<sigma> a) \<and>
      (\<forall>b. b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> b |\<notin>| D \<and> M b = None))"

definition bound_map :: "nat \<Rightarrow> ('a \<Rightarrow> (nat \<times> 'a shared_pattern) option) \<Rightarrow> ('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow>
    'a \<Rightarrow> (nat \<times> 'a shared_pattern) option" where
  "bound_map n M \<sigma> D a = (if a |\<in>| D then Some (n, \<sigma> a) else M a)"

definition store_bind :: "'a binding_store \<Rightarrow> ('a \<Rightarrow> 'a shared_pattern) \<Rightarrow> 'a fset \<Rightarrow> 'a binding_store" where
  "store_bind S \<sigma> D = \<lparr>binding_next_rank = Suc (binding_next_rank S),
    binding_map = bound_map (binding_next_rank S) (binding_map S) \<sigma> D\<rparr>"

theorem store_bind_formed:
  assumes S: "binding_store_formed T S" and ready: "unifier_ready T (binding_map S) \<sigma> D"
  shows "binding_store_formed T (store_bind S \<sigma> D)"
proof -
  let ?n = "binding_next_rank S" and ?M = "binding_map S"
  have dom: "dom (bound_map ?n ?M \<sigma> D) = fset D \<union> dom ?M"
    by (auto simp: bound_map_def split: if_splits)
  have old: "\<forall>a r p. ?M a = Some (r, p) \<longrightarrow> r < ?n \<and> shared_pattern_formed T p \<and> shared_collapsed p \<and>
      (\<forall>b r' p'. b |\<in>| shared_pattern_variables p \<longrightarrow> ?M b = Some (r', p') \<longrightarrow> r < r')"
    using S unfolding binding_store_formed_def ranked_bindings_def by blast
  have new: "\<forall>a. a |\<in>| D \<longrightarrow> ?M a = None \<and> shared_pattern_formed T (\<sigma> a) \<and> shared_collapsed (\<sigma> a) \<and>
      (\<forall>b. b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> b |\<notin>| D \<and> ?M b = None)"
    using ready by (simp add: unifier_ready_def)
  have bindings: "\<forall>a r p. bound_map ?n ?M \<sigma> D a = Some (r, p) \<longrightarrow> r < Suc ?n \<and> shared_pattern_formed T p \<and>
      shared_collapsed p \<and>
      (\<forall>b r' p'. b |\<in>| shared_pattern_variables p \<longrightarrow> bound_map ?n ?M \<sigma> D b = Some (r', p') \<longrightarrow> r < r')"
  proof (intro allI impI)
    fix a r p assume a: "bound_map ?n ?M \<sigma> D a = Some (r, p)"
    show "r < Suc ?n \<and> shared_pattern_formed T p \<and> shared_collapsed p \<and>
      (\<forall>b r' p'. b |\<in>| shared_pattern_variables p \<longrightarrow> bound_map ?n ?M \<sigma> D b = Some (r', p') \<longrightarrow> r < r')"
    proof (cases "a |\<in>| D")
      case True
      then have rp: "r = ?n" "p = \<sigma> a" using a by (simp_all add: bound_map_def)
      have n: "shared_pattern_formed T (\<sigma> a)" "shared_collapsed (\<sigma> a)"
        "\<forall>b. b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> b |\<notin>| D \<and> ?M b = None" using new True by blast+
      have none: "bound_map ?n ?M \<sigma> D b = None" if "b |\<in>| shared_pattern_variables p" for b
        using n(3) that rp by (simp add: bound_map_def)
      show ?thesis using rp n(1,2) none by auto
    next
      case False
      then have m: "?M a = Some (r, p)" using a by (simp add: bound_map_def)
      have r: "r < ?n" and fp: "shared_pattern_formed T p" and cp: "shared_collapsed p"
        and ranks: "\<forall>b r' p'. b |\<in>| shared_pattern_variables p \<longrightarrow> ?M b = Some (r', p') \<longrightarrow> r < r'"
        using old m by blast+
      have later: "r < r'" if "b |\<in>| shared_pattern_variables p" "bound_map ?n ?M \<sigma> D b = Some (r', p')" for b r' p'
      proof (cases "b |\<in>| D")
        case True
        then show ?thesis using that(2) r by (simp add: bound_map_def)
      next
        case False
        then have "?M b = Some (r', p')" using that(2) by (simp add: bound_map_def)
        with ranks that(1) show ?thesis by blast
      qed
      show ?thesis using r fp cp later by auto
    qed
  qed
  show ?thesis using S dom bindings
    unfolding binding_store_formed_def ranked_bindings_def store_bind_def by auto
qed

lemma shared_substitute_unbound:
  assumes outside: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
    and disjoint: "shared_pattern_variables x |\<inter>| D = {||}"
  shows "shared_substitute \<sigma> D x = x"
  using assms by (cases x) (auto simp: fset_eq_iff)

lemma shared_substitute_node:
  assumes outside: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_substitute \<sigma> D (shared_node x y) = shared_node (shared_substitute \<sigma> D x) (shared_substitute \<sigma> D y)"
proof (cases "(shared_pattern_variables x |\<union>| shared_pattern_variables y) |\<inter>| D = {||}")
  case True
  then have "shared_pattern_variables x |\<inter>| D = {||}" "shared_pattern_variables y |\<inter>| D = {||}"
    by (auto simp: fset_eq_iff)
  then show ?thesis using True shared_substitute_unbound[OF outside] by (simp add: shared_node_def)
next
  case False
  then show ?thesis by (simp add: shared_node_def)
qed

lemma binding_resolve_from_bind_unbound:
  assumes ready: "unifier_ready T M \<sigma> D" and r: "r \<le> n"
  shows "shared_pattern_formed T p \<Longrightarrow> \<forall>b. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = None \<Longrightarrow>
    binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) p = shared_substitute \<sigma> D p"
proof (induction p)
  case (Shared_Variable a)
  show ?case
  proof (cases "a |\<in>| D")
    case True
    have none: "\<forall>b. b |\<in>| shared_pattern_variables (\<sigma> a) \<longrightarrow> bound_map n M \<sigma> D b = None"
      using ready True by (auto simp: unifier_ready_def bound_map_def)
    have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) (Shared_Variable a) =
        binding_resolve_from (Suc n) (Suc n) (bound_map n M \<sigma> D) (\<sigma> a)"
      by (rule binding_resolve_from_followed) (use True r in \<open>simp_all add: bound_map_def\<close>)
    then show ?thesis using binding_resolve_from_unbound[OF none] by simp
  next
    case False
    then show ?thesis using ready Shared_Variable.prems(2) by (simp add: bound_map_def unifier_ready_def)
  qed
next
  case (Shared_Ground i)
  show ?case by simp
next
  case (Shared_Node A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q" using Shared_Node.prems(1) by simp
  have test: "fBall A (\<lambda>a. bound_map n M \<sigma> D a = None) \<longleftrightarrow> A |\<inter>| D = {||}"
    using Shared_Node.prems(2) by (auto simp: fset_eq_iff bound_map_def)
  have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) p = shared_substitute \<sigma> D p"
    by (rule Shared_Node.IH(1)) (use Shared_Node.prems A in auto)
  moreover have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) q = shared_substitute \<sigma> D q"
    by (rule Shared_Node.IH(2)) (use Shared_Node.prems A in auto)
  ultimately show ?case using test by simp
qed

lemma binding_resolve_from_bind:
  "ranked_bindings n T M \<Longrightarrow> unifier_ready T M \<sigma> D \<Longrightarrow> shared_pattern_formed T p \<Longrightarrow>
    \<forall>b r' u. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = Some (r', u) \<longrightarrow> r \<le> r' \<Longrightarrow> r \<le> n \<Longrightarrow>
    binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) p = shared_substitute \<sigma> D (binding_resolve_from n r M p)"
proof (induction n r M p rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  have aD: "a |\<notin>| D" using bound.hyps(1) bound.prems(2) by (auto simp: unifier_ready_def)
  have u: "shared_pattern_formed T u"
    "\<forall>b r'' u'. b |\<in>| shared_pattern_variables u \<longrightarrow> M b = Some (r'', u') \<longrightarrow> Suc r' \<le> r''"
    using bound.prems(1) bound.hyps(1) unfolding ranked_bindings_def by (blast, fastforce)
  have ih: "binding_resolve_from (Suc n) (Suc r') (bound_map n M \<sigma> D) u =
      shared_substitute \<sigma> D (binding_resolve_from n (Suc r') M u)"
    using bound.IH[OF bound.prems(1,2) u] bound.hyps(3) by simp
  have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) (Shared_Variable a) =
      binding_resolve_from (Suc n) (Suc r') (bound_map n M \<sigma> D) u"
    by (rule binding_resolve_from_followed) (use aD bound.hyps in \<open>simp_all add: bound_map_def\<close>)
  then show ?case using ih bound.hyps by simp
next
  case (unbound n r M a)
  have none: "M a = None"
  proof (rule ccontr)
    assume "M a \<noteq> None"
    then obtain r' u where a: "M a = Some (r', u)" by (metis not_None_eq surj_pair)
    have "r \<le> r'" using unbound.prems(4) a by auto
    moreover have "r' < n" using unbound.prems(1) a unfolding ranked_bindings_def by blast
    ultimately show False using unbound.hyps a by blast
  qed
  have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) (Shared_Variable a) = shared_substitute \<sigma> D (Shared_Variable a)"
    by (rule binding_resolve_from_bind_unbound[OF unbound.prems(2) unbound.prems(5)]) (use none in simp_all)
  then show ?case using binding_resolve_from_unfollowed[of M a r n, OF unbound.hyps] by simp
next
  case (ground n r M i)
  show ?case by simp
next
  case (node n r M A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q"
    and fp: "shared_pattern_formed T p" and fq: "shared_pattern_formed T q" using node.prems(3) by simp_all
  show ?case
  proof (cases "fBall A (\<lambda>a. M a = None)")
    case True
    have "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) (Shared_Node A p q) =
        shared_substitute \<sigma> D (Shared_Node A p q)"
      by (rule binding_resolve_from_bind_unbound[OF node.prems(2) node.prems(5) node.prems(3)])
        (use True in simp)
    then show ?thesis using True by simp
  next
    case False
    have new: "\<not> fBall A (\<lambda>a. bound_map n M \<sigma> D a = None)"
      using False by (auto simp: bound_map_def)
    have ep: "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) p = shared_substitute \<sigma> D (binding_resolve_from n r M p)"
      by (rule node.IH(1)[OF False]) (use node.prems A fp in auto)
    have eq: "binding_resolve_from (Suc n) r (bound_map n M \<sigma> D) q = shared_substitute \<sigma> D (binding_resolve_from n r M q)"
      by (rule node.IH(2)[OF False]) (use node.prems A fq in auto)
    have outside: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" using node.prems(2) by (simp add: unifier_ready_def)
    show ?thesis
      unfolding binding_resolve_from_node[OF new] binding_resolve_from_node[OF False] shared_substitute_node[OF outside]
      using ep eq by simp
  qed
qed

text \<open>The bind law: resolution after a bind is the unifier's substitution of the resolution before.\<close>

theorem store_bind_resolve:
  assumes S: "binding_store_formed T S" and ready: "unifier_ready T (binding_map S) \<sigma> D"
    and p: "shared_pattern_formed T p"
  shows "binding_resolve (store_bind S \<sigma> D) p = shared_substitute \<sigma> D (binding_resolve S p)"
  unfolding binding_resolve_def store_bind_def
  using binding_resolve_from_bind[OF binding_store_formedD(2)[OF S] ready p, where r=0] by simp

lemma shared_substitute_variables:
  assumes outside: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a"
  shows "shared_pattern_formed T x \<Longrightarrow> c |\<in>| shared_pattern_variables (shared_substitute \<sigma> D x) \<longleftrightarrow>
    c |\<in>| shared_pattern_variables x \<and> c |\<notin>| D \<or>
    (\<exists>a. a |\<in>| shared_pattern_variables x \<and> a |\<in>| D \<and> c |\<in>| shared_pattern_variables (\<sigma> a))"
proof (induction x)
  case (Shared_Variable a)
  show ?case
  proof (cases "a |\<in>| D")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis using outside by auto
  qed
next
  case (Shared_Ground i)
  then show ?case by simp
next
  case (Shared_Node A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q" using Shared_Node.prems by simp
  show ?case
  proof (cases "A |\<inter>| D = {||}")
    case True
    have kept: "shared_substitute \<sigma> D (Shared_Node A p q) = Shared_Node A p q" using True by simp
    have "\<forall>a. a |\<in>| A \<longrightarrow> a |\<notin>| D" using True unfolding fset_eq_iff finter_iff fempty_iff by blast
    then show ?thesis unfolding kept shared_pattern_variables.simps by blast
  next
    case False
    have IHp: "c |\<in>| shared_pattern_variables (shared_substitute \<sigma> D p) \<longleftrightarrow>
        c |\<in>| shared_pattern_variables p \<and> c |\<notin>| D \<or>
        (\<exists>a. a |\<in>| shared_pattern_variables p \<and> a |\<in>| D \<and> c |\<in>| shared_pattern_variables (\<sigma> a))"
      by (rule Shared_Node.IH(1)) (use Shared_Node.prems in simp)
    have IHq: "c |\<in>| shared_pattern_variables (shared_substitute \<sigma> D q) \<longleftrightarrow>
        c |\<in>| shared_pattern_variables q \<and> c |\<notin>| D \<or>
        (\<exists>a. a |\<in>| shared_pattern_variables q \<and> a |\<in>| D \<and> c |\<in>| shared_pattern_variables (\<sigma> a))"
      by (rule Shared_Node.IH(2)) (use Shared_Node.prems in simp)
    have eq: "shared_substitute \<sigma> D (Shared_Node A p q) =
        shared_node (shared_substitute \<sigma> D p) (shared_substitute \<sigma> D q)" using False by simp
    have vA: "shared_pattern_variables (Shared_Node A p q) = shared_pattern_variables p |\<union>| shared_pattern_variables q"
      using A by simp
    show ?thesis unfolding eq vA shared_node_fields funion_iff using IHp IHq by blast
  qed
qed

text \<open>
  The variables law: the variables of a resolution after a bind are those before outside the domain, and
  the variables of the unifier's bindings at the members of the domain the resolution before held. A step
  updates the variables of a kept pattern by this set arithmetic, walking no pattern.
\<close>

theorem store_bind_variables:
  assumes S: "binding_store_formed T S" and ready: "unifier_ready T (binding_map S) \<sigma> D"
    and p: "shared_pattern_formed T p"
  shows "c |\<in>| shared_pattern_variables (binding_resolve (store_bind S \<sigma> D) p) \<longleftrightarrow>
    c |\<in>| shared_pattern_variables (binding_resolve S p) \<and> c |\<notin>| D \<or>
    (\<exists>a. a |\<in>| shared_pattern_variables (binding_resolve S p) \<and> a |\<in>| D \<and> c |\<in>| shared_pattern_variables (\<sigma> a))"
proof -
  have outside: "\<forall>a. a |\<notin>| D \<longrightarrow> \<sigma> a = Shared_Variable a" using ready by (simp add: unifier_ready_def)
  show ?thesis
    unfolding store_bind_resolve[OF S ready p]
    by (rule shared_substitute_variables[OF outside binding_resolve_formed[OF S p]])
qed

subsection \<open>Compression: a binding replaced by a resolution of it\<close>

definition store_compress :: "'a binding_store \<Rightarrow> 'a \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a binding_store" where
  "store_compress S a q = \<lparr>binding_next_rank = binding_next_rank S,
    binding_map = (binding_map S)(a := map_option (\<lambda>x. (fst x, q)) (binding_map S a))\<rparr>"

theorem store_compress_formed:
  assumes S: "binding_store_formed T S" and a: "binding_map S a = Some (ra, qa)" and table: "table_formed T"
    and ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
    and f: "shared_pattern_formed T' q" and c: "shared_collapsed q"
    and unbound: "\<forall>b. b |\<in>| shared_pattern_variables q \<longrightarrow> binding_map S b = None"
  shows "binding_store_formed T' (store_compress S a q)"
proof -
  let ?M = "binding_map S" and ?n = "binding_next_rank S"
  have S': "binding_store_formed T' S" by (rule binding_store_formed_extended[OF S table ext])
  have map: "binding_map (store_compress S a q) = ?M(a := Some (ra, q))" using a by (simp add: store_compress_def)
  have old: "\<forall>b r p. ?M b = Some (r, p) \<longrightarrow> r < ?n \<and> shared_pattern_formed T' p \<and> shared_collapsed p \<and>
      (\<forall>c r' p'. c |\<in>| shared_pattern_variables p \<longrightarrow> ?M c = Some (r', p') \<longrightarrow> r < r')"
    using S' unfolding binding_store_formed_def ranked_bindings_def by blast
  have aq: "a |\<notin>| shared_pattern_variables q" using unbound a by auto
  have dom: "dom (?M(a := Some (ra, q))) = dom ?M" using a by auto
  have bindings: "\<forall>b r p. (?M(a := Some (ra, q))) b = Some (r, p) \<longrightarrow> r < ?n \<and> shared_pattern_formed T' p \<and>
      shared_collapsed p \<and>
      (\<forall>c r' p'. c |\<in>| shared_pattern_variables p \<longrightarrow> (?M(a := Some (ra, q))) c = Some (r', p') \<longrightarrow> r < r')"
  proof (intro allI impI)
    fix b r p assume b: "(?M(a := Some (ra, q))) b = Some (r, p)"
    show "r < ?n \<and> shared_pattern_formed T' p \<and> shared_collapsed p \<and>
      (\<forall>c r' p'. c |\<in>| shared_pattern_variables p \<longrightarrow> (?M(a := Some (ra, q))) c = Some (r', p') \<longrightarrow> r < r')"
    proof (cases "b = a")
      case True
      then have rp: "r = ra" "p = q" using b by simp_all
      have "ra < ?n" using old a by blast
      then show ?thesis using rp f c unbound aq by auto
    next
      case False
      then have m: "?M b = Some (r, p)" using b by simp
      have r: "r < ?n" and fp: "shared_pattern_formed T' p" and cp: "shared_collapsed p"
        and ranks: "\<forall>c r' p'. c |\<in>| shared_pattern_variables p \<longrightarrow> ?M c = Some (r', p') \<longrightarrow> r < r'"
        using old m by blast+
      have later: "r < r'" if "c |\<in>| shared_pattern_variables p" "(?M(a := Some (ra, q))) c = Some (r', p')"
        for c r' p'
      proof (cases "c = a")
        case True
        have "r < ra" using ranks that(1) a True by blast
        then show ?thesis using that(2) True by simp
      next
        case False
        then have "?M c = Some (r', p')" using that(2) by simp
        with ranks that(1) show ?thesis by blast
      qed
      show ?thesis using r fp cp later by auto
    qed
  qed
  show ?thesis using S' map dom bindings
    unfolding binding_store_formed_def ranked_bindings_def by (simp add: store_compress_def)
qed

lemma binding_resolve_from_compress:
  "ranked_bindings n T M \<Longrightarrow> M a = Some (ra, qa) \<Longrightarrow> table_formed T \<Longrightarrow>
    \<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u \<Longrightarrow>
    \<forall>b. b |\<in>| shared_pattern_variables q \<longrightarrow> M b = None \<Longrightarrow>
    shared_pattern_project T' q = shared_pattern_project T (binding_resolve_from n 0 M qa) \<Longrightarrow>
    shared_pattern_formed T p \<Longrightarrow> \<forall>b r' u. b |\<in>| shared_pattern_variables p \<longrightarrow> M b = Some (r', u) \<longrightarrow> r \<le> r' \<Longrightarrow>
    shared_pattern_project T' (binding_resolve_from n r (M(a := Some (ra, q))) p) =
      shared_pattern_project T (binding_resolve_from n r M p)"
proof (induction n r M p rule: binding_resolve_from_induct)
  case (bound n r M b r' u)
  have u: "shared_pattern_formed T u"
    "\<forall>c r'' u'. c |\<in>| shared_pattern_variables u \<longrightarrow> M c = Some (r'', u') \<longrightarrow> Suc r' \<le> r''"
    using bound.prems(1) bound.hyps(1) unfolding ranked_bindings_def by (blast, fastforce)
  show ?case
  proof (cases "b = a")
    case True
    then have rq: "r' = ra" "u = qa" using bound.hyps(1) bound.prems(2) by simp_all
    have aq: "\<forall>c. c |\<in>| shared_pattern_variables q \<longrightarrow> (M(a := Some (ra, q))) c = None"
      using bound.prems(2,5) by auto
    have "binding_resolve_from n r (M(a := Some (ra, q))) (Shared_Variable b) =
        binding_resolve_from n (Suc r') (M(a := Some (ra, q))) q"
      by (rule binding_resolve_from_followed) (use True rq bound.hyps in simp_all)
    also have "\<dots> = q" by (rule binding_resolve_from_unbound[OF aq])
    finally have left: "binding_resolve_from n r (M(a := Some (ra, q))) (Shared_Variable b) = q" .
    have right: "binding_resolve_from n r M (Shared_Variable b) = binding_resolve_from n 0 M qa"
      using bound.hyps binding_resolve_from_rank[OF u(1) u(2)] rq by simp
    show ?thesis by (simp only: left right bound.prems(6))
  next
    case False
    have "binding_resolve_from n r (M(a := Some (ra, q))) (Shared_Variable b) =
        binding_resolve_from n (Suc r') (M(a := Some (ra, q))) u"
      by (rule binding_resolve_from_followed) (use False bound.hyps in simp_all)
    moreover have "binding_resolve_from n r M (Shared_Variable b) = binding_resolve_from n (Suc r') M u"
      by (rule binding_resolve_from_followed) (use bound.hyps in simp_all)
    ultimately show ?thesis by (simp only: bound.IH[OF bound.prems(1-6) u])
  qed
next
  case (unbound n r M b)
  have none: "M b = None"
  proof (rule ccontr)
    assume "M b \<noteq> None"
    then obtain r' u where b: "M b = Some (r', u)" by (metis not_None_eq surj_pair)
    have "r \<le> r'" using unbound.prems(8) b by auto
    moreover have "r' < n" using unbound.prems(1) b unfolding ranked_bindings_def by blast
    ultimately show False using unbound.hyps b by blast
  qed
  have "b \<noteq> a" using none unbound.prems(2) by auto
  then have h: "\<not> (\<exists>r' u. (M(a := Some (ra, q))) b = Some (r', u) \<and> r \<le> r' \<and> r' < n)" using none by simp
  show ?case by (simp only: binding_resolve_from_unfollowed[of "M(a := Some (ra, q))" b r n, OF h]
      binding_resolve_from_unfollowed[of M b r n, OF unbound.hyps] shared_pattern_project.simps(1))
next
  case (ground n r M i)
  then show ?case using shared_pattern_extended[OF ground.prems(3) ground.prems(7) ground.prems(4)[rule_format]]
    by simp
next
  case (node n r M A p1 p2)
  have A: "A = shared_pattern_variables p1 |\<union>| shared_pattern_variables p2"
    and f1: "shared_pattern_formed T p1" and f2: "shared_pattern_formed T p2" using node.prems(7) by simp_all
  have test: "fBall A (\<lambda>c. (M(a := Some (ra, q))) c = None) = fBall A (\<lambda>c. M c = None)"
    using node.prems(2) by auto
  show ?case
  proof (cases "fBall A (\<lambda>c. M c = None)")
    case True
    then show ?thesis
      using test shared_pattern_extended[OF node.prems(3) node.prems(7) node.prems(4)[rule_format]] by simp
  next
    case False
    have e1: "shared_pattern_project T' (binding_resolve_from n r (M(a := Some (ra, q))) p1) =
        shared_pattern_project T (binding_resolve_from n r M p1)"
      by (rule node.IH(1)[OF False]) (use node.prems A f1 in auto)
    have e2: "shared_pattern_project T' (binding_resolve_from n r (M(a := Some (ra, q))) p2) =
        shared_pattern_project T (binding_resolve_from n r M p2)"
      by (rule node.IH(2)[OF False]) (use node.prems A f2 in auto)
    have new: "\<not> fBall A (\<lambda>c. (M(a := Some (ra, q))) c = None)" unfolding test by (rule False)
    show ?thesis unfolding binding_resolve_from_node[OF new] binding_resolve_from_node[OF False] shared_node_fields
      using e1 e2 by simp
  qed
qed

text \<open>
  Compression: a binding replaced by a formed, collapsed pattern of an extended table whose projection is
  that of the binding's resolution, and whose variables are unbound, leaves the projection of every
  resolution as it was.
\<close>

theorem store_compress_resolve:
  assumes S: "binding_store_formed T S" and a: "binding_map S a = Some (ra, qa)" and table: "table_formed T"
    and ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
    and unbound: "\<forall>b. b |\<in>| shared_pattern_variables q \<longrightarrow> binding_map S b = None"
    and project: "shared_pattern_project T' q = shared_pattern_project T (binding_resolve S qa)"
    and p: "shared_pattern_formed T p"
  shows "shared_pattern_project T' (binding_resolve (store_compress S a q) p) =
    shared_pattern_project T (binding_resolve S p)"
  using binding_resolve_from_compress[OF binding_store_formedD(2)[OF S] a table ext unbound
      project[unfolded binding_resolve_def] p, where r=0] a
  by (simp add: binding_resolve_def store_compress_def)

subsection \<open>The keyed resolution collapses as it builds\<close>

lemma keyed_share_collapse_collapsed:
  "shared_pattern_formed T p \<Longrightarrow> shared_collapsed p \<Longrightarrow> keyed_share_collapse p st = (p, st)"
proof (induction p arbitrary: st)
  case (Shared_Node A p r)
  have ind: "keyed_share_collapse p st = (p, st)" "keyed_share_collapse r st = (r, st)"
    using Shared_Node by simp_all
  have "\<not> (\<exists>i j. p = Shared_Ground i \<and> r = Shared_Ground j)" using Shared_Node.prems by auto
  then have "keyed_share_node p r st = (shared_node p r, st)" by (cases p; cases r) auto
  then show ?case using ind Shared_Node.prems by (simp add: shared_node_def)
qed simp_all

lemma keyed_resolve_from_collapse:
  "\<forall>b r' u. M b = Some (r', u) \<longrightarrow> shared_pattern_formed T u \<and> shared_collapsed u \<Longrightarrow>
    shared_pattern_formed T p \<Longrightarrow> shared_collapsed p \<Longrightarrow>
    keyed_resolve_from n r M p st = keyed_share_collapse (binding_resolve_from n r M p) st"
proof (induction n r M p arbitrary: st rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  have u: "shared_pattern_formed T u" "shared_collapsed u" using bound.prems(1) bound.hyps(1) by blast+
  have "keyed_resolve_from n (Suc r') M u st = keyed_share_collapse (binding_resolve_from n (Suc r') M u) st"
    by (rule bound.IH[OF bound.prems(1) u])
  then show ?case using bound.hyps bound.hyps
    by simp
next
  case (unbound n r M a)
  then show ?case
    using keyed_resolve_from_unfollowed[of M a r n st, OF unbound.hyps] binding_resolve_from_unfollowed[of M a r n, OF unbound.hyps] by simp
next
  case (ground n r M i)
  show ?case by simp
next
  case (node n r M A p q)
  have fp: "shared_pattern_formed T p" "shared_collapsed p" and fq: "shared_pattern_formed T q" "shared_collapsed q"
    using node.prems(2,3) by simp_all
  show ?case
  proof (cases "fBall A (\<lambda>a. M a = None)")
    case True
    then show ?thesis using keyed_share_collapse_collapsed[OF node.prems(2,3)] by simp
  next
    case False
    have ep: "keyed_resolve_from n r M p st' = keyed_share_collapse (binding_resolve_from n r M p) st'" for st'
      by (rule node.IH(1)[OF False node.prems(1) fp])
    have eq: "keyed_resolve_from n r M q st' = keyed_share_collapse (binding_resolve_from n r M q) st'" for st'
      by (rule node.IH(2)[OF False node.prems(1) fq])
    show ?thesis
      unfolding keyed_resolve_from_node[OF False] binding_resolve_from_node[OF False] shared_node_def
        keyed_share_collapse.simps(1)
      using ep eq by simp
  qed
qed

definition keyed_binding_resolve :: "'a binding_store \<Rightarrow> 'a shared_pattern \<Rightarrow> share_state \<Rightarrow>
    'a shared_pattern \<times> share_state" where
  "keyed_binding_resolve S = keyed_resolve_from (binding_next_rank S) 0 (binding_map S)"

lemma keyed_binding_resolve_collapse:
  assumes S: "binding_store_formed T S" and p: "shared_pattern_formed T p" and c: "shared_collapsed p"
  shows "keyed_binding_resolve S p st = keyed_share_collapse (binding_resolve S p) st"
  unfolding keyed_binding_resolve_def binding_resolve_def
  by (rule keyed_resolve_from_collapse[OF binding_store_formedD(3)[OF S] p c])

theorem keyed_binding_resolve_exact:
  assumes S: "binding_store_formed T S" and table: "table_formed T" and rep: "keyed_state_represents st T"
    and p: "shared_pattern_formed T p" and c: "shared_collapsed p"
  shows "fst (keyed_binding_resolve S p st) = fst (share_collapse (binding_resolve S p) T) \<and>
    keyed_state_represents (snd (keyed_binding_resolve S p st)) (snd (share_collapse (binding_resolve S p) T)) \<and>
    table_formed (snd (share_collapse (binding_resolve S p) T)) \<and>
    shared_pattern_formed (snd (share_collapse (binding_resolve S p) T)) (fst (keyed_binding_resolve S p st)) \<and>
    shared_pattern_project (snd (share_collapse (binding_resolve S p) T)) (fst (keyed_binding_resolve S p st)) =
      shared_pattern_project T (binding_resolve S p) \<and>
    shared_collapsed (fst (keyed_binding_resolve S p st)) \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term (snd (share_collapse (binding_resolve S p) T)) i = Some u)"
  using keyed_binding_resolve_collapse[OF S p c, of st] keyed_share_collapse_exact[OF rep, of "binding_resolve S p"]
    share_collapse_exact[OF table binding_resolve_formed[OF S p]] by simp

text \<open>
  Memoizing a binding: its keyed resolution, collapsed, replaces it, a ground resolution becoming its
  reference. The store stays formed over the extended table and every resolution projects as before.
\<close>

definition store_memoize :: "'a binding_store \<Rightarrow> 'a \<Rightarrow> share_state \<Rightarrow> 'a binding_store \<times> share_state" where
  "store_memoize S a st = (case binding_map S a of None \<Rightarrow> (S, st)
    | Some x \<Rightarrow> (case keyed_binding_resolve S (snd x) st of (q, st') \<Rightarrow> (store_compress S a q, st')))"

theorem store_memoize_exact:
  assumes S: "binding_store_formed T S" and table: "table_formed T" and rep: "keyed_state_represents st T"
    and a: "binding_map S a = Some (ra, qa)"
  defines "T' \<equiv> snd (share_collapse (binding_resolve S qa) T)"
  shows "keyed_state_represents (snd (store_memoize S a st)) T' \<and> table_formed T' \<and>
    (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u) \<and>
    binding_store_formed T' (fst (store_memoize S a st)) \<and>
    (\<forall>p. shared_pattern_formed T p \<longrightarrow>
      shared_pattern_project T' (binding_resolve (fst (store_memoize S a st)) p) =
        shared_pattern_project T (binding_resolve S p))"
proof -
  have qa: "shared_pattern_formed T qa" "shared_collapsed qa" using binding_store_formedD(3)[OF S] a by blast+
  obtain q st' where k: "keyed_binding_resolve S qa st = (q, st')" by (cases "keyed_binding_resolve S qa st")
  have e: "keyed_state_represents st' T' \<and> table_formed T' \<and> shared_pattern_formed T' q \<and>
      shared_pattern_project T' q = shared_pattern_project T (binding_resolve S qa) \<and> shared_collapsed q \<and>
      (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u)"
    using keyed_binding_resolve_exact[OF S table rep qa] k unfolding T'_def by auto
  have memo: "store_memoize S a st = (store_compress S a q, st')" using a k by (simp add: store_memoize_def)
  have ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u" using e by blast
  have variables: "shared_pattern_variables q = shared_pattern_variables (binding_resolve S qa)"
  proof -
    have "shared_pattern_variables q = finite_pattern_variables (shared_pattern_project T' q)"
      by (rule shared_pattern_variables_project) (use e in blast)
    also have "\<dots> = finite_pattern_variables (shared_pattern_project T (binding_resolve S qa))" using e by simp
    also have "\<dots> = shared_pattern_variables (binding_resolve S qa)"
      by (rule shared_pattern_variables_project[symmetric]) (rule binding_resolve_formed[OF S qa(1)])
    finally show ?thesis .
  qed
  have unbound: "\<forall>b. b |\<in>| shared_pattern_variables q \<longrightarrow> binding_map S b = None"
    using binding_resolve_variables[OF S qa(1)] variables by auto
  have formed: "binding_store_formed T' (store_compress S a q)"
    by (rule store_compress_formed[OF S a table ext _ _ unbound]) (use e in blast)+
  have resolved: "\<forall>p. shared_pattern_formed T p \<longrightarrow>
      shared_pattern_project T' (binding_resolve (store_compress S a q) p) = shared_pattern_project T (binding_resolve S p)"
    using store_compress_resolve[OF S a table ext unbound] e by blast
  show ?thesis using e memo formed resolved by simp
qed

text \<open>
  A store memoized from another: formed over an extended table, with the same next rank and the same bound variables,
  every resolution of a pattern of the old table projecting as before. Memoizing a binding is an instance
  (@{text store_memoize_memoized}); the relation is reflexive and transitive over extended tables, so any sequence of
  memoizations, in any order, is one.
\<close>

definition store_memoized :: "shape list \<Rightarrow> 'a binding_store \<Rightarrow> shape list \<Rightarrow> 'a binding_store \<Rightarrow> bool" where
  "store_memoized T S T' S' \<longleftrightarrow> table_formed T' \<and> (\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u) \<and>
    binding_store_formed T' S' \<and> binding_next_rank S' = binding_next_rank S \<and>
    (\<forall>a. binding_map S' a = None \<longleftrightarrow> binding_map S a = None) \<and>
    (\<forall>p. shared_pattern_formed T p \<longrightarrow> shared_pattern_project T' (binding_resolve S' p) = shared_pattern_project T (binding_resolve S p))"

lemma store_memoized_refl:
  "binding_store_formed T S \<Longrightarrow> table_formed T \<Longrightarrow> store_memoized T S T S"
  by (simp add: store_memoized_def)

lemma store_memoized_trans:
  assumes first: "store_memoized T S T1 S1" and second: "store_memoized T1 S1 T2 S2" and table: "table_formed T"
  shows "store_memoized T S T2 S2"
proof -
  have e1: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T1 i = Some u" using first by (simp add: store_memoized_def)
  have p: "shared_pattern_project T2 (binding_resolve S2 p) = shared_pattern_project T (binding_resolve S p)"
    if pf: "shared_pattern_formed T p" for p
  proof -
    have "shared_pattern_formed T1 p" using shared_pattern_extended[OF table pf e1[rule_format]] by blast
    then have "shared_pattern_project T2 (binding_resolve S2 p) = shared_pattern_project T1 (binding_resolve S1 p)"
      using second by (simp add: store_memoized_def)
    also have "\<dots> = shared_pattern_project T (binding_resolve S p)" using first pf by (simp add: store_memoized_def)
    finally show ?thesis .
  qed
  show ?thesis using first second p unfolding store_memoized_def by simp
qed

lemma store_memoized_extended:
  assumes S: "binding_store_formed T S" and table: "table_formed T" and table': "table_formed T'"
    and ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u"
  shows "store_memoized T S T' S"
proof -
  have "shared_pattern_project T' (binding_resolve S p) = shared_pattern_project T (binding_resolve S p)"
    if "shared_pattern_formed T p" for p
    using shared_pattern_extended[OF table binding_resolve_formed[OF S that] ext[rule_format]] by blast
  then show ?thesis using binding_store_formed_extended[OF S table ext] table' ext unfolding store_memoized_def by blast
qed

text \<open>A memoized store's resolutions hold the variables they held: they project as before.\<close>

lemma store_memoized_variables:
  assumes m: "store_memoized T S T' S'" and S: "binding_store_formed T S" and table: "table_formed T"
    and p: "shared_pattern_formed T p"
  shows "shared_pattern_variables (binding_resolve S' p) = shared_pattern_variables (binding_resolve S p)"
proof -
  have ext: "\<forall>i u. reference_term T i = Some u \<longrightarrow> reference_term T' i = Some u" and S': "binding_store_formed T' S'"
    and pr: "shared_pattern_project T' (binding_resolve S' p) = shared_pattern_project T (binding_resolve S p)"
    using m p by (simp_all add: store_memoized_def)
  have p': "shared_pattern_formed T' p" using shared_pattern_extended[OF table p ext[rule_format]] by blast
  have "shared_pattern_variables (binding_resolve S' p) =
      finite_pattern_variables (shared_pattern_project T' (binding_resolve S' p))"
    by (rule shared_pattern_variables_project[OF binding_resolve_formed[OF S' p']])
  also have "\<dots> = finite_pattern_variables (shared_pattern_project T (binding_resolve S p))" using pr by simp
  also have "\<dots> = shared_pattern_variables (binding_resolve S p)"
    by (rule shared_pattern_variables_project[symmetric, OF binding_resolve_formed[OF S p]])
  finally show ?thesis .
qed

theorem store_memoize_memoized:
  assumes S: "binding_store_formed T S" and table: "table_formed T" and rep: "keyed_state_represents st T"
  shows "\<exists>T'. keyed_state_represents (snd (store_memoize S a st)) T' \<and> store_memoized T S T' (fst (store_memoize S a st))"
proof (cases "binding_map S a")
  case None
  then show ?thesis using S table rep store_memoized_refl[OF S table] by (auto simp: store_memoize_def)
next
  case (Some x)
  obtain ra qa where a: "binding_map S a = Some (ra, qa)" using Some by (cases x) auto
  let ?T' = "snd (share_collapse (binding_resolve S qa) T)"
  note E = store_memoize_exact[OF S table rep a]
  obtain q st' where k: "keyed_binding_resolve S qa st = (q, st')" by (cases "keyed_binding_resolve S qa st")
  have memo: "store_memoize S a st = (store_compress S a q, st')" using a k by (simp add: store_memoize_def)
  have fields: "binding_next_rank (store_compress S a q) = binding_next_rank S"
    "\<And>b. binding_map (store_compress S a q) b = None \<longleftrightarrow> binding_map S b = None"
    using a by (auto simp: store_compress_def split: option.splits)
  show ?thesis using E memo fields unfolding store_memoized_def by (intro exI[of _ ?T']) simp
qed

subsection \<open>The store read through a red-black tree at a variable key\<close>

text \<open>
  The store's code holds its bindings in a red-black tree at a key injective on its variables: the index
  notion's tree carrier (@{text Tree_Map_Indexes}) read through the key
  (@{thm [source] carrier_index_through_key}), updated in place by insertion
  (@{text tree_map_updates}). The key is read only for equality through the tree's order, never presented.
  A tree represents a store on the variables Q when every variable of Q is looked up at its key to its
  binding; resolution through the tree is then the store's at every pattern over Q.
\<close>

type_synonym ('k,'a) binding_tree = "nat \<times> ('k, nat \<times> 'a shared_pattern) rbt"

definition binding_tree_store :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,'a) binding_tree \<Rightarrow> 'a binding_store" where
  "binding_tree_store key K = \<lparr>binding_next_rank = fst K, binding_map = (\<lambda>a. RBT.lookup (snd K) (key a))\<rparr>"

definition binding_tree_represents :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a set \<Rightarrow> ('k,'a) binding_tree \<Rightarrow> 'a binding_store \<Rightarrow> bool" where
  "binding_tree_represents key Q K S \<longleftrightarrow> fst K = binding_next_rank S \<and>
    (\<forall>a\<in>Q. RBT.lookup (snd K) (key a) = binding_map S a)"

definition binding_store_within :: "'a set \<Rightarrow> 'a binding_store \<Rightarrow> bool" where
  "binding_store_within Q S \<longleftrightarrow> dom (binding_map S) \<subseteq> Q \<and>
    (\<forall>a r q. binding_map S a = Some (r, q) \<longrightarrow> fset (shared_pattern_variables q) \<subseteq> Q)"

lemma binding_rows_index:
  assumes key: "inj_on key Q"
  shows "carrier_index (\<lambda>(rows :: ('a \<times> nat \<times> 'a shared_pattern) list) a v. (a, v) \<in> set rows)
    (\<lambda>rows. distinct (map fst rows) \<and> fst ` set rows \<subseteq> Q) Q key
    (\<lambda>rows. RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows)) tree_search"
proof (rule carrier_index_through_key[OF tree_map_carrier_index])
  fix rows :: "('a \<times> nat \<times> 'a shared_pattern) list"
  assume rows: "distinct (map fst rows) \<and> fst ` set rows \<subseteq> Q"
  have keys: "map fst (map (\<lambda>(a, v). (key a, v)) rows) = map key (map fst rows)" by (induction rows) auto
  have "inj_on key (set (map fst rows))" using key rows by (auto intro: inj_on_subset)
  then have d: "distinct (map key (map fst rows))" using rows by (simp only: distinct_map)
  show "distinct (map fst (map (\<lambda>(a, v). (key a, v)) rows))" unfolding keys by (rule d)
next
  fix rows :: "('a \<times> nat \<times> 'a shared_pattern) list" and k v
  assume rows: "distinct (map fst rows) \<and> fst ` set rows \<subseteq> Q"
  show "(k, v) \<in> set (map (\<lambda>(a, v). (key a, v)) rows) \<longleftrightarrow> (\<exists>q\<in>Q. key q = k \<and> (q, v) \<in> set rows)"
  proof
    assume "(k, v) \<in> set (map (\<lambda>(a, v). (key a, v)) rows)"
    then obtain a where av: "(a, v) \<in> set rows" and k: "k = key a" by auto
    have "a \<in> fst ` set rows" using av by (rule rev_image_eqI) simp
    then have "a \<in> Q" using rows by blast
    then show "\<exists>q\<in>Q. key q = k \<and> (q, v) \<in> set rows" using av k by blast
  next
    assume "\<exists>q\<in>Q. key q = k \<and> (q, v) \<in> set rows"
    then obtain q where "key q = k" "(q, v) \<in> set rows" by blast
    then show "(k, v) \<in> set (map (\<lambda>(a, v). (key a, v)) rows)" by (auto intro!: bexI[of _ "(q, v)"])
  qed
next
  show "inj_on key Q" by (rule key)
qed

definition binding_tree_load :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> nat \<Rightarrow> ('a \<times> nat \<times> 'a shared_pattern) list \<Rightarrow>
    ('k,'a) binding_tree" where
  "binding_tree_load key n rows = (n, RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows))"

theorem binding_tree_load_represents:
  assumes key: "inj_on key Q" and rows: "distinct (map fst rows)" "fst ` set rows \<subseteq> Q"
  shows "binding_tree_represents key Q (binding_tree_load key n rows)
    \<lparr>binding_next_rank = n, binding_map = map_of rows\<rparr>"
proof -
  interpret rows_index: carrier_index "\<lambda>(rows :: ('a \<times> nat \<times> 'a shared_pattern) list) a v. (a, v) \<in> set rows"
    "\<lambda>rows. distinct (map fst rows) \<and> fst ` set rows \<subseteq> Q" Q key
    "\<lambda>rows. RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows)" tree_search
    by (rule binding_rows_index[OF key])
  have "RBT.lookup (RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows)) (key a) = map_of rows a" if a: "a \<in> Q" for a
  proof (rule option_eq_by_Some)
    fix v
    have "RBT.lookup (RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows)) (key a) = Some v \<longleftrightarrow> (a, v) \<in> set rows"
      by (rule rows_index.query_search[OF conjI[OF rows] a])
    also have "\<dots> \<longleftrightarrow> map_of rows a = Some v" by (rule map_of_eq_Some_iff[OF rows(1), symmetric])
    finally show "RBT.lookup (RBT.bulkload (map (\<lambda>(a, v). (key a, v)) rows)) (key a) = Some v \<longleftrightarrow>
      map_of rows a = Some v" .
  qed
  then show ?thesis by (simp add: binding_tree_represents_def binding_tree_load_def)
qed

definition binding_tree_empty :: "('k::linorder,'a) binding_tree" where
  "binding_tree_empty = (0, RBT.empty)"

theorem binding_tree_empty_represents: "binding_tree_represents key Q binding_tree_empty binding_store_empty"
  by (simp add: binding_tree_represents_def binding_tree_empty_def binding_store_empty_def)


definition binding_tree_bind :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,'a) binding_tree \<Rightarrow> ('a \<times> 'a shared_pattern) list \<Rightarrow>
    ('k,'a) binding_tree" where
  "binding_tree_bind key K s = (Suc (fst K), fold (\<lambda>(a, p) t. RBT.insert (key a) (fst K, p) t) (rev s) (snd K))"

lemma binding_tree_fold_lookup:
  assumes key: "inj_on key Q" and s: "set (map fst s) \<subseteq> Q" and b: "b \<in> Q"
  shows "RBT.lookup (fold (\<lambda>(a, p) t. RBT.insert (key a) (n, p) t) (rev s) t) (key b) =
    (case map_of s b of Some p \<Rightarrow> Some (n, p) | None \<Rightarrow> RBT.lookup t (key b))"
  using s
proof (induction s)
  case Nil
  then show ?case by simp
next
  case (Cons x s)
  obtain a p where x: "x = (a, p)" by (cases x)
  have a: "a \<in> Q" using Cons.prems x by simp
  have eq: "key b = key a \<longleftrightarrow> b = a" using inj_onD[OF key _ b a] by blast
  have insert: "RBT.lookup (RBT.insert (key a) (n, p) U) (key b) = (if key b = key a then Some (n, p) else RBT.lookup U (key b))"
    for U by (rule option_eq_by_Some) (auto simp: tree_map_updates.updated)
  show ?case using Cons x eq by (simp add: insert)
qed

theorem binding_tree_bind_represents:
  assumes key: "inj_on key Q" and s: "set (map fst s) \<subseteq> Q" and rep: "binding_tree_represents key Q K S"
  shows "binding_tree_represents key Q (binding_tree_bind key K s)
    (store_bind S (shared_binding_substitution s) (shared_binding_domain s))"
proof -
  have "RBT.lookup (snd (binding_tree_bind key K s)) (key b) =
      bound_map (binding_next_rank S) (binding_map S) (shared_binding_substitution s) (shared_binding_domain s) b"
    if b: "b \<in> Q" for b
  proof (cases "map_of s b")
    case None
    then have "b |\<notin>| shared_binding_domain s"
      by (simp add: shared_binding_domain_def fset_of_list.rep_eq map_of_eq_None_iff)
    then show ?thesis using binding_tree_fold_lookup[OF key s b, where n="fst K" and t="snd K"] rep b None
      by (simp add: binding_tree_bind_def binding_tree_represents_def bound_map_def)
  next
    case (Some p)
    then have "b |\<in>| shared_binding_domain s"
      by (force simp: shared_binding_domain_def fset_of_list.rep_eq dest: map_of_SomeD)
    then show ?thesis using binding_tree_fold_lookup[OF key s b, where n="fst K" and t="snd K"] rep Some
      by (simp add: binding_tree_bind_def binding_tree_represents_def bound_map_def shared_binding_substitution_def)
  qed
  then show ?thesis using rep by (simp add: binding_tree_represents_def store_bind_def binding_tree_bind_def)
qed

lemma store_bind_within:
  assumes "binding_store_within Q S" "fset D \<subseteq> Q" "\<forall>a. a |\<in>| D \<longrightarrow> fset (shared_pattern_variables (\<sigma> a)) \<subseteq> Q"
  shows "binding_store_within Q (store_bind S \<sigma> D)"
  using assms by (auto simp: binding_store_within_def store_bind_def bound_map_def dom_def split: if_splits)

lemma store_compress_within:
  assumes "binding_store_within Q S" "fset (shared_pattern_variables q) \<subseteq> Q"
  shows "binding_store_within Q (store_compress S a q)"
  using assms by (auto simp: binding_store_within_def store_compress_def dom_def split: if_splits)

lemma binding_resolve_from_agree:
  "\<forall>a\<in>Q. M' a = M a \<Longrightarrow>
    \<forall>a r q. M a = Some (r, q) \<longrightarrow> shared_pattern_formed T q \<and> fset (shared_pattern_variables q) \<subseteq> Q \<Longrightarrow>
    shared_pattern_formed T p \<Longrightarrow> fset (shared_pattern_variables p) \<subseteq> Q \<Longrightarrow>
    binding_resolve_from n r M' p = binding_resolve_from n r M p \<and>
      keyed_resolve_from n r M' p st = keyed_resolve_from n r M p st"
proof (induction n r M p arbitrary: st rule: binding_resolve_from_induct)
  case (bound n r M a r' u)
  have aQ: "a \<in> Q" using bound.prems(4) by simp
  have u: "shared_pattern_formed T u" "fset (shared_pattern_variables u) \<subseteq> Q"
    using bound.prems(2) bound.hyps(1) by blast+
  have M': "M' a = Some (r', u)" using bound.prems(1) aQ bound.hyps(1) by simp
  show ?case using bound.IH[OF bound.prems(1,2) u] bound.hyps
      M' bound.hyps
      M'
    by simp
next
  case (unbound n r M a)
  have aQ: "a \<in> Q" using unbound.prems(4) by simp
  have h: "\<not> (\<exists>r' u. M' a = Some (r', u) \<and> r \<le> r' \<and> r' < n)" using unbound.hyps unbound.prems(1) aQ by simp
  show ?case using binding_resolve_from_unfollowed[of M a r n, OF unbound.hyps] binding_resolve_from_unfollowed[of M' a r n, OF h]
      keyed_resolve_from_unfollowed[of M a r n st, OF unbound.hyps] keyed_resolve_from_unfollowed[of M' a r n st, OF h]
    by simp
next
  case (ground n r M i)
  show ?case by simp
next
  case (node n r M A p q)
  have A: "A = shared_pattern_variables p |\<union>| shared_pattern_variables q"
    and fp: "shared_pattern_formed T p" and fq: "shared_pattern_formed T q" using node.prems(3) by simp_all
  have AQ: "fset A \<subseteq> Q" using node.prems(4) by simp
  have agreeA: "\<forall>a. a |\<in>| A \<longrightarrow> M' a = M a" using node.prems(1) AQ by blast
  have test: "fBall A (\<lambda>a. M' a = None) = fBall A (\<lambda>a. M a = None)"
    by (rule fBall_cong) (use agreeA in auto)
  show ?case
  proof (cases "fBall A (\<lambda>a. M a = None)")
    case True
    have new: "fBall A (\<lambda>a. M' a = None)" unfolding test by (rule True)
    show ?thesis unfolding binding_resolve_from_kept[OF True] binding_resolve_from_kept[OF new]
      keyed_resolve_from_kept[OF True] keyed_resolve_from_kept[OF new] by simp
  next
    case False
    have new: "\<not> fBall A (\<lambda>a. M' a = None)" unfolding test by (rule False)
    have e1: "binding_resolve_from n r M' p = binding_resolve_from n r M p \<and>
        keyed_resolve_from n r M' p st' = keyed_resolve_from n r M p st'" for st'
      by (rule node.IH(1)[OF False]) (use node.prems A AQ fp in auto)
    have e2: "binding_resolve_from n r M' q = binding_resolve_from n r M q \<and>
        keyed_resolve_from n r M' q st' = keyed_resolve_from n r M q st'" for st'
      by (rule node.IH(2)[OF False]) (use node.prems A AQ fq in auto)
    show ?thesis unfolding binding_resolve_from_node[OF new] binding_resolve_from_node[OF False]
      keyed_resolve_from_node[OF new] keyed_resolve_from_node[OF False] using e1 e2 by simp
  qed
qed

theorem binding_tree_resolve:
  assumes rep: "binding_tree_represents key Q K S" and within: "binding_store_within Q S"
    and S: "binding_store_formed T S" and p: "shared_pattern_formed T p"
    and pQ: "fset (shared_pattern_variables p) \<subseteq> Q"
  shows "binding_resolve (binding_tree_store key K) p = binding_resolve S p"
    and "keyed_binding_resolve (binding_tree_store key K) p st = keyed_binding_resolve S p st"
proof -
  have agree: "\<forall>a\<in>Q. RBT.lookup (snd K) (key a) = binding_map S a"
    using rep by (simp add: binding_tree_represents_def)
  have M: "\<forall>a r q. binding_map S a = Some (r, q) \<longrightarrow> shared_pattern_formed T q \<and> fset (shared_pattern_variables q) \<subseteq> Q"
    using binding_store_formedD(3)[OF S] within by (auto simp: binding_store_within_def)
  have e: "binding_resolve_from (binding_next_rank S) 0 (\<lambda>a. RBT.lookup (snd K) (key a)) p =
      binding_resolve_from (binding_next_rank S) 0 (binding_map S) p \<and>
    keyed_resolve_from (binding_next_rank S) 0 (\<lambda>a. RBT.lookup (snd K) (key a)) p st =
      keyed_resolve_from (binding_next_rank S) 0 (binding_map S) p st"
    by (rule binding_resolve_from_agree[OF agree M p pQ])
  have n: "fst K = binding_next_rank S" using rep by (simp add: binding_tree_represents_def)
  show "binding_resolve (binding_tree_store key K) p = binding_resolve S p"
    using e n by (simp add: binding_resolve_def binding_tree_store_def)
  show "keyed_binding_resolve (binding_tree_store key K) p st = keyed_binding_resolve S p st"
    using e n by (simp add: keyed_binding_resolve_def binding_tree_store_def)
qed

text \<open>
  Compression in the tree: a binding replaced in place at its key, its rank kept; memoization replaces it by
  its keyed resolution read through the tree. Both represent the store's operations.
\<close>

definition binding_tree_compress :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,'a) binding_tree \<Rightarrow> 'a \<Rightarrow> 'a shared_pattern \<Rightarrow>
    ('k,'a) binding_tree" where
  "binding_tree_compress key K a q = (case RBT.lookup (snd K) (key a) of None \<Rightarrow> K
    | Some x \<Rightarrow> (fst K, RBT.insert (key a) (fst x, q) (snd K)))"

theorem binding_tree_compress_represents:
  assumes key: "inj_on key Q" and a: "a \<in> Q" and rep: "binding_tree_represents key Q K S"
  shows "binding_tree_represents key Q (binding_tree_compress key K a q) (store_compress S a q)"
proof -
  have la: "RBT.lookup (snd K) (key a) = binding_map S a" using rep a by (simp add: binding_tree_represents_def)
  have insert: "RBT.lookup (RBT.insert (key a) w U) (key b) = (if key b = key a then Some w else RBT.lookup U (key b))"
    for w U b by (rule option_eq_by_Some) (auto simp: tree_map_updates.updated)
  have eq: "key b = key a \<longleftrightarrow> b = a" if "b \<in> Q" for b using inj_onD[OF key _ that a] by blast
  show ?thesis
  proof (cases "binding_map S a")
    case None
    then show ?thesis using rep la
      by (auto simp: binding_tree_compress_def binding_tree_represents_def store_compress_def)
  next
    case (Some x)
    then show ?thesis using rep la eq
      by (auto simp: binding_tree_compress_def binding_tree_represents_def store_compress_def insert)
  qed
qed

definition binding_tree_memoize :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,'a) binding_tree \<Rightarrow> 'a \<Rightarrow> share_state \<Rightarrow>
    ('k,'a) binding_tree \<times> share_state" where
  "binding_tree_memoize key K a st = (case RBT.lookup (snd K) (key a) of None \<Rightarrow> (K, st)
    | Some x \<Rightarrow> (case keyed_binding_resolve (binding_tree_store key K) (snd x) st of
        (q, st') \<Rightarrow> (binding_tree_compress key K a q, st')))"

theorem binding_tree_memoize_represents:
  assumes key: "inj_on key Q" and a: "a \<in> Q" and rep: "binding_tree_represents key Q K S"
    and within: "binding_store_within Q S" and S: "binding_store_formed T S"
  shows "binding_tree_represents key Q (fst (binding_tree_memoize key K a st)) (fst (store_memoize S a st)) \<and>
    snd (binding_tree_memoize key K a st) = snd (store_memoize S a st)"
proof (cases "binding_map S a")
  case None
  have "RBT.lookup (snd K) (key a) = None" using rep a None by (simp add: binding_tree_represents_def)
  then show ?thesis using rep None by (simp add: binding_tree_memoize_def store_memoize_def)
next
  case (Some x)
  obtain r u where x: "x = (r, u)" by (cases x)
  have l: "RBT.lookup (snd K) (key a) = Some (r, u)" using rep a Some x by (simp add: binding_tree_represents_def)
  have u: "shared_pattern_formed T u" "fset (shared_pattern_variables u) \<subseteq> Q"
    using binding_store_formedD(3)[OF S] within Some x unfolding binding_store_within_def by blast+
  have k: "keyed_binding_resolve (binding_tree_store key K) u st = keyed_binding_resolve S u st"
    by (rule binding_tree_resolve(2)[OF rep within S u])
  obtain q st' where e: "keyed_binding_resolve S u st = (q, st')" by (cases "keyed_binding_resolve S u st")
  have m: "binding_tree_memoize key K a st = (binding_tree_compress key K a q, st')"
    using l k e by (simp add: binding_tree_memoize_def)
  have s: "store_memoize S a st = (store_compress S a q, st')" using Some x e by (simp add: store_memoize_def)
  show ?thesis using m s binding_tree_compress_represents[OF key a rep] by simp
qed

end
