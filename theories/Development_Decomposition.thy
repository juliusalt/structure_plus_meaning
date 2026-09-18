theory Development_Decomposition
  imports Development_Problems
begin

section \<open>Decomposition is inference over a library of rules, apart from prerequisites\<close>

text \<open>
  Two relations between problems are kept apart. A prerequisite row states that a problem's own
  answer needs other answers first; it fires only once the problem itself is answered. A
  decomposition rule of the development library states that a problem is settled by composing
  the answers of its subproblems; it fires when every subproblem is settled, and its head is
  never answered on its own. Settlement is the least closure of both, so the composition law is
  the existing one of finite inference, and a rule with an unsettled subproblem settles nothing.

  A problem is issued to an executor only as a leaf: no rule of the library has it as its head.
  That is an account of the problem's decomposition scope, the library, and not a search that
  found nothing at some bound. A problem some rule decomposes is never issued as a broad request;
  its subproblems are. The leaf reading is an absence, so it is retained with the issued request:
  extending the library with a rule for the problem changes the reading, and the request is no
  longer current.
\<close>

definition development_leaf :: "development_dependencies \<Rightarrow> development_problem \<Rightarrow> bool" where
  "development_leaf L p \<longleftrightarrow> fBall L (\<lambda>(q,H). q\<noteq>p)"

definition development_library_reading :: "development_dependencies \<Rightarrow> development_problem \<Rightarrow> (nat\<times>development_problem) fset fset" where
  "development_library_reading L p=development_decompositions L p"

lemma development_leaf_reading:
  "development_leaf L p \<longleftrightarrow> development_library_reading L p={||}"
proof -
  have "development_library_reading L p={||} \<longleftrightarrow> ffilter (\<lambda>(q,H). q=p) L={||}"
    by (simp add: development_library_reading_def development_decompositions_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>x. x |\<in>| L \<longrightarrow> \<not>(case x of (q,H) \<Rightarrow> q=p))"
    by (auto simp: fset_eq_iff)
  also have "\<dots> \<longleftrightarrow> development_leaf L p"
    by (auto simp: development_leaf_def)
  finally show ?thesis by simp
qed

definition development_composed_settled ::
    "development_dependencies \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem set" where
  "development_composed_settled D L answered=finite_inference_result (development_answered_rules D answered |\<union>| L) {||}"

theorem development_composed_settled_exact:
  "development_composed_settled D L answered=
    inference_closure (finite_inference_rules (development_answered_rules D answered |\<union>| L)) {}"
  by (simp add: development_composed_settled_def finite_inference_result_exact)

text \<open>
  Without decomposition rules the composed settlement is the existing settlement, so every
  decision already made on prerequisites alone is unchanged.
\<close>

lemma development_composed_settled_empty:
  "development_composed_settled D {||} answered=development_settled D answered"
  by (simp only: development_composed_settled_def development_settled_def sup_bot_right)

text \<open>
  A decomposition rule whose subproblems are all settled settles its head: this is the
  composition law, instantiated from the least closure rather than restated.
\<close>

theorem development_composition_settles:
  assumes rule: "(p,H) |\<in>| L" and formed: "finite_premise_functional H"
    and subproblems: "\<And>n q. (n,q) |\<in>| H \<Longrightarrow> q\<in>development_composed_settled D L answered"
  shows "p\<in>development_composed_settled D L answered"
proof -
  let ?R="finite_inference_rules (development_answered_rules D answered |\<union>| L)"
  have member: "(p,H) |\<in>| development_answered_rules D answered |\<union>| L" using rule by simp
  have rules: "?R p (fset H)" unfolding finite_inference_rules_def using member by blast
  have functional: "single_valued (fset H)" using formed by (simp only: finite_premise_functional_exact)
  have range: "rel_ran (fset H)\<subseteq>inference_closure ?R {}"
    using subproblems by (auto simp: rel_ran_def development_composed_settled_exact)
  have "p\<in>inference_consequences ?R (inference_closure ?R {})"
    unfolding inference_consequences_def mem_Collect_eq
    by (intro exI[of _ "fset H"] conjI finite_fset rules functional range)
  then have "p\<in>{}\<union>inference_consequences ?R (inference_closure ?R {})" by (rule UnI2)
  then show ?thesis by (simp only: development_composed_settled_exact inference_closure_unfold[of ?R "{}", symmetric])
qed

definition development_issuable ::
    "development_dependencies \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem \<Rightarrow> bool" where
  "development_issuable D L answered p \<longleftrightarrow> development_leaf L p \<and> p |\<notin>| answered \<and>
    fBall (development_premises D p) (\<lambda>q. q\<in>development_composed_settled D L answered)"

theorem development_broad_refused:
  assumes "(p,H) |\<in>| L"
  shows "\<not>development_issuable D L answered p"
  using assms by (auto simp: development_issuable_def development_leaf_def)

theorem development_issuable_without_library:
  "development_issuable D {||} answered p \<longleftrightarrow> development_ready D answered p"
  by (simp add: development_issuable_def development_leaf_def development_ready_def
    development_composed_settled_empty)

definition development_issuable_problems ::
    "development_dependencies \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      development_problem list" where
  "development_issuable_problems D L answered ps=filter (development_issuable D L answered) ps"

text \<open>
  A decomposition rule with a subproblem that has no answer and no rule of its own leaves its
  head unsettled: missing premises are retained, never assumed.
\<close>

end
