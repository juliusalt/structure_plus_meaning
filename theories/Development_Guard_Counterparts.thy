theory Development_Guard_Counterparts
  imports Development_First_Problem_Guard Factor_Audit_Counterparts Factor_Additions_Counterparts
begin

text \<open>
  The guard's counterparts (DECISIONS.md "The native evaluator evaluates above an implemented base: the given's
  readers enter through counterparts exact to their native definitions", build C3): 522, the audit at a
  member's site, as the argument rearrangement @{thm [source] audit_callee_rule} states before the audit's
  counterpart; 525, the additions counterpart at 522's; and the guard's base, a decision at each of 113, 80, 392
  and 525 by its counterpart, exact at every finite term to the site's call in the guard's program.
\<close>

section \<open>The audit at a member's site (522)\<close>

definition finite_audit_callee :: "finite_factor_term \<Rightarrow> bool" where
  "finite_audit_callee z=(case z of Finite_Pair (Finite_Pair x (Finite_Pair y c)) (Finite_Pair a b) \<Rightarrow>
      finite_term_formed x \<and> finite_term_formed c \<and> finite_payload_audit (Finite_Pair (Finite_Pair y a) b)
    | _ \<Rightarrow> False)"

lemma finite_audit_callee_parts:
  "finite_audit_callee z \<longleftrightarrow> (\<exists>x y c a b. z=Finite_Pair (Finite_Pair x (Finite_Pair y c)) (Finite_Pair a b) \<and>
    finite_term_formed x \<and> finite_term_formed c \<and> finite_payload_audit (Finite_Pair (Finite_Pair y a) b))"
  by (auto simp: finite_audit_callee_def split: finite_factor_term.splits)

theorem finite_audit_callee_exact:
  "finite_audit_callee z \<longleftrightarrow> (522,decode_finite_term z)\<in>positive_meaning first_problem_goals_system"
proof -
  have "(\<exists>x y c a b. z=Finite_Pair (Finite_Pair x (Finite_Pair y c)) (Finite_Pair a b) \<and>
      finite_term_formed x \<and> finite_term_formed c \<and> finite_payload_audit (Finite_Pair (Finite_Pair y a) b)) \<longleftrightarrow>
    (\<exists>x y c a b. decode_finite_term z=Pair_Term (Pair_Term x (Pair_Term y c)) (Pair_Term a b) \<and>
      term_formed x \<and> term_formed c \<and> (505,Pair_Term (Pair_Term y a) b)\<in>positive_meaning payload_audit_system)"
    by (auto simp: decode_finite_pair_iff finite_term_formed_correct finite_payload_audit_meaning)
  then show ?thesis by (simp only: finite_audit_callee_parts audit_callee_rule)
qed

section \<open>The audit goal (525): the additions counterpart at the audit's\<close>

definition finite_audit_additions :: "finite_factor_term \<Rightarrow> bool" where
  "finite_audit_additions=finite_package_additions finite_audit_callee"

theorem finite_audit_additions_exact:
  "finite_audit_additions z \<longleftrightarrow> (525,decode_finite_term z)\<in>positive_meaning first_problem_goals_system"
  using finite_package_additions_exact[where C="\<lambda>t. (522,t)\<in>positive_meaning first_problem_goals_system",
    OF finite_audit_callee_exact, of z]
  by (simp only: finite_audit_additions_def audit_additions.exact)

corollary finite_audit_additions_on_values:
  assumes pair: "decode_finite_term z=Pair_Term t w"
    and first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "finite_audit_additions z \<longleftrightarrow> (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
  by (simp only: finite_audit_additions_exact pair audit_goal_on_values[OF first second])

section \<open>The guard's base\<close>

text \<open>
  One decision on the guard's calls, keyed by site: at 113 and 80 C1's counterparts, at 392 C2's, at 525 the
  audit goal's. It is exact at every call of the base to the guard's program, the form a base's decision takes
  in @{text Factor_Implemented_Base_Evaluation}'s exactness; each site's meaning is carried to the guard's program by
  @{thm [source] first_problem_goals_components} and the installation's unchanged original meaning. Outside the
  base it decides nothing.
\<close>

definition guard_base :: "nat fset" where
  "guard_base={|113,80,392,525|}"

definition guard_base_decision :: "nat\<times>finite_factor_term \<Rightarrow> bool" where
  "guard_base_decision q=(if fst q=113 then finite_environment_inclusion_decision (snd q)
    else if fst q=80 then finite_package_admission_decision (snd q)
    else if fst q=392 then finite_use_additions (snd q)
    else fst q=525 \<and> finite_audit_additions (snd q))"

theorem guard_base_decision_exact:
  assumes base: "fst q |\<in>| guard_base"
  shows "guard_base_decision q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning first_problem_guard_system"
proof -
  obtain d t where q: "q=(d,t)" by (cases q)
  have site: "d=113 \<or> d=80 \<or> d=392 \<or> d=525" using base by (simp add: q guard_base_def)
  have member: "d\<in>system_definitions first_problem_goals_system"
    using site guard_reader_sites goal_sites by auto
  have guard: "(d,decode_finite_term t)\<in>positive_meaning first_problem_guard_system \<longleftrightarrow>
      (d,decode_finite_term t)\<in>positive_meaning first_problem_goals_system"
    by (rule first_problem_guard.unchanged_original_meaning[OF member])
  show ?thesis using site guard
    by (elim disjE) (simp_all add: q decode_finite_call_term_def guard_base_decision_def first_problem_goals_components
      finite_environment_inclusion_decision_meaning finite_package_admission_decision_meaning
      finite_use_additions_exact finite_audit_additions_exact)
qed

section \<open>Controls\<close>

text \<open>
  The audit goal at the pair of the empty package's site and the site of the installed one-definition
  program: the given's package holds nothing, so the added definition passes exactly when the audit holds of
  it. Beside each outcome, the payloads the added definition states, which the relation's outcome is by the
  exactness above.
\<close>

definition audit_goal_control :: "octets \<Rightarrow> (bool\<times>octets fset fset option) option" where
  "audit_goal_control v=map_option (\<lambda>(K,w).
      (finite_audit_additions (Finite_Pair (control_site (fst audit_control_selection) (snd audit_control_selection) [])
        (control_site K w [])),
      map_option (\<lambda>R. ffUnion (fimage (\<lambda>d. fimage (\<lambda>(p,F). finite_definition_payloads p F)
        (finite_native_definition_readings K (fst d) (snd d))) (finite_system_definitions R))) (finite_native_source K w [])))
    (audit_control_installed v)"

value "[(''525: the added definition states the empty payload'', audit_goal_control []),
  (''525: the added definition states the literal [1]'', audit_goal_control [1])]"

end
