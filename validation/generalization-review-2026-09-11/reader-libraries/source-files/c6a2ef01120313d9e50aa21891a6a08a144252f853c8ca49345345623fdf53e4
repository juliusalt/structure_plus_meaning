theory Observation_Invariance
  imports Obligation_Reductions
begin

section \<open>Equality of observations is preserved along every finite path\<close>

theorem observation_invariance_closure:
  "rel_fun (rtranclp E) (=) f f \<longleftrightarrow> rel_fun E (=) f f"
proof
  assume all: "rel_fun (rtranclp E) (=) f f"
  show "rel_fun E (=) f f"
    using all r_into_rtranclp by (auto simp: rel_fun_def)
next
  assume local: "rel_fun E (=) f f"
  have same: "f p=f q" if "E p q" for p q
    using local that by (auto simp: rel_fun_def)
  have paths: "f p=f q" if "rtranclp E p q" for p q
    using that by (induction rule: rtranclp_induct) (use same in auto)
  show "rel_fun (rtranclp E) (=) f f" using paths by (simp add: rel_fun_def)
qed

theorem observation_invariance_pair:
  "rel_fun E (=) (\<lambda>p. (f p,g p)) (\<lambda>p. (f p,g p)) \<longleftrightarrow>
    rel_fun E (=) f f \<and> rel_fun E (=) g g"
  by (auto simp: rel_fun_def)

theorem observation_invariance_same_closure:
  assumes "rtranclp E=rtranclp F"
  shows "rel_fun E (=) f f \<longleftrightarrow> rel_fun F (=) f f"
proof -
  have left: "rel_fun E (=) f f \<longleftrightarrow> rel_fun (rtranclp E) (=) f f"
    by (rule observation_invariance_closure[symmetric])
  have right: "rel_fun (rtranclp F) (=) f f \<longleftrightarrow> rel_fun F (=) f f"
    by (rule observation_invariance_closure)
  show ?thesis using left right assms by simp
qed

lemma relational_path_simulation:
  assumes steps: "\<And>p q. E p q \<Longrightarrow> rtranclp F (h p) (h q)"
    and path: "rtranclp E p q"
  shows "rtranclp F (h p) (h q)"
  using path by (induction rule: rtranclp_induct)
    (auto intro: rtranclp_trans steps)

section \<open>Every comparison keeps its observation and both endpoints\<close>

definition observation_condition :: "(('p \<Rightarrow> 'v) \<times> 'p \<times> 'p) \<Rightarrow> bool" where
  "observation_condition c \<longleftrightarrow> fst c (fst (snd c))=fst c (snd (snd c))"

definition observation_obligations ::
  "('p \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow> ('p \<Rightarrow> 'v) \<Rightarrow>
    (('p \<times> 'p) \<times> (('p \<Rightarrow> 'v) \<times> 'p \<times> 'p)) set" where
  "observation_obligations E f = {((p,q),(f,p,q)) |p q. E p q}"

lemma observation_obligation_member [simp]:
  "((p,q),c)\<in>observation_obligations E f \<longleftrightarrow> E p q \<and> c=(f,p,q)"
  by (auto simp: observation_obligations_def)

lemma observation_obligations_functional:
  "single_valued (observation_obligations E f)"
  by (auto simp: single_valued_def)

lemma observation_obligations_finite:
  assumes "finite {(p,q). E p q}"
  shows "finite (observation_obligations E f)"
proof -
  have image: "observation_obligations E f=
      (\<lambda>(p,q). ((p,q),(f,p,q))) ` {(p,q). E p q}"
    by (auto simp: observation_obligations_def)
  show ?thesis by (simp only: image; rule finite_imageI[OF assms])
qed

theorem observation_obligations_exact:
  "rel_ran (observation_obligations E f)\<subseteq>{c. observation_condition c} \<longleftrightarrow>
    rel_fun E (=) f f"
proof
  assume all: "rel_ran (observation_obligations E f)\<subseteq>{c. observation_condition c}"
  show "rel_fun E (=) f f"
    unfolding rel_fun_def
  proof (intro allI impI)
    fix p q assume edge: "E p q"
    have member: "(f,p,q)\<in>rel_ran (observation_obligations E f)"
      unfolding rel_ran_def by (rule CollectI, rule exI[of _ "(p,q)"]) (use edge in simp)
    have "observation_condition (f,p,q)" using subsetD[OF all member] by simp
    then show "f p=f q" by (simp add: observation_condition_def)
  qed
next
  assume local: "rel_fun E (=) f f"
  show "rel_ran (observation_obligations E f)\<subseteq>{c. observation_condition c}"
    using local by (auto simp: observation_obligations_def observation_condition_def rel_ran_def rel_fun_def)
qed

theorem observation_invariance_reduction:
  "exact_obligation_reduction UNIV (\<lambda>f. rel_fun E (=) f f)
    observation_condition (observation_obligations E)"
  by (simp add: exact_obligation_reduction_def observation_obligations_exact)

theorem observation_residual_occurrences:
  "rel_dom (remaining_obligations K (observation_obligations E f))=
    {(p,q). E p q \<and> (f,p,q)\<notin>K}"
  by (auto simp: rel_dom_def)

theorem observation_refutation_remains:
  assumes edge: "E p q" and different: "f p\<noteq>f q"
    and known: "K\<subseteq>{c. observation_condition c}"
  shows "((p,q),(f,p,q))\<in>remaining_obligations K (observation_obligations E f)"
  using assms by (auto simp: observation_condition_def)

text \<open>
  The standard function relator expresses an observation's invariance. Its
  equality is value-polymorphic; predicates are one instance. A single-step
  preservation law is equivalent to preservation along every finite path.
  Simulating edges by paths therefore reuses the same invariant observations.

  The exact reduction retains the actual function and both compared endpoints.
  Equal outcomes do not merge different endpoint occurrences. A finite edge
  relation gives a finite family, while a quantified generator may be infinite.
  The reduction checks preservation; it does not establish that those edges
  cover the independently required equivalence relation.
\<close>

end
