theory Factor_Implemented_Base_Evaluation
  imports Shared_Native_Evaluation
begin

text \<open>
  DECISIONS.md, "The native evaluator evaluates above an implemented base", build E1. The native evaluator
  answers a demand only where every clause of a demanded definition binds in its head every variable its
  premises use. Above a base of definitions, the program loses the base's clause families and keeps its
  interfaces; the demand's base calls are seeded by a decision, and the evaluation is exact wherever that
  decision is exact to the program's positive meaning at them (@{thm [source] inference_restriction_above_base}).
\<close>

section \<open>The program above a base keeps its interfaces and loses the base's clauses\<close>

definition implemented_base_program ::
    "'d fset \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) finite_schema_system" where
  "implemented_base_program B P=
    P\<lparr>finite_system_clauses:=ffilter (\<lambda>z. fst (fst z) |\<notin>| B) (finite_system_clauses P)\<rparr>"

lemma implemented_base_program_fields [simp]:
  "finite_system_interfaces (implemented_base_program B P)=finite_system_interfaces P"
  "finite_system_clauses (implemented_base_program B P)=
    ffilter (\<lambda>z. fst (fst z) |\<notin>| B) (finite_system_clauses P)"
  by (simp_all add: implemented_base_program_def)

lemma implemented_base_decoded_clauses:
  "((d,c),S)\<in>system_clauses (decode_finite_system (implemented_base_program B P)) \<longleftrightarrow>
    ((d,c),S)\<in>system_clauses (decode_finite_system P) \<and> d |\<notin>| B"
  by (auto simp: ffilter.rep_eq)

lemma implemented_base_program_formed:
  assumes formed: "finite_system_formed P"
  shows "finite_system_formed (implemented_base_program B P)"
proof -
  let ?Q="implemented_base_program B P"
  have sub: "system_clauses (decode_finite_system ?Q)\<subseteq>system_clauses (decode_finite_system P)"
    unfolding decode_finite_system_fields implemented_base_program_fields map_relation_values_def
    by (rule image_mono) (auto simp: ffilter.rep_eq)
  have same: "system_interfaces (decode_finite_system ?Q)=system_interfaces (decode_finite_system P)"
    by simp
  have definitions: "system_definitions (decode_finite_system ?Q)=system_definitions (decode_finite_system P)"
    using finite_system_definitions_correct[of ?Q] finite_system_definitions_correct[of P]
    by (simp add: finite_system_definitions_def)
  have original: "schema_system_formed (decode_finite_system P)"
    using formed by (simp only: finite_system_formed_correct)
  have "schema_system_formed (decode_finite_system ?Q)"
    using original sub unfolding schema_system_formed_def same definitions single_valued_def
    by (blast intro: finite_subset)
  then show ?thesis by (simp only: finite_system_formed_correct)
qed

lemma implemented_base_call_formed:
  assumes formed: "finite_system_formed P"
  shows "schema_call_formed (decode_finite_system (implemented_base_program B P)) d t \<longleftrightarrow>
    schema_call_formed (decode_finite_system P) d t"
  using formed implemented_base_program_formed[OF formed]
  by (simp add: schema_call_formed_def finite_system_formed_correct)

lemma implemented_base_admitted:
  assumes formed: "finite_system_formed P"
  shows "admitted_schema_instance (decode_finite_system (implemented_base_program B P)) d c V t Q \<longleftrightarrow>
    admitted_schema_instance (decode_finite_system P) d c V t Q \<and> d |\<notin>| B"
  unfolding admitted_schema_instance_def implemented_base_call_formed[OF formed]
    implemented_base_decoded_clauses
  by blast

lemma implemented_base_rules:
  assumes formed: "finite_system_formed P"
  shows "schema_inference_rules (decode_finite_system (implemented_base_program B P)) q H \<longleftrightarrow>
    schema_inference_rules (decode_finite_system P) q H \<and> fst q |\<notin>| B"
  unfolding schema_inference_rules_def implemented_base_admitted[OF formed] by blast

section \<open>The base's demanded calls enter only through an exact decision\<close>

definition implemented_base_seeds ::
    "'d fset \<Rightarrow> ('d\<times>finite_factor_term \<Rightarrow> bool) \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow>
      ('d\<times>finite_factor_term) fset" where
  "implemented_base_seeds B decide D=ffilter (\<lambda>q. fst q |\<in>| B \<and> decide q) D"

theorem implemented_base_closure_exact:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
  assumes formed: "finite_system_formed P"
    and covered: "finite_program_head_covered (implemented_base_program B P) D"
    and closed: "finite_program_demand_closed (implemented_base_program B P) D"
    and decided: "\<And>q. q |\<in>| D \<Longrightarrow> fst q |\<in>| B \<Longrightarrow>
      decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    and demand: "q |\<in>| D"
  shows "q\<in>finite_inference_result (finite_program_rule_table (implemented_base_program B P) D)
      (implemented_base_seeds B decide D) \<longleftrightarrow>
    decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  let ?f="decode_finite_call_term :: 'd\<times>finite_factor_term \<Rightarrow> 'd\<times>factor_term"
  let ?Q="implemented_base_program B P"
  let ?F="finite_program_rule_table ?Q D"
  let ?K="implemented_base_seeds B decide D"
  let ?R="schema_inference_rules (decode_finite_system P)"
  let ?D="?f ` fset D"
  let ?B="{a. fst a |\<in>| B}"
  have fst_decode: "fst (?f x)=fst x" for x by (simp add: decode_finite_call_term_def)
  have rules: "embedded_inferences ?f (finite_inference_rules ?F)=(\<lambda>a H. ?R a H \<and> a\<in>?D \<and> a\<notin>?B)"
    by (rule ext, rule ext) (auto simp: finite_program_rules_exact[OF covered] implemented_base_rules[OF formed])
  have known: "?f ` fset ?K={}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}}"
  proof (rule set_eqI)
    fix b
    show "b\<in>?f ` fset ?K \<longleftrightarrow> b\<in>{}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}}"
    proof
      assume "b\<in>?f ` fset ?K"
      then obtain x where x: "x |\<in>| D" "fst x |\<in>| B" "decide x" "b=?f x"
        by (auto simp: implemented_base_seeds_def ffilter.rep_eq)
      show "b\<in>{}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}}"
        using x decided[OF x(1,2)] by (auto simp: fst_decode schema_inference_closure)
    next
      assume "b\<in>{}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}}"
      then obtain x where x: "x |\<in>| D" "b=?f x" "fst x |\<in>| B" "?f x\<in>positive_meaning (decode_finite_system P)"
        by (auto simp: fst_decode schema_inference_closure)
      have "x |\<in>| ?K" using x decided[OF x(1,3)] by (auto simp: implemented_base_seeds_def ffilter.rep_eq)
      then show "b\<in>?f ` fset ?K" using x(2) by blast
    qed
  qed
  have image: "?f ` finite_inference_result ?F ?K=
    inference_closure (\<lambda>a H. ?R a H \<and> a\<in>?D \<and> a\<notin>?B) ({}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}})"
    by (simp only: finite_inference_result_embedding[OF decode_finite_call_inj(2)] rules known)
  have native_closed: "program_demand_closed (decode_finite_system ?Q) ?D"
    using closed by (simp only: finite_program_demand_closed_correct[OF covered])
  have inside: "?f q\<in>?D" by (rule imageI[OF demand])
  have restricted: "?f q\<in>inference_closure (\<lambda>a H. ?R a H \<and> a\<in>?D \<and> a\<notin>?B)
      ({}\<union>{b\<in>?D. b\<in>?B \<and> b\<in>inference_closure ?R {}}) \<longleftrightarrow> ?f q\<in>inference_closure ?R {}"
  proof (rule inference_restriction_above_base[OF _ inside])
    fix a H assume demanded: "a\<in>?D" and outside: "a\<notin>?B" and "a\<notin>{}" "finite H" "single_valued H"
      and rule: "?R a H"
    have "schema_inference_rules (decode_finite_system ?Q) a H"
      using rule outside by (simp add: implemented_base_rules[OF formed])
    then show "rel_ran H\<subseteq>?D" using native_closed demanded
      unfolding program_demand_closed_def by blast
  qed
  have reflect: "?f q\<in>?f ` finite_inference_result ?F ?K \<longleftrightarrow> q\<in>finite_inference_result ?F ?K"
    using decode_finite_call_inj(2) by (auto dest: injD)
  show ?thesis using restricted by (simp only: reflect[symmetric] image schema_inference_closure)
qed

section \<open>The evaluation above an implemented base\<close>

definition implemented_base_ready ::
    "'d fset \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>finite_factor_term) fset \<Rightarrow> bool" where
  "implemented_base_ready B P D=(finite_system_formed P \<and>
    finite_program_head_covered (implemented_base_program B P) D \<and>
    finite_program_demand_closed (implemented_base_program B P) D)"

definition implemented_base_evaluation ::
    "'d fset \<Rightarrow> ('d\<times>finite_factor_term \<Rightarrow> bool) \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('d\<times>finite_factor_term) fset \<Rightarrow> ('d\<times>finite_factor_term) fset option" where
  "implemented_base_evaluation B decide P D=(if implemented_base_ready B P D then
      Some (let settled=finite_inference_result (finite_program_rule_table (implemented_base_program B P) D)
          (implemented_base_seeds B decide D)
        in ffilter (\<lambda>q. q\<in>settled) D) else None)"

theorem implemented_base_evaluation_conditions:
  "(\<exists>A. implemented_base_evaluation B decide P D=Some A) \<longleftrightarrow> implemented_base_ready B P D"
  by (simp add: implemented_base_evaluation_def)

theorem implemented_base_evaluation_unavailable:
  "\<not>implemented_base_ready B P D \<Longrightarrow> implemented_base_evaluation B decide P D=None"
  by (simp add: implemented_base_evaluation_def)

theorem implemented_base_evaluation_exact:
  assumes result: "implemented_base_evaluation B decide P D=Some A"
    and decided: "\<And>q. q |\<in>| D \<Longrightarrow> fst q |\<in>| B \<Longrightarrow>
      decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
  shows "schema_system_formed (decode_finite_system P)"
    "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
proof -
  have ready: "implemented_base_ready B P D"
    and answer: "A=ffilter (\<lambda>q. q\<in>finite_inference_result
      (finite_program_rule_table (implemented_base_program B P) D) (implemented_base_seeds B decide D)) D"
    using result by (auto simp: implemented_base_evaluation_def Let_def split: if_splits)
  have formed: "finite_system_formed P"
    and covered: "finite_program_head_covered (implemented_base_program B P) D"
    and closed: "finite_program_demand_closed (implemented_base_program B P) D"
    using ready by (simp_all add: implemented_base_ready_def)
  show "schema_system_formed (decode_finite_system P)"
    using formed by (simp only: finite_system_formed_correct)
  show "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    using implemented_base_closure_exact[OF formed covered closed decided]
    by (auto simp: answer ffilter.rep_eq)
qed

theorem implemented_base_evaluation_base_independent:
  assumes first: "implemented_base_evaluation B decide P D=Some A"
    and first_decided: "\<And>q. q |\<in>| D \<Longrightarrow> fst q |\<in>| B \<Longrightarrow>
      decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    and second: "implemented_base_evaluation C decide' P D=Some A'"
    and second_decided: "\<And>q. q |\<in>| D \<Longrightarrow> fst q |\<in>| C \<Longrightarrow>
      decide' q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
  shows "A=A'"
proof -
  have "fset A=fset A'"
    by (simp only: implemented_base_evaluation_exact(2)[OF first first_decided]
      implemented_base_evaluation_exact(2)[OF second second_decided])
  then show ?thesis by (simp only: fset_inject)
qed

section \<open>The empty base is the plain evaluator\<close>

lemma implemented_base_program_empty [simp]: "implemented_base_program {||} P=P"
  by (cases P) (simp add: implemented_base_program_def fset_eq_iff ffilter.rep_eq)

lemma implemented_base_seeds_empty [simp]: "implemented_base_seeds {||} decide D={||}"
  by (simp add: implemented_base_seeds_def fset_eq_iff ffilter.rep_eq)

theorem implemented_base_empty:
  "implemented_base_evaluation {||} decide P D=finite_program_evaluation P D"
  by (simp add: implemented_base_evaluation_def implemented_base_ready_def
    finite_program_evaluation_def finite_program_evaluation_ready_def)

section \<open>The native demand above a base\<close>

text \<open>
  The requests are closed over the program above the base, so a base call is a leaf of the demand: the
  program there holds no clause, and its premise calls are never demanded. The demand is then evaluated
  above the base.
\<close>

definition native_base_evaluation ::
    "local_address option definition_site fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term \<Rightarrow> bool) \<Rightarrow>
      local_address option finite_native_system \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset\<times>
        (local_address option definition_site\<times>finite_factor_term) fset option" where
  "native_base_evaluation B decide P R=(let D=native_call_closure (implemented_base_program B P) R in
    (D,implemented_base_evaluation B decide P D))"

theorem native_base_evaluation_empty:
  "native_base_evaluation {||} decide P R=native_call_evaluation P R"
  by (simp add: native_base_evaluation_def native_call_evaluation_def implemented_base_empty)

lemma native_base_evaluation_requests: "R |\<subseteq>| fst (native_base_evaluation B decide P R)"
  by (simp add: native_base_evaluation_def Let_def native_call_closure_requests)

theorem native_base_evaluation_exact:
  assumes result: "native_base_evaluation B decide P R=(D,Some A)"
    and decided: "\<And>q. q |\<in>| D \<Longrightarrow> fst q |\<in>| B \<Longrightarrow>
      decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
  shows "R |\<subseteq>| D"
    "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    "q |\<in>| R \<Longrightarrow> q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  have demand: "D=fst (native_base_evaluation B decide P R)" using result by simp
  have evaluated: "implemented_base_evaluation B decide P D=Some A"
    using result by (auto simp: native_base_evaluation_def Let_def)
  show requests: "R |\<subseteq>| D" using native_base_evaluation_requests[of R B decide P] by (simp only: demand)
  show answer: "fset A={q\<in>fset D. decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)}"
    by (rule implemented_base_evaluation_exact(2)[OF evaluated decided])
  assume "q |\<in>| R"
  then show "q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    using requests answer by auto
qed

text \<open>
  The general lemma consumes only the closure's finite derivations; the finite evaluation consumes the
  rule table's exactness at the program above the base, whose rules are the program's outside the base,
  and the decision's exactness at the demand's base calls. The answer does not depend on which exact base
  is chosen, and the empty base is the plain evaluator by an equation. An unavailable evaluation is
  @{const None} and admits no call.
\<close>

end
