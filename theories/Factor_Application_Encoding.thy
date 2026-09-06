theory Factor_Application_Encoding
  imports Factor_Applications
begin

section \<open>Use renaming preserves term quotation\<close>

lemma term_quoted_use_renaming:
  assumes quote: "term_quoted_at E u r t I K" and injective: "inj h"
  shows "term_quoted_at (rename_environment h E) (h u) r t I K"
  using quote
proof (induction rule: term_quoted_at.induct)
  case (target u R r c I t)
  have ef: "environment_formed (rename_environment h E)" by (rule environment_renaming_formed[OF target.hyps(1) injective])
  have art: "artifact_at (rename_environment h E) (h u) R"
    using artifact_at_renamed_use[OF injective, of E u R] target.hyps(2) by simp
  have interp: "interpret_citation (rename_environment h E) (h u) c t"
    using citation_use_renaming[OF injective, of E u c t] target.hyps(5) by simp
  show ?case by (rule term_quoted_at.target[OF ef art target.hyps(3,4) interp])
next
  case (pair u R r ps l q x L A y Q B)
  have ef: "environment_formed (rename_environment h E)" by (rule environment_renaming_formed[OF pair.hyps(1) injective])
  have art: "artifact_at (rename_environment h E) (h u) R"
    using artifact_at_renamed_use[OF injective, of E u R] pair.hyps(2) by simp
  show ?case by (rule term_quoted_at.pair[OF ef art pair.hyps(3) pair.IH pair.hyps(6-8)])
next
  case (payload u R r v)
  have ef: "environment_formed (rename_environment h E)"
    by (rule environment_renaming_formed[OF payload.hyps(1) injective])
  have art: "artifact_at (rename_environment h E) (h u) R"
    using artifact_at_renamed_use[OF injective, of E u R] payload.hyps(2) by simp
  show ?case by (rule term_quoted_at.payload[OF ef art payload.hyps(3)])
qed

lemma native_application_from_term_pair:
  assumes quote: "term_quoted_at E u r (Pair_Term x t) I K"
    and art: "artifact_at E u R" and rec: "record_at R r ps [c,a]"
    and cite: "citation_at R c code C"
    and loc: "citation_location E u code (fst d) (snd d)"
  shows "native_application_at E u r d t I K"
proof -
  have ef: "environment_formed E" by (rule term_quoted_environment_formed[OF quote])
  obtain L A J B where parts:
    "term_quoted_at E u c x L A" "term_quoted_at E u a t J B"
    "I = insert r (set ps \<union> L \<union> J)" "K = A \<union> B"
    "insert r (set ps) \<inter> (L \<union> J) = {}" "L \<inter> J = {}" "I \<inter> K = {}"
    using term_quoted_with_pair_record[OF ef art rec quote] by auto
  have leaf: "L = C \<and> A = citation_slots code"
    using term_quoted_with_citation[OF ef art cite parts(1)] by blast
  show ?thesis using ef art rec cite loc parts leaf unfolding native_application_at_def by blast
qed

section \<open>A call environment keeps the target artifact at its existing use\<close>

fun call_use :: "local_address option \<Rightarrow> local_address option" where
  "call_use None = Some []"
| "call_use (Some k) = (if k = [] then Some [2,4] else if k = [2,4] then None else Some k)"

lemma call_use_injective:
  "inj call_use"
  by (rule injI) (case_tac x; case_tac y; auto split: if_splits)

lemma call_use_callee [simp]: "call_use (Some [2,4]) = None" by simp
lemma call_use_argument [simp]: "call_use (Some (3#k)) = Some (3#k)" by simp

definition call_environment ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> local_address option artifact_environment" where
  "call_environment R a t = rename_environment call_use
    (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))"

definition call_syntax ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> exact_artifact" where
  "call_syntax R a t = term_syntax (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)"

lemma call_environment_formed:
  assumes anchor: "anchor_formed (R,a)" and argument: "term_formed t"
  shows "environment_formed (call_environment R a t)"
proof -
  have formed: "term_formed (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)" using assms by simp
  show ?thesis unfolding call_environment_def
    by (rule environment_renaming_formed[OF term_environment_formed[OF formed] call_use_injective])
qed

lemma call_environment_source:
  "artifact_at (call_environment R a t) (Some []) (call_syntax R a t)"
proof -
  have source: "artifact_at (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))
    None (call_syntax R a t)" unfolding call_syntax_def by (rule term_environment_source)
  have copied: "artifact_at (rename_environment call_use
    (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)))
    (call_use None) (call_syntax R a t)"
    using source by (simp only: artifact_at_renamed_use[OF call_use_injective])
  show ?thesis using copied by (simp add: call_environment_def)
qed

lemma call_environment_target:
  "artifact_at (call_environment R a t) None R"
proof -
  have source: "artifact_at (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))
    (Some [2,4]) R" by (simp add: term_environment_def)
  have copied: "artifact_at (rename_environment call_use
    (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)))
    (call_use (Some [2,4])) R"
    using source by (simp only: artifact_at_renamed_use[OF call_use_injective])
  show ?thesis using copied by (simp add: call_environment_def)
qed

lemma call_environment_target_binding:
  "binds_slot (call_environment R a t) (Some []) [2,4] None"
proof -
  have source: "binds_slot (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))
    None [2,4] (Some [2,4])" by (auto simp: term_environment_def rel_dom_def)
  have copied: "binds_slot (rename_environment call_use
    (term_environment (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)))
    (call_use None) [2,4] (call_use (Some [2,4]))"
    using source by (simp only: binds_slot_renamed_use[OF call_use_injective])
  show ?thesis using copied by (simp add: call_environment_def)
qed

lemma call_environment_extends_target:
  "environment_included (literal_environment R {}) (call_environment R a t)"
  using call_environment_target[of R a t]
  by (auto simp: environment_included_def literal_environment_def rel_dom_def artifact_at_def)


lemma call_syntax_formed:
  assumes "anchor_formed (R,a)" "term_formed t"
  shows "exact_formed (call_syntax R a t)"
  unfolding call_syntax_def by (rule term_syntax_formed) (use assms in simp)

lemma call_syntax_record:
  assumes "anchor_formed (R,a)" "term_formed t"
  shows "record_at (call_syntax R a t) [] [[0],[1]] [[2],[3]]"
  using pair_syntax_record[of "literal_syntax (Occurrence_Anchor (R,a))" "term_syntax t"]
    call_syntax_formed[OF assms] by (simp add: call_syntax_def)

lemma call_syntax_callee:
  assumes anchor: "anchor_formed (R,a)" and arg: "term_formed t"
  shows "citation_at (call_syntax R a t) [2] (External [2,4] a) {[2],[2,5]}"
proof -
  let ?L = "literal_syntax (Occurrence_Anchor (R,a))"
  have target: "target_formed (Occurrence_Anchor (R,a))" using anchor by simp
  have formed: "exact_formed ?L" by (rule literal_syntax_formed[OF target])
  have cite: "citation_at ?L [] (External [4] a) {[],[5]}"
    using literal_syntax_citation[OF target] by simp
  have addressing: "finite_addressing (rra_carrier (object_structure ?L)) (Cons 2)"
    by (rule prefix_addressing[OF formed]) simp
  have copied: "citation_at (push_object (Cons 2) ?L) [2] (External [2,4] a) {[2],[2,5]}"
    using citation_at_push[OF cite addressing] by simp
  have counts: "bag_count (object_data ?L) = (\<lambda>_. 0)" by (rule literal_syntax_properties(4))
  have full: "object_reads_agree (push_object (Cons 2) ?L) (call_syntax R a t)
    (Cons 2 ` rra_carrier (object_structure ?L))"
    using pair_syntax_reads_left[OF counts, of "term_syntax t"] by (simp add: call_syntax_def)
  have subset: "{[2],[2,5]} \<subseteq> Cons 2 ` rra_carrier (object_structure ?L)" by simp
  have reads: "object_reads_agree (push_object (Cons 2) ?L) (call_syntax R a t) {[2],[2,5]}"
    by (rule object_reads_agree_mono[OF full subset])
  show ?thesis by (rule citation_at_read_transport[OF copied call_syntax_formed[OF anchor arg] reads])
qed

lemma call_environment_location:
  assumes "anchor_formed (R,a)"
  shows "citation_location (call_environment R a t) (Some []) (External [2,4] a) None a"
  using assms call_environment_target[of R a t] call_environment_target_binding[of R a t]
  by auto

lemma call_environment_quotation:
  assumes anchor: "anchor_formed (R,a)" and arg: "term_formed t"
  shows "term_quoted_at (call_environment R a t) (Some []) []
    (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)
    (term_syntax_interior (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))
    (rel_dom (term_literal_bindings (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)))"
proof -
  have formed: "term_formed (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)" using assms by simp
  show ?thesis using term_quoted_use_renaming[OF term_syntax_recovers[OF formed] call_use_injective]
    by (simp only: call_use.simps(1) call_environment_def)
qed

theorem native_application_representation:
  assumes anchor: "anchor_formed (R,a)" and arg: "term_formed t"
  shows "native_application_at (call_environment R a t) (Some []) [] (None,a) t
    (term_syntax_interior (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))
    (rel_dom (term_literal_bindings (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t)))"
  by (rule native_application_from_term_pair[OF call_environment_quotation[OF anchor arg]
        call_environment_source call_syntax_record[OF anchor arg] call_syntax_callee[OF anchor arg]])
     (use call_environment_location[OF anchor, of t] in simp)

lemma native_application_complete_carrier:
  "rra_carrier (object_structure (call_syntax R a t)) =
    term_syntax_interior (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t) \<union>
    rel_dom (term_literal_bindings (Pair_Term (Target_Term (Occurrence_Anchor (R,a))) t))"
  unfolding call_syntax_def by (rule term_syntax_carrier)

text \<open>
  Every formed term can be placed in a finite native call to any formed target
  anchor. An injective permutation of use occurrences puts the target artifact
  at None and the call at Some [], while preserving literal interpretations.
  These coordinates construct a witness; the application reader inspects the
  incidence and bindings. The complete call carrier is its recovered interior
  together with its external slots.
\<close>

end
