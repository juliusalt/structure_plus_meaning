theory Factor_Pattern_Programs
  imports Factor_Positive_Meaning
begin

section \<open>Finite recognition programs from ordinary patterns\<close>

definition recognizer_schema :: "'a term_pattern \<Rightarrow> ('a,'s,'d) factor_schema" where
  "recognizer_schema p = \<lparr>schema_conclusion=p, schema_premises={}, schema_material_premises={}\<rparr>"

definition recognizer_system :: "'a \<Rightarrow> 'a term_pattern \<Rightarrow> ('a,unit,unit,unit) schema_system" where
  "recognizer_system a p = \<lparr>system_interfaces={((),Pattern_Variable a)},
    system_clauses={(((),()),recognizer_schema p)}\<rparr>"

lemma recognizer_schema_variables [simp]:
  "schema_variables (recognizer_schema p)=pattern_variables p"
  by (simp add: schema_variables_def recognizer_schema_def)

lemma recognizer_schema_formed [simp]:
  "schema_formed (recognizer_schema p) \<longleftrightarrow> pattern_formed p"
  by (simp add: schema_formed_def recognizer_schema_def single_valued_def)

lemma recognizer_system_formed:
  assumes "pattern_formed p"
  shows "schema_system_formed (recognizer_system a p)"
  using assms by (auto simp: schema_system_formed_def recognizer_system_def
    recognizer_schema_def schema_formed_def schema_dependencies_def system_definitions_def
    rel_dom_def rel_ran_def single_valued_def)

lemma recognizer_call_formed:
  assumes "pattern_formed p"
  shows "schema_call_formed (recognizer_system a p) () t \<longleftrightarrow> term_formed t"
  using recognizer_system_formed[OF assms]
  by (simp add: schema_call_formed_def recognizer_system_def)

theorem recognizer_positive_meaning:
  assumes pf: "pattern_formed p"
  shows "((),t)\<in>positive_meaning (recognizer_system a p) \<longleftrightarrow> pattern_accepts p t"
proof
  assume positive: "((),t)\<in>positive_meaning (recognizer_system a p)"
  obtain c V Q where inst: "admitted_schema_instance (recognizer_system a p) () c V t Q"
    using positive by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have bindings: "term_bindings_formed (pattern_variables p) V" and head: "pattern_instance V p t"
    using inst by (auto simp: admitted_schema_instance_def recognizer_system_def
      schema_instance_def recognizer_schema_def schema_variables_def)
  have formed: "term_formed t"
    using positive_meaning_formed[OF positive] by (simp add: recognizer_call_formed[OF pf])
  show "pattern_accepts p t" using bindings head formed by (auto simp: pattern_accepts_def)
next
  assume accepts: "pattern_accepts p t"
  then obtain V where bindings: "term_bindings_formed (pattern_variables p) V"
    and head: "pattern_instance V p t" and formed: "term_formed t"
    by (auto simp: pattern_accepts_def)
  have inst: "schema_instance (recognizer_schema p) V t {}"
    using pf bindings head
    by (auto simp: schema_instance_def recognizer_schema_def schema_variables_def
      schema_formed_def schema_premise_instance_def single_valued_def)
  have admitted: "admitted_schema_instance (recognizer_system a p) () () V t {}"
    using inst formed recognizer_call_formed[OF pf]
    by (auto simp: admitted_schema_instance_def recognizer_system_def
      schema_material_satisfied_def recognizer_schema_def)
  show "((),t)\<in>positive_meaning (recognizer_system a p)"
    by (rule positive_meaning_step[OF admitted]) simp
qed

fun exact_term_pattern :: "factor_term \<Rightarrow> 'a term_pattern" where
  "exact_term_pattern (Target_Term t)=Pattern_Target t"
| "exact_term_pattern (Payload_Term b)=Pattern_Payload b"
| "exact_term_pattern (Pair_Term x y)=Pattern_Pair (exact_term_pattern x) (exact_term_pattern y)"

lemma exact_term_pattern_substitute [simp]:
  "pattern_substitute s (exact_term_pattern t)=exact_term_pattern t"
  by (induction t) auto

lemma exact_term_pattern_formed [simp]:
  "pattern_formed (exact_term_pattern t) \<longleftrightarrow> term_formed t"
  by (induction t) auto

lemma exact_term_pattern_variables [simp]: "pattern_variables (exact_term_pattern t)={}"
  by (induction t) auto

lemma exact_term_pattern_instance [simp]:
  "pattern_instance V (exact_term_pattern t) u \<longleftrightarrow> term_formed t \<and> u=t"
  by (induction t arbitrary: u) auto

lemma exact_term_pattern_accepts [simp]:
  "pattern_accepts (exact_term_pattern t) u \<longleftrightarrow> term_formed t \<and> u=t"
  unfolding pattern_accepts_def
  by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def)

text \<open>
  These are ordinary premise-free positive programs. Exact-term recognition
  follows from the existing pattern rules. No new observation primitive or
  truth callback is introduced. The explicitly supplied interface binder has
  its own scope; every choice of it accepts exactly every formed term.
\<close>

end
