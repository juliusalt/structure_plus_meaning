theory Factor_Pattern_Restrictions
  imports Factor_Argument_Clauses Factor_Tagged_Views
begin

section \<open>An ordinary interface restricts an existing whole-subject call\<close>

definition restrict_call_system :: "(nat,nat,nat,nat) schema_system \<Rightarrow>
    nat \<Rightarrow> nat term_pattern \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "restrict_call_system P entry p callee=add_view_definition P entry p
    {(0,argument_call_clause 0 0 callee data_x)}"

locale pattern_restriction =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry callee :: nat
    and p :: "nat term_pattern"
  assumes source: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and pattern: "pattern_formed p" and member: "callee\<in>system_definitions P"
begin

sublocale installed: positive_view P entry p "{(0,argument_call_clause 0 0 callee data_x)}"
  by (rule positive_view.intro[OF source fresh pattern])
    (use member in \<open>auto simp: single_valued_def\<close>)

abbreviation restricted where "restricted \<equiv> restrict_call_system P entry p callee"

lemma formed: "schema_system_formed restricted"
  using installed.formed by (simp only: restrict_call_system_def)

lemma call: "schema_call_formed restricted entry t \<longleftrightarrow> pattern_accepts p t"
  by (simp only: restrict_call_system_def installed.view_call)

lemma old_meaning:
  assumes "d\<in>system_definitions P"
  shows "(d,t)\<in>positive_meaning restricted \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  using installed.old_meaning[OF assms] by (simp only: restrict_call_system_def)

theorem exact:
  "(entry,t)\<in>positive_meaning restricted \<longleftrightarrow>
    pattern_accepts p t \<and> (callee,t)\<in>positive_meaning P"
  by (simp only: restrict_call_system_def installed.view_meaning)
    (auto simp: argument_call_rule pattern_accepts_def)

end

text \<open>
  The supplied pattern belongs to the installed interface, before future
  operands. The sole ordinary premise applies the original predicate to the
  same complete operand. Pattern matching neither changes that predicate's
  meaning nor supplies an independent truth claim about the operand.
\<close>

end
