theory Candidate_Generators
imports "HOL-Library.FSet"
begin

section \<open>A generator of the accepted candidates\<close>

text \<open>
  This is the second notion stated in DECISIONS.md, "The in-place refinements apply two notions: a check
  made where its premise is established, and a generator of the accepted candidates", checked. A
  reader's meaning is the accepted part of a complete candidate space, filtered by its acceptance. A
  generator that constructs only candidates the reader can accept, rather than the whole space, gives
  the same accepted part when every generated candidate it accepts lies in the space (obligation (1),
  soundness) and every accepted candidate of the space is generated (obligation (2), completeness):
  @{text accepted_generated}. A tight generator constructs only accepted candidates (obligation (3)),
  and is then the meaning itself, no filter running over it: @{text generated_accepted}. This separates
  the meaning of a complete candidate space from a method that finds the candidates it needs.

  The subject is the accepted part, not the generator: two generators of one space and acceptance have
  one accepted part, so a generator acquires no subject of its own, and which generator is cheaper is an
  observation of its use. No attribute is declared here and nothing is stated about cost. The law at the
  empty space is @{text RRA_Selection.ffilter_empty_set}, cited where it stands.
\<close>

locale candidate_generator =
  fixes space :: "'a fset" and accepts :: "'a \<Rightarrow> bool" and generated :: "'a fset"
  assumes sound: "x |\<in>| generated \<Longrightarrow> accepts x \<Longrightarrow> x |\<in>| space"
    and complete: "x |\<in>| space \<Longrightarrow> accepts x \<Longrightarrow> x |\<in>| generated"
begin

theorem accepted_generated: "ffilter accepts generated = ffilter accepts space"
  by (rule fset_eqI) (auto intro: sound complete)

end

locale tight_candidate_generator = candidate_generator space accepts generated
  for space :: "'a fset" and accepts :: "'a \<Rightarrow> bool" and generated :: "'a fset" +
  assumes tight: "x |\<in>| generated \<Longrightarrow> accepts x"
begin

theorem generated_accepted: "generated = ffilter accepts space"
  by (rule fset_eqI) (auto intro: sound complete tight)

end

text \<open>
  The law at a one-candidate space: the guarded candidate is the tight generator of that space.
\<close>

lemma singleton_tight_generator:
  "tight_candidate_generator {|x|} accepts (if accepts x then {|x|} else {||})"
  by unfold_locales (auto split: if_splits)

theorem accepted_singleton: "ffilter accepts {|x|} = (if accepts x then {|x|} else {||})"
  by (rule sym, rule tight_candidate_generator.generated_accepted[OF singleton_tight_generator[of x accepts]])

end
