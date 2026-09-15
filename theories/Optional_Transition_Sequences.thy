theory Optional_Transition_Sequences
  imports Main
begin

theorem optional_bind_projection:
  assumes input: "map_option project initial=original_initial"
    and step: "\<And>q. map_option output (following q)=original_following (project q)"
  shows "map_option output (Option.bind initial following)=
    Option.bind original_initial original_following"
  by (cases initial) (simp_all add: input[symmetric] step)

theorem function_iteration_projection:
  assumes each: "\<And>x. project (step x)=original (project x)"
  shows "project ((step ^^ n) x)=(original ^^ n) (project x)"
  by (induction n arbitrary: x) (simp_all add: each)

fun optional_transition_sequence where
  "optional_transition_sequence step [] q=Some q"
| "optional_transition_sequence step (x#xs) q=(case step q x of
    None \<Rightarrow> None | Some following \<Rightarrow> optional_transition_sequence step xs following)"

theorem optional_transition_sequence_projection:
  assumes each: "\<And>q x. map_option project (step q x)=original (project q) x"
  shows "map_option project (optional_transition_sequence step xs q)=
    optional_transition_sequence original xs (project q)"
  by (induction xs arbitrary: q)
    (simp_all add: each[symmetric] split: option.splits)

theorem optional_transition_sequence_invariant:
  assumes initial: "P q"
    and each: "\<And>q x following. P q \<Longrightarrow> step q x=Some following \<Longrightarrow> P following"
    and result: "optional_transition_sequence step xs q=Some following"
  shows "P following"
  using initial result
  by (induction xs arbitrary: q) (auto split: option.splits intro: each)

text \<open>
  Complete optional transition projection and invariant preservation compose
  over any supplied action sequence. The first missing step remains missing;
  no later action can supply a result for it.
\<close>

end
