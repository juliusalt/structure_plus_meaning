theory RRA_Bounded_Environment_States
  imports RRA_Use_Head_Bounds RRA_Indexed_Environment_Views
begin

type_synonym bounded_environment_state = "nat\<times>indexed_artifact_environment"

definition bounded_environment_valid :: "bounded_environment_state\<Rightarrow>bool" where
  "bounded_environment_valid q=(indexed_environment_valid (snd q) \<and> 0<fst q \<and>
    (\<forall>u R. R |\<in>| indexed_environment_artifacts (snd q) u \<longrightarrow> use_word_head u<fst q))"

definition bounded_environment_rows where
  "bounded_environment_rows A B=(finite_compact_use_head (fimage fst (fset_of_list A)) None,
    index_environment_rows A B)"

lemma bounded_environment_rows_valid:
  assumes formed: "finite_environment_formed (finite_enumerated_environment A B)"
  shows "bounded_environment_valid (bounded_environment_rows A B)"
proof -
  have positive: "0<finite_compact_use_head (fimage fst (fset_of_list A)) None"
    by (simp add: finite_compact_use_head_def)
  have original: "indexed_environment_valid (index_environment_rows A B)"
    by (rule indexed_loaded_environment_valid[OF formed])
  have bound: "use_word_head u<finite_compact_use_head (fimage fst (fset_of_list A)) None"
    if at: "R |\<in>| indexed_environment_artifacts (index_environment_rows A B) u" for u R
  proof -
    have row: "(u,R)\<in>set A" using at index_environment_rows_exact[of A B]
      by (auto simp: indexed_environment_represents_def finite_enumerated_environment_def fset_of_list.rep_eq)
    have projection: "fst (u,R)\<in>fst ` set A" by (rule imageI[OF row])
    have member: "u |\<in>| finsert None (fimage fst (fset_of_list A))"
      using projection by (simp add: fimage.rep_eq fset_of_list.rep_eq)
    show ?thesis by (rule finite_compact_use_head_greater[OF member])
  qed
  show ?thesis using original positive bound by (simp add: bounded_environment_valid_def bounded_environment_rows_def)
qed

lemma bounded_empty_environment_valid:
  "bounded_environment_valid (bounded_environment_rows [] [])"
  by (rule bounded_environment_rows_valid)
    (simp add: finite_environment_formed_def finite_enumerated_environment_def finite_relation_functional_def)

definition bounded_environment_load where
  "bounded_environment_load A B=(if finite_environment_formed (finite_enumerated_environment A B)
    then Some (bounded_environment_rows A B) else None)"

lemma bounded_environment_load_valid:
  "bounded_environment_load A B=Some q \<Longrightarrow> bounded_environment_valid q"
  by (auto simp: bounded_environment_load_def intro: bounded_environment_rows_valid split: if_splits)

definition bounded_environment_next_use where
  "bounded_environment_next_use q=Some [fst q]"

lemma bounded_environment_next_fresh:
  assumes valid: "bounded_environment_valid q"
  shows "indexed_environment_artifacts (snd q) (bounded_environment_next_use q)={||}"
  using valid by (auto simp: bounded_environment_valid_def bounded_environment_next_use_def
    intro!: fset_inject[THEN iffD1] set_eqI)

text \<open>
  The counter bounds the actual head of every original artifact use in the
  represented environment. Loading computes it from all source rows. Formation
  and the bound are invariant facts about the stored value, not caller flags.
  This initialization traverses the source; later allocation must not repeat it.
\<close>

end
