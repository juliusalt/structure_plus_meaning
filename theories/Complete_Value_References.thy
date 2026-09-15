theory Complete_Value_References
  imports Main
begin

fun value_reference_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "value_reference_index x []=None"
| "value_reference_index x (y#ys)=(if x=y then Some 0 else map_option Suc (value_reference_index x ys))"

lemma value_reference_index_read:
  "value_reference_index x xs=Some i \<Longrightarrow> i<length xs \<and> xs!i=x"
  by (induction xs arbitrary: i) (auto split: option.splits if_splits)

lemma value_reference_index_absent:
  "value_reference_index x xs=None \<longleftrightarrow> x\<notin>set xs"
  by (induction xs) auto

definition value_reference_read :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "value_reference_read table i=(if i<length table then Some (table!i) else None)"

definition value_reference_step :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<times> 'a list" where
  "value_reference_step x table=(case value_reference_index x table of
    None \<Rightarrow> (length table,table@[x]) | Some i \<Rightarrow> (i,table))"

theorem value_reference_step_exact:
  "value_reference_read (snd (value_reference_step x table)) (fst (value_reference_step x table))=Some x"
  by (auto simp: value_reference_step_def value_reference_read_def nth_append
      dest: value_reference_index_read split: option.splits)

theorem value_reference_step_prefix:
  "take (length table) (snd (value_reference_step x table))=table"
  by (auto simp: value_reference_step_def split: option.splits)

theorem value_reference_step_preserves:
  assumes "value_reference_read table i=Some y"
  shows "value_reference_read (snd (value_reference_step x table)) i=Some y"
  using assms by (auto simp: value_reference_read_def value_reference_step_def nth_append
      split: option.splits if_splits)

fun value_reference_sequence :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat list \<times> 'a list" where
  "value_reference_sequence [] table=([],table)"
| "value_reference_sequence (x#xs) table=(let (i,next)=value_reference_step x table;
      (indices,last)=value_reference_sequence xs next in (i#indices,last))"

lemma value_reference_sequence_preserves:
  "value_reference_read table i=Some y \<Longrightarrow>
    value_reference_read (snd (value_reference_sequence xs table)) i=Some y"
proof (induction xs arbitrary: table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain j next_table where step: "value_reference_step x table=(j,next_table)" by (cases "value_reference_step x table") auto
  have kept: "value_reference_read next_table i=Some y"
    using value_reference_step_preserves[OF Cons.prems, of x] by (simp only: step snd_conv)
  have last: "value_reference_read (snd (value_reference_sequence xs next_table)) i=Some y"
    by (rule Cons.IH[OF kept])
  show ?case using last by (simp add: step case_prod_unfold Let_def)
qed

theorem value_reference_sequence_exact:
  "map (value_reference_read (snd (value_reference_sequence xs table)))
    (fst (value_reference_sequence xs table))=map Some xs"
proof (induction xs arbitrary: table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain i next_table where step: "value_reference_step x table=(i,next_table)" by (cases "value_reference_step x table") auto
  have first: "value_reference_read next_table i=Some x"
    using value_reference_step_exact[of x table] by (simp only: step fst_conv snd_conv)
  have kept: "value_reference_read (snd (value_reference_sequence xs next_table)) i=Some x"
    by (rule value_reference_sequence_preserves[OF first])
  show ?case using Cons.IH[of next_table] kept by (simp add: step case_prod_unfold Let_def)
qed

text \<open>Each reference recovers the complete supplied value. Later insertions
  preserve every earlier reference, and decoding an entire reference sequence
  recovers the original ordered sequence exactly. The table may start with
  arbitrary values or duplicates; no cache-supplied assertion is trusted.\<close>

end
