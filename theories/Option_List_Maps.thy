theory Option_List_Maps
  imports Main
begin

section \<open>Complete partial maps retain their input sequence\<close>

lemma those_map_result:
  "those (map f xs)=Some ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x=Some y) xs ys"
  by (induction xs arbitrary: ys; cases ys)
    (auto simp: list_all2_Cons1 split: option.splits)

definition guarded_option_map :: "bool\<Rightarrow>('a\<Rightarrow>'b option)\<Rightarrow>'a list\<Rightarrow>'b list option" where
  "guarded_option_map accepted f xs=(if accepted then those (map f xs) else None)"

lemma guarded_option_map_result:
  "guarded_option_map accepted f xs=Some ys \<longleftrightarrow>
    accepted \<and> list_all2 (\<lambda>x y. f x=Some y) xs ys"
  by (simp add: guarded_option_map_def those_map_result)

definition paired_option_outputs ::
  "('a\<Rightarrow>'b option)\<Rightarrow>('a\<Rightarrow>'c option)\<Rightarrow>'a\<Rightarrow>('b\<times>'c) option" where
  "paired_option_outputs first second x=(case first x of None \<Rightarrow> None
    | Some y \<Rightarrow> map_option (Pair y) (second x))"

lemma paired_option_outputs_result:
  "paired_option_outputs first second x=Some (y,z) \<longleftrightarrow>
    first x=Some y \<and> second x=Some z"
  by (auto simp: paired_option_outputs_def split: option.splits)

text \<open>
  The guard applies even to an empty sequence. A result contains one output
  for every input occurrence, in its original order. The paired operation
  applies both partial functions to the same complete input and returns
  neither result unless both succeed.
\<close>

end
