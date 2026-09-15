theory Structural_Word_Lists
  imports Finite_Set_Composition
begin

definition framed_structural_word :: "nat list\<Rightarrow>nat list" where
  "framed_structural_word word=length word#word"

fun take_structural_words :: "nat\<Rightarrow>nat list\<Rightarrow>(nat list list\<times>nat list) option" where
  "take_structural_words 0 tail=Some ([],tail)"
| "take_structural_words (Suc n) []=None"
| "take_structural_words (Suc n) (k#tail)=(if k\<le>length tail then
    map_option (\<lambda>(words,rest). (take k tail#words,rest)) (take_structural_words n (drop k tail)) else None)"

lemma take_structural_words_framed:
  "take_structural_words (length words) (concat (map framed_structural_word words)@tail)=Some (words,tail)"
  by (induction words arbitrary: tail) (simp_all add: framed_structural_word_def)

definition structural_words_code :: "nat list list\<Rightarrow>nat list" where
  "structural_words_code words=length words#concat (map framed_structural_word words)"

fun read_structural_words where
  "read_structural_words []=None"
| "read_structural_words (n#body)=(case take_structural_words n body of None \<Rightarrow> None
    | Some (words,tail) \<Rightarrow> if tail=[] then Some words else None)"

theorem read_structural_words_code:
  "read_structural_words (structural_words_code words)=Some words"
  using take_structural_words_framed[of words "[]"] by (simp add: structural_words_code_def)

theorem structural_words_code_injective:
  "structural_words_code xs=structural_words_code ys \<longleftrightarrow> xs=ys"
  by (metis read_structural_words_code option.inject)

lemma structural_map_injective:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "map encode xs=map encode ys \<longleftrightarrow> xs=ys"
  using each by (induction xs arbitrary: ys; cases ys)
    auto

lemma finite_image_equality_from_source:
  assumes same: "fimage encode A=fimage encode B"
    and faithful: "\<And>x y. x |\<in>| A \<Longrightarrow> encode x=encode y \<Longrightarrow> x=y"
  shows "A=B"
proof -
  have left: "x |\<in>| A \<Longrightarrow> x |\<in>| B" for x
  proof -
    assume member: "x |\<in>| A"
    have "encode x |\<in>| fimage encode B" using member same
      by (auto simp: finite_image_member)
    then obtain y where "y |\<in>| B" "encode x=encode y" by (auto simp: finite_image_member)
    then show "x |\<in>| B" using faithful[OF member] by blast
  qed
  have right: "x |\<in>| B \<Longrightarrow> x |\<in>| A" for x
  proof -
    assume member: "x |\<in>| B"
    have "encode x |\<in>| fimage encode A" using member same
      by (auto simp: finite_image_member)
    then obtain y where "y |\<in>| A" "encode y=encode x" by (auto simp: finite_image_member)
    then show "x |\<in>| A" using faithful by blast
  qed
  show ?thesis using left right by (auto simp: fset_inject[symmetric])
qed

text \<open>
  Explicit lengths preserve arbitrary natural-number words and the complete
  ordered list of words. Decoding recovers every boundary and value. The code
  is a complete structural representation, not a digest or supplied identity.
\<close>

end
