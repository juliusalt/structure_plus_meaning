theory Structural_Word_Collections
  imports Structural_Word_Lists "HOL-Library.List_Lexorder"
begin

fun structural_optional_word where
  "structural_optional_word None=structural_words_code []"
| "structural_optional_word (Some word)=structural_words_code [word]"

lemma structural_optional_word_injective:
  "structural_optional_word x=structural_optional_word y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp_all add: structural_words_code_injective)

lemma structural_distinct_map:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "distinct (map encode xs) \<longleftrightarrow> distinct xs"
  by (simp add: distinct_map inj_on_def each)

definition structural_fset_code :: "('a\<Rightarrow>nat list)\<Rightarrow>'a fset\<Rightarrow>nat list" where
  "structural_fset_code encode X=structural_words_code (sorted_list_of_fset (fimage encode X))"

lemma structural_fset_code_injective:
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
  shows "structural_fset_code encode X=structural_fset_code encode Y \<longleftrightarrow> X=Y"
proof
  assume equal: "structural_fset_code encode X=structural_fset_code encode Y"
  have rows: "sorted_list_of_fset (fimage encode X)=sorted_list_of_fset (fimage encode Y)"
    using equal by (simp only: structural_fset_code_def structural_words_code_injective)
  have image: "fimage encode X=fimage encode Y"
    by (rule fset_inject[THEN iffD1]) (use arg_cong[where f=set, OF rows] in simp)
  have injective: "inj encode" by (auto simp: inj_def each)
  show "X=Y" using image by (simp only: fset_image_equality[OF injective])
next
  assume "X=Y" then show "structural_fset_code encode X=structural_fset_code encode Y" by simp
qed

text \<open>
  A finite collection is represented by the sorted list of every complete
  member word. Injective member encoding preserves exactly its unordered
  members. Optional words retain the distinction between absence and an empty
  present word. Neither construction requires a formation predicate.
\<close>

end
