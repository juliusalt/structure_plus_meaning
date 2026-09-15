theory Delimited_Bit_Words
  imports Main
begin

fun delimited_bit_word where
  "delimited_bit_word []=[False]"
| "delimited_bit_word (b#bs)=True#b#delimited_bit_word bs"

fun read_delimited_bit_word where
  "read_delimited_bit_word []=None"
| "read_delimited_bit_word (False#source)=Some ([],source)"
| "read_delimited_bit_word [True]=None"
| "read_delimited_bit_word (True#b#source)=map_option (\<lambda>(bs,rest). (b#bs,rest))
    (read_delimited_bit_word source)"

lemma delimited_bit_word_nonempty [simp]: "delimited_bit_word bs\<noteq>[]"
  by (cases bs) simp_all

lemma delimited_bit_word_length:
  "length (delimited_bit_word bs)=2*length bs+1"
  by (induction bs) simp_all

lemma read_delimited_bit_word_encoded [simp]:
  "read_delimited_bit_word (delimited_bit_word bs@rest)=Some (bs,rest)"
  by (induction bs) simp_all

lemma read_delimited_bit_word_sound:
  "read_delimited_bit_word source=Some (bs,rest) \<Longrightarrow> source=delimited_bit_word bs@rest"
  by (induction source arbitrary: bs rest rule: read_delimited_bit_word.induct)
    (auto split: option.splits prod.splits)

theorem read_delimited_bit_word_exact:
  "read_delimited_bit_word source=Some (bs,rest) \<longleftrightarrow> source=delimited_bit_word bs@rest"
  using read_delimited_bit_word_sound by auto

lemma delimited_bit_word_cancel:
  "delimited_bit_word bs@xs=delimited_bit_word cs@ys \<longleftrightarrow> bs=cs \<and> xs=ys"
  by (induction bs arbitrary: cs) (case_tac cs; auto)+

text \<open>
  A marker accompanies each actual bit and a separate terminator ends the word.
  The parser preserves the complete remaining suffix. Its exact equation owns
  prefix cancellation and does not assign natural-number meaning to the bits.
\<close>

end
