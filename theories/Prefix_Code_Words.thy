theory Prefix_Code_Words
  imports Main
begin

fun prefix_word_encoding where
  "prefix_word_encoding code []=[]"
| "prefix_word_encoding code (x#xs)=code x@prefix_word_encoding code xs"

fun read_prefix_word_fuel where
  "read_prefix_word_fuel parser 0 source=(if source=[] then Some [] else None)"
| "read_prefix_word_fuel parser (Suc fuel) source=(if source=[] then Some [] else
    case parser source of None \<Rightarrow> None | Some (x,rest) \<Rightarrow>
      map_option (Cons x) (read_prefix_word_fuel parser fuel rest))"

definition read_prefix_word where
  "read_prefix_word parser source=read_prefix_word_fuel parser (length source) source"

locale prefix_word_code =
  fixes code :: "'a\<Rightarrow>'b list" and parser :: "'b list\<Rightarrow>('a\<times>'b list) option"
  assumes code_nonempty: "\<And>x. code x\<noteq>[]"
    and parser_exact: "\<And>source x rest. parser source=Some (x,rest) \<longleftrightarrow> source=code x@rest"
begin

lemma encoding_empty [simp]: "prefix_word_encoding code xs=[] \<longleftrightarrow> xs=[]"
  by (cases xs) (auto simp: code_nonempty)

lemma parser_encoded [simp]: "parser (code x@rest)=Some (x,rest)"
  by (rule parser_exact[THEN iffD2]) (rule refl)

lemma prefix_cancel:
  "code x@xs=code y@ys \<longleftrightarrow> x=y \<and> xs=ys"
proof
  assume same: "code x@xs=code y@ys"
  have parsed: "parser (code x@xs)=Some (y,ys)" by (simp only: same parser_encoded)
  show "x=y \<and> xs=ys" using parsed by (simp only: parser_encoded option.inject prod.inject)
next
  assume "x=y \<and> xs=ys"
  then show "code x@xs=code y@ys" by simp
qed

theorem read_fuel_exact:
  "read_prefix_word_fuel parser fuel source=Some xs \<longleftrightarrow>
    source=prefix_word_encoding code xs \<and> length xs\<le>fuel"
  by (induction fuel arbitrary: source xs)
    (case_tac xs; auto simp: parser_exact parser_encoded prefix_cancel code_nonempty split: option.splits prod.splits)+

lemma encoding_length:
  "length xs\<le>length (prefix_word_encoding code xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have positive: "0<length (code x)" using code_nonempty[of x] by simp
  show ?case using Cons.IH positive by (simp; arith)
qed

theorem read_exact:
  "read_prefix_word parser source=Some xs \<longleftrightarrow> source=prefix_word_encoding code xs"
  by (auto simp: read_prefix_word_def read_fuel_exact intro: encoding_length)

lemma encoding_injective:
  "prefix_word_encoding code xs=prefix_word_encoding code ys \<longleftrightarrow> xs=ys"
proof
  assume same: "prefix_word_encoding code xs=prefix_word_encoding code ys"
  have decoded: "read_prefix_word parser (prefix_word_encoding code xs)=Some ys"
    by (simp only: read_exact same)
  have own: "read_prefix_word parser (prefix_word_encoding code xs)=Some xs"
    by (simp only: read_exact)
  show "xs=ys" using decoded own by simp
next
  assume "xs=ys"
  then show "prefix_word_encoding code xs=prefix_word_encoding code ys" by simp
qed

end

text \<open>
  Any exact nonempty prefix reader extends to complete finite words. The input
  length supplies sufficient structural fuel. The whole reader consumes every
  position; malformed prefixes or an unsupported trailing suffix cannot be
  silently discarded. Instances supply their own symbol meaning and prefix law.
\<close>

end
