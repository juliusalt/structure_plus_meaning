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

text \<open>
  A code whose words cancel under arbitrary suffixes keeps that cancellation through any injective
  map of its symbols: a mapped word that extends another mapped word extends it by the image of a
  suffix of the unmapped word.
\<close>

lemma mapped_prefix_extended:
  assumes cancel: "\<And>m n xs ys. code m @ xs = code n @ ys \<longleftrightarrow> m = n \<and> xs = ys"
    and injective: "inj f"
    and longer: "map f (code m) = map f (code n) @ us" and rest: "us @ xs = ys"
  shows "m = n \<and> xs = ys"
proof -
  let ?k = "length (code n)"
  let ?v = "drop ?k (code m)"
  have "take ?k (map f (code m)) = map f (code n)"
    by (simp only: longer take_append length_map diff_self_eq_0 take_0 append_Nil2 take_all_iff order_refl)
  then have "map f (take ?k (code m)) = map f (code n)" by (simp only: take_map)
  then have head: "take ?k (code m) = code n" by (simp only: inj_map_eq_map[OF injective])
  have "drop ?k (map f (code m)) = us"
    by (simp only: longer drop_append length_map diff_self_eq_0 drop_0 drop_all order_refl append_Nil)
  then have tail: "map f ?v = us" by (simp only: drop_map)
  have "code m @ [] = code n @ ?v"
    using append_take_drop_id[of ?k "code m"] head by simp
  then have "m = n \<and> [] = ?v" by (rule iffD1[OF cancel])
  then show ?thesis using tail rest by auto
qed

theorem mapped_prefix_cancel:
  assumes cancel: "\<And>m n xs ys. code m @ xs = code n @ ys \<longleftrightarrow> m = n \<and> xs = ys"
    and injective: "inj f"
  shows "map f (code m) @ xs = map f (code n) @ ys \<longleftrightarrow> m = n \<and> xs = ys"
proof
  assume eq: "map f (code m) @ xs = map f (code n) @ ys"
  obtain us where "map f (code m) = map f (code n) @ us \<and> us @ xs = ys \<or>
      map f (code m) @ us = map f (code n) \<and> xs = us @ ys"
    using eq by (auto simp: append_eq_append_conv2)
  then show "m = n \<and> xs = ys"
  proof (elim disjE conjE)
    assume "map f (code m) = map f (code n) @ us" "us @ xs = ys"
    then show ?thesis by (rule mapped_prefix_extended[OF cancel injective])
  next
    assume "map f (code m) @ us = map f (code n)" "xs = us @ ys"
    then have "n = m \<and> ys = xs" by (intro mapped_prefix_extended[OF cancel injective, of n m us]) simp_all
    then show ?thesis by simp
  qed
qed simp

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
