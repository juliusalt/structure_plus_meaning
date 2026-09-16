theory Finite_Term_Words
  imports RRA_Digit_Use_Paths
    Factor_Executable_Artifact_Values
begin

section \<open>A counted digit word delimits a sequence of prefix codes\<close>

definition counted_digit_word :: "('a \<Rightarrow> bool list) \<Rightarrow> 'a list \<Rightarrow> bool list" where
  "counted_digit_word code xs=digit_natural_path (length xs)@prefix_word_encoding code xs"

lemma prefix_word_encoding_cancel:
  assumes cancel: "\<And>x y u v. code x@u=code y@v \<longleftrightarrow> x=y \<and> u=v"
    and same_length: "length xs=length ys"
  shows "prefix_word_encoding code xs@r=prefix_word_encoding code ys@s \<longleftrightarrow> xs=ys \<and> r=s"
  using same_length
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y zs where ys: "ys=y#zs" by (cases ys) auto
  have "prefix_word_encoding code (x#xs)@r=prefix_word_encoding code ys@s \<longleftrightarrow>
      code x@(prefix_word_encoding code xs@r)=code y@(prefix_word_encoding code zs@s)"
    by (simp add: ys)
  also have "\<dots> \<longleftrightarrow> x=y \<and> prefix_word_encoding code xs@r=prefix_word_encoding code zs@s"
    by (rule cancel)
  also have "\<dots> \<longleftrightarrow> x=y \<and> xs=zs \<and> r=s"
    using Cons.IH[of zs] Cons.prems by (simp add: ys)
  finally show ?case by (simp add: ys)
qed

lemma counted_digit_word_cancel:
  assumes cancel: "\<And>x y u v. code x@u=code y@v \<longleftrightarrow> x=y \<and> u=v"
  shows "counted_digit_word code xs@r=counted_digit_word code ys@s \<longleftrightarrow> xs=ys \<and> r=s"
proof -
  have "counted_digit_word code xs@r=counted_digit_word code ys@s \<longleftrightarrow>
      digit_natural_path (length xs)@(prefix_word_encoding code xs@r)=
      digit_natural_path (length ys)@(prefix_word_encoding code ys@s)"
    by (simp add: counted_digit_word_def)
  also have "\<dots> \<longleftrightarrow> length xs=length ys \<and> prefix_word_encoding code xs@r=prefix_word_encoding code ys@s"
    by (rule digit_natural_path_cancel)
  also have "\<dots> \<longleftrightarrow> xs=ys \<and> r=s"
    using prefix_word_encoding_cancel[OF cancel, of xs ys r s] by auto
  finally show ?thesis .
qed

definition pair_word :: "('a \<Rightarrow> bool list) \<Rightarrow> ('b \<Rightarrow> bool list) \<Rightarrow> 'a\<times>'b \<Rightarrow> bool list" where
  "pair_word c d z=c (fst z)@d (snd z)"

lemma pair_word_cancel:
  assumes left: "\<And>x y u v. c x@u=c y@v \<longleftrightarrow> x=y \<and> u=v"
    and right: "\<And>x y u v. d x@u=d y@v \<longleftrightarrow> x=y \<and> u=v"
  shows "pair_word c d z@r=pair_word c d w@s \<longleftrightarrow> z=w \<and> r=s"
  by (simp add: pair_word_def left right prod_eq_iff)

section \<open>Addresses, octets and artifact rows keep their digit words\<close>

definition digit_address_word :: "local_address \<Rightarrow> bool list" where
  "digit_address_word=counted_digit_word digit_natural_path"

lemma digit_address_word_path:
  "digit_address_word a=digit_natural_path (length a)@digit_address_path a"
  by (simp add: digit_address_word_def counted_digit_word_def digit_address_path_def)

lemma digit_address_word_cancel [simp]:
  "digit_address_word a@r=digit_address_word b@s \<longleftrightarrow> a=b \<and> r=s"
  unfolding digit_address_word_def by (rule counted_digit_word_cancel[OF digit_natural_path_cancel])

definition incidence_row_word :: "local_address\<times>local_address\<times>local_address \<Rightarrow> bool list" where
  "incidence_row_word=pair_word digit_address_word (pair_word digit_address_word digit_address_word)"

definition data_row_word :: "local_address\<times>octets \<Rightarrow> bool list" where
  "data_row_word=pair_word digit_address_word digit_address_word"

lemma row_word_cancel [simp]:
  "incidence_row_word x@r=incidence_row_word y@s \<longleftrightarrow> x=y \<and> r=s"
  "data_row_word z@r=data_row_word w@s \<longleftrightarrow> z=w \<and> r=s"
  unfolding incidence_row_word_def data_row_word_def
  by (rule pair_word_cancel[OF digit_address_word_cancel pair_word_cancel[OF digit_address_word_cancel digit_address_word_cancel]],
      rule pair_word_cancel[OF digit_address_word_cancel digit_address_word_cancel])

definition artifact_rows_word :: "artifact_value_rows \<Rightarrow> bool list" where
  "artifact_rows_word=pair_word (counted_digit_word digit_address_word)
    (pair_word (counted_digit_word incidence_row_word)
      (pair_word (counted_digit_word data_row_word) (counted_digit_word data_row_word)))"

lemma artifact_rows_word_cancel [simp]:
  "artifact_rows_word p@r=artifact_rows_word q@s \<longleftrightarrow> p=q \<and> r=s"
  unfolding artifact_rows_word_def
  by (rule pair_word_cancel[OF counted_digit_word_cancel[OF digit_address_word_cancel]
      pair_word_cancel[OF counted_digit_word_cancel[OF row_word_cancel(1)]
        pair_word_cancel[OF counted_digit_word_cancel[OF row_word_cancel(2)]
          counted_digit_word_cancel[OF row_word_cancel(2)]]]])

section \<open>Every executable term has one prefix-free digit word\<close>

fun finite_term_word :: "finite_factor_term \<Rightarrow> bool list" where
  "finite_term_word (Finite_Payload v)=False#False#digit_address_word v"
| "finite_term_word (Finite_Pair t u)=True#finite_term_word t@finite_term_word u"
| "finite_term_word (Finite_Target (Finite_Whole C))=False#True#False#artifact_rows_word (finite_artifact_rows C)"
| "finite_term_word (Finite_Target (Finite_Anchor C a))=
    False#True#True#artifact_rows_word (finite_artifact_rows C)@digit_address_word a"

lemma finite_term_word_cancel:
  "finite_term_word t@xs=finite_term_word u@ys \<longleftrightarrow> t=u \<and> xs=ys"
proof (induction t arbitrary: u xs ys rule: finite_term_word.induct)
  case (1 v)
  then show ?case by (cases u rule: finite_term_word.cases) auto
next
  case (2 t1 t2)
  show ?case
  proof (cases u rule: finite_term_word.cases)
    case (2 u1 u2)
    have "finite_term_word (Finite_Pair t1 t2)@xs=finite_term_word u@ys \<longleftrightarrow>
        finite_term_word t1@(finite_term_word t2@xs)=finite_term_word u1@(finite_term_word u2@ys)"
      by (simp add: 2)
    also have "\<dots> \<longleftrightarrow> t1=u1 \<and> finite_term_word t2@xs=finite_term_word u2@ys"
      by (rule "2.IH"(1))
    also have "\<dots> \<longleftrightarrow> t1=u1 \<and> t2=u2 \<and> xs=ys"
      by (simp add: "2.IH"(2))
    finally show ?thesis by (simp add: 2)
  qed auto
next
  case (3 C)
  then show ?case by (cases u rule: finite_term_word.cases) (auto simp: finite_artifact_rows_injective)
next
  case (4 C a)
  then show ?case by (cases u rule: finite_term_word.cases) (auto simp: finite_artifact_rows_injective)
qed

theorem finite_term_word_injective: "finite_term_word t=finite_term_word u \<longleftrightarrow> t=u"
  using finite_term_word_cancel[of t "[]" u "[]"] by simp

fun finite_term_word_fold :: "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> finite_factor_term \<Rightarrow> 's \<Rightarrow> 's" where
  "finite_term_word_fold f (Finite_Pair t u) s=finite_term_word_fold f u (finite_term_word_fold f t (f s True))"
| "finite_term_word_fold f t s=foldl f s (finite_term_word t)"

theorem finite_term_word_fold_exact:
  "finite_term_word_fold f t s=foldl f s (finite_term_word t)"
  by (induction f t s rule: finite_term_word_fold.induct) simp_all

export_code finite_term_word finite_term_word_fold checking SML

text \<open>
  Payloads and addresses use the natural digit path of their length followed by
  the existing address digit path, so a digit word is self-delimiting. Artifact
  rows, pairs and targets compose those words, and the prefix cancellation of
  every component gives the cancellation of the whole term word. The fold
  delivers the same word incrementally without materializing it.
\<close>

end
