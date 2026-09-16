theory Finite_Term_Words
  imports RRA_Digit_Use_Paths
    Factor_Executable_Artifact_Values Complete_Value_References
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

section \<open>Every executable term has one prefix-free digit word over a target code\<close>

fun finite_term_targets :: "finite_factor_term \<Rightarrow> finite_exact_target set" where
  "finite_term_targets (Finite_Payload v)={}"
| "finite_term_targets (Finite_Pair t u)=finite_term_targets t \<union> finite_term_targets u"
| "finite_term_targets (Finite_Target x)={x}"

definition target_code_cancels :: "(finite_exact_target \<Rightarrow> bool list) \<Rightarrow> finite_exact_target set \<Rightarrow> bool" where
  "target_code_cancels leaf A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>u v. leaf x@u=leaf y@v \<longleftrightarrow> x=y \<and> u=v)"

lemma target_code_cancels_subset:
  "target_code_cancels leaf B \<Longrightarrow> A\<subseteq>B \<Longrightarrow> target_code_cancels leaf A"
  by (auto simp: target_code_cancels_def)

fun finite_term_word_with :: "(finite_exact_target \<Rightarrow> bool list) \<Rightarrow> finite_factor_term \<Rightarrow> bool list" where
  "finite_term_word_with leaf (Finite_Payload v)=False#False#digit_address_word v"
| "finite_term_word_with leaf (Finite_Pair t u)=True#finite_term_word_with leaf t@finite_term_word_with leaf u"
| "finite_term_word_with leaf (Finite_Target x)=False#True#leaf x"

lemma finite_term_word_with_cancel:
  assumes "target_code_cancels leaf (finite_term_targets t \<union> finite_term_targets s)"
  shows "finite_term_word_with leaf t@xs=finite_term_word_with leaf s@ys \<longleftrightarrow> t=s \<and> xs=ys"
  using assms
proof (induction t arbitrary: s xs ys rule: finite_term_targets.induct)
  case (1 v)
  then show ?case by (cases s) auto
next
  case (2 t1 t2)
  show ?case
  proof (cases s)
    case (Finite_Pair s1 s2)
    have left: "target_code_cancels leaf (finite_term_targets t1 \<union> finite_term_targets s1)"
      and right: "target_code_cancels leaf (finite_term_targets t2 \<union> finite_term_targets s2)"
      by (rule target_code_cancels_subset[OF "2.prems"]; auto simp: Finite_Pair)+
    have "finite_term_word_with leaf (Finite_Pair t1 t2)@xs=finite_term_word_with leaf s@ys \<longleftrightarrow>
        finite_term_word_with leaf t1@(finite_term_word_with leaf t2@xs)=
        finite_term_word_with leaf s1@(finite_term_word_with leaf s2@ys)"
      by (simp add: Finite_Pair)
    also have "\<dots> \<longleftrightarrow> t1=s1 \<and> finite_term_word_with leaf t2@xs=finite_term_word_with leaf s2@ys"
      by (rule "2.IH"(1)[OF left])
    also have "\<dots> \<longleftrightarrow> t1=s1 \<and> t2=s2 \<and> xs=ys"
      by (simp add: "2.IH"(2)[OF right])
    finally show ?thesis by (simp add: Finite_Pair)
  qed auto
next
  case (3 x)
  then show ?case by (cases s) (auto simp: target_code_cancels_def)
qed

fun finite_term_word_with_fold ::
  "(finite_exact_target \<Rightarrow> bool list) \<Rightarrow> ('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> finite_factor_term \<Rightarrow> 's \<Rightarrow> 's" where
  "finite_term_word_with_fold leaf f (Finite_Pair t u) s=
    finite_term_word_with_fold leaf f u (finite_term_word_with_fold leaf f t (f s True))"
| "finite_term_word_with_fold leaf f t s=foldl f s (finite_term_word_with leaf t)"

lemma finite_term_word_with_fold_exact:
  "finite_term_word_with_fold leaf f t s=foldl f s (finite_term_word_with leaf t)"
  by (induction leaf f t s rule: finite_term_word_with_fold.induct) simp_all

section \<open>Repeated artifacts share one first-occurrence table\<close>

lemma value_reference_step_set: "set (snd (value_reference_step x T))=insert x (set T)"
proof (cases "value_reference_index x T")
  case None
  then show ?thesis by (simp add: value_reference_step_def)
next
  case (Some i)
  have "x\<in>set T" using value_reference_index_read[OF Some] nth_mem by metis
  then show ?thesis using Some by (auto simp: value_reference_step_def)
qed

fun finite_term_rows_onto :: "finite_factor_term \<Rightarrow> artifact_value_rows list \<Rightarrow> artifact_value_rows list" where
  "finite_term_rows_onto (Finite_Payload v) T=T"
| "finite_term_rows_onto (Finite_Pair t u) T=finite_term_rows_onto u (finite_term_rows_onto t T)"
| "finite_term_rows_onto (Finite_Target x) T=
    snd (value_reference_step (finite_artifact_rows (finite_target_artifact x)) T)"

lemma finite_term_rows_onto_set:
  "set (finite_term_rows_onto t T)=set T \<union> (finite_artifact_rows \<circ> finite_target_artifact) ` finite_term_targets t"
  by (induction t T rule: finite_term_rows_onto.induct) (auto simp: value_reference_step_set)

definition finite_term_rows :: "finite_factor_term \<Rightarrow> artifact_value_rows list" where
  "finite_term_rows t=finite_term_rows_onto t []"

definition finite_rows_index_word :: "artifact_value_rows list \<Rightarrow> finite_exact_artifact \<Rightarrow> bool list" where
  "finite_rows_index_word T C=digit_natural_path (case value_reference_index (finite_artifact_rows C) T of
    None \<Rightarrow> length T | Some i \<Rightarrow> i)"

lemma finite_rows_index_word_cancel:
  assumes "finite_artifact_rows C\<in>set T" "finite_artifact_rows D\<in>set T"
  shows "finite_rows_index_word T C@u=finite_rows_index_word T D@v \<longleftrightarrow> C=D \<and> u=v"
proof -
  obtain i where i: "value_reference_index (finite_artifact_rows C) T=Some i"
    using assms(1) value_reference_index_absent[of "finite_artifact_rows C" T]
    by (cases "value_reference_index (finite_artifact_rows C) T") auto
  obtain j where j: "value_reference_index (finite_artifact_rows D) T=Some j"
    using assms(2) value_reference_index_absent[of "finite_artifact_rows D" T]
    by (cases "value_reference_index (finite_artifact_rows D) T") auto
  have same_index: "i=j \<longleftrightarrow> C=D"
  proof
    assume "i=j"
    then have "finite_artifact_rows C=finite_artifact_rows D"
      using value_reference_index_read[OF i] value_reference_index_read[OF j] by simp
    then show "C=D" by (simp add: finite_artifact_rows_injective)
  next
    assume "C=D"
    then show "i=j" using i j by simp
  qed
  show ?thesis by (simp add: finite_rows_index_word_def i j digit_natural_path_cancel same_index)
qed

fun finite_target_reference_word :: "artifact_value_rows list \<Rightarrow> finite_exact_target \<Rightarrow> bool list" where
  "finite_target_reference_word T (Finite_Whole C)=False#finite_rows_index_word T C"
| "finite_target_reference_word T (Finite_Anchor C a)=True#finite_rows_index_word T C@digit_address_word a"

lemma finite_target_reference_word_cancels:
  assumes "\<forall>x\<in>A. finite_artifact_rows (finite_target_artifact x)\<in>set T"
  shows "target_code_cancels (finite_target_reference_word T) A"
  unfolding target_code_cancels_def
proof (intro ballI allI)
  fix x y u v assume x: "x\<in>A" and y: "y\<in>A"
  have xm: "finite_artifact_rows (finite_target_artifact x)\<in>set T" using assms x by blast
  have ym: "finite_artifact_rows (finite_target_artifact y)\<in>set T" using assms y by blast
  show "finite_target_reference_word T x@u=finite_target_reference_word T y@v \<longleftrightarrow> x=y \<and> u=v"
    using xm ym by (cases x; cases y) (simp_all add: finite_rows_index_word_cancel)
qed

definition finite_term_shared_word :: "finite_factor_term \<Rightarrow> bool list" where
  "finite_term_shared_word t=(let T=finite_term_rows t in
    counted_digit_word artifact_rows_word T@finite_term_word_with (finite_target_reference_word T) t)"

theorem finite_term_shared_word_injective:
  "finite_term_shared_word t=finite_term_shared_word s \<longleftrightarrow> t=s"
proof
  assume same: "finite_term_shared_word t=finite_term_shared_word s"
  let ?T="finite_term_rows t"
  have parts: "finite_term_rows t=finite_term_rows s \<and>
      finite_term_word_with (finite_target_reference_word (finite_term_rows t)) t=
      finite_term_word_with (finite_target_reference_word (finite_term_rows s)) s"
    using same by (simp (no_asm_use) only: finite_term_shared_word_def Let_def
      counted_digit_word_cancel[OF artifact_rows_word_cancel])
  have tables: "finite_term_rows s=?T" using parts by simp
  have words: "finite_term_word_with (finite_target_reference_word ?T) t@[]=
      finite_term_word_with (finite_target_reference_word ?T) s@[]"
    using conjunct2[OF parts] by (simp only: tables append_Nil2)
  have table_t: "\<forall>x\<in>finite_term_targets t. finite_artifact_rows (finite_target_artifact x)\<in>set ?T"
    by (simp add: finite_term_rows_def finite_term_rows_onto_set)
  have table_s: "\<forall>x\<in>finite_term_targets s. finite_artifact_rows (finite_target_artifact x)\<in>set (finite_term_rows s)"
    by (simp add: finite_term_rows_def finite_term_rows_onto_set)
  have members: "\<forall>x\<in>finite_term_targets t \<union> finite_term_targets s.
      finite_artifact_rows (finite_target_artifact x)\<in>set ?T"
    using table_t table_s tables by auto
  show "t=s"
    using words finite_term_word_with_cancel[OF finite_target_reference_word_cancels[OF members], of "[]" "[]"]
    by blast
qed simp

definition finite_term_shared_word_fold :: "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> finite_factor_term \<Rightarrow> 's \<Rightarrow> 's" where
  "finite_term_shared_word_fold f t s=(let T=finite_term_rows t in
    finite_term_word_with_fold (finite_target_reference_word T) f t (foldl f s (counted_digit_word artifact_rows_word T)))"

theorem finite_term_shared_word_fold_exact:
  "finite_term_shared_word_fold f t s=foldl f s (finite_term_shared_word t)"
  by (simp add: finite_term_shared_word_fold_def finite_term_shared_word_def Let_def finite_term_word_with_fold_exact)

export_code finite_term_shared_word finite_term_shared_word_fold checking SML

text \<open>
  Payloads and addresses use the natural digit path of their length followed by
  the existing address digit path, so a digit word is self-delimiting. A term word
  is parameterized by the code of its target leaves, and it cancels whenever that
  code cancels on the targets of the compared terms. The shared word first gives
  the rows of every distinct artifact in first-occurrence order and then codes
  each target by the natural index of its artifact in that table; the
  first-occurrence table of the value reference theory makes the index code
  cancel on every artifact of the term. The fold delivers the same word
  incrementally without materializing it.
\<close>

end
