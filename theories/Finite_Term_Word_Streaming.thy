theory Finite_Term_Word_Streaming
  imports Finite_Term_Words
begin

section \<open>Counted sequences and artifact fields deliver their bits incrementally\<close>

definition counted_word_fold where
  "counted_word_fold deliver f xs s=foldl (\<lambda>a x. deliver f x a)
    (foldl f s (digit_natural_path (length xs))) xs"

lemma prefix_word_fold:
  "foldl (\<lambda>a x. foldl f a (code x)) s xs=foldl f s (prefix_word_encoding code xs)"
  by (induction xs arbitrary: s) simp_all

lemma counted_word_fold_exact:
  assumes "\<And>x a. deliver f x a=foldl f a (code x)"
  shows "counted_word_fold deliver f xs s=foldl f s (counted_digit_word code xs)"
  by (simp add: counted_word_fold_def counted_digit_word_def assms prefix_word_fold)

definition address_word_fold where
  "address_word_fold f a s=counted_word_fold (\<lambda>f n s. foldl f s (digit_natural_path n)) f a s"

lemma address_word_fold_exact:
  "address_word_fold f a s=foldl f s (digit_address_word a)"
  by (simp add: address_word_fold_def digit_address_word_def counted_word_fold_exact)

definition incidence_word_fold where
  "incidence_word_fold f row s=address_word_fold f (snd (snd row))
    (address_word_fold f (fst (snd row)) (address_word_fold f (fst row) s))"

definition data_word_fold where
  "data_word_fold f row s=address_word_fold f (snd row) (address_word_fold f (fst row) s)"

lemma row_word_fold_exact:
  "incidence_word_fold f row s=foldl f s (incidence_row_word row)"
  "data_word_fold f item s=foldl f s (data_row_word item)"
  by (simp_all add: incidence_word_fold_def data_word_fold_def address_word_fold_exact
      incidence_row_word_def data_row_word_def pair_word_def)

definition artifact_word_fold where
  "artifact_word_fold f rows s=counted_word_fold data_word_fold f (snd (snd (snd rows)))
    (counted_word_fold data_word_fold f (fst (snd (snd rows)))
    (counted_word_fold incidence_word_fold f (fst (snd rows))
    (counted_word_fold address_word_fold f (fst rows) s)))"

lemma artifact_word_fold_exact:
  "artifact_word_fold f rows s=foldl f s (artifact_rows_word rows)"
  by (simp add: artifact_word_fold_def counted_word_fold_exact[where deliver="address_word_fold" and code="digit_address_word", OF address_word_fold_exact]
      counted_word_fold_exact[where deliver="incidence_word_fold" and code="incidence_row_word", OF row_word_fold_exact(1)] counted_word_fold_exact[where deliver="data_word_fold" and code="data_row_word", OF row_word_fold_exact(2)]
      artifact_rows_word_def pair_word_def)

section \<open>Explicit pending terms replace the recursive traversal stack\<close>

function finite_term_rows_pending ::
  "finite_factor_term list \<Rightarrow> artifact_value_rows list \<Rightarrow> artifact_value_rows list" where
  "finite_term_rows_pending [] T=T"
| "finite_term_rows_pending (Finite_Payload v#ts) T=finite_term_rows_pending ts T"
| "finite_term_rows_pending (Finite_Pair t u#ts) T=finite_term_rows_pending (t#u#ts) T"
| "finite_term_rows_pending (Finite_Target x#ts) T=finite_term_rows_pending ts
    (snd (value_reference_step (finite_artifact_rows (finite_target_artifact x)) T))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(ts,T). 2*sum_list (map size ts)+length ts)") auto

lemma finite_term_rows_pending_exact:
  "finite_term_rows_pending ts T=foldl (\<lambda>A t. finite_term_rows_onto t A) T ts"
  by (induction ts T rule: finite_term_rows_pending.induct) simp_all

function finite_term_word_pending ::
  "(finite_exact_target \<Rightarrow> bool list) \<Rightarrow> ('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow>
    finite_factor_term list \<Rightarrow> 's \<Rightarrow> 's" where
  "finite_term_word_pending leaf f [] s=s"
| "finite_term_word_pending leaf f (Finite_Pair t u#ts) s=
    finite_term_word_pending leaf f (t#u#ts) (f s True)"
| "finite_term_word_pending leaf f (Finite_Payload v#ts) s=
    finite_term_word_pending leaf f ts (address_word_fold f v (f (f s False) False))"
| "finite_term_word_pending leaf f (Finite_Target x#ts) s=
    finite_term_word_pending leaf f ts (foldl f (f (f s False) True) (leaf x))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(leaf,f,ts,s). 2*sum_list (map size ts)+length ts)") auto

lemma finite_term_word_pending_exact:
  "finite_term_word_pending leaf f ts s=foldl f s (concat (map (finite_term_word_with leaf) ts))"
  by (induction leaf f ts s rule: finite_term_word_pending.induct)
    (simp_all add: address_word_fold_exact)

declare finite_term_rows_def[code del]
lemma finite_term_rows_pending_code [code]:
  "finite_term_rows t=finite_term_rows_pending [t] []"
  by (simp add: finite_term_rows_def finite_term_rows_pending_exact)

declare finite_term_shared_word_fold_def[code del]
lemma finite_term_shared_word_stream_code [code]:
  "finite_term_shared_word_fold f t s=(let T=finite_term_rows t in
    finite_term_word_pending (finite_target_reference_word T) f [t]
      (counted_word_fold artifact_word_fold f T s))"
  by (simp add: finite_term_shared_word_fold_exact finite_term_shared_word_def Let_def
      finite_term_word_pending_exact counted_word_fold_exact[where deliver="artifact_word_fold" and code="artifact_rows_word", OF artifact_word_fold_exact])

text \<open>
  The streamed word is exactly the existing shared word. Artifact rows, payloads
  and term branches are delivered without constructing their concatenated bit
  sequences, and pending terms live in an explicit list rather than the call
  stack. Every complete artifact, count, address and term occurrence remains.
\<close>

end
