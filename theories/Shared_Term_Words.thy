theory Shared_Term_Words
  imports Shared_Term_Tables Indexed_Term_Words "HOL-Library.IArray"
begin

section \<open>The word of a term read off its shared terms\<close>

text \<open>
  Build B1 of DECISIONS.md, "The published state holds its targets once, and a report's word is read off
  them". A report whose value arrives as a shared term over a table has the word of the term it decodes
  to; no reference enters the word, and a shared term that does not decode has the empty word.
\<close>

definition shared_term_word_fold :: "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> shape list \<Rightarrow> shared_term \<Rightarrow> 's \<Rightarrow> 's" where
  "shared_term_word_fold f T s z=(case shared_decode T s of None \<Rightarrow> z
    | Some t \<Rightarrow> finite_term_shared_word_fold f t z)"

theorem shared_term_word_fold_exact:
  assumes "shared_decode T s=Some t"
  shows "shared_term_word_fold f T s z=finite_term_shared_word_fold f t z"
  using assms by (simp add: shared_term_word_fold_def)

corollary shared_term_word_fold_word:
  assumes "shared_decode T s=Some t"
  shows "shared_term_word_fold f T s z=foldl f z (finite_term_shared_word t)"
  using assms by (simp add: shared_term_word_fold_exact finite_term_shared_word_fold_exact)

section \<open>The target occurrences of a shared term\<close>

text \<open>
  A target leaf of the decoded term is found at the table's position that holds it, or is a target leaf
  the table does not hold, which enters by its value: the rows key of its artifact. The occurrences are
  ordered through that pair of kinds, a position compared as a number.
\<close>

datatype shared_target_occurrence = Table_Target nat | Explicit_Target compared_artifact_rows

fun occurrence_order :: "shared_target_occurrence \<Rightarrow> compared_artifact_rows option \<times> nat" where
  "occurrence_order (Table_Target i)=(None,i)"
| "occurrence_order (Explicit_Target k)=(Some k,0)"

lemma occurrence_order_injective: "inj occurrence_order"
proof (rule injI)
  fix x y assume "occurrence_order x=occurrence_order y"
  then show "x=y" by (cases x; cases y) simp_all
qed

instantiation shared_target_occurrence :: linorder
begin

definition less_eq_shared_target_occurrence :: "shared_target_occurrence \<Rightarrow> shared_target_occurrence \<Rightarrow> bool" where
  "less_eq_shared_target_occurrence x y \<longleftrightarrow> occurrence_order x\<le>occurrence_order y"

definition less_shared_target_occurrence :: "shared_target_occurrence \<Rightarrow> shared_target_occurrence \<Rightarrow> bool" where
  "less_shared_target_occurrence x y \<longleftrightarrow> occurrence_order x<occurrence_order y"

instance
proof
  fix x y z :: shared_target_occurrence
  show "x<y \<longleftrightarrow> x\<le>y \<and> \<not>y\<le>x"
    by (simp add: less_eq_shared_target_occurrence_def less_shared_target_occurrence_def less_le_not_le)
  show "x\<le>x" by (simp add: less_eq_shared_target_occurrence_def)
  show "x\<le>y \<Longrightarrow> y\<le>z \<Longrightarrow> x\<le>z"
    unfolding less_eq_shared_target_occurrence_def by (rule order_trans)
  show "x\<le>y \<Longrightarrow> y\<le>x \<Longrightarrow> x=y"
    unfolding less_eq_shared_target_occurrence_def by (auto intro: injD[OF occurrence_order_injective] antisym)
  show "x\<le>y \<or> y\<le>x" by (simp add: less_eq_shared_target_occurrence_def linear)
qed

end

definition target_rows_key :: "finite_exact_target \<Rightarrow> compared_artifact_rows" where
  "target_rows_key x=compared_artifact_rows (finite_artifact_rows (finite_target_artifact x))"

fun occurrence_key :: "shape list \<Rightarrow> shared_target_occurrence \<Rightarrow> compared_artifact_rows" where
  "occurrence_key T (Table_Target i)=(case value_reference_read T i of
      Some (Leaf_Shape (Target_Leaf x)) \<Rightarrow> target_rows_key x
    | _ \<Rightarrow> target_rows_key (Finite_Whole finite_empty_artifact))"
| "occurrence_key T (Explicit_Target k)=k"

function reference_occurrences :: "shape list \<Rightarrow> nat \<Rightarrow> shared_target_occurrence list" where
  "reference_occurrences T i=(case value_reference_read T i of
      Some (Leaf_Shape (Target_Leaf x)) \<Rightarrow> [Table_Target i]
    | Some (Pair_Shape j k) \<Rightarrow> (if j<i \<and> k<i then reference_occurrences T j@reference_occurrences T k else [])
    | _ \<Rightarrow> [])"
  by pat_completeness auto
termination by (relation "measure snd") auto

declare reference_occurrences.simps [simp del]

fun shared_occurrences :: "shape list \<Rightarrow> shared_term \<Rightarrow> shared_target_occurrence list" where
  "shared_occurrences T (Shared_Reference i)=reference_occurrences T i"
| "shared_occurrences T (Shared_Leaf (Target_Leaf x))=[Explicit_Target (target_rows_key x)]"
| "shared_occurrences T (Shared_Leaf (Payload_Leaf v))=[]"
| "shared_occurrences T (Shared_Pair a b)=shared_occurrences T a@shared_occurrences T b"

lemma reference_occurrences_decoded:
  "reference_term T i=Some t \<Longrightarrow>
    map (occurrence_key T) (reference_occurrences T i)=map target_rows_key (finite_term_target_list t)"
proof (induction i arbitrary: t rule: less_induct)
  case (less i)
  show ?case
  proof (rule reference_term_cases[OF less.prems])
    fix l assume "value_reference_read T i=Some (Leaf_Shape l)" "t=leaf_term l"
    then show ?thesis by (cases l) (simp_all add: reference_occurrences.simps[of T i])
  next
    fix j k x y assume read: "value_reference_read T i=Some (Pair_Shape j k)" and "j<i" "k<i"
      and "reference_term T j=Some x" "reference_term T k=Some y" and "t=Finite_Pair x y"
    then show ?thesis using less.IH[of j x] less.IH[of k y] by (simp add: reference_occurrences.simps[of T i])
  qed
qed

theorem shared_occurrences_decoded:
  "shared_decode T s=Some t \<Longrightarrow>
    map (occurrence_key T) (shared_occurrences T s)=map target_rows_key (finite_term_target_list t)"
proof (induction s arbitrary: t)
  case (Shared_Reference i)
  then show ?case by (simp add: reference_occurrences_decoded)
next
  case (Shared_Leaf l)
  then show ?case by (cases l) auto
next
  case (Shared_Pair a b)
  then show ?case by (auto simp: pair_decoded_some)
qed

section \<open>The word computed over the occurrences\<close>

text \<open>
  The occurrences in traversal order are referenced over their numbers, the rows key of each distinct
  occurrence's artifact is computed once, in parallel, and the distinct keys are referenced in turn; the
  composed indices are those of the plain word's run (@{text value_reference_sequence_map}), which the word
  consumes in the same order. Two occurrences with one artifact meet at its key. An occurrence costs a
  comparison of numbers, and each distinct target's rows are computed once.
\<close>

lemma shared_term_word_fold_code [code]:
  "shared_term_word_fold f T s z=(case shared_decode T s of None \<Rightarrow> z | Some t \<Rightarrow> (let
      (L,D)=keyed_reference_run id (shared_occurrences T s) RBT.empty 0 [] [];
      (G,U)=keyed_reference_compared_run compare_compared_rows (Parallel.map (occurrence_key T) D) RBT.empty 0 [] [];
      A=IArray G
    in finite_term_word_indexed f [t] (map (IArray.sub A) L)
      (counted_word_fold artifact_word_fold f (map compared_rows_listing U) z)))"
proof (cases "shared_decode T s")
  case None
  then show ?thesis by (simp add: shared_term_word_fold_def)
next
  case (Some t)
  let ?O="shared_occurrences T s"
  obtain L D where local_run: "value_reference_sequence ?O []=(L,D)"
    by (cases "value_reference_sequence ?O []")
  obtain G U where keyed_run: "value_reference_sequence (map (occurrence_key T) D) []=(G,U)"
    by (cases "value_reference_sequence (map (occurrence_key T) D) []")
  have factored: "value_reference_sequence (map (occurrence_key T) ?O) []=(map (nth G) L,U)"
    by (rule value_reference_sequence_map[OF _ local_run keyed_run]) simp
  have occurrences: "keyed_reference_run id ?O RBT.empty 0 [] []=(L,D)"
    using keyed_reference_run_exact[OF inj_on_id, of ?O] local_run by simp
  have keyed: "keyed_reference_compared_run compare_compared_rows (map (occurrence_key T) D)
      RBT.empty 0 [] []=(G,U)"
    using keyed_run by (simp only: keyed_compared_reference_sequence)
  have keys: "Parallel.map (compared_artifact_rows \<circ> finite_artifact_rows \<circ> finite_target_artifact)
      (finite_term_targets_pending [t] [])=map (occurrence_key T) ?O"
    using shared_occurrences_decoded[OF Some]
    by (simp add: Parallel.map_def finite_term_targets_pending_exact target_rows_key_def comp_def)
  have word: "finite_term_shared_word_fold f t z=finite_term_word_indexed f [t] (map (nth G) L)
      (counted_word_fold artifact_word_fold f (map compared_rows_listing U) z)"
    by (simp only: finite_term_shared_word_compared_code keys keyed_compared_reference_sequence factored
      Let_def case_prod_conv)
  have array: "IArray.sub (IArray G)=nth G" by (rule ext) simp
  show ?thesis
    using Some by (simp add: shared_term_word_fold_def word occurrences keyed array Parallel.map_def Let_def)
qed

export_code shared_term_word_fold checking SML

end
