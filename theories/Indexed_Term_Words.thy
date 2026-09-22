theory Indexed_Term_Words
  imports Finite_Term_Object_Words Keyed_Value_References Ordered_Artifact_Comparison "HOL-Library.Parallel"
begin

section \<open>One reference sequence supplies every artifact index of a term word\<close>

fun finite_term_target_list :: "finite_factor_term \<Rightarrow> finite_exact_target list" where
  "finite_term_target_list (Finite_Payload v)=[]"
| "finite_term_target_list (Finite_Pair t u)=finite_term_target_list t@finite_term_target_list u"
| "finite_term_target_list (Finite_Target x)=[x]"

function finite_term_targets_pending ::
  "finite_factor_term list \<Rightarrow> finite_exact_target list \<Rightarrow> finite_exact_target list" where
  "finite_term_targets_pending [] xs=rev xs"
| "finite_term_targets_pending (Finite_Payload v#ts) xs=finite_term_targets_pending ts xs"
| "finite_term_targets_pending (Finite_Pair t u#ts) xs=finite_term_targets_pending (t#u#ts) xs"
| "finite_term_targets_pending (Finite_Target x#ts) xs=finite_term_targets_pending ts (x#xs)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(ts,xs). 2*sum_list (map size ts)+length ts)") auto

lemma finite_term_targets_pending_exact:
  "finite_term_targets_pending ts xs=rev xs@concat (map finite_term_target_list ts)"
  by (induction ts xs rule: finite_term_targets_pending.induct) simp_all

lemma finite_term_objects_onto_sequence:
  "finite_term_objects_onto t T=snd (value_reference_sequence (map finite_target_artifact (finite_term_target_list t)) T)"
  by (induction t arbitrary: T) (simp_all add: value_reference_sequence_append case_prod_unfold Let_def)

fun target_index_word :: "finite_exact_target \<Rightarrow> nat \<Rightarrow> bool list" where
  "target_index_word (Finite_Whole C) i=False#digit_natural_path i"
| "target_index_word (Finite_Anchor C a) i=True#digit_natural_path i@digit_address_word a"

lemma target_object_index_word:
  "value_reference_index (finite_target_artifact x) T=Some i \<Longrightarrow> target_object_word T x=target_index_word x i"
  by (cases x) (simp_all add: object_index_word_def)

function finite_term_word_indexed ::
  "('s \<Rightarrow> bool \<Rightarrow> 's) \<Rightarrow> finite_factor_term list \<Rightarrow> nat list \<Rightarrow> 's \<Rightarrow> 's" where
  "finite_term_word_indexed f [] is s=s"
| "finite_term_word_indexed f (Finite_Pair t u#ts) is s=finite_term_word_indexed f (t#u#ts) is (f s True)"
| "finite_term_word_indexed f (Finite_Payload v#ts) is s=
    finite_term_word_indexed f ts is (address_word_fold f v (f (f s False) False))"
| "finite_term_word_indexed f (Finite_Target x#ts) is s=
    finite_term_word_indexed f ts (tl is) (foldl f (f (f s False) True) (target_index_word x (hd is)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(f,ts,is,s). 2*sum_list (map size ts)+length ts)") auto

lemma finite_term_word_indexed_pending:
  "(\<And>x. x\<in>set (concat (map finite_term_target_list ts)) \<Longrightarrow> leaf x=target_index_word x (index x)) \<Longrightarrow>
    finite_term_word_indexed f ts (map index (concat (map finite_term_target_list ts))@rest) s=
    finite_term_word_pending leaf f ts s"
proof (induction "2*sum_list (map size ts)+length ts" arbitrary: ts rest s rule: less_induct)
  case less
  show ?case
  proof (cases ts)
    case (Cons t ts')
    show ?thesis
    proof (cases t)
      case (Finite_Pair t1 t2)
      have "finite_term_word_indexed f (t1#t2#ts') (map index (concat (map finite_term_target_list (t1#t2#ts')))@rest) (f s True)=
          finite_term_word_pending leaf f (t1#t2#ts') (f s True)"
        by (rule less.hyps) (use less.prems in \<open>auto simp: Cons Finite_Pair\<close>)
      then show ?thesis by (simp add: Cons Finite_Pair)
    next
      case (Finite_Payload v)
      have "finite_term_word_indexed f ts' (map index (concat (map finite_term_target_list ts'))@rest)
          (address_word_fold f v (f (f s False) False))=
        finite_term_word_pending leaf f ts' (address_word_fold f v (f (f s False) False))"
        by (rule less.hyps) (use less.prems in \<open>auto simp: Cons Finite_Payload\<close>)
      then show ?thesis by (simp add: Cons Finite_Payload)
    next
      case (Finite_Target x)
      have leaf: "leaf x=target_index_word x (index x)" using less.prems by (simp add: Cons Finite_Target)
      have "finite_term_word_indexed f ts' (map index (concat (map finite_term_target_list ts'))@rest)
          (foldl f (f (f s False) True) (target_index_word x (index x)))=
        finite_term_word_pending leaf f ts' (foldl f (f (f s False) True) (target_index_word x (index x)))"
        by (rule less.hyps) (use less.prems in \<open>auto simp: Cons Finite_Target\<close>)
      then show ?thesis by (simp add: Cons Finite_Target leaf)
    qed
  qed simp
qed

declare finite_term_shared_object_word_code[code del]

lemma finite_term_shared_word_indexed:
  "finite_term_shared_word_fold f t s=(let
      (indices,T)=value_reference_sequence (map finite_target_artifact (finite_term_targets_pending [t] [])) []
    in finite_term_word_indexed f [t] indices (counted_word_fold artifact_word_fold f (map finite_artifact_rows T) s))"
proof -
  let ?objects="map finite_target_artifact (finite_term_target_list t)"
  let ?T="snd (value_reference_sequence ?objects [])"
  let ?I="fst (value_reference_sequence ?objects [])"
  let ?index="\<lambda>x. the (value_reference_index (finite_target_artifact x) ?T)"
  have table: "finite_term_objects_pending [t] []=?T"
    by (simp add: finite_term_objects_pending_exact finite_term_objects_onto_sequence)
  have distinct: "distinct ?T" by (rule value_reference_sequence_distinct) simp
  have reads: "map (value_reference_read ?T) ?I=map Some ?objects"
    by (rule value_reference_sequence_exact)
  have lengths: "length ?I=length (finite_term_target_list t)"
    using arg_cong[OF reads, of length] by simp
  have index_at: "value_reference_index (finite_target_artifact (finite_term_target_list t!k)) ?T=Some (?I!k)"
    if k: "k<length (finite_term_target_list t)" for k
  proof -
    have "value_reference_read ?T (?I!k)=Some (?objects!k)"
      using arg_cong[OF reads, of "\<lambda>xs. xs!k"] k lengths by simp
    then show ?thesis using k by (simp add: value_reference_index_distinct_read[OF distinct])
  qed
  have indices: "?I=map ?index (finite_term_target_list t)"
    by (rule nth_equalityI) (simp_all add: lengths index_at)
  have leaves: "target_object_word ?T x=target_index_word x (?index x)"
    if "x\<in>set (concat (map finite_term_target_list [t]))" for x
  proof -
    have member: "x\<in>set (finite_term_target_list t)" using that by simp
    obtain k where k: "k<length (finite_term_target_list t)" "finite_term_target_list t!k=x"
      using member by (meson in_set_conv_nth)
    show ?thesis using index_at[OF k(1)] k(2) by (simp add: target_object_index_word)
  qed
  have word: "finite_term_word_indexed f [t] (map ?index (concat (map finite_term_target_list [t]))@[])
      (counted_word_fold artifact_word_fold f (map finite_artifact_rows ?T) s)=
    finite_term_word_pending (target_object_word ?T) f [t] (counted_word_fold artifact_word_fold f (map finite_artifact_rows ?T) s)"
    by (rule finite_term_word_indexed_pending[OF leaves])
  have sequence: "value_reference_sequence (map finite_target_artifact (finite_term_targets_pending [t] [])) []=(?I,?T)"
    by (simp add: finite_term_targets_pending_exact)
  show ?thesis
    using word by (simp only: finite_term_shared_object_word_code Let_def table sequence indices
      case_prod_conv append_Nil2 concat.simps list.map)
qed

lemma compared_artifact_rows_key_inj: "inj (compared_artifact_rows \<circ> finite_artifact_rows)"
  by (rule injI) (simp add: compared_artifact_rows_def finite_artifact_rows_injective)

lemma finite_term_shared_word_compared_code [code]:
  "finite_term_shared_word_fold f t s=(let
      keys=Parallel.map (compared_artifact_rows \<circ> finite_artifact_rows \<circ> finite_target_artifact)
        (finite_term_targets_pending [t] []);
      (indices,table)=keyed_reference_compared_run compare_compared_rows keys RBT.empty 0 [] []
    in finite_term_word_indexed f [t] indices (counted_word_fold artifact_word_fold f (map compared_rows_listing table) s))"
proof -
  let ?key="compared_artifact_rows \<circ> finite_artifact_rows"
  let ?objects="map finite_target_artifact (finite_term_targets_pending [t] [])"
  have run: "keyed_reference_compared_run compare_compared_rows (map ?key ?objects) RBT.empty 0 [] []=
      (fst (value_reference_sequence ?objects []),map ?key (snd (value_reference_sequence ?objects [])))"
    by (simp only: keyed_reference_compared_run_exact[OF compare_compared_rows_linear]
      keyed_reference_run_keys[symmetric] keyed_reference_run_exact[OF compared_artifact_rows_key_inj])
  have keys: "Parallel.map (compared_artifact_rows \<circ> finite_artifact_rows \<circ> finite_target_artifact)
      (finite_term_targets_pending [t] [])=map ?key ?objects"
    by (simp add: comp_def)
  have rows: "map compared_rows_listing (map ?key T)=map finite_artifact_rows T" for T
    by (induction T) simp_all
  show ?thesis
    by (simp only: finite_term_shared_word_indexed keys run rows Let_def case_prod_unfold fst_conv snd_conv)
qed

lemma keyed_compared_reference_sequence:
  "keyed_reference_compared_run compare_compared_rows ks RBT.empty 0 [] []=value_reference_sequence ks []"
proof -
  have "keyed_reference_compared_run compare_compared_rows ks RBT.empty 0 [] []=keyed_reference_run id ks RBT.empty 0 [] []"
    by (rule keyed_reference_compared_run_exact[OF compare_compared_rows_linear])
  also have "\<dots>=(fst (value_reference_sequence ks []),map id (snd (value_reference_sequence ks [])))"
    by (rule keyed_reference_run_exact[OF inj_on_id])
  finally show ?thesis by (simp only: list.map_id prod.collapse)
qed

definition keyed_segmented_references ::
  "compared_artifact_rows list list \<Rightarrow> nat list\<times>compared_artifact_rows list" where
  "keyed_segmented_references cs=(let
      locals=Parallel.map (\<lambda>c. keyed_reference_compared_run compare_compared_rows c RBT.empty 0 [] []) cs;
      (G,U)=keyed_reference_compared_run compare_compared_rows (concat (map snd locals)) RBT.empty 0 [] []
    in (value_reference_merged locals G,U))"

lemma keyed_segmented_references_exact:
  "keyed_segmented_references cs=value_reference_sequence (concat cs) []"
proof -
  have split: "value_reference_sequence (concat cs) []=(let locals=map (\<lambda>c. value_reference_sequence c []) cs;
      (G,U)=value_reference_sequence (concat (map snd locals)) [] in (value_reference_merged locals G,U))"
    by (rule value_reference_sequence_concat[OF distinct.simps(1)[THEN eqTrueE]])
  show ?thesis
    by (simp only: keyed_segmented_references_def keyed_compared_reference_sequence Parallel.map_def split)
qed

declare finite_term_shared_word_compared_code[code del]

lemma finite_term_shared_word_segmented_code [code]:
  "finite_term_shared_word_fold f t s=(let
      keys=Parallel.map (compared_artifact_rows \<circ> finite_artifact_rows \<circ> finite_target_artifact)
        (finite_term_targets_pending [t] []);
      (indices,table)=keyed_segmented_references (value_reference_chunks (length keys div 8+1) keys)
    in finite_term_word_indexed f [t] indices (counted_word_fold artifact_word_fold f (map compared_rows_listing table) s))"
  by (simp only: finite_term_shared_word_compared_code keyed_segmented_references_exact
    value_reference_chunks_concat keyed_compared_reference_sequence)

text \<open>
  The first-occurrence references of the keys are computed segment by segment: each of about
  eight consecutive segments against its own empty table, in parallel, and then only the segments'
  distinct keys against one table (\<open>value_reference_sequence_concat\<close>). The indices and the
  table are those of the one sequential run, so the word is unchanged. A report whose targets repeat
  few distinct artifacts many times spent its word in the one sequential run, one complete comparison
  of equal keys per occurrence; the segments share that work among the threads.
\<close>

text \<open>
  Each complete artifact occurrence is compared with the first-occurrence table
  once. The existing reference sequence returns every occurrence's index while it
  builds exactly the prior object table, whose complete rows are still converted
  once per entry. The word consumes those indices in traversal order instead of
  searching the table again. The complete rows of each occurrence are its
  injective ordered key with its field sizes, computed for all occurrences in
  parallel. The first-occurrence table is searched through an ordered tree of
  those keys with one comparison of three outcomes per node, and its table
  already supplies the emitted rows. The
  delivered word is the existing shared word.
\<close>

end
