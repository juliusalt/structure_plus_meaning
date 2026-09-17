theory Finite_Term_Object_Words
  imports Finite_Term_Word_Streaming
    Complete_Object_References
begin

fun finite_term_objects_onto :: "finite_factor_term \<Rightarrow> finite_exact_artifact list \<Rightarrow> finite_exact_artifact list" where
  "finite_term_objects_onto (Finite_Payload v) T=T"
| "finite_term_objects_onto (Finite_Pair t u) T=finite_term_objects_onto u (finite_term_objects_onto t T)"
| "finite_term_objects_onto (Finite_Target x) T=snd (value_reference_step (finite_target_artifact x) T)"

lemma finite_term_objects_rows:
  "map finite_artifact_rows (finite_term_objects_onto t T)=finite_term_rows_onto t (map finite_artifact_rows T)"
proof (induction t T rule: finite_term_objects_onto.induct)
  case (3 x T)
  have equality: "map_prod id (map finite_artifact_rows) (value_reference_step (finite_target_artifact x) T)=
      value_reference_step (finite_artifact_rows (finite_target_artifact x)) (map finite_artifact_rows T)"
    by (rule value_reference_step_identity_map[OF finite_artifact_rows_injective])
  show ?case using arg_cong[OF equality, of snd]
    by (simp add: map_prod_def case_prod_unfold)
qed simp_all

function finite_term_objects_pending ::
  "finite_factor_term list \<Rightarrow> finite_exact_artifact list \<Rightarrow> finite_exact_artifact list" where
  "finite_term_objects_pending [] T=T"
| "finite_term_objects_pending (Finite_Payload v#ts) T=finite_term_objects_pending ts T"
| "finite_term_objects_pending (Finite_Pair t u#ts) T=finite_term_objects_pending (t#u#ts) T"
| "finite_term_objects_pending (Finite_Target x#ts) T=finite_term_objects_pending ts
    (snd (value_reference_step (finite_target_artifact x) T))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(ts,T). 2*sum_list (map size ts)+length ts)") auto

lemma finite_term_objects_pending_exact:
  "finite_term_objects_pending ts T=foldl (\<lambda>A t. finite_term_objects_onto t A) T ts"
  by (induction ts T rule: finite_term_objects_pending.induct) simp_all

definition object_index_word where
  "object_index_word T C=digit_natural_path (case value_reference_index C T of None \<Rightarrow> length T | Some i \<Rightarrow> i)"

lemma object_index_word_rows:
  "object_index_word T C=finite_rows_index_word (map finite_artifact_rows T) C"
  by (simp add: object_index_word_def finite_rows_index_word_def
      value_reference_index_identity_map[OF finite_artifact_rows_injective] length_map split: option.splits)

fun target_object_word where
  "target_object_word T (Finite_Whole C)=False#object_index_word T C"
| "target_object_word T (Finite_Anchor C a)=True#object_index_word T C@digit_address_word a"

lemma target_object_word_rows:
  "target_object_word T=finite_target_reference_word (map finite_artifact_rows T)"
  by (rule ext; case_tac x) (simp_all add: object_index_word_rows)

lemma finite_term_objects_table:
  "map finite_artifact_rows (finite_term_objects_pending [t] [])=finite_term_rows t"
  by (simp add: finite_term_objects_pending_exact finite_term_objects_rows finite_term_rows_def)

declare finite_term_shared_word_stream_code[code del]

lemma finite_term_shared_object_word_code [code]:
  "finite_term_shared_word_fold f t s=(let T=finite_term_objects_pending [t] []; rows=map finite_artifact_rows T in
    finite_term_word_pending (target_object_word T) f [t]
      (counted_word_fold artifact_word_fold f rows s))"
  by (simp add: finite_term_shared_word_stream_code Let_def target_object_word_rows finite_term_objects_table)

export_code finite_term_shared_word_fold checking SML

text \<open>
  Reference lookup retains the complete artifact itself. Its complete row
  conversion is applied once to each retained table entry, not again at each
  target occurrence. The existing injective identity-map laws establish exactly
  the same indices, row table and emitted word, including every malformed value.
\<close>

end
