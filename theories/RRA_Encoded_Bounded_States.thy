theory RRA_Encoded_Bounded_States
  imports RRA_Environment_Index_Equivalence RRA_Allocated_Environment_Projection
begin

definition encoded_bounded_valid ::
  "(local_address option\<Rightarrow>bool list)\<Rightarrow>(local_address\<Rightarrow>bool list)\<Rightarrow>
    bounded_environment_state\<Rightarrow>bool" where
  "encoded_bounded_valid use_code slot_code q \<longleftrightarrow>
    (\<exists>E. finite_environment_formed E \<and> encoded_environment_represents use_code slot_code (snd q) E) \<and>
    0<fst q \<and> (\<forall>u R. R |\<in>| encoded_environment_artifacts use_code (snd q) u \<longrightarrow> use_word_head u<fst q)"

definition encoded_bounded_equivalent where
  "encoded_bounded_equivalent use_code slot_code q r \<longleftrightarrow>
    fst q=fst r \<and> environment_indexes_equivalent use_code slot_code (snd q) (snd r)"

lemma equivalent_bounded_valid:
  assumes equivalent: "encoded_bounded_equivalent use_code slot_code q r"
  shows "encoded_bounded_valid use_code slot_code q=bounded_environment_valid r"
proof -
  have head: "fst q=fst r" and indexes: "environment_indexes_equivalent use_code slot_code (snd q) (snd r)"
    using equivalent by (auto simp: encoded_bounded_equivalent_def)
  have artifacts: "encoded_environment_artifacts use_code (snd q)=indexed_environment_artifacts (snd r)"
    using indexes by (simp add: environment_indexes_equivalent_def)
  show ?thesis by (simp only: encoded_bounded_valid_def bounded_environment_valid_def indexed_environment_valid_def
    head artifacts equivalent_environment_representation[OF indexes])
qed

definition encoded_bounded_rows where
  "encoded_bounded_rows use_code slot_code A B=(finite_compact_use_head (fimage fst (fset_of_list A)) None,
    encoded_environment_rows use_code slot_code A B)"

definition encoded_bounded_load where
  "encoded_bounded_load use_code slot_code A B=(if finite_environment_formed (finite_enumerated_environment A B)
    then Some (encoded_bounded_rows use_code slot_code A B) else None)"

context environment_key_codec
begin

lemma bounded_original_exists:
  "\<exists>r::bounded_environment_state. encoded_bounded_equivalent use_code slot_code q r"
proof -
  obtain J::indexed_artifact_environment where equivalent: "environment_indexes_equivalent use_code slot_code (snd q) J"
    using original_index_exists[of "snd q"] by blast
  show ?thesis by (rule exI[where x="(fst q,J)"]) (simp add: encoded_bounded_equivalent_def equivalent)
qed

lemma bounded_valid_original:
  "encoded_bounded_valid use_code slot_code q \<Longrightarrow>
    \<exists>r::bounded_environment_state. encoded_bounded_equivalent use_code slot_code q r \<and> bounded_environment_valid r"
  using bounded_original_exists[of q] equivalent_bounded_valid by blast

lemma bounded_rows_equivalent:
  "encoded_bounded_equivalent use_code slot_code (encoded_bounded_rows use_code slot_code A B) (bounded_environment_rows A B)"
  using environment_indexes_same_subject[OF rows_exact index_environment_rows_exact, of A B]
  by (simp add: encoded_bounded_equivalent_def encoded_bounded_rows_def bounded_environment_rows_def)

lemma bounded_rows_valid:
  "finite_environment_formed (finite_enumerated_environment A B) \<Longrightarrow>
    encoded_bounded_valid use_code slot_code (encoded_bounded_rows use_code slot_code A B)"
  using equivalent_bounded_valid[OF bounded_rows_equivalent, of A B] bounded_environment_rows_valid[of A B] by blast

lemma bounded_empty_valid:
  "encoded_bounded_valid use_code slot_code (encoded_bounded_rows use_code slot_code [] [])"
  using equivalent_bounded_valid[OF bounded_rows_equivalent, of "[]" "[]"] bounded_empty_environment_valid by blast

lemma bounded_load_valid:
  "encoded_bounded_load use_code slot_code A B=Some q \<Longrightarrow> encoded_bounded_valid use_code slot_code q"
  by (auto simp: encoded_bounded_load_def intro: bounded_rows_valid split: if_splits)

lemma bounded_next_fresh:
  assumes valid: "encoded_bounded_valid use_code slot_code q"
  shows "encoded_environment_artifacts use_code (snd q) (bounded_environment_next_use q)={||}"
proof -
  obtain r where equivalent: "encoded_bounded_equivalent use_code slot_code q r" and old: "bounded_environment_valid r"
    using bounded_valid_original[OF valid] by blast
  have artifacts: "encoded_environment_artifacts use_code (snd q)=indexed_environment_artifacts (snd r)"
    and next_item: "bounded_environment_next_use q=bounded_environment_next_use r"
    using equivalent by (auto simp: encoded_bounded_equivalent_def environment_indexes_equivalent_def bounded_environment_next_use_def)
  show ?thesis by (simp only: artifacts next_item bounded_environment_next_fresh[OF old])
qed

end

text \<open>
  The encoded state's actual head bounds every represented original use and
  its environment is formed. Equality of complete lookups transfers the
  established original bound invariant and freshness proof. Initialization
  computes the head from its original rows once; no validity flag is supplied.
\<close>

end
