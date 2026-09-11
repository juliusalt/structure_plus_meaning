theory Factor_Observation_Table_Contracts
  imports Factor_Observation_Table_Witnesses
begin

section \<open>The public results admit every complete presentation of the computed graph\<close>

lemma observation_table_profile_rows_output:
  assumes "observation_profile_rows_presents S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning observation_table_system \<longleftrightarrow> observation_profile_rows_presents S q"
  by (simp only: observation_table_components observation_profile_rows_output[OF assms])

lemma observation_table_loss_rows_output:
  assumes "observation_loss_rows_presents S p"
  shows "(317,Pair_Term p q)\<in>positive_meaning observation_table_system \<longleftrightarrow> observation_loss_rows_presents S q"
  by (simp only: observation_table_components observation_loss_rows_output[OF assms])

theorem observation_profile_table_contract:
  "presented_function_contract observation_scope_presents observation_scope_domain
    (\<lambda>p. \<exists>z. observation_scope_presents z p)
    observation_profile_rows_presents (observation_keyed_rows_domain observation_datum)
    (\<lambda>q. \<exists>S. observation_profile_rows_presents S q) observation_profile_table_subject
    (\<lambda>p q. (330,Pair_Term p q)\<in>positive_meaning observation_table_system)"
  by (rule observation_table_profile_comparison.presented_contract[OF observation_profile_table_witness
    observation_table_profile_rows_output])

theorem observation_loss_table_contract:
  "presented_function_contract observation_scope_presents observation_scope_domain
    (\<lambda>p. \<exists>z. observation_scope_presents z p)
    observation_loss_rows_presents (observation_keyed_rows_domain (\<lambda>(c,d). data_elements [c,d]))
    (\<lambda>q. \<exists>S. observation_loss_rows_presents S q) observation_loss_table_subject
    (\<lambda>p q. (335,Pair_Term p q)\<in>positive_meaning observation_table_system)"
  by (rule observation_table_loss_comparison.presented_contract[OF observation_loss_table_witness
    observation_table_loss_rows_output])

interpretation observation_profile_tables: presented_function_contract observation_scope_presents observation_scope_domain
  "\<lambda>p. \<exists>z. observation_scope_presents z p" observation_profile_rows_presents
  "observation_keyed_rows_domain observation_datum" "\<lambda>q. \<exists>S. observation_profile_rows_presents S q"
  observation_profile_table_subject "\<lambda>p q. (330,Pair_Term p q)\<in>positive_meaning observation_table_system"
  by (rule observation_profile_table_contract)

interpretation observation_loss_tables: presented_function_contract observation_scope_presents observation_scope_domain
  "\<lambda>p. \<exists>z. observation_scope_presents z p" observation_loss_rows_presents
  "observation_keyed_rows_domain (\<lambda>(c,d). data_elements [c,d])" "\<lambda>q. \<exists>S. observation_loss_rows_presents S q"
  observation_loss_table_subject "\<lambda>p q. (335,Pair_Term p q)\<in>positive_meaning observation_table_system"
  by (rule observation_loss_table_contract)

corollary observation_profile_table_output:
  assumes "observation_scope_presents z p"
  shows "(330,Pair_Term p q)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    observation_profile_rows_presents (observation_profile_table_subject z) q"
  by (rule observation_profile_tables.output[OF assms])

corollary observation_loss_table_output:
  assumes "observation_scope_presents z p"
  shows "(335,Pair_Term p q)\<in>positive_meaning observation_table_system \<longleftrightarrow>
    observation_loss_rows_presents (observation_loss_table_subject z) q"
  by (rule observation_loss_tables.output[OF assms])

corollary observation_profile_table_invariance:
  assumes "observation_scope_presents z p" "observation_scope_presents z p'"
    "observation_profile_rows_presents S q" "observation_profile_rows_presents S q'"
  shows "((330,Pair_Term p q)\<in>positive_meaning observation_table_system)=
    ((330,Pair_Term p' q')\<in>positive_meaning observation_table_system)"
  by (rule observation_profile_tables.invariance[OF assms(1,3,2,4)])

corollary observation_loss_table_invariance:
  assumes "observation_scope_presents z p" "observation_scope_presents z p'"
    "observation_loss_rows_presents S q" "observation_loss_rows_presents S q'"
  shows "((335,Pair_Term p q)\<in>positive_meaning observation_table_system)=
    ((335,Pair_Term p' q')\<in>positive_meaning observation_table_system)"
  by (rule observation_loss_tables.invariance[OF assms(1,3,2,4)])

abbreviation observation_profile_table_result where
  "observation_profile_table_result t \<equiv> \<exists>z p q. t=Pair_Term p q \<and> observation_scope_presents z p \<and>
    observation_profile_rows_presents (observation_profile_table_subject z) q"

abbreviation observation_loss_table_result where
  "observation_loss_table_result t \<equiv> \<exists>z p q. t=Pair_Term p q \<and> observation_scope_presents z p \<and>
    observation_loss_rows_presents (observation_loss_table_subject z) q"

theorem observation_profile_table_exact:
  "(330,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> observation_profile_table_result t"
  by (rule observation_table_profile_comparison.presented_exact[OF observation_profile_table_contract])

theorem observation_loss_table_exact:
  "(335,t)\<in>positive_meaning observation_table_system \<longleftrightarrow> observation_loss_table_result t"
  by (rule observation_table_loss_comparison.presented_exact[OF observation_loss_table_contract])

text \<open>
  The complete input class is the existing admitted scope record. The output
  classes remain the existing complete nested finite-set classes. The native
  computation determines their values from that input, and the existing
  comparison admits every presentation of the resulting finite graph.

  Every declared candidate and every ordered pair remains a key, including
  keys with empty values. Output functionality is a consequence of these
  graphs, not an extra primitive requirement on arbitrary collection rows.
  Both positive and negative decisions are invariant under the allowed
  changes of input and output presentation. Admission still checks all
  available and selected facets and every table row when a map is empty.
\<close>

end
