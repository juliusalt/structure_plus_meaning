theory Factor_Indexed_History_Members
  imports Factor_Required_History_Projection RRA_Encoded_Site_Relations RRA_Digit_Environment_Instance
begin

type_synonym history_member_index = "finite_generation fset binary_path_store binary_path_store"
type_synonym indexed_required_history_state = "finite_required_history_state\<times>history_member_index"

definition history_members_index where
  "history_members_index rows=encoded_site_rows digit_use_path digit_address_path rows"

definition history_member_lookup where
  "history_member_lookup (I::history_member_index) u k=
    encoded_site_lookup digit_use_path digit_address_path I u k"

definition history_member_insert where
  "history_member_insert (I::history_member_index) u k G=
    encoded_site_insert digit_use_path digit_address_path I u k G"

definition history_member_index_exact where
  "history_member_index_exact I rows \<longleftrightarrow>
    encoded_site_represents digit_use_path digit_address_path I (set rows)"

definition history_member_view where
  "history_member_view (I::history_member_index)=
    encoded_site_view read_digit_use_path read_digit_address_path I"

definition indexed_history_members where
  "indexed_history_members I rows=list_all (\<lambda>((u,k),G). G |\<in>| history_member_lookup I u k) rows"

definition indexed_required_history_valid where
  "indexed_required_history_valid (q::indexed_required_history_state) \<longleftrightarrow>
    finite_required_history_valid (fst q) \<and>
    history_member_index_exact (snd q) (required_history_members (fst q))"

lemma history_members_index_exact:
  "history_member_index_exact (history_members_index rows) rows"
  by (simp add: history_member_index_exact_def history_members_index_def
    RRA_Encoded_Site_Relations.environment_key_encoding.site_rows_exact[OF digit_environment.environment_key_encoding_axioms])

lemma history_member_lookup_exact:
  "history_member_index_exact I rows \<Longrightarrow>
    G |\<in>| history_member_lookup I u k \<longleftrightarrow> ((u,k),G)\<in>set rows"
  by (auto simp: history_member_index_exact_def history_member_lookup_def encoded_site_represents_def)

lemma history_member_insert_exact:
  "history_member_index_exact I rows \<Longrightarrow>
    history_member_index_exact (history_member_insert I u k G) (((u,k),G)#rows)"
  by (simp add: history_member_index_exact_def history_member_insert_def
    RRA_Encoded_Site_Relations.environment_key_encoding.site_insert_exact[OF digit_environment.environment_key_encoding_axioms])

lemma indexed_history_members_exact:
  "history_member_index_exact I ledger \<Longrightarrow>
    indexed_history_members I rows=list_all (\<lambda>row. row\<in>set ledger) rows"
  by (auto simp: indexed_history_members_def list_all_iff history_member_lookup_exact)

lemma history_member_view_exact:
  "history_member_index_exact I rows \<Longrightarrow> history_member_view I=fset_of_list rows"
  using RRA_Encoded_Site_Relations.environment_key_codec.site_view_exact[OF digit_environment.environment_key_codec_axioms]
  by (auto simp: history_member_view_def history_member_index_exact_def fset_of_list.rep_eq fset_inject[symmetric])

lemma indexed_required_history_initial:
  "finite_required_history_valid q \<Longrightarrow>
    indexed_required_history_valid (q,history_members_index (required_history_members q))"
  by (simp add: indexed_required_history_valid_def history_members_index_exact)

text \<open>
  The ledger remains the complete original list. The index implements exactly
  its membership relation, never generation readability in retained material.
  Complete decoded cache observation is proved equal to that relation. It can
  therefore expose missing updates even when the immediate original state
  projection is correct.
\<close>

end
