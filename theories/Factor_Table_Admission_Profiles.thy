theory Factor_Table_Admission_Profiles
  imports Factor_Table_Presentations Factor_Recursive_Groups
begin

section \<open>Native key uniqueness combines with complete row admission\<close>

theorem encoded_table_admission_formed:
  assumes injective: "inj f"
    and shape: "\<And>z p. R z p \<Longrightarrow> \<exists>v. p=Pair_Term (f (fst z)) v"
    and data: "\<And>z p. R z p \<Longrightarrow> term_formed p \<and> self_contained_term (f (fst z))"
  shows "((21,t)\<in>positive_meaning keyed_list_system \<and> (\<exists>xs. data_sequence_presents R xs t))
    \<longleftrightarrow> (\<exists>Q. single_valued Q \<and> data_collection_presents R Q t)"
proof
  assume accepted: "(21,t)\<in>positive_meaning keyed_list_system \<and> (\<exists>xs. data_sequence_presents R xs t)"
  then obtain xs ts where read: "list_all2 R xs ts" and encoded: "t=data_list_term ts"
    by (auto simp: data_sequence_presents_def)
  have all: "\<forall>t\<in>set ts. term_formed t"
    and key_data: "\<forall>z\<in>set xs. self_contained_term (f (fst z))"
    using read by (induction xs arbitrary: ts) (auto simp: list_all2_Cons1 dest: data)+
  have keys: "distinct xs \<and> single_valued (set xs)"
    using accepted keyed_list_encoded_keys_formed[OF read all key_data injective shape] encoded by blast
  show "\<exists>Q. single_valued Q \<and> data_collection_presents R Q t"
    by (rule exI[of _ "set xs"])
      (use read encoded keys in \<open>auto simp: data_collection_presents_def\<close>)
next
  assume "\<exists>Q. single_valued Q \<and> data_collection_presents R Q t"
  then obtain Q xs ts where sv: "single_valued Q" and distinct: "distinct xs"
    and set: "set xs=Q" and read: "list_all2 R xs ts" and encoded: "t=data_list_term ts"
    by (auto simp: data_collection_presents_def)
  have all: "\<forall>t\<in>set ts. term_formed t"
    and key_data: "\<forall>z\<in>set xs. self_contained_term (f (fst z))"
    using read by (induction xs arbitrary: ts) (auto simp: list_all2_Cons1 dest: data)+
  have keys: "(21,t)\<in>positive_meaning keyed_list_system"
    using keyed_list_encoded_keys_formed[OF read all key_data injective shape] distinct sv set encoded by blast
  show "(21,t)\<in>positive_meaning keyed_list_system \<and> (\<exists>xs. data_sequence_presents R xs t)"
    using keys read encoded by (auto simp: data_sequence_presents_def)
qed

theorem encoded_table_admission:
  assumes injective: "inj f"
    and shape: "\<And>z p. R z p \<Longrightarrow> \<exists>v. p=Pair_Term (f (fst z)) v"
    and data: "\<And>z p. R z p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "((21,t)\<in>positive_meaning keyed_list_system \<and> (\<exists>xs. data_sequence_presents R xs t))
    \<longleftrightarrow> (\<exists>Q. single_valued Q \<and> data_collection_presents R Q t)"
proof (rule encoded_table_admission_formed[OF injective shape])
  fix z p assume read: "R z p"
  obtain v where row: "p=Pair_Term (f (fst z)) v" using shape[OF read] by blast
  show "term_formed p \<and> self_contained_term (f (fst z))"
    using data[OF read] by (simp add: row)
qed

definition table_admission_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "table_admission_schema keys rows=data_rule data_x {(0,keys,data_x),(1,rows,data_x)}"

locale table_admission_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry keys_site rows_site :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>{(0,table_admission_schema keys_site rows_site)}"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (keys_site,t)\<in>positive_meaning P \<and> (rows_site,t)\<in>positive_meaning P"
proof -
  have valuation: "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> t=h 0 \<and>
        (keys_site,h 0)\<in>positive_meaning P \<and> (rows_site,h 0)\<in>positive_meaning P)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: family table_admission_schema_def schema_variables_def call)
  have formed: "term_formed t" if "(keys_site,t)\<in>positive_meaning P"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  show ?thesis
  proof
    assume "(entry,t)\<in>positive_meaning P"
    then show "(keys_site,t)\<in>positive_meaning P \<and> (rows_site,t)\<in>positive_meaning P"
      by (simp only: valuation; blast)
  next
    assume supported: "(keys_site,t)\<in>positive_meaning P \<and> (rows_site,t)\<in>positive_meaning P"
    show "(entry,t)\<in>positive_meaning P"
      by (simp only: valuation; rule exI[of _ "\<lambda>_::nat. t"])
        (use supported formed in auto)
  qed
qed

theorem presented_formed:
  assumes injective: "inj f"
    and shape: "\<And>z p. R z p \<Longrightarrow> \<exists>v. p=Pair_Term (f (fst z)) v"
    and data: "\<And>z p. R z p \<Longrightarrow> term_formed p \<and> self_contained_term (f (fst z))"
    and keys: "\<And>t. (keys_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (21,t)\<in>positive_meaning keyed_list_system"
    and rows: "\<And>t. (rows_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>xs. data_sequence_presents R xs t)"
  shows "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>Q. single_valued Q \<and> data_collection_presents R Q t)"
  by (simp only: exact keys rows encoded_table_admission_formed[OF injective shape data])

theorem presented:
  assumes injective: "inj f"
    and shape: "\<And>z p. R z p \<Longrightarrow> \<exists>v. p=Pair_Term (f (fst z)) v"
    and data: "\<And>z p. R z p \<Longrightarrow> term_formed p \<and> self_contained_term p"
    and keys: "\<And>t. (keys_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (21,t)\<in>positive_meaning keyed_list_system"
    and rows: "\<And>t. (rows_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>xs. data_sequence_presents R xs t)"
  shows "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>Q. single_valued Q \<and> data_collection_presents R Q t)"
  by (simp only: exact keys rows encoded_table_admission[OF injective shape data])

end

text \<open>
  The generic table class permits relational key presentations. This native
  profile has the narrower, explicit contract that each key has one injective
  data encoding. The existing key checker then tests semantic key uniqueness.
  Complete row admission separately owns every key and value boundary.
  The generalized contract requires self-containment only of keys; formed
  target-bearing values are also admitted. The earlier data-row contract
  follows as a stronger-input instance without changing the native clauses.

  Equal values at different keys remain admitted. A repeated key is rejected
  even if its two values agree. Both checks are ordinary premises with distinct
  sockets; the profile introduces no negative premise or table oracle.
\<close>

end
