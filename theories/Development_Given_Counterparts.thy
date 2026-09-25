theory Development_Given_Counterparts
  imports Development_Given_Installation Factor_Definition_Reader_Counterparts Factor_Audit_Counterparts
begin

text \<open>
  The given's base (DECISIONS.md "The native evaluator evaluates above an implemented base: the given's
  readers enter through counterparts exact to their native definitions", decisions 2 and 5): a decision at
  the installed site of every entry the guard reaches in the given (@{const given_guard_entries}), each by that
  entry's counterpart — C1's at 113 and 80, C2's at 392 and 393, C3's at 505, C4's at 77, 79, 83 and 122 and
  at 72, 81 and 82. It is exact at every finite term to the site's positive meaning in the given's program and
  in the readers' installed program, carried there by the given's rooted contracts and the placement's meaning
  lemmas, none re-proved: the form a base's decision takes in the exactness of
  @{text Factor_Implemented_Base_Evaluation}. The granted entries have no counterpart: a demand that
  reaches one leaves its evaluation unavailable.
\<close>

section \<open>Each entry by its counterpart\<close>

definition given_entry_decision :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "given_entry_decision d t=(if d=72 then finite_definition_call_admission_decision t
    else if d=77 then finite_package_closure_admission_decision t
    else if d=79 then finite_root_family_reading_decision t
    else if d=80 then finite_package_admission_decision t
    else if d=81 then finite_definition_clause_reading_decision t
    else if d=82 then finite_definition_edge_reading_decision t
    else if d=83 then finite_package_membership_decision t
    else if d=113 then finite_environment_inclusion_decision t
    else if d=122 then finite_package_retention_admission_decision t
    else if d=392 then finite_use_additions t
    else if d=393 then finite_use_absence t
    else d=505 \<and> finite_payload_audit t)"

theorem given_entry_decision_rooted:
  assumes entry: "d |\<in>| given_guard_entries"
  shows "given_entry_decision d t \<longleftrightarrow> (d,decode_finite_term t)\<in>positive_meaning given_rooted_readers_system"
proof -
  have site: "d=72 \<or> d=77 \<or> d=79 \<or> d=80 \<or> d=81 \<or> d=82 \<or> d=83 \<or> d=113 \<or> d=122 \<or> d=392 \<or> d=393 \<or> d=505"
    using entry by (simp add: given_guard_entries_def)
  have additions: "(392,decode_finite_term t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow>
      (392,decode_finite_term t)\<in>positive_meaning use_additions_system"
    "(393,decode_finite_term t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow>
      (393,decode_finite_term t)\<in>positive_meaning use_additions_system"
    by (simp_all only: given_rooted_guard_meaning[OF given_guard_members(10)]
      given_rooted_guard_meaning[OF given_guard_members(11)]
      guard_readers_left[OF given_entry_members(10)] guard_readers_left[OF given_entry_members(11)])
  show ?thesis using site
    by (elim disjE) (simp_all add: given_entry_decision_def additions
      finite_definition_call_admission_decision_exact given_rooted_definition_call_admission_exact
      finite_package_closure_admission_decision_exact given_rooted_package_closure_admission_exact
      finite_root_family_reading_decision_exact given_rooted_root_family_reading_exact
      finite_package_admission_decision_exact given_rooted_package_admission_exact
      finite_definition_clause_reading_decision_exact given_rooted_definition_clause_reading_exact
      finite_definition_edge_reading_decision_exact given_rooted_definition_edge_reading_exact
      finite_package_membership_decision_exact given_rooted_package_membership_exact
      finite_environment_inclusion_decision_exact given_rooted_environment_inclusion_exact
      finite_package_retention_admission_decision_exact given_rooted_package_retention_admission_exact
      finite_use_additions_exact finite_use_absence_exact
      finite_payload_audit_exact given_rooted_payload_audit_exact)
qed

lemma given_guard_rooted:
  assumes "d |\<in>| given_guard_entries"
  shows "d\<in>system_definitions given_rooted_readers_system"
  by (rule given_entry_rooted) (simp add: given_reader_entries_def assms)

section \<open>The given's base\<close>

text \<open>
  The base is keyed by the installed sites of the guard's entries; the table pairs each site with its entry,
  and a call is decided by the counterpart of an entry placed at the call's site. Two entries placed at one
  site would both be exact there, so the decision needs no injectivity of the placement.
\<close>

definition given_base_sites :: "local_address option definition_site fset" where
  "given_base_sites=fimage given_readers_placement given_guard_entries"

definition given_base_table :: "(local_address option definition_site\<times>nat) list" where
  "given_base_table=map (\<lambda>d. (given_readers_placement d,d)) (sorted_list_of_fset given_guard_entries)"

definition given_base_decision :: "local_address option definition_site\<times>finite_factor_term \<Rightarrow> bool" where
  "given_base_decision q=list_ex (\<lambda>(s,d). s=fst q \<and> given_entry_decision d (snd q)) given_base_table"

lemma given_base_table_member:
  "(s,d)\<in>set given_base_table \<longleftrightarrow> d |\<in>| given_guard_entries \<and> s=given_readers_placement d"
  by (auto simp: given_base_table_def sorted_list_of_fset.rep_eq)

theorem given_base_decision_at:
  assumes meaning: "\<And>d t. d\<in>system_definitions given_rooted_readers_system \<Longrightarrow>
      (given_readers_placement d,t)\<in>positive_meaning P \<longleftrightarrow> (d,t)\<in>positive_meaning given_rooted_readers_system"
    and base: "fst q |\<in>| given_base_sites"
  shows "given_base_decision q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning P"
proof -
  obtain s t where q: "q=(s,t)" by (cases q)
  have entry: "given_entry_decision d t \<longleftrightarrow> (given_readers_placement d,decode_finite_term t)\<in>positive_meaning P"
    if "d |\<in>| given_guard_entries" for d
    by (simp only: given_entry_decision_rooted[OF that] meaning[OF given_guard_rooted[OF that]])
  obtain d where d: "d |\<in>| given_guard_entries" and s: "s=given_readers_placement d"
    using base by (auto simp: q given_base_sites_def)
  have "given_base_decision q \<longleftrightarrow> (\<exists>s' e. (s',e)\<in>set given_base_table \<and> s'=s \<and> given_entry_decision e t)"
    by (auto simp: q given_base_decision_def list_ex_iff)
  also have "\<dots> \<longleftrightarrow>
      (\<exists>e. e |\<in>| given_guard_entries \<and> given_readers_placement e=s \<and> given_entry_decision e t)"
    by (simp only: given_base_table_member) blast
  also have "\<dots> \<longleftrightarrow> (s,decode_finite_term t)\<in>positive_meaning P"
  proof
    assume "\<exists>e. e |\<in>| given_guard_entries \<and> given_readers_placement e=s \<and> given_entry_decision e t"
    then obtain e where "e |\<in>| given_guard_entries" "given_readers_placement e=s" "given_entry_decision e t"
      by blast
    then show "(s,decode_finite_term t)\<in>positive_meaning P" using entry by blast
  next
    assume "(s,decode_finite_term t)\<in>positive_meaning P"
    then show "\<exists>e. e |\<in>| given_guard_entries \<and> given_readers_placement e=s \<and> given_entry_decision e t"
      using d s entry[OF d] by blast
  qed
  finally show ?thesis by (simp add: q)
qed

theorem given_base_decision_exact:
  assumes "fst q |\<in>| given_base_sites"
  shows "given_base_decision q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning given_program"
  by (rule given_base_decision_at[OF given_readers_meaning assms])

theorem given_base_decision_installed:
  assumes "fst q |\<in>| given_base_sites"
  shows "given_base_decision q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning given_readers_program"
  by (rule given_base_decision_at[OF given_installed_meaning assms])

end
