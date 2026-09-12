theory Factor_Judgment_Dependency_Contracts
  imports Factor_Judgment_Retention_Admission
begin

section \<open>Each dependency notion owns its native relation contract\<close>

theorem judgment_demanded_slot_presented:
  "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    presented_relation judgment_source_presents site_coordinate_presents (\<lambda>z a. a\<in>judgment_required_slots z) p q"
  by (simp only: judgment_demanded_slot_exact presented_relation_def factor_term.inject) blast

interpretation judgment_demanded_slot_contract: presented_relation_contract
  judgment_source_presents judgment_source_readable "\<lambda>p. (178,p)\<in>positive_meaning judgment_retention_system"
  site_coordinate_presents "\<lambda>_. True" "\<lambda>q. \<exists>a. site_coordinate_presents a q"
  "\<lambda>z a. a\<in>judgment_required_slots z"
  "\<lambda>p q. (179,Pair_Term p q)\<in>positive_meaning judgment_retention_system"
  using judgment_source_native_class site_coordinate_presentation judgment_demanded_slot_presented
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def; blast)

corollary judgment_demanded_slot_query:
  assumes source: "judgment_source_presents z p"
  shows "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>a. q=definition_site_value a \<and> a\<in>judgment_required_slots z)"
  using judgment_demanded_slot_contract.at_source[OF source, of q] by simp

theorem judgment_required_use_presented:
  "(180,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    presented_relation judgment_source_presents (\<lambda>u t. t=use_data_term u) (\<lambda>z u. u\<in>judgment_required_uses z) p q"
  by (simp only: judgment_required_use_exact presented_relation_def factor_term.inject) blast

interpretation judgment_required_use_contract: presented_relation_contract
  judgment_source_presents judgment_source_readable "\<lambda>p. (178,p)\<in>positive_meaning judgment_retention_system"
  "\<lambda>u t. t=use_data_term u" "\<lambda>_. True" "\<lambda>q. \<exists>u. q=use_data_term u"
  "\<lambda>z u. u\<in>judgment_required_uses z"
  "\<lambda>p q. (180,Pair_Term p q)\<in>positive_meaning judgment_retention_system"
  using judgment_source_native_class use_coordinate_presentation judgment_required_use_presented
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def; blast)

corollary judgment_required_use_query:
  assumes source: "judgment_source_presents z p"
  shows "(180,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>u. q=use_data_term u \<and> u\<in>judgment_required_uses z)"
  by (rule judgment_required_use_contract.at_source[OF source])

theorem judgment_dependency_source_boundary:
  assumes entry: "d\<in>{179,180}" and holds: "(d,Pair_Term p q)\<in>positive_meaning judgment_retention_system"
  shows "(178,p)\<in>positive_meaning judgment_retention_system"
  using entry holds judgment_demanded_slot_contract.boundaries judgment_required_use_contract.boundaries by auto

theorem judgment_native_demand_has_binding:
  assumes source: "judgment_source_presents z p"
    and selected: "(179,Pair_Term p (site_data_term u k))\<in>positive_meaning judgment_retention_system"
  shows "\<exists>v. binds_slot (fst z) u k v"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have member: "(u,k)\<in>judgment_required_slots z"
    using selected by (simp only: judgment_demanded_slot_query[OF source])
      (auto simp: site_data_term_def inj_eq[OF use_data_term_injective])
  have domain: "(u,k)\<in>rel_dom (environment_bindings (judgment_required_environment z))"
    by (simp only: judgment_required_environment_domains(2)[OF readable]; rule member)
  obtain v where kept: "binds_slot (judgment_required_environment z) u k v"
    using domain by (auto simp: rel_dom_def binds_slot_def)
  have included: "environment_included (judgment_required_environment z) (fst z)"
    by (rule native_judgment_environment_included)
  show ?thesis using included_binding[OF included kept] by blast
qed

theorem judgment_native_required_use_exists:
  assumes source: "judgment_source_presents z p"
    and selected: "(180,Pair_Term p (use_data_term u))\<in>positive_meaning judgment_retention_system"
  shows "u\<in>environment_uses (fst z)"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have member: "u\<in>judgment_required_uses z"
    using selected by (simp only: judgment_required_use_query[OF source])
      (auto simp: inj_eq[OF use_data_term_injective])
  have kept: "u\<in>environment_uses (judgment_required_environment z)"
    by (simp only: judgment_required_environment_domains(1)[OF readable]; rule member)
  have included: "environment_included (judgment_required_environment z) (fst z)"
    by (rule native_judgment_environment_included)
  show ?thesis using included_uses[OF included] kept by blast
qed

section \<open>Least restriction preserves every dependency query\<close>

theorem judgment_dependency_queries_retained:
  assumes source: "judgment_source_presents z p"
    and retained: "judgment_source_presents (judgment_required_environment z,snd z) p'"
  shows "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (179,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    and "(180,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (180,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    and "(181,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (181,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    and "(182,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (182,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have boundary: "judgment_required_uses (judgment_required_environment z,snd z)=judgment_required_uses z"
    "judgment_required_slots (judgment_required_environment z,snd z)=judgment_required_slots z"
    using judgment_retained_context(3,4)[OF readable] by blast+
  show "(179,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (179,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_demanded_slot_query[OF source] judgment_demanded_slot_query[OF retained] boundary(2))
  show "(180,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (180,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_required_use_query[OF source] judgment_required_use_query[OF retained] boundary(1))
  have formed: "term_formed p" "term_formed p'"
    using judgment_source_presents_formed[OF source] judgment_source_presents_formed[OF retained] by blast+
  have use_list: "(181,Pair_Term c q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (\<exists>xs. q=data_list_term xs \<and> term_formed c \<and>
        (\<forall>x\<in>set xs. (180,Pair_Term c x)\<in>positive_meaning judgment_retention_system))" for c
    by (simp only: judgment_use_lists.exact factor_term.inject) blast
  have slot_list: "(182,Pair_Term c q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (\<exists>xs. q=data_list_term xs \<and> term_formed c \<and>
        (\<forall>x\<in>set xs. (179,Pair_Term c x)\<in>positive_meaning judgment_retention_system))" for c
    by (simp only: judgment_slot_lists.exact factor_term.inject) blast
  show "(181,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (181,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    by (simp only: use_list judgment_required_use_query[OF source]
      judgment_required_use_query[OF retained] boundary(1); use formed in blast)
  show "(182,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (182,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
    by (simp only: slot_list judgment_demanded_slot_query[OF source]
      judgment_demanded_slot_query[OF retained] boundary(2); use formed in blast)
qed

text \<open>
  The local contracts expose every permitted output and supply general
  presentation transport and composition. Every queried slot has an actual
  binding, and every queried use belongs to the supplied environment.
  Least restriction preserves all slot, use, and complete-list queries,
  including queries with malformed or unsupported output terms.
\<close>

end
