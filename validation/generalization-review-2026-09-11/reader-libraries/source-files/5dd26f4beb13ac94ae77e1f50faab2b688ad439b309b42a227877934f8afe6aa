theory Factor_Reference_Environments
  imports Factor_Reference_Tables RRA_Literal_Extension
begin

section \<open>Realizing literal and callee requirements in the actual environment\<close>

definition callee_binding_table ::
  "(local_address \<times> 'u definition_site) set \<Rightarrow> (local_address \<times> 'u) set" where
  "callee_binding_table C = (\<lambda>(k,d). (k,fst d)) ` C"

lemma callee_binding_domain:
  "rel_dom (callee_binding_table C) = rel_dom C"
  by (simp add: callee_binding_table_def pair_image_domain)

lemma callee_binding_member:
  assumes "(k,d) \<in> C"
  shows "(k,fst d) \<in> callee_binding_table C"
  using imageI[OF assms, of "\<lambda>(k,d). (k,fst d)"] by (simp add: callee_binding_table_def)

lemma callee_binding_finite:
  assumes "finite C"
  shows "finite (callee_binding_table C)"
  using assms by (simp add: callee_binding_table_def)

lemma callee_binding_functional:
  assumes "single_valued C"
  shows "single_valued (callee_binding_table C)"
proof -
  have injective: "inj_on id (rel_dom C)" by simp
  show ?thesis using single_valued_pair_image[OF assms injective, where g=fst]
    by (simp add: callee_binding_table_def)
qed

definition install_reference_tables ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> exact_artifact \<Rightarrow>
    (local_address \<times> exact_artifact) set \<Rightarrow>
    (local_address \<times> local_address option definition_site) set \<Rightarrow>
    local_address option artifact_environment" where
  "install_reference_tables E u R L C =
    add_source_bindings (graft_environment E u (literal_environment R L)) u (callee_binding_table C)"

locale reference_extension =
  fixes E :: "local_address option artifact_environment" and u :: "local_address option" and R :: exact_artifact
    and L :: "(local_address \<times> exact_artifact) set"
    and C :: "(local_address \<times> local_address option definition_site) set"
  assumes old_formed: "environment_formed E" and old_source: "artifact_at E u R"
    and table: "reference_table_formed L C"
    and slots_inside: "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    and callees: "\<forall>k d. (k,d) \<in> C \<longrightarrow> (\<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d))"
    and slots_unbound: "\<And>k v. k \<in> rel_dom L \<union> rel_dom C \<Longrightarrow> \<not> binds_slot E u k v"
begin

abbreviation installed where "installed \<equiv> install_reference_tables E u R L C"
abbreviation literal_environment_added where "literal_environment_added \<equiv> graft_environment E u (literal_environment R L)"

lemma literal_slots_inside: "rel_dom L \<subseteq> rra_carrier (object_structure R)"
  using slots_inside by blast

lemma literal_slots_unbound:
  assumes "k \<in> rel_dom L"
  shows "\<not> binds_slot E u k v"
  by (rule slots_unbound) (use assms in blast)

sublocale literals: literal_extension E u R L
  by (rule literal_extension.intro[OF old_formed old_source
        reference_table_properties(1,3,6)[OF table] literal_slots_inside literal_slots_unbound])

lemma callee_targets_present: "rel_ran (callee_binding_table C) \<subseteq> environment_uses E"
proof
  fix v assume member: "v \<in> rel_ran (callee_binding_table C)"
  obtain k d where entry: "(k,d) \<in> C" "v=fst d"
    using member by (auto simp: callee_binding_table_def rel_ran_def)
  obtain T where target: "artifact_at E (fst d) T" using callees entry(1) by blast
  show "v \<in> environment_uses E" using target entry(2)
    by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
qed

lemma callee_slots_unbound:
  assumes key: "k \<in> rel_dom (callee_binding_table C)"
  shows "\<not> binds_slot literal_environment_added u k v"
proof -
  have in_callees: "k \<in> rel_dom C" using key by (simp add: callee_binding_domain)
  have outside: "k \<notin> rel_dom L" using reference_table_properties(5)[OF table] in_callees by blast
  have old: "\<not> binds_slot E u k v" by (rule slots_unbound) (use in_callees in blast)
  show ?thesis using literals.other_bindings[of u k v] outside old by simp
qed

theorem formed: "environment_formed installed"
proof -
  have fin: "finite (callee_binding_table C)"
    by (rule callee_binding_finite[OF reference_table_properties(2)[OF table]])
  have sv: "single_valued (callee_binding_table C)"
    by (rule callee_binding_functional[OF reference_table_properties(4)[OF table]])
  have slots: "rel_dom (callee_binding_table C) \<subseteq> rra_carrier (object_structure R)"
    using slots_inside by (auto simp: callee_binding_domain)
  have targets: "rel_ran (callee_binding_table C) \<subseteq> environment_uses literal_environment_added"
    by (rule subset_trans[OF callee_targets_present included_uses[OF literals.included]])
  show ?thesis unfolding install_reference_tables_def
    by (rule add_source_bindings_formed[OF literals.formed literals.source fin sv slots targets callee_slots_unbound])
qed

lemma included: "environment_included E installed"
  unfolding install_reference_tables_def
  by (rule environment_included_trans[OF literals.included add_source_included])

lemma source: "artifact_at installed u R"
  by (rule included_artifact[OF included old_source])

lemma literal_recovered:
  assumes entry: "(k,T) \<in> L"
  shows "external_slot_values installed u k = {T}"
proof -
  have key: "k \<in> rel_dom L" by (rule rel_domI[OF entry])
  have outside: "k \<notin> rel_dom (callee_binding_table C)"
    using reference_table_properties(5)[OF table] key by (auto simp: callee_binding_domain)
  have same: "external_slot_values installed u k = external_slot_values literal_environment_added u k"
    unfolding install_reference_tables_def by (rule add_source_literal_values_elsewhere) (use outside in simp)
  show ?thesis using same literals.literal_singleton[OF entry] by simp
qed

lemma callee_recovered:
  assumes entry: "(k,d) \<in> C"
  shows "binds_slot installed u k (fst d) \<and>
    (\<exists>T. artifact_at installed (fst d) T \<and> anchor_formed (T,snd d))"
proof -
  have binding: "binds_slot installed u k (fst d)"
    using callee_binding_member[OF entry] by (simp add: install_reference_tables_def)
  obtain T where original: "artifact_at E (fst d) T" "anchor_formed (T,snd d)"
    using callees entry by blast
  have target: "artifact_at installed (fst d) T" by (rule included_artifact[OF included original(1)])
  show ?thesis using binding target original(2) by blast
qed

theorem references: "syntax_references installed u L C"
  using literal_recovered callee_recovered unfolding syntax_references_def by blast

lemma old_artifacts:
  assumes "v \<in> environment_uses E"
  shows "artifact_at installed v T \<longleftrightarrow> artifact_at E v T"
  by (simp only: install_reference_tables_def add_source_artifact literals.old_artifacts[OF assms])

lemma other_bindings:
  assumes separate: "v \<noteq> u \<or> k \<notin> rel_dom L \<union> rel_dom C"
  shows "binds_slot installed v k w \<longleftrightarrow> binds_slot E v k w"
proof -
  have no_callee: "v \<noteq> u \<or> k \<notin> rel_dom (callee_binding_table C)"
    using separate by (auto simp: callee_binding_domain)
  have no_literal: "v \<noteq> u \<or> k \<notin> rel_dom L" using separate by blast
  show ?thesis
    by (simp only: install_reference_tables_def add_source_bindings_elsewhere[OF no_callee]
        literals.other_bindings[OF no_literal])
qed

end

lemma external_slot_values_included:
  assumes ff: "environment_formed F" and included: "environment_included E F"
    and present: "R \<in> external_slot_values E u k"
  shows "external_slot_values F u k = external_slot_values E u k"
proof -
  obtain v where original: "binds_slot E u k v" "artifact_at E v R"
    using present by (auto simp: external_slot_values_def)
  have binding: "binds_slot F u k v" by (rule included_binding[OF included original(1)])
  have artifact: "artifact_at F v R" by (rule included_artifact[OF included original(2)])
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix T assume "T \<in> external_slot_values F u k"
    then obtain w where target: "binds_slot F u k w" "artifact_at F w T"
      by (auto simp: external_slot_values_def)
    have use: "w=v" by (rule environment_binding_unique[OF ff target(1) binding])
    have other: "artifact_at F v T" using target(2) use by simp
    have same: "T=R" by (rule environment_artifact_unique[OF ff other artifact])
    show "T \<in> external_slot_values E u k" using present same by simp
  next
    fix T assume "T \<in> external_slot_values E u k"
    then obtain w where old: "binds_slot E u k w" "artifact_at E w T"
      by (auto simp: external_slot_values_def)
    show "T \<in> external_slot_values F u k"
      using included_binding[OF included old(1)] included_artifact[OF included old(2)]
      by (auto simp: external_slot_values_def)
  qed
qed

lemma syntax_references_included:
  assumes ff: "environment_formed F" and included: "environment_included E F"
    and refs: "syntax_references E u L C"
  shows "syntax_references F u L C"
proof -
  have literals: "\<forall>k R. (k,R) \<in> L \<longrightarrow> external_slot_values F u k = {R}"
  proof (intro allI impI)
    fix k R assume entry: "(k,R) \<in> L"
    have old: "external_slot_values E u k = {R}" using refs entry by (auto simp: syntax_references_def)
    have present: "R \<in> external_slot_values E u k" using old by simp
    show "external_slot_values F u k = {R}" using external_slot_values_included[OF ff included present] old by simp
  qed
  have callees: "\<forall>k d. (k,d) \<in> C \<longrightarrow> binds_slot F u k (fst d) \<and>
    (\<exists>R. artifact_at F (fst d) R \<and> anchor_formed (R,snd d))"
  proof (intro allI impI)
    fix k d assume entry: "(k,d) \<in> C"
    obtain R where old: "binds_slot E u k (fst d)" "artifact_at E (fst d) R" "anchor_formed (R,snd d)"
      using refs entry unfolding syntax_references_def by blast
    show "binds_slot F u k (fst d) \<and> (\<exists>R. artifact_at F (fst d) R \<and> anchor_formed (R,snd d))"
      using included_binding[OF included old(1)] included_artifact[OF included old(2)] old(3) by blast
  qed
  show ?thesis using literals callees by (simp add: syntax_references_def)
qed

section \<open>Adding a fresh source with all of its exact reference requirements\<close>

theorem reference_environment_total:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and rf: "exact_formed R"
    and profile: "reference_table_formed L C"
    and bounds: "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    and callees: "\<forall>d\<in>rel_ran C. \<exists>T. artifact_at E (fst d) T \<and> anchor_formed (T,snd d)"
  shows "\<exists>F u. environment_formed F \<and> environment_included E F \<and> u \<notin> environment_uses E \<and>
    artifact_at F u R \<and> syntax_references F u L C \<and>
    (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  let ?u = "clone_source_use E None"
  let ?A = "add_artifact_use E ?u R"
  let ?F = "install_reference_tables ?A ?u R L C"
  have fresh: "?u \<notin> environment_uses E" by (rule clone_source_use_fresh[OF ef])
  have af: "environment_formed ?A" by (rule added_artifact_formed[OF ef rf fresh])
  have source: "artifact_at ?A ?u R" by simp
  have inclusion: "environment_included E ?A" by (rule added_artifact_included)
  have unbound: "\<And>k v. \<not> binds_slot ?A ?u k v"
  proof -
    fix k v show "\<not> binds_slot ?A ?u k v"
    proof
      assume binding: "binds_slot ?A ?u k v"
      have old: "binds_slot E ?u k v" using binding by simp
      obtain T where art: "artifact_at E ?u T" using ef old unfolding environment_formed_def by blast
      have member: "?u \<in> environment_uses E" using art by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
      show False using member fresh by blast
    qed
  qed
  have targets: "\<forall>k d. (k,d) \<in> C \<longrightarrow> (\<exists>T. artifact_at ?A (fst d) T \<and> anchor_formed (T,snd d))"
  proof (intro allI impI)
    fix k d assume entry: "(k,d) \<in> C"
    have member: "d \<in> rel_ran C" by (rule rel_ranI[OF entry])
    obtain T where old: "artifact_at E (fst d) T" "anchor_formed (T,snd d)" using callees member by blast
    have added: "artifact_at ?A (fst d) T" by (rule included_artifact[OF inclusion old(1)])
    show "\<exists>T. artifact_at ?A (fst d) T \<and> anchor_formed (T,snd d)" using added old(2) by blast
  qed
  interpret extension: reference_extension ?A ?u R L C
    by (rule reference_extension.intro[OF af source profile bounds targets]) (rule unbound)
  have included: "environment_included E ?F"
    by (rule environment_included_trans[OF inclusion extension.included])
  have old_artifacts: "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
  proof (intro ballI allI)
    fix v T assume member: "v \<in> environment_uses E"
    have inside: "v \<in> environment_uses ?A" using member by simp
    have apart: "v \<noteq> ?u" using member fresh by blast
    show "artifact_at ?F v T \<longleftrightarrow> artifact_at E v T"
      by (simp only: extension.old_artifacts[OF inside] added_artifact_at) (use apart in auto)
  qed
  have old_bindings: "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w"
  proof (intro ballI allI)
    fix v k w assume member: "v \<in> environment_uses E"
    have apart: "v \<noteq> ?u" using member fresh by blast
    have separate: "v \<noteq> ?u \<or> k \<notin> rel_dom L \<union> rel_dom C" using apart by blast
    show "binds_slot ?F v k w \<longleftrightarrow> binds_slot E v k w"
      by (simp only: extension.other_bindings[OF separate] added_artifact_bindings)
  qed
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ ?u])
    (use extension.formed included fresh extension.source extension.references old_artifacts old_bindings in blast)
qed

text \<open>
  This constructor supplies the actual reference predicate used by native
  syntax recovery. It allocates fresh literal uses and installs callee bindings
  to existing exact anchors, including self references. Formation and all
  reference values are proved. Existing artifacts and bindings outside the new
  source slots are unchanged; all earlier bindings are retained.
\<close>

end
