theory Factor_Dependency_Evidence_Examples
  imports Factor_Transition_Dependencies Factor_Transition_Account_Examples
begin

lemma constant_entry_site_permission_invariant:
  assumes every: "\<And>t. term_formed t \<Longrightarrow>
    schema_call_formed P d t \<and> ((d,t)\<in>positive_meaning P\<longleftrightarrow>b)"
  shows "site_permission_invariant P d"
  unfolding site_permission_invariant_def
proof (intro allI impI)
  fix N u r t v assume first: "site_value_presents N u r t" and second: "site_value_presents N u r v"
  have tf: "term_formed t" and vf: "term_formed v"
    using site_value_presents_formed[OF first] site_value_presents_formed[OF second] by auto
  show "(schema_call_formed P d t\<longleftrightarrow>schema_call_formed P d v) \<and>
    ((d,t)\<in>positive_meaning P\<longleftrightarrow>(d,v)\<in>positive_meaning P)"
    using every[OF tf] every[OF vf] by blast
qed

section \<open>A universal current entry supplies an irredundant complete proof family\<close>

theorem universal_current_dependency_evidence:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and subjects: "amendment_dependency_subjects C q H U"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
  shows "\<exists>Rs. amendment_dependency_evidence C q H C q Rs \<and> finite Rs \<and> Rs\<noteq>{} \<and>
    (\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{R}))"
proof -
  have invariant: "site_permission_invariant P d"
    by (rule constant_entry_site_permission_invariant[where b=True]) (use every in auto)
  have permitted: "\<And>x. x\<in>U \<Longrightarrow> factor_permits_site P d (fst x) (fst (snd x)) (snd (snd x))"
  proof -
    fix x assume member: "x\<in>U"
    obtain N e where shape: "x=(N,e)" by (cases x) auto
    have required: "(N,e)\<in>U" using member shape by simp
    have fields: "environment_formed N \<and> e\<in>environment_positions N"
      using amendment_dependency_subjects_boundary(3)[OF subjects, rule_format, OF required] by blast
    have formed: "environment_formed N" and site: "(fst e,snd e)\<in>environment_positions N"
      using fields by auto
    obtain t where present: "site_value_presents N (fst e) (snd e) t"
      using site_value_presents_total[OF formed site] by blast
    have tf: "term_formed t" using site_value_presents_formed[OF present] by blast
    have allowed: "factor_permits_site P d N (fst e) (snd e)"
      using invariant present every[OF tf] unfolding factor_permits_site_def by blast
    show "factor_permits_site P d (fst x) (fst (snd x)) (snd (snd x))" using allowed shape by simp
  qed
  have companion: "current_companion C q C q" by (rule current_companion_reflexive[OF current])
  obtain Rs where evidence: "amendment_dependency_evidence C q H C q Rs"
    and needed: "\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{R})"
    using amendment_dependency_evidence_total[OF subjects companion current permitted] by blast
  show ?thesis using evidence needed amendment_dependency_evidence_formed[OF evidence] by blast
qed

theorem fixed_current_dependency_policy_for_all_candidates:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and> site_permission_invariant P d \<and>
    (\<forall>H F qu qr Q. generation_program_scope H F qu qr Q \<longrightarrow>
      (\<exists>Rs. amendment_dependency_evidence C [] H C [] Rs \<and> finite Rs \<and> Rs\<noteq>{} \<and>
        (\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C [] H C [] (Rs-{R}))))"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu P where program:
    "closed_native_package_at E pu [] P"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have member: "g True\<in>system_definitions P" using program(2) by blast
  have every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P (g True) t \<and> (g True,t)\<in>positive_meaning P"
    using program(2)[rule_format, of True] by blast
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P (g True)"
    using current_entry_scope_construction[OF program(1) member authority locus] by blast
  have invariant: "site_permission_invariant P (g True)"
    by (rule constant_entry_site_permission_invariant[where b=True]) (use every in auto)
  have future: "\<forall>H F qu qr Q. generation_program_scope H F qu qr Q \<longrightarrow>
      (\<exists>Rs. amendment_dependency_evidence C [] H C [] Rs \<and> finite Rs \<and> Rs\<noteq>{} \<and>
        (\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C [] H C [] (Rs-{R})))"
  proof (intro allI impI)
    fix H F qu qr Q assume candidate: "generation_program_scope H F qu qr Q"
    obtain U where subjects: "amendment_dependency_subjects C [] H U"
      using amendment_dependency_subjects_total[OF current candidate] by blast
    show "\<exists>Rs. amendment_dependency_evidence C [] H C [] Rs \<and> finite Rs \<and> Rs\<noteq>{} \<and>
        (\<forall>R\<in>Rs. \<not>amendment_dependency_evidence C [] H C [] (Rs-{R}))"
      by (rule universal_current_dependency_evidence[OF current subjects every])
  qed
  show ?thesis using current invariant future by blast
qed

section \<open>Permission evidence does not make the permitted definition's calls true\<close>

theorem site_permission_does_not_prove_dependency_calls:
  assumes authority: "target_formed A" and locus: "target_formed l"
  shows "\<exists>C G p E pu P d e R.
    current_entry_scope_quoted_at C [] A l G p E pu [] P d \<and> e\<in>system_definitions P \<and>
    current_site_permission_certificate C [] R [] E (fst e) (snd e) \<and>
    (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P e t \<and> (e,t)\<notin>positive_meaning P)"
proof -
  obtain g :: "bool \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu P where program:
    "closed_native_package_at E pu [] P"
    "\<forall>b. g b\<in>system_definitions P \<and> amendment_permission_invariant P (g b) \<and>
      (\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g b) t \<and>
        ((g b,t)\<in>positive_meaning P\<longleftrightarrow>b))"
    using entry_choice_native_program by blast
  have member: "g True\<in>system_definitions P" "g False\<in>system_definitions P" using program(2) by blast+
  have every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P (g True) t \<and> (g True,t)\<in>positive_meaning P"
    and refusal: "\<forall>t. term_formed t \<longrightarrow> schema_call_formed P (g False) t \<and>
      (g False,t)\<notin>positive_meaning P"
    using program(2)[rule_format, of True] program(2)[rule_format, of False] by blast+
  obtain C G p where current: "current_entry_scope_quoted_at C [] A l G p E pu [] P (g True)"
    using current_entry_scope_construction[OF program(1) member(1) authority locus] by blast
  have package: "native_package_at E pu [] P" using program(1) by (simp add: closed_native_package_at_def)
  have ef: "environment_formed E" and inside: "g False\<in>environment_positions E"
    using native_package_definition_subjects[OF package] member(2) by blast+
  have site: "(fst (g False),snd (g False))\<in>environment_positions E" using inside by simp
  obtain t where present: "site_value_presents E (fst (g False)) (snd (g False)) t"
    using site_value_presents_total[OF ef site] by blast
  have tf: "term_formed t" using site_value_presents_formed[OF present] by blast
  have invariant: "site_permission_invariant P (g True)"
    by (rule constant_entry_site_permission_invariant[where b=True]) (use every in auto)
  have permitted: "factor_permits_site P (g True) E (fst (g False)) (snd (g False))"
    using invariant present every[OF tf] unfolding factor_permits_site_def by blast
  obtain R where proof_record: "current_site_permission_certificate C [] R [] E (fst (g False)) (snd (g False))"
    using current_site_permission_certificate_total[OF current permitted] by blast
  show ?thesis using current member(2) proof_record refusal by blast
qed

section \<open>Formed empty material fails an actual nonempty requirement\<close>

theorem empty_dependency_material_has_no_evidence:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and remainder: "environment_formed L" "(lu,lr)\<in>environment_positions L"
  shows "\<exists>U N. amendment_dependency_subjects C q H U \<and> U\<noteq>{} \<and>
    dependency_support_at N None [] C {} L lu lr \<and> \<not>amendment_dependency_evidence_at C q H N None []"
proof -
  obtain U where subjects: "amendment_dependency_subjects C q H U"
    using amendment_dependency_subjects_total[OF current candidate] by blast
  have nonempty: "U\<noteq>{}" by (rule amendment_dependency_subjects_boundary(2)[OF subjects])
  have cf: "exact_formed C" using current_entry_scope_formed[OF current] by blast
  have finite: "finite ({} :: exact_artifact set)" and each: "\<forall>R\<in>{}. exact_formed R" by simp_all
  obtain N where support: "dependency_support_at N None [] C {} L lu lr"
    using dependency_support_total[OF cf finite each remainder] by blast
  have invalid: "\<not>amendment_dependency_evidence_at C q H N None []"
    by (simp only: amendment_dependency_evidence_at_with_support[OF support]
      amendment_dependency_empty_evidence_rejected; blast)
  show ?thesis using subjects nonempty support invalid by blast
qed

section \<open>Dependency material is complete before continuation and acceptance are recorded\<close>

theorem universal_current_transition_dependencies_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and successor: "current_entry_scope_quoted_at X r A' m H z E' qu qr Q e"
    and before: "current_snapshot_at C q S" and after: "current_snapshot_at X r U"
    and trans: "transact S T (Applied U)" and history: "G\<in>fset (generation_predecessors H)"
    and assembly: "predecessor_assembly_certificate C q D a R b H xs B0 W Z"
    and invariant: "amendment_permission_invariant P d"
    and every: "\<And>t. term_formed t \<Longrightarrow> schema_call_formed P d t \<and> (d,t)\<in>positive_meaning P"
    and remainder: "environment_formed L" "(lu,lr)\<in>environment_positions L"
  shows "\<exists>Rs N M B K F au R' N' root.
    amendment_dependency_evidence C q H C q Rs \<and>
    (\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})) \<and>
    dependency_support_at N None [] C Rs L lu lr \<and>
    assembly_support_at M None [] D R N None [] \<and> successor_material_at B None [] X M None [] \<and>
    continuation_envelope C q K S T U B None [] \<and>
    current_transition_dependencies_at C q F au [] H K X \<and> certified_transition_dependencies C q R' [] H K X \<and>
    replay_scope_quoted_at R' [] N' pu pr au [] root {} \<and>
    native_package_environment F pu pr=E \<and> native_package_environment N' pu pr=E \<and>
    native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
proof -
  have candidate: "generation_program_scope H E' qu qr Q"
    using successor by (simp add: current_entry_scope_quoted_at_def current_program_scope_quoted_at_def)
  obtain V where subjects: "amendment_dependency_subjects C q H V"
    using amendment_dependency_subjects_total[OF current candidate] by blast
  obtain Rs where evidence: "amendment_dependency_evidence C q H C q Rs"
    and needed: "\<forall>Q\<in>Rs. \<not>amendment_dependency_evidence C q H C q (Rs-{Q})"
    using universal_current_dependency_evidence[OF current subjects every] by blast
  obtain N where dependency: "dependency_support_at N None [] C Rs L lu lr"
    and valid: "amendment_dependency_evidence_at C q H N None []"
    using amendment_dependency_material_total[OF evidence remainder] by blast
  have nf: "environment_formed N" and site: "(None,[])\<in>environment_positions N"
    using amendment_dependency_evidence_at_formed[OF valid] by auto
  obtain M B K F au R' N' root where actual:
    "assembly_support_at M None [] D R N None []" "successor_material_at B None [] X M None []"
    "continuation_envelope C q K S T U B None []"
    "current_transition_account_at C q F au [] H K X" "certified_transition_account C q R' [] H K X"
    "replay_scope_quoted_at R' [] N' pu pr au [] root {}"
    "native_package_environment F pu pr=E" "native_package_environment N' pu pr=E"
    "native_judgment_environment N' pu pr au []=native_judgment_environment F pu pr au []"
    using universal_current_account_total[
      OF current successor before after trans history assembly invariant every nf site] by blast
  have account: "transition_account_certificate C q K H X"
    and accepted: "current_accepts_at C q F au [] H (Whole_Artifact K)"
    using actual(4) by (auto simp: current_transition_account_at_def)
  have complete: "transition_dependency_certificate C q K H X"
    using account valid by (simp only: transition_dependency_with_material[OF actual(3,2,1)])
  have transition: "current_transition_dependencies_at C q F au [] H K X"
    using accepted complete by (simp add: current_transition_dependencies_at_def)
  have retained: "current_acceptance_certificate C q R' [] H (Whole_Artifact K)"
    using actual(5) by (simp add: certified_transition_account_def)
  have certified: "certified_transition_dependencies C q R' [] H K X"
    using retained complete by (simp add: certified_transition_dependencies_def)
  show ?thesis
    by (rule exI[of _ Rs], rule exI[of _ N], rule exI[of _ M], rule exI[of _ B], rule exI[of _ K],
        rule exI[of _ F], rule exI[of _ au], rule exI[of _ R'], rule exI[of _ N'], rule exI[of _ root])
       (use evidence needed dependency actual(1-3,6-9) transition certified in blast)
qed

text \<open>
  One actual finite native program is fixed before arbitrary future program
  candidates are supplied. Every required dependency has a complete closed
  proof under that program. The constructed collection is nonempty, and each
  of its records is needed for coverage. Formation of an empty collection
  cannot satisfy the same actual nonempty obligation. A native permission
  proof also coexists with refusal of every formed call at its permitted
  dependency, while all those calls retain formed interfaces.

  Given the separate actual candidate frame, assembly account, historical
  edge, and successful publication transaction, the dependency family and
  remaining material are constructed before the continuation envelope and
  acceptance record. The old program and complete minimal acceptance scope
  survive. Every remaining formed scope can be used in this conditional
  construction.

  The example policy permits every formed site argument. Its complete evidence
  therefore does not establish that it performs adequate dependency checking.
  Comparison, migration, cross-version interpretation, a concrete complete
  transition policy, and genesis adequacy remain independent obligations.
\<close>

end
