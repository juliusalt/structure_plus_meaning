theory Factor_Context_Admission
  imports Factor_Context_Clauses Factor_Judgment_Presentations Factor_Presentation_Transport
begin

abbreviation site_context_presents :: "site_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "site_context_presents z t \<equiv> site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t"

section \<open>Site admission is exactly occurrence membership in the actual use\<close>

lemma site_context_calls:
  "(156,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>e u r a. t=Pair_Term e (Pair_Term u r) \<and>
      (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
      (35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system)"
proof -
  have accepts: "schema_call_formed context_admission_system 156
      (evaluate_pattern h (schema_conclusion site_context_admission_schema))"
    if "\<forall>a\<in>schema_variables site_context_admission_schema. term_formed (h a)" for h
    using that by (auto simp: context_admission_call site_context_admission_schema_def schema_variables_def)
  have valuation: "(156,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
        t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
        (37,artifact_lookup_argument (h 0) (h 1) (h 3))\<in>positive_meaning artifact_lookup_system \<and>
        (35,Pair_Term (h 3) (Pair_Term (h 2) (Payload_Term [])))\<in>positive_meaning target_admission_system)"
    by (subst ordinary_single_clause_valuation[OF context_admission_clauses(1) _ accepts])
      (auto simp: site_context_admission_schema_def schema_variables_def context_admission_components)
  show ?thesis
  proof
    assume "(156,t)\<in>positive_meaning context_admission_system"
    then show "\<exists>e u r a. t=Pair_Term e (Pair_Term u r) \<and>
        (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
        (35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system"
      by (simp only: valuation) blast
  next
    assume "\<exists>e u r a. t=Pair_Term e (Pair_Term u r) \<and>
        (37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system \<and>
        (35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system"
    then obtain e u r a where parts: "t=Pair_Term e (Pair_Term u r)"
      "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
      "(35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system" by blast
    have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed a"
      using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
        schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by auto
    show "(156,t)\<in>positive_meaning context_admission_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else a"])
        (use parts formed in auto)
  qed
qed

lemma site_context_occurrence:
  assumes source: "artifact_value_presents R a"
  shows "(35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system
    \<longleftrightarrow> (\<exists>s. r=Payload_Term s \<and> s\<in>rra_carrier (object_structure R))"
proof -
  have optional: "Pair_Term r (Payload_Term [])=optional_payload_term s \<longleftrightarrow>
      (\<exists>a. s=Some a \<and> r=Payload_Term a)" for s
    by (cases s) auto
  show ?thesis by (simp only: target_admission_at_source[OF source] optional) auto
qed

theorem site_context_exact:
  "(156,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>E u r. site_value_presents E u r t)"
proof
  assume "(156,t)\<in>positive_meaning context_admission_system"
  then obtain e u r a where shape: "t=Pair_Term e (Pair_Term u r)"
    and lookup: "(37,artifact_lookup_argument e u a)\<in>positive_meaning artifact_lookup_system"
    and target: "(35,Pair_Term a (Pair_Term r (Payload_Term [])))\<in>positive_meaning target_admission_system"
    by (simp only: site_context_calls) blast
  obtain E v R where fields: "environment_value_presents E e" "u=use_data_term v"
    "artifact_at E v R" "artifact_value_presents R a"
    using lookup by (auto simp: artifact_lookup_exact)
  obtain s where root: "r=Payload_Term s" "s\<in>rra_carrier (object_structure R)"
    using target by (simp only: site_context_occurrence[OF fields(4)]) blast
  have site: "(v,s)\<in>environment_positions E" using fields(3) root(2) by auto
  show "\<exists>E u r. site_value_presents E u r t"
    by (rule exI[of _ E], rule exI[of _ v], rule exI[of _ s])
      (use shape fields(1,2) root(1) site in \<open>auto simp: site_value_presents_def site_data_term_def\<close>)
next
  assume "\<exists>E u r. site_value_presents E u r t"
  then obtain E u r where presented: "site_value_presents E u r t" by blast
  have site: "(u,r)\<in>environment_positions E" using presented
    by (simp only: site_value_presents_def; blast)
  obtain e where source: "environment_value_presents E e" and shape: "t=Pair_Term e (site_data_term u r)"
    using presented by (simp only: site_value_presents_def) blast
  obtain R where actual: "artifact_at E u R" and root: "r\<in>rra_carrier (object_structure R)"
    using site by auto
  have formed: "exact_formed R"
    using environment_value_presents_formed[OF source] actual by (auto simp: environment_formed_def)
  obtain a where material: "artifact_value_presents R a" using artifact_value_presents_total[OF formed] by blast
  have lookup: "(37,artifact_lookup_argument e (use_data_term u) a)\<in>positive_meaning artifact_lookup_system"
    using source actual material by (auto simp: artifact_lookup_exact)
  have target: "(35,Pair_Term a (Pair_Term (Payload_Term r) (Payload_Term [])))\<in>positive_meaning target_admission_system"
    using root by (simp only: site_context_occurrence[OF material]) blast
  show "(156,t)\<in>positive_meaning context_admission_system"
    by (simp only: site_context_calls; rule exI[of _ e], rule exI[of _ "use_data_term u"],
      rule exI[of _ "Payload_Term r"], rule exI[of _ a])
      (use shape lookup target in \<open>simp add: site_data_term_def\<close>)
qed

section \<open>Both sites belong to one complete judgment environment\<close>

lemma judgment_context_calls:
  "(157,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>e p a. t=Pair_Term e (Pair_Term p a) \<and>
      (156,Pair_Term e p)\<in>positive_meaning context_admission_system \<and>
      (156,Pair_Term e a)\<in>positive_meaning context_admission_system)"
proof -
  have accepts: "schema_call_formed context_admission_system 157
      (evaluate_pattern h (schema_conclusion judgment_context_admission_schema))"
    if "\<forall>a\<in>schema_variables judgment_context_admission_schema. term_formed (h a)" for h
    using that by (auto simp: context_admission_call judgment_context_admission_schema_def schema_variables_def)
  have valuation: "(157,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
        t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
        (156,Pair_Term (h 0) (h 1))\<in>positive_meaning context_admission_system \<and>
        (156,Pair_Term (h 0) (h 2))\<in>positive_meaning context_admission_system)"
    by (subst ordinary_single_clause_valuation[OF context_admission_clauses(2) _ accepts])
      (auto simp: judgment_context_admission_schema_def schema_variables_def)
  have formed: "term_formed e \<and> term_formed p \<and> term_formed a"
    if "(156,Pair_Term e p)\<in>positive_meaning context_admission_system"
      "(156,Pair_Term e a)\<in>positive_meaning context_admission_system" for e p a
    using schema_call_formed_target[OF positive_meaning_formed[OF that(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF that(2)]] by auto
  show ?thesis
  proof (simp only: valuation, rule iffI)
    assume "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
        t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
        (156,Pair_Term (h 0) (h 1))\<in>positive_meaning context_admission_system \<and>
        (156,Pair_Term (h 0) (h 2))\<in>positive_meaning context_admission_system"
    then show "\<exists>e p a. t=Pair_Term e (Pair_Term p a) \<and>
        (156,Pair_Term e p)\<in>positive_meaning context_admission_system \<and>
        (156,Pair_Term e a)\<in>positive_meaning context_admission_system" by blast
  next
    assume "\<exists>e p a. t=Pair_Term e (Pair_Term p a) \<and>
        (156,Pair_Term e p)\<in>positive_meaning context_admission_system \<and>
        (156,Pair_Term e a)\<in>positive_meaning context_admission_system"
    then obtain e p a where parts: "t=Pair_Term e (Pair_Term p a)"
      "(156,Pair_Term e p)\<in>positive_meaning context_admission_system"
      "(156,Pair_Term e a)\<in>positive_meaning context_admission_system" by blast
    show "\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
        t=Pair_Term (h 0) (Pair_Term (h 1) (h 2)) \<and>
        (156,Pair_Term (h 0) (h 1))\<in>positive_meaning context_admission_system \<and>
        (156,Pair_Term (h 0) (h 2))\<in>positive_meaning context_admission_system"
      by (rule exI[of _ "\<lambda>i::nat. if i=0 then e else if i=1 then p else a"])
        (use parts formed[OF parts(2,3)] in auto)
  qed
qed

theorem judgment_context_exact:
  "(157,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>j. judgment_context_presents j t)"
proof -
  have same: "F=E" if "environment_value_presents E e" "environment_value_presents F e" for E F e
    by (rule environment_value_presents_unique[OF that(2,1)])
  show ?thesis
    by (simp only: judgment_context_calls site_context_exact)
      (auto simp: site_value_presents_def judgment_value_presents_def; metis same fst_conv snd_conv)
qed

section \<open>The context classes own their canonical correspondence\<close>

lemma context_identity_calls:
  assumes entry: "(d=158 \<and> admission=156) \<or> (d=159 \<and> admission=157)"
  shows "(d,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>e f s. t=Pair_Term (Pair_Term e s) (Pair_Term f s) \<and>
      (admission,Pair_Term e s)\<in>positive_meaning context_admission_system \<and>
      (27,Pair_Term e f)\<in>positive_meaning environment_identity_system)"
proof -
  have family: "((d,c),S)\<in>system_clauses context_admission_system \<longleftrightarrow>
      c=0 \<and> S=context_identity_schema admission" for c S
    using entry by auto
  have accepts: "schema_call_formed context_admission_system d
      (evaluate_pattern h (schema_conclusion (context_identity_schema admission)))"
    if "\<forall>a\<in>schema_variables (context_identity_schema admission). term_formed (h a)" for h
    using that entry by (auto simp: context_admission_call context_identity_schema_def schema_variables_def)
  have valuation: "(d,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
        t=Pair_Term (Pair_Term (h 0) (h 2)) (Pair_Term (h 1) (h 2)) \<and>
        (admission,Pair_Term (h 0) (h 2))\<in>positive_meaning context_admission_system \<and>
        (27,Pair_Term (h 0) (h 1))\<in>positive_meaning environment_identity_system)"
    by (subst ordinary_single_clause_valuation[OF family _ accepts])
      (auto simp: context_identity_schema_def schema_variables_def context_admission_components)
  have formed: "term_formed e \<and> term_formed f \<and> term_formed s"
    if "(admission,Pair_Term e s)\<in>positive_meaning context_admission_system"
      "(27,Pair_Term e f)\<in>positive_meaning environment_identity_system" for e f s
    using schema_call_formed_target[OF positive_meaning_formed[OF that(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF that(2)]] by auto
  show ?thesis
  proof
    assume "(d,t)\<in>positive_meaning context_admission_system"
    then show "\<exists>e f s. t=Pair_Term (Pair_Term e s) (Pair_Term f s) \<and>
        (admission,Pair_Term e s)\<in>positive_meaning context_admission_system \<and>
        (27,Pair_Term e f)\<in>positive_meaning environment_identity_system"
      by (simp only: valuation) blast
  next
    assume "\<exists>e f s. t=Pair_Term (Pair_Term e s) (Pair_Term f s) \<and>
        (admission,Pair_Term e s)\<in>positive_meaning context_admission_system \<and>
        (27,Pair_Term e f)\<in>positive_meaning environment_identity_system"
    then obtain e f s where parts: "t=Pair_Term (Pair_Term e s) (Pair_Term f s)"
      "(admission,Pair_Term e s)\<in>positive_meaning context_admission_system"
      "(27,Pair_Term e f)\<in>positive_meaning environment_identity_system" by blast
    show "(d,t)\<in>positive_meaning context_admission_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then e else if i=1 then f else s"])
        (use parts formed[OF parts(2,3)] in auto)
  qed
qed

theorem site_context_identity_exact:
  "(158,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> presentation_transport site_context_presents site_context_presents p q)"
  by (simp only: context_identity_calls[of 158 156, simplified] site_context_exact environment_identity_exact)
    (auto simp: site_value_presents_def presentation_transport_def;
      metis environment_value_presents_unique fst_conv snd_conv)

theorem judgment_context_identity_exact:
  "(159,t)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> presentation_transport judgment_context_presents judgment_context_presents p q)"
  by (simp only: context_identity_calls[of 159 157, simplified] judgment_context_exact environment_identity_exact)
    (auto simp: judgment_value_presents_def presentation_transport_def;
      metis environment_value_presents_unique fst_conv snd_conv)

theorem site_context_native_class:
  "presentation_class site_context_presents site_context_formed
    (\<lambda>t. (156,t)\<in>positive_meaning context_admission_system)"
  using site_presentations.presentation_class_axioms by (simp only: site_context_exact)

theorem judgment_context_native_class:
  "presentation_class judgment_context_presents judgment_context_formed
    (\<lambda>t. (157,t)\<in>positive_meaning context_admission_system)"
  using judgment_context_presentation_class by (simp only: judgment_context_exact)

theorem site_context_identity_transport:
  "(158,Pair_Term p q)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    presentation_transport site_context_presents site_context_presents p q"
  by (auto simp: site_context_identity_exact)

theorem judgment_context_identity_transport:
  "(159,Pair_Term p q)\<in>positive_meaning context_admission_system \<longleftrightarrow>
    presentation_transport judgment_context_presents judgment_context_presents p q"
  by (auto simp: judgment_context_identity_exact)

interpretation site_context_identity: presented_function_contract
  site_context_presents site_context_formed "\<lambda>t. (156,t)\<in>positive_meaning context_admission_system"
  site_context_presents site_context_formed "\<lambda>t. (156,t)\<in>positive_meaning context_admission_system"
  id "\<lambda>p q. (158,Pair_Term p q)\<in>positive_meaning context_admission_system"
proof -
  have operation: "(\<lambda>p q. (158,Pair_Term p q)\<in>positive_meaning context_admission_system)=
      presentation_transport site_context_presents site_context_presents"
    by (intro ext; rule site_context_identity_transport)
  show "presented_function_contract site_context_presents site_context_formed
      (\<lambda>t. (156,t)\<in>positive_meaning context_admission_system) site_context_presents site_context_formed
      (\<lambda>t. (156,t)\<in>positive_meaning context_admission_system) id
      (\<lambda>p q. (158,Pair_Term p q)\<in>positive_meaning context_admission_system)"
    by (simp only: operation; rule presentation_identity_function[OF site_context_native_class site_context_native_class])
qed

interpretation judgment_context_identity: presented_function_contract
  judgment_context_presents judgment_context_formed "\<lambda>t. (157,t)\<in>positive_meaning context_admission_system"
  judgment_context_presents judgment_context_formed "\<lambda>t. (157,t)\<in>positive_meaning context_admission_system"
  id "\<lambda>p q. (159,Pair_Term p q)\<in>positive_meaning context_admission_system"
proof -
  have operation: "(\<lambda>p q. (159,Pair_Term p q)\<in>positive_meaning context_admission_system)=
      presentation_transport judgment_context_presents judgment_context_presents"
    by (intro ext; rule judgment_context_identity_transport)
  show "presented_function_contract judgment_context_presents judgment_context_formed
      (\<lambda>t. (157,t)\<in>positive_meaning context_admission_system) judgment_context_presents judgment_context_formed
      (\<lambda>t. (157,t)\<in>positive_meaning context_admission_system) id
      (\<lambda>p q. (159,Pair_Term p q)\<in>positive_meaning context_admission_system)"
    by (simp only: operation; rule presentation_identity_function[OF judgment_context_native_class judgment_context_native_class])
qed

section \<open>Four fixed native entries precede every future context\<close>

abbreviation context_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "context_operation_result d t \<equiv>
    if d=156 then (\<exists>E u r. site_value_presents E u r t)
    else if d=157 then (\<exists>j. judgment_context_presents j t)
    else if d=158 then (\<exists>p q. t=Pair_Term p q \<and> presentation_transport site_context_presents site_context_presents p q)
    else (\<exists>p q. t=Pair_Term p q \<and> presentation_transport judgment_context_presents judgment_context_presents p q)"

theorem context_operations_exact:
  assumes "d\<in>{156,157,158,159}"
  shows "(d,t)\<in>positive_meaning context_admission_system \<longleftrightarrow> context_operation_result d t"
  using assms by (auto simp: site_context_exact judgment_context_exact site_context_identity_exact judgment_context_identity_exact)

theorem native_context_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {156::nat,157,158,159} \<and>
    (\<forall>d\<in>{156,157,158,159}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> context_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{156,157,158,159}\<subseteq>system_definitions context_admission_system" by auto
  have calls: "schema_call_formed context_admission_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{156,157,158,159}" for d t
    using context_admission_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF context_admission_system_formed selected calls context_operations_exact])
qed

text \<open>
  These entries admit exactly the existing site and judgment context classes.
  Complete environment presentations may vary while their actual site
  coordinates remain exact. The two identity operations are the canonical
  correspondences of those classes and export the general function contracts.
  Higher roles can specialize the independently formed contexts locally.

  The native program and all four distinct entries are fixed before future
  context data. Its original scope, artifacts, and bindings persist across
  those applications. Site admission supplies no program grammar, application
  formation, minimality, or truth premise.
\<close>

end
