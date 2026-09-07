theory Factor_Program_Scope_Reading
  imports Factor_Complete_Data_Admission Factor_Constrained_Readings
begin

section \<open>The scope class recovers its intrinsically determined program\<close>

abbreviation program_scope_subject where
  "program_scope_subject z \<equiv> closed_native_package_at
    (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z)"

abbreviation program_scope_value_presents where
  "program_scope_value_presents z t \<equiv>
    site_value_presents (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) t \<and>
    program_scope_subject z"

theorem program_scope_value_presentation_class:
  "presentation_class program_scope_value_presents program_scope_subject
    (\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system)"
proof -
  let ?site="\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t"
  let ?domain="\<lambda>z. environment_formed (fst z) \<and> snd z\<in>environment_positions (fst z)"
  let ?link="\<lambda>z P. closed_native_package_at (fst z) (fst (snd z)) (snd (snd z)) P"
  have determined: "P=Q" if "?link z P" "?link z Q" for z P Q
    using that by (auto simp: closed_native_package_at_def dest: native_package_unique)
  have result: "presentation_class
    (\<lambda>z t. ?site (fst z) t \<and> ?link (fst z) (snd z))
    (\<lambda>z. ?domain (fst z) \<and> ?link (fst z) (snd z))
    (\<lambda>t. \<exists>z P. ?site z t \<and> ?link z P)"
    by (rule presentation_class_determined[OF site_presentations.presentation_class_axioms determined])
  have domain: "(\<lambda>z. ?domain (fst z) \<and> ?link (fst z) (snd z)) = program_scope_subject"
    by (rule ext)
      (auto simp: closed_native_package_at_def environment_closed_def dest: native_package_root_position)
  have admission: "(\<lambda>t. \<exists>z P. ?site z t \<and> ?link z P) =
    (\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system)"
    by (rule ext) (auto simp: package_retention_admission_exact; metis fst_conv snd_conv)
  show ?thesis using result by (simp only: domain admission)
qed

theorem program_scope_quotation_presentation_class:
  "presentation_class
    (\<lambda>z p. program_scope_quoted_at (fst p) (snd p)
      (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z))
    program_scope_subject
    (\<lambda>p. \<exists>t. (122,t)\<in>positive_meaning package_retention_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t)"
proof -
  have result: "presentation_class
    (composed_presentation program_scope_value_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    program_scope_subject
    (\<lambda>p. \<exists>t. (122,t)\<in>positive_meaning package_retention_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t)"
    by (rule complete_quotation_presentation_class[OF program_scope_value_presentation_class])
      (use site_value_presents_formed in \<open>auto simp: package_retention_admission_exact; blast\<close>)
  have reads: "composed_presentation program_scope_value_presents
      (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t) =
    (\<lambda>z p. program_scope_quoted_at (fst p) (snd p)
      (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z))"
    by (intro ext)
      (auto simp: composed_presentation_def program_scope_quoted_at_def site_value_quoted_at_def)
  show ?thesis using result by (simp only: reads)
qed

section \<open>The quoted body is the actual closed program scope\<close>

abbreviation program_scope_reading_result :: "factor_term \<Rightarrow> bool" where
  "program_scope_reading_result z \<equiv>
    \<exists>C c q t E u r P. z=Pair_Term c t \<and> artifact_value_presents C c \<and>
      complete_data_quoted_at C q t \<and> site_value_presents E u r t \<and>
      closed_native_package_at E u r P"

definition program_scope_reading_schema :: "(nat,nat,nat) factor_schema" where
  "program_scope_reading_schema=constrained_reading_schema 123 122"

definition program_scope_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "program_scope_reading_system=add_view_definition complete_data_admission_system 124 data_x {(0,program_scope_reading_schema)}"

lemma program_scope_reading_system_formed [simp]: "schema_system_formed program_scope_reading_system"
  unfolding program_scope_reading_system_def program_scope_reading_schema_def
  by (rule positive_view.formed, rule constrained_reading_view) auto

lemma program_scope_reading_definitions [simp]:
  "system_definitions program_scope_reading_system=insert 124 (system_definitions complete_data_admission_system)"
  by (simp add: program_scope_reading_system_def)

lemma program_scope_reading_call:
  "schema_call_formed program_scope_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions program_scope_reading_system \<and> term_formed t"
  using added_variable_calls[OF complete_data_admission_system_formed
    program_scope_reading_system_formed[unfolded program_scope_reading_system_def] complete_data_admission_call]
  by (simp only: program_scope_reading_system_def[symmetric])

lemma program_scope_reading_old_meaning:
  assumes "d\<in>system_definitions complete_data_admission_system"
  shows "(d,t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning complete_data_admission_system"
  using added_definition_preserves_old(2)[OF complete_data_admission_system_formed
    program_scope_reading_system_formed[unfolded program_scope_reading_system_def], of d t] assms
  by (auto simp: program_scope_reading_system_def)

lemma program_scope_reading_clause [simp]:
  "((124,c),S)\<in>system_clauses program_scope_reading_system \<longleftrightarrow> (c,S)\<in>{(0,program_scope_reading_schema)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses complete_data_admission_system \<Longrightarrow>
    d\<in>system_definitions complete_data_admission_system" for d c S
    using complete_data_admission_system_formed unfolding schema_system_formed_def by blast
  have absent: "((124,c),S)\<notin>system_clauses complete_data_admission_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: program_scope_reading_system_def)
qed

lemma program_scope_reading_components:
  "(123,t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (123,t)\<in>positive_meaning complete_data_admission_system"
  "(122,t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (122,t)\<in>positive_meaning package_retention_admission_system"
  using program_scope_reading_old_meaning[of 123 t]
    program_scope_reading_old_meaning[of 122 t] complete_data_admission_old_meaning[of 122 t] by auto

interpretation scope_composition: constrained_reading_profile program_scope_reading_system 124 123 122
  by (unfold_locales)
    (auto simp: program_scope_reading_schema_def program_scope_reading_call)

lemma program_scope_reading_step:
  assumes quote: "(123,complete_data_quotation_argument c q t)\<in>positive_meaning complete_data_admission_system"
    and body: "(122,t)\<in>positive_meaning package_retention_admission_system"
  shows "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
  by (rule scope_composition.step)
    (use quote body in \<open>simp_all only: program_scope_reading_components\<close>)

lemma program_scope_reading_fields:
  "(124,z)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (\<exists>c q t. z=Pair_Term c t \<and>
      (123,complete_data_quotation_argument c q t)\<in>positive_meaning complete_data_admission_system \<and>
      (122,t)\<in>positive_meaning package_retention_admission_system)"
  by (simp only: scope_composition.exact program_scope_reading_components)

theorem program_scope_reading_exact:
  "(124,z)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow> program_scope_reading_result z"
  by (simp only: program_scope_reading_fields complete_data_admission_exact package_retention_admission_exact)
    blast

theorem program_scope_reading_class_relation:
  "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    presented_relation artifact_value_presents (=)
      (\<lambda>C t. \<exists>r. complete_data_quoted_at C r t \<and> package_retention_admission_result t) c t"
proof -
  have read: "(123,Pair_Term c (Pair_Term q t))\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (\<exists>C. artifact_value_presents C c \<and>
      (\<exists>r. q=Payload_Term r \<and> complete_data_quoted_at C r t))" for c q t
    by (auto simp: program_scope_reading_components complete_data_admission_exact)
  have check: "(122,t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    package_retention_admission_result t" for t
    by (simp only: program_scope_reading_components package_retention_admission_exact)
  have composed: "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    presented_relation artifact_value_presents (=)
      (\<lambda>C t. \<exists>q. (\<exists>r. q=Payload_Term r \<and> complete_data_quoted_at C r t)
        \<and> package_retention_admission_result t) c t"
    by (rule scope_composition.relation_exact[OF read check])
  show ?thesis using composed by (auto simp: presented_relation_def)
qed

corollary program_scope_reading_at_artifact:
  assumes material: "artifact_value_presents C c"
  shows "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (\<exists>q. complete_data_quoted_at C q t \<and> package_retention_admission_result t)"
proof -
  have predicate: "presented_relation artifact_value_presents (=)
      (\<lambda>C t. \<exists>q. complete_data_quoted_at C q t \<and> package_retention_admission_result t) c t \<longleftrightarrow>
    presented_predicate artifact_value_presents
      (\<lambda>C. \<exists>q. complete_data_quoted_at C q t \<and> package_retention_admission_result t) c"
    by (auto simp: presented_relation_def presented_predicate_def)
  show ?thesis by (simp only: program_scope_reading_class_relation predicate
    artifact_presentations.predicate_at[OF material])
qed

theorem program_scope_reading_admits_artifact:
  assumes material: "artifact_value_presents C c"
  shows "(\<exists>t. (124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system) \<longleftrightarrow>
    (\<exists>q E u r P. program_scope_quoted_at C q E u r P)"
  by (simp only: program_scope_reading_at_artifact[OF material])
    (auto simp: program_scope_quoted_at_def site_value_quoted_at_def; blast)

corollary program_scope_reading_presentation_invariance:
  assumes "artifact_value_presents C c" "artifact_value_presents C d"
  shows "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    (124,Pair_Term d t)\<in>positive_meaning program_scope_reading_system"
  by (simp only: program_scope_reading_at_artifact[OF assms(1)] program_scope_reading_at_artifact[OF assms(2)])

theorem program_scope_reading_body_unique:
  assumes material: "artifact_value_presents C c"
    and first: "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
    and second: "(124,Pair_Term c s)\<in>positive_meaning program_scope_reading_system"
  shows "t=s"
  using first second complete_data_quotation_whole_unique
  by (auto simp: program_scope_reading_at_artifact[OF material])

theorem program_scope_reading_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E u r P"
  shows "\<exists>C c t. artifact_value_presents C c \<and>
    site_value_presents (native_package_environment E u r) u r t \<and>
    program_scope_quoted_at C [] (native_package_environment E u r) u r P \<and>
    (124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
proof -
  obtain C where formed: "exact_formed C"
    and scope: "program_scope_quoted_at C [] (native_package_environment E u r) u r P"
    using program_scope_quoted_total[OF package] by blast
  obtain t where body: "site_value_presents (native_package_environment E u r) u r t"
    and quote: "complete_data_quoted_at C [] t"
    using scope by (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)
  have closed: "closed_native_package_at (native_package_environment E u r) u r P"
    using scope by (simp add: program_scope_quoted_at_def)
  obtain c where material: "artifact_value_presents C c"
    using artifact_value_presents_total[OF formed] by blast
  have read: "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
    by (simp only: program_scope_reading_at_artifact[OF material])
      (use quote body closed in blast)
  show ?thesis using material body scope read by blast
qed

theorem program_scope_reading_interpretation:
  assumes material: "artifact_value_presents C c"
    and read: "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
    and body: "site_value_presents E pu pr t"
  shows "\<exists>q P. program_scope_quoted_at C q E pu pr P \<and>
    (\<forall>F au ar d x I K. environment_formed F \<longrightarrow> environment_included E F \<longrightarrow>
      native_application_at F au ar d x I K \<longrightarrow>
      native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
      (native_application_formed F pu pr au ar \<longleftrightarrow> schema_call_formed P d x) \<and>
      (native_positive_holds F pu pr au ar \<longleftrightarrow> (d,x)\<in>positive_meaning P))"
proof -
  obtain q D u r P where quote: "complete_data_quoted_at C q t"
    and represented: "site_value_presents D u r t" and closed: "closed_native_package_at D u r P"
    using read by (simp only: program_scope_reading_at_artifact[OF material]) blast
  have same: "D=E \<and> u=pu \<and> r=pr" by (rule site_value_presents_unique[OF represented body])
  have scope: "program_scope_quoted_at C q E pu pr P"
    using quote body closed same by (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)
  have applications: "native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
      (native_application_formed F pu pr au ar \<longleftrightarrow> schema_call_formed P d x) \<and>
      (native_positive_holds F pu pr au ar \<longleftrightarrow> (d,x)\<in>positive_meaning P)"
    if formed: "environment_formed F" and included: "environment_included E F"
      and app: "native_application_at F au ar d x I K" for F au ar d x I K
    using program_scope_future_application[OF scope formed included app] by blast
  show ?thesis by (rule exI[of _ q], rule exI[of _ P]) (use scope applications in blast)
qed

section \<open>Two fixed ordinary entries serve every future formed input\<close>

abbreviation complete_scope_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "complete_scope_operation_result d t \<equiv>
    (d=123 \<and> complete_data_admission_result t) \<or> (d=124 \<and> program_scope_reading_result t)"

lemma complete_scope_operations_exact:
  assumes "d\<in>{123,124}"
  shows "(d,t)\<in>positive_meaning program_scope_reading_system \<longleftrightarrow>
    complete_scope_operation_result d t"
  using assms by (auto simp: program_scope_reading_components complete_data_admission_exact program_scope_reading_exact; blast)

theorem native_complete_scope_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {123::nat,124} \<and>
    (\<forall>d\<in>{123,124}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> complete_scope_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions program_scope_reading_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions program_scope_reading_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed program_scope_reading_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning program_scope_reading_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF program_scope_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have sites: "inj_on g {123,124}" by (rule inj_on_subset[OF injective]) auto
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {123,124}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{123,124}" and tf: "term_formed t"
    have member: "d\<in>system_definitions program_scope_reading_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed program_scope_reading_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning program_scope_reading_system"
      "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R"
      "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
      using future[rule_format, OF member tf] by (elim exE conjE) (rule that; assumption)
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow> complete_scope_operation_result d t) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member complete_scope_operations_exact[OF selected] in
          \<open>auto simp: program_scope_reading_call\<close>)
  qed
qed

section \<open>The native scope reader admits presentations of its own scope\<close>

theorem native_scope_reader_self_presentation:
  "\<exists>g :: nat\<Rightarrow>local_address option definition_site. \<exists>E pu Q.
    inj_on g (system_definitions program_scope_reading_system) \<and>
    closed_native_package_at E pu [] Q \<and>
    system_alpha_variant (rename_system g program_scope_reading_system) Q \<and>
    (\<exists>C c q t. artifact_value_presents C c \<and> complete_data_quoted_at C q t \<and>
      site_value_presents E pu [] t) \<and>
    (\<forall>C c q t. artifact_value_presents C c \<longrightarrow> complete_data_quoted_at C q t \<longrightarrow>
      site_value_presents E pu [] t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and>
        native_application_at F au [] (g 124) (Pair_Term c t) I K \<and>
        native_package_environment F pu []=E \<and>
        native_application_formed F pu [] au [] \<and> native_positive_holds F pu [] au [] \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where compiled: "inj_on g (system_definitions program_scope_reading_system)"
      "closed_native_package_at E pu [] Q" "native_package_environment E pu []=E"
      "system_alpha_variant (rename_system g program_scope_reading_system) Q"
      "positive_meaning Q=image (map_prod g id) (positive_meaning program_scope_reading_system)"
    using program_compilation_total[OF program_scope_reading_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have package: "native_package_at E pu [] Q"
    using compiled(2) by (simp add: closed_native_package_at_def)
  interpret scopes: presentation_class
    "\<lambda>z p. program_scope_quoted_at (fst p) (snd p)
      (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) (snd z)"
    program_scope_subject
    "\<lambda>p. \<exists>t. (122,t)\<in>positive_meaning package_retention_admission_system \<and>
      complete_data_quoted_at (fst p) (snd p) t"
    by (rule program_scope_quotation_presentation_class)
  have domain: "program_scope_subject ((E,pu,[]),Q)" using compiled(2) by simp
  obtain p where quoted: "program_scope_quoted_at (fst p) (snd p) E pu [] Q"
    using scopes.total[OF domain] by auto
  obtain t where body: "site_value_presents E pu [] t"
    and quotation: "complete_data_quoted_at (fst p) (snd p) t"
    using quoted by (auto simp: program_scope_quoted_at_def site_value_quoted_at_def)
  have cf: "exact_formed (fst p)" using complete_data_quotation_formed[OF quotation] by blast
  obtain c where material: "artifact_value_presents (fst p) c"
    using artifact_value_presents_total[OF cf] by blast
  have inhabited: "\<exists>C c q t. artifact_value_presents C c \<and> complete_data_quoted_at C q t \<and>
    site_value_presents E pu [] t"
    using material quotation body by blast
  have member: "124\<in>system_definitions program_scope_reading_system" by simp
  have target: "g 124\<in>system_definitions Q"
    using compiled(4) member by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have all_presentations:
    "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] (g 124) (Pair_Term c t) I K \<and>
      native_package_environment F pu []=E \<and>
      native_application_formed F pu [] au [] \<and> native_positive_holds F pu [] au [] \<and>
      (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
    if material: "artifact_value_presents C c" and quote: "complete_data_quoted_at C q t"
      and body: "site_value_presents E pu [] t" for C c q t
  proof -
    have read: "(124,Pair_Term c t)\<in>positive_meaning program_scope_reading_system"
      by (simp only: program_scope_reading_at_artifact[OF material])
        (use quote body compiled(2) in blast)
    have formed: "term_formed (Pair_Term c t)"
      using artifact_value_presents_formed[OF material] site_value_presents_formed[OF body] by auto
    have source_call: "schema_call_formed program_scope_reading_system 124 (Pair_Term c t)"
      using member formed by (simp only: program_scope_reading_call)
    have target_call: "schema_call_formed Q (g 124) (Pair_Term c t)"
      using source_call compiled_system_call_boundary[OF program_scope_reading_system_formed
        compiled(1,4) member] by blast
    have target_truth: "(g 124,Pair_Term c t)\<in>positive_meaning Q"
      using read compiled_system_meaning_at[OF compiled(1) member compiled(5)] by blast
    obtain F au I K where future: "environment_formed F" "environment_included E F"
      "au\<notin>environment_uses E" "native_package_at F pu [] Q"
      "native_application_at F au [] (g 124) (Pair_Term c t) I K"
      "native_package_environment F pu []=native_package_environment E pu []"
      "native_application_formed F pu [] au []\<longleftrightarrow>schema_call_formed Q (g 124) (Pair_Term c t)"
      "native_positive_holds F pu [] au []\<longleftrightarrow>(g 124,Pair_Term c t)\<in>positive_meaning Q"
      "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R"
      "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w"
      using native_application_extension_total[OF package target formed]
      by (elim exE conjE) (rule that; assumption)
    have canonical: "native_package_environment F pu []=E"
      using future(6) compiled(3) by simp
    have accepted: "native_application_formed F pu [] au []" using future(7) target_call by blast
    have true_call: "native_positive_holds F pu [] au []" using future(8) target_truth by blast
    show ?thesis
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use future(1-5,9,10) canonical accepted true_call in blast)
  qed
  show ?thesis by (rule exI[of _ g], rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q])
    (use compiled(1,2,4) inhabited all_presentations in blast)
qed

text \<open>
  The scope class is obtained by adjoining the uniquely determined native
  program to its presented environment and site, then composing that class
  with complete quotation. Its reader instantiates the general constrained
  reading constructor. Two ordinary premises share the actual quoted body.
  The root is a private witness recovered from the whole artifact; the
  returned body is the actual quoted term.
  No second program value is stored. Existential body admission is exactly
  the existing program-scope quotation relation.

  The recovered environment and program site determine formation and meaning
  of all actual future applications in formed extensions retaining that scope.
  This is an explicit composition theorem for quotation, environment, package,
  and semantic definition, including their common stored boundary.

  The two entries belong to one fixed native program before arbitrary future
  inputs. Every earlier entry, the fixed minimal program environment, and all
  prior artifacts and outgoing bindings are preserved. These exactness results
  concern the declared presentation classes. Admission and composition for the
  remaining generation, authority, and transition material remain separate.

  The same class construction presents the fixed native reader's own closed
  program scope. Every compatible complete presentation of that scope is
  admitted by an actual future call to its own compiled reading definition.
  The original scope is retained; its presentation is a future operand.
  This establishes self-application for the operative reader and its program
  structure. Presentation and native checking of further presentation contracts,
  exactness proofs, and authority transitions remain explicit obligations.
\<close>

end
