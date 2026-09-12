theory Finite_Retained_Clause_Admission
  imports Factor_Retained_Clause_Admission Factor_Executable_Packages
    Factor_Executable_Environment_Values RRA_Finite_Inclusion
begin

section \<open>Finite recovery checks the complete variable-interface definition\<close>

fun finite_single_clause_shape :: "'u finite_native_schema \<Rightarrow> 'u finite_native_definition \<Rightarrow> bool" where
  "finite_single_clause_shape S (Finite_Variable i,C)=fBex C (\<lambda>(c,T). C={|(c,S)|})"
| "finite_single_clause_shape S (p,C)=False"

lemma finite_single_clause_shape_exact:
  "finite_single_clause_shape S (p,C) \<longleftrightarrow>
    (\<exists>i c. p=Finite_Variable i \<and> C={|(c,S)|})"
  by (cases p) auto

definition finite_single_clause_at ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u finite_native_schema \<Rightarrow> bool" where
  "finite_single_clause_at E u r S \<longleftrightarrow>
    fBex (finite_native_definition_readings E u r) (finite_single_clause_shape S)"

theorem finite_single_clause_at_correct:
  "finite_single_clause_at E u r S \<longleftrightarrow>
    native_single_clause_at (decode_finite_environment E) u r (decode_finite_schema S)"
proof
  assume admitted: "finite_single_clause_at E u r S"
  then obtain i c where row: "(Finite_Variable i,{|(c,S)|}) |\<in>| finite_native_definition_readings E u r"
    by (auto simp: finite_single_clause_at_def finite_single_clause_shape_exact)
  show "native_single_clause_at (decode_finite_environment E) u r (decode_finite_schema S)"
    using row by (auto simp: finite_native_definition_readings_correct native_single_clause_at_def map_relation_values_def)
next
  assume "native_single_clause_at (decode_finite_environment E) u r (decode_finite_schema S)"
  then obtain i c where read: "native_definition_at (decode_finite_environment E) u r
    (Pattern_Variable i) {(c,decode_finite_schema S)}" by (auto simp: native_single_clause_at_def)
  have row: "(Finite_Variable i,{|(c,S)|}) |\<in>| finite_native_definition_readings E u r"
    using read by (simp add: finite_native_definition_readings_correct map_relation_values_def)
  show "finite_single_clause_at E u r S"
    unfolding finite_single_clause_at_def by (rule rev_fBexI[OF row]) simp
qed

definition finite_package_member ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site \<Rightarrow> bool" where
  "finite_package_member E u r d \<longleftrightarrow>
    fBex (finite_native_package_readings E u r) (\<lambda>P. d |\<in>| finite_system_definitions P)"

theorem finite_package_member_correct:
  "finite_package_member E u r d \<longleftrightarrow>
    (\<exists>P. native_package_at (decode_finite_environment E) u r P \<and> d\<in>system_definitions P)"
proof
  assume member: "finite_package_member E u r d"
  then obtain P where read: "P |\<in>| finite_native_package_readings E u r"
    and entry: "d |\<in>| finite_system_definitions P" by (auto simp: finite_package_member_def)
  show "\<exists>P. native_package_at (decode_finite_environment E) u r P \<and> d\<in>system_definitions P"
    by (rule exI[of _ "decode_finite_system P"])
      (use read entry in \<open>simp add: finite_native_package_readings_correct finite_system_definitions_correct\<close>)
next
  assume "\<exists>P. native_package_at (decode_finite_environment E) u r P \<and> d\<in>system_definitions P"
  then obtain P where package: "native_package_at (decode_finite_environment E) u r P"
    and entry: "d\<in>system_definitions P" by blast
  obtain Q where read: "Q |\<in>| finite_native_package_readings E u r" and same: "decode_finite_system Q=P"
    using finite_native_package_readings_complete[OF package] by blast
  show "finite_package_member E u r d" unfolding finite_package_member_def
    by (rule rev_fBexI[OF read]) (use entry same in \<open>simp add: finite_system_definitions_correct\<close>)
qed

definition finite_retained_clause_admitted ::
  "'u finite_artifact_environment \<Rightarrow> 'u finite_native_schema \<Rightarrow>
    'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site \<Rightarrow> bool" where
  "finite_retained_clause_admitted C S D u r d \<longleftrightarrow>
    finite_environment_formed C \<and> finite_environment_included C D \<and>
    finite_package_member D u r d \<and> finite_single_clause_at D (fst d) (snd d) S"

theorem finite_retained_clause_correct:
  "finite_retained_clause_admitted C S D u r d \<longleftrightarrow>
    environment_formed (decode_finite_environment C) \<and>
    environment_included (decode_finite_environment C) (decode_finite_environment D) \<and>
    (\<exists>P. native_package_at (decode_finite_environment D) u r P \<and> d\<in>system_definitions P) \<and>
    native_single_clause_at (decode_finite_environment D) (fst d) (snd d) (decode_finite_schema S)"
  by (simp only: finite_retained_clause_admitted_def finite_environment_formed_correct
    finite_environment_included_correct finite_package_member_correct finite_single_clause_at_correct)

lemma finite_package_member_formed:
  assumes "finite_package_member E u r d"
  shows "finite_environment_formed E"
proof -
  obtain P where package: "native_package_at (decode_finite_environment E) u r P"
    using assms by (simp only: finite_package_member_correct; blast)
  have formed: "environment_formed (decode_finite_environment E)"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  show ?thesis by (simp only: finite_environment_formed_correct formed)
qed

section \<open>The finite calculation is the ordinary native admission judgment\<close>

theorem finite_retained_clause_native:
  assumes source: "finite_environment_formed C"
    and reference: "schema_reference_presents (decode_finite_schema S) v"
  shows "finite_retained_clause_admitted C S D u r d \<longleftrightarrow>
    (370,package_subject_argument (finite_environment_term D) (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning (retained_clause_system (finite_environment_term C) v)"
proof -
  have encoded: "environment_value_presents (decode_finite_environment C) (finite_environment_term C)"
    using finite_environment_value_exact[where E="decode_finite_environment C" and C=C] source by simp
  interpret reader: retained_clause_reader "finite_environment_term C" v
    by (rule retained_clause_reader.intro)
      (use environment_value_presents_formed[OF encoded] schema_reference_presents_formed[OF reference] in auto)
  show ?thesis
  proof (cases "finite_environment_formed D")
    case True
    have target: "environment_value_presents (decode_finite_environment D) (finite_environment_term D)"
      using finite_environment_value_exact[where E="decode_finite_environment D" and C=D] True by simp
    show ?thesis by (simp only: reader.on_values[OF encoded reference target] finite_retained_clause_correct
      finite_environment_formed_correct[symmetric] source) blast
  next
    case False
    have refused: "\<not>finite_retained_clause_admitted C S D u r d"
      using False by (auto simp: finite_retained_clause_admitted_def dest: finite_package_member_formed)
    have invalid: "\<not>environment_value_presents F (finite_environment_term D)" for F
      using finite_environment_value_exact[where E=F and C=D] False by simp
    have native: "\<not>retained_clause_result (decode_finite_environment C) (decode_finite_schema S)
      (package_subject_argument (finite_environment_term D) (use_data_term u) (Payload_Term r) (definition_site_value d))"
      using invalid by (auto simp: retained_clause_result_def)
    show ?thesis by (simp only: refused reader.exact[OF encoded reference] native)
  qed
qed

export_code finite_single_clause_at finite_package_member finite_retained_clause_admitted checking SML

text \<open>
  The candidate tables and every recovered definition come from the supplied
  complete finite artifacts. No package domain, successful clause reading, or
  source-retention flag is supplied by the caller. The exact equation covers
  every finite candidate, including malformed environments and missing sites.
\<close>

end
