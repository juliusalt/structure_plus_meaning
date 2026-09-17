theory Factor_Finite_Source_Observations
  imports Factor_Executable_Packages Factor_Finite_System_Fields
begin

section \<open>Finite observations concern the actual complete native source\<close>

type_synonym 'u finite_source_subject =
  "'u finite_artifact_environment \<times> 'u \<times> local_address \<times> 'u finite_native_system"

definition native_source_subject_matches :: "'u finite_source_subject \<Rightarrow> bool" where
  "native_source_subject_matches X \<longleftrightarrow> (case X of (E,u,r,P) \<Rightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P))"

definition finite_source_subject_matches :: "'u finite_source_subject \<Rightarrow> bool" where
  "finite_source_subject_matches X \<longleftrightarrow> (case X of (E,u,r,P) \<Rightarrow>
    P |\<in>| finite_native_package_readings E u r)"

lemma finite_source_subject_matches_correct:
  "finite_source_subject_matches X \<longleftrightarrow> native_source_subject_matches X"
  by (cases X; simp add: finite_source_subject_matches_def native_source_subject_matches_def
    finite_native_package_readings_correct split: prod.splits)

definition finite_source_fields_match :: "nat \<Rightarrow> 'u finite_native_system \<Rightarrow> 'u finite_native_system \<Rightarrow> bool" where
  "finite_source_fields_match f P N=(if f=0 then finite_system_definitions P=finite_system_definitions N
    else if f=1 then finite_system_interfaces P=finite_system_interfaces N
    else if f=2 then finite_system_clauses P=finite_system_clauses N else P=N)"

definition finite_source_observation :: "nat \<Rightarrow> 'u finite_source_subject \<Rightarrow> bool" where
  "finite_source_observation f X=(case X of (E,u,r,P) \<Rightarrow>
    fBex (finite_native_package_readings E u r) (finite_source_fields_match f P))"

definition native_source_observation :: "nat \<Rightarrow> 'u finite_source_subject \<Rightarrow> bool" where
  "native_source_observation f X=(case X of (E,u,r,P) \<Rightarrow>
    \<exists>N. native_package_at (decode_finite_environment E) u r (decode_finite_system N) \<and>
      finite_source_fields_match f P N)"

lemma finite_source_observation_correct:
  "finite_source_observation f X \<longleftrightarrow> native_source_observation f X"
  by (cases X; auto simp: finite_source_observation_def native_source_observation_def Bex_def
    finite_native_package_readings_correct split: prod.splits)

lemma finite_source_whole_observation:
  "finite_source_observation 3 X \<longleftrightarrow> native_source_subject_matches X"
  by (cases X; simp add: finite_source_observation_def finite_source_fields_match_def Bex_def
    finite_native_package_readings_correct native_source_subject_matches_def split: prod.splits)

lemma finite_source_whole_fields:
  "finite_source_fields_match 3 P N \<longleftrightarrow>
    finite_system_interfaces P=finite_system_interfaces N \<and> finite_system_clauses P=finite_system_clauses N"
  by (auto simp: finite_source_fields_match_def intro: finite_schema_system.equality)

text \<open>
  The independent condition is the complete program reading at the supplied
  environment, use, and root. Every observation reads that same native source.
  Projection equality has no authority to supply omitted fields. The whole
  observation has the exact package-reading contract on every input, including
  malformed environments and absent packages.

  This condition fixes the complete recovered source value. It does not decide
  alpha equivalence between arbitrary independently supplied program models.
  A consumer can use the recovered value itself to establish its source premise.
\<close>

end
