theory Finite_Presented_Coordinates
  imports Finite_Presented_Collections
    Factor_Coordinate_Values
    Factor_Premise_Instances
    Factor_Report_Programs
    Factor_Target_Values
    Factor_Executable_Environment_Values_Base
begin

section \<open>Coordinates keep their owned data terms\<close>

fun finite_natural_data :: "nat \<Rightarrow> finite_factor_term" where
  "finite_natural_data 0=Finite_Payload []"
| "finite_natural_data (Suc n)=Finite_Pair (Finite_Payload []) (finite_natural_data n)"

lemma decode_finite_natural_data [simp]:
  "decode_finite_term (finite_natural_data n)=natural_data_term n"
  by (induction n) simp_all

lemma finite_natural_data_injective [intro]: "inj finite_natural_data"
proof (rule injI)
  fix m n assume "finite_natural_data m=finite_natural_data n"
  then have "natural_data_term m=natural_data_term n" by (metis decode_finite_natural_data)
  then show "m=n" by (rule injD[OF natural_data_term_injective])
qed

definition finite_boolean_data :: "bool \<Rightarrow> finite_factor_term" where
  "finite_boolean_data b=finite_natural_data (if b then 1 else 0)"

lemma decode_finite_boolean_data [simp]:
  "decode_finite_term (finite_boolean_data b)=report_boolean_term b"
  by (cases b) (simp_all add: finite_boolean_data_def One_nat_def)

lemma finite_boolean_data_injective [intro]: "inj finite_boolean_data"
  by (rule injI) (simp add: finite_boolean_data_def inj_eq[OF finite_natural_data_injective] split: if_splits)

definition finite_use_data :: "local_address option \<Rightarrow> finite_factor_term" where
  "finite_use_data=finite_option_presentation (finite_sequence_presentation finite_natural_data)"

lemma decode_finite_use_data [simp]:
  "decode_finite_term (finite_use_data u)=use_data_term u"
  by (cases u) (simp_all add: finite_use_data_def finite_sequence_presentation_def comp_def)

lemma finite_use_data_injective [intro]: "inj finite_use_data"
  unfolding finite_use_data_def
  by (intro finite_option_presentation_injective finite_sequence_presentation_injective finite_natural_data_injective)

definition finite_site_data :: "local_address option definition_site \<Rightarrow> finite_factor_term" where
  "finite_site_data=finite_pair_presentation finite_use_data Finite_Payload"

lemma decode_finite_site_data [simp]:
  "decode_finite_term (finite_site_data d)=site_data_term (fst d) (snd d)"
  by (cases d) (simp add: finite_site_data_def site_data_term_def)

lemma finite_site_data_injective [intro]: "inj finite_site_data"
  unfolding finite_site_data_def
  by (intro finite_pair_presentation_injective finite_use_data_injective finite_payload_injective)

definition finite_call_value :: "(local_address option definition_site\<times>finite_factor_term) \<Rightarrow> finite_factor_term" where
  "finite_call_value=finite_pair_presentation finite_site_data id"

lemma decode_finite_call_value [simp]:
  "decode_finite_term (finite_call_value q)=call_instance_value (fst q) (decode_finite_term (snd q))"
  by (cases q) (simp add: finite_call_value_def call_instance_value_def)

lemma finite_call_value_injective [intro]: "inj finite_call_value"
  unfolding finite_call_value_def
  by (intro finite_pair_presentation_injective finite_site_data_injective inj_on_id)

section \<open>Artifacts, targets and environments keep their complete values\<close>

lemma finite_artifact_value_inj [intro]: "inj finite_artifact_value"
  by (rule injI) (simp add: finite_artifact_value_injective)

fun finite_target_occurrence :: "finite_exact_target \<Rightarrow> local_address option" where
  "finite_target_occurrence (Finite_Whole C)=None"
| "finite_target_occurrence (Finite_Anchor C a)=Some a"

definition finite_target_value :: "finite_exact_target \<Rightarrow> finite_factor_term" where
  "finite_target_value x=Finite_Pair (finite_artifact_value (finite_target_artifact x))
    (finite_option_presentation Finite_Payload (finite_target_occurrence x))"

lemma decode_finite_target_value [simp]:
  "decode_finite_term (finite_target_value x)=Pair_Term
    (artifact_rows_term (finite_artifact_rows (finite_target_artifact x)))
    (optional_payload_term (finite_target_occurrence x))"
  by (cases "finite_target_occurrence x") (simp_all add: finite_target_value_def)

lemma finite_target_value_injective [intro]: "inj finite_target_value"
proof (rule injI)
  fix x y assume same: "finite_target_value x=finite_target_value y"
  have "finite_target_artifact x=finite_target_artifact y" "finite_target_occurrence x=finite_target_occurrence y"
    using same by (simp_all add: finite_target_value_def finite_artifact_value_injective
      inj_eq[OF finite_option_presentation_injective[OF finite_payload_injective]])
  then show "x=y" by (cases x; cases y) simp_all
qed

theorem finite_target_value_exact:
  "target_value_presents x (decode_finite_term (finite_target_value C)) \<longleftrightarrow>
    finite_target_formed C \<and> x=decode_finite_target C"
proof -
  let ?R="finite_target_artifact C" and ?u="finite_target_occurrence C"
  have "target_value_presents x (decode_finite_term (finite_target_value C)) \<longleftrightarrow>
      target_formed x \<and> artifact_value_presents (target_artifact x) (artifact_rows_term (finite_artifact_rows ?R)) \<and>
      optional_payload_term ?u=optional_payload_term (target_occurrence x)"
    by (auto simp: target_value_presents_def)
  also have "\<dots> \<longleftrightarrow> target_formed x \<and> finite_exact_formed ?R \<and>
      target_artifact x=decode_finite_object ?R \<and> ?u=target_occurrence x"
    by (simp add: finite_artifact_rows_value_exact inj_eq[OF optional_payload_term_injective])
  also have "\<dots> \<longleftrightarrow> finite_target_formed C \<and> x=decode_finite_target C"
  proof -
    have identity: "x=decode_finite_target C \<longleftrightarrow>
        target_artifact x=decode_finite_object ?R \<and> ?u=target_occurrence x"
      by (cases C; cases x) (auto simp: prod_eq_iff)
    have formed: "finite_target_formed C \<longleftrightarrow> target_formed (decode_finite_target C)"
      by (rule finite_target_formed_correct)
    have artifact: "finite_target_formed C \<Longrightarrow> finite_exact_formed ?R"
      by (cases C) simp_all
    show ?thesis using identity formed artifact by blast
  qed
  finally show ?thesis .
qed

lemma finite_environment_value_injective [intro]: "inj finite_environment_value"
proof (rule injI)
  fix C D :: "local_address option finite_artifact_environment"
  assume same: "finite_environment_value C=finite_environment_value D"
  have row_terms: "inj environment_artifact_rows_term"
    by (rule injI) (auto simp: environment_artifact_rows_term_def prod_eq_iff inj_eq[OF use_data_term_injective])
  have "finite_environment_term C=finite_environment_term D"
    using arg_cong[OF same, of decode_finite_term] by simp
  then have rows: "finite_environment_artifact_rows C=finite_environment_artifact_rows D"
    and bindings: "sorted_list_of_fset (finite_environment_bindings C)=sorted_list_of_fset (finite_environment_bindings D)"
    by (simp_all add: finite_environment_term_def data_list_term_injective inj_map_eq_map[OF row_terms]
      inj_map_eq_map[OF binding_data_injective])
  have artifacts: "finite_environment_artifacts C=finite_environment_artifacts D"
  proof (rule fset_eqI)
    fix z :: "local_address option\<times>finite_exact_artifact"
    obtain u R where z: "z=(u,R)" by (cases z)
    have "(u,finite_artifact_rows R)\<in>set (finite_environment_artifact_rows C) \<longleftrightarrow>
        (u,finite_artifact_rows R)\<in>set (finite_environment_artifact_rows D)"
      by (simp only: rows)
    then show "z |\<in>| finite_environment_artifacts C \<longleftrightarrow> z |\<in>| finite_environment_artifacts D"
      by (auto simp: z finite_environment_artifact_rows_def fimage.rep_eq finite_artifact_rows_injective)
  qed
  have "finite_environment_bindings C=finite_environment_bindings D"
    using arg_cong[OF bindings, of fset_of_list] by simp
  then show "C=D" using artifacts by (intro finite_artifact_environment.equality) simp_all
qed

export_code finite_natural_data finite_boolean_data finite_use_data finite_site_data finite_call_value
  finite_target_value finite_environment_value checking SML

text \<open>
  Every coordinate presentation decodes into the notion's existing data term:
  natural indices into natural_data_term, truth values into report_boolean_term,
  uses into use_data_term, definition sites into site_data_term and calls into
  call_instance_value. Targets and environments keep their complete artifact
  rows. Each executable presentation is injective over all values, including
  unformed ones, and a target's presentation is exactly the native target class
  of its decoded target when it is formed.
\<close>

end
