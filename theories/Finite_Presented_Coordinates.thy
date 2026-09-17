theory Finite_Presented_Coordinates
  imports Finite_Presented_Collections
    Factor_Coordinate_Values Natural_Binary_Digits
    Factor_Premise_Instances
    Factor_Report_Programs
    Factor_Environment_Values
begin

section \<open>Coordinates keep their owned data terms\<close>

fun finite_natural_data :: "nat \<Rightarrow> finite_factor_term" where
  "finite_natural_data 0=Finite_Payload []"
| "finite_natural_data (Suc n)=Finite_Pair (Finite_Payload []) (finite_natural_data n)"

lemma decode_finite_natural_data [simp]:
  "decode_finite_term (finite_natural_data n)=natural_data_term n"
  by (induction n) simp_all

lemma finite_natural_data_formed [simp]: "finite_term_formed (finite_natural_data n)"
  by (induction n) (simp_all add: octets_formed_def)

lemma finite_natural_data_injective [intro]: "inj finite_natural_data"
proof (rule injI)
  fix m n assume "finite_natural_data m=finite_natural_data n"
  then have "natural_data_term m=natural_data_term n" by (metis decode_finite_natural_data)
  then show "m=n" by (rule injD[OF natural_data_term_injective])
qed

definition finite_storage_path_value where
 "finite_storage_path_value path=Finite_Payload (map (\<lambda>b. if b then 1 else 0) path)"

lemma finite_storage_path_value_injective [intro]: "inj finite_storage_path_value"
proof -
 have digit: "inj (\<lambda>b. if b then (1::nat) else 0)" by (auto simp: inj_def)
 show ?thesis by (rule injI) (simp add: finite_storage_path_value_def inj_map_eq_map[OF digit])
qed

text \<open>A bit path is one flat native payload of its exact zero/one digits.
 This injective presentation preserves long paths without a deeply nested pair
 per bit. It changes the presentation, not the path, its length or any reading.\<close>

definition finite_binary_natural_value where
 "finite_binary_natural_value n=finite_storage_path_value (natural_binary_digits n)"
lemma finite_binary_natural_value_injective [intro]: "inj finite_binary_natural_value"
 by (rule injI) (simp add: finite_binary_natural_value_def inj_eq[OF finite_storage_path_value_injective])
lemma finite_binary_natural_identity:
 "finite_binary_natural_value n=finite_binary_natural_value m \<longleftrightarrow> finite_natural_data n=finite_natural_data m"
 by (simp only: inj_eq[OF finite_binary_natural_value_injective] inj_eq[OF finite_natural_data_injective])

lemma finite_storage_path_value_formed [simp]: "finite_term_formed (finite_storage_path_value path)"
  by (auto simp: finite_storage_path_value_def octets_formed_def)

lemma finite_binary_natural_value_formed [simp]: "finite_term_formed (finite_binary_natural_value n)"
  by (simp add: finite_binary_natural_value_def)

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

section \<open>Artifacts and targets are target terms; environments present their members\<close>

lemma finite_target_injective [intro]: "inj Finite_Target"
  by (rule injI) simp

definition finite_artifact_term :: "finite_exact_artifact \<Rightarrow> finite_factor_term" where
  "finite_artifact_term R=Finite_Target (Finite_Whole R)"

lemma decode_finite_artifact_term [simp]:
  "decode_finite_term (finite_artifact_term R)=Target_Term (Whole_Artifact (decode_finite_object R))"
  by (simp add: finite_artifact_term_def)

lemma finite_artifact_term_injective [intro]: "inj finite_artifact_term"
  by (rule injI) (simp add: finite_artifact_term_def)

definition finite_binding_value ::
  "((local_address option\<times>local_address)\<times>local_address option) \<Rightarrow> finite_factor_term" where
  "finite_binding_value=finite_pair_presentation finite_site_data finite_use_data"

lemma decode_finite_binding_value [simp]:
  "decode_finite_term (finite_binding_value z)=binding_data z"
  by (cases z) (simp add: finite_binding_value_def binding_data_def site_data_term_def)

lemma finite_binding_value_injective [intro]: "inj finite_binding_value"
  unfolding finite_binding_value_def
  by (intro finite_pair_presentation_injective finite_site_data_injective finite_use_data_injective)

definition finite_environment_presentation ::
  "local_address option finite_artifact_environment \<Rightarrow> finite_factor_term" where
  "finite_environment_presentation C=Finite_Pair
    (finite_collection_presentation (finite_pair_presentation finite_use_data finite_artifact_term)
      (finite_environment_artifacts C))
    (finite_collection_presentation finite_binding_value (finite_environment_bindings C))"

lemma finite_environment_presentation_injective [intro]: "inj finite_environment_presentation"
proof (rule injI)
  fix C D :: "local_address option finite_artifact_environment"
  assume same: "finite_environment_presentation C=finite_environment_presentation D"
  have members: "inj (finite_collection_presentation (finite_pair_presentation finite_use_data finite_artifact_term))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_use_data_injective finite_artifact_term_injective)
  have bindings: "inj (finite_collection_presentation finite_binding_value)"
    by (intro finite_collection_presentation_injective finite_binding_value_injective)
  show "C=D"
    by (rule finite_artifact_environment.equality;
      use same in \<open>simp add: finite_environment_presentation_def inj_eq[OF members] inj_eq[OF bindings]\<close>)
qed

text \<open>
  Every coordinate presentation decodes into the notion's existing data term:
  natural indices into natural_data_term, truth values into report_boolean_term,
  uses into use_data_term, definition sites into site_data_term, calls into
  call_instance_value and bindings into binding_data. Artifacts and targets are
  the native target terms, so repeated artifacts keep one identity that a word
  can share. An environment presents its use and artifact members and its
  bindings. Each presentation is injective over all values, including unformed
  ones.
\<close>

end
