theory Factor_Required_History_States
  imports Factor_Finite_Required_Causes RRA_Finite_Generation_Monotonicity
begin

record finite_required_history_state =
  required_history_source :: "local_address option finite_artifact_environment"
  required_history_source_use :: "local_address option"
  required_history_source_root :: local_address
  required_history_goals :: "local_address option definition_site admission_goal list"
  required_history_entry :: "local_address option definition_site"
  required_history_policy :: "local_address option finite_artifact_environment"
  required_history_policy_use :: "local_address option"
  required_history_material :: "local_address option finite_artifact_environment"
  required_history_members :: "(local_address option definition_site\<times>finite_generation) list"

definition required_generation_payload where
  "required_generation_payload P gs G \<longleftrightarrow> (\<exists>R. generation_payload G=Finite_Whole R \<and>
    admission_requirements_hold (positive_meaning (decode_finite_system P)) gs
      (Target_Term (Whole_Artifact (decode_finite_object R))))"

definition finite_required_history_valid :: "finite_required_history_state \<Rightarrow> bool" where
  "finite_required_history_valid q \<longleftrightarrow> (\<exists>P.
    finite_native_source (required_history_source q) (required_history_source_use q)
      (required_history_source_root q)=Some P \<and>
    finite_construct_source_requirements (required_history_source q) (required_history_source_use q)
      (required_history_source_root q) (required_history_goals q)=
        Some (required_history_entry q,required_history_policy q,required_history_policy_use q) \<and>
    finite_environment_formed (required_history_material q) \<and>
    (\<forall>d G. (d,G)\<in>set (required_history_members q) \<longrightarrow>
      finite_check_generation G (required_history_material q) (fst d) (snd d) \<and>
      required_generation_payload P (required_history_goals q) G))"

definition finite_prepare_required_history where
  "finite_prepare_required_history S su sr gs=map_option (\<lambda>(d,K,pu).
    \<lparr>required_history_source=S,required_history_source_use=su,required_history_source_root=sr,
      required_history_goals=gs,required_history_entry=d,required_history_policy=K,
      required_history_policy_use=pu,required_history_material=finite_enumerated_environment [] [],
      required_history_members=[]\<rparr>) (finite_construct_source_requirements S su sr gs)"

theorem finite_prepare_required_history_valid:
  assumes result: "finite_prepare_required_history S su sr gs=Some q"
  shows "finite_required_history_valid q"
proof -
  obtain d K pu where built: "finite_construct_source_requirements S su sr gs=Some (d,K,pu)"
    and q: "q=\<lparr>required_history_source=S,required_history_source_use=su,required_history_source_root=sr,
      required_history_goals=gs,required_history_entry=d,required_history_policy=K,
      required_history_policy_use=pu,required_history_material=finite_enumerated_environment [] [],
      required_history_members=[]\<rparr>"
    using result by (auto simp: finite_prepare_required_history_def split: option.splits)
  obtain P where source: "finite_native_source S su sr=Some P"
    using finite_construct_source_requirements_correct[OF built]
    by (simp only: finite_native_source_correct; blast)
  show ?thesis unfolding finite_required_history_valid_def
    by (rule exI[of _ P]) (simp add: q source built finite_environment_formed_def
      finite_enumerated_environment_def finite_relation_functional_def)
qed

text \<open>
  The stored source, whole original requirement family, actual constructed
  policy and called entry are fixed before records are considered. Every
  accepted payload retains truth under that original source meaning. Preparing
  an unavailable or unsupported request yields no initialized history.
\<close>

end
