theory Factor_Finite_Source_Extensions
  imports Factor_Finite_Native_Sources Factor_Finite_Mapped_Extensions
begin

section \<open>Establish the entire source premise before extending the package\<close>

definition finite_source_extension_context :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option finite_native_system \<Rightarrow>
    local_address option finite_native_system option" where
  "finite_source_extension_context E pu pr Q=(case finite_native_source E pu pr of None \<Rightarrow> None
    | Some P \<Rightarrow> if finite_system_formed Q \<and>
        finite_system_agrees_on P Q (finite_system_definitions P) then Some P else None)"

theorem finite_source_extension_context_correct:
  "finite_source_extension_context E pu pr Q=Some P \<longleftrightarrow>
    native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    schema_system_formed (decode_finite_system Q) \<and>
    systems_agree_on (decode_finite_system P) (decode_finite_system Q)
      (system_definitions (decode_finite_system P))"
  by (auto simp: finite_source_extension_context_def finite_native_source_correct[symmetric]
    finite_system_formed_correct finite_system_agrees_on_correct finite_system_definitions_correct
    split: option.splits if_splits)

lemma finite_source_extension_profile:
  assumes ready: "finite_source_extension_context E pu pr Q=Some P"
  shows "finite_mapped_native_extension E P Q pu pr (decode_finite_system P) id"
proof -
  have native: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    and target: "schema_system_formed (decode_finite_system Q)"
    and agreement: "systems_agree_on (decode_finite_system P) (decode_finite_system Q)
      (system_definitions (decode_finite_system P))"
    using ready by (simp only: finite_source_extension_context_correct; blast)+
  have source: "schema_system_formed (decode_finite_system P)"
    by (rule native_package_system_formed[OF native])
  have pf: "finite_system_formed P" using source by (simp only: finite_system_formed_correct)
  have qf: "finite_system_formed Q" using target by (simp only: finite_system_formed_correct)
  have variant: "system_alpha_variant (rename_system id (decode_finite_system P)) (decode_finite_system P)"
    using system_alpha_identity[OF source] by simp
  show ?thesis
    by (rule finite_mapped_native_extension.intro[OF native pf qf agreement _ variant]) simp
qed

definition finite_extend_source_native :: "local_address option finite_artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option finite_native_system \<Rightarrow>
    (local_address option finite_native_system \<times> local_address option finite_artifact_environment \<times>
      local_address option) option" where
  "finite_extend_source_native E pu pr Q=(case finite_source_extension_context E pu pr Q of None \<Rightarrow> None
    | Some P \<Rightarrow> map_option (\<lambda>(F,u). (P,F,u)) (finite_extend_mapped_native E P Q id))"

theorem finite_extend_source_native_conditions:
  "finite_extend_source_native E pu pr Q=Some (P,F,u) \<longleftrightarrow>
    finite_source_extension_context E pu pr Q=Some P \<and> finite_extend_mapped_native E P Q id=Some (F,u)"
  by (auto simp: finite_extend_source_native_def split: option.splits prod.splits)

theorem finite_extend_source_native_total:
  "(\<exists>F u. finite_extend_source_native E pu pr Q=Some (P,F,u)) \<longleftrightarrow>
    finite_source_extension_context E pu pr Q=Some P"
proof
  assume "\<exists>F u. finite_extend_source_native E pu pr Q=Some (P,F,u)"
  then show "finite_source_extension_context E pu pr Q=Some P"
    by (simp only: finite_extend_source_native_conditions; blast)
next
  assume ready: "finite_source_extension_context E pu pr Q=Some P"
  interpret extension: finite_mapped_native_extension E P Q pu pr "decode_finite_system P" id
    by (rule finite_source_extension_profile[OF ready])
  show "\<exists>F u. finite_extend_source_native E pu pr Q=Some (P,F,u)"
    using extension.total by (simp only: finite_extend_source_native_conditions ready; blast)
qed

theorem finite_extend_source_native_failure:
  "finite_extend_source_native E pu pr Q=None \<longleftrightarrow> finite_source_extension_context E pu pr Q=None"
proof -
  have present: "(\<exists>P F u. finite_extend_source_native E pu pr Q=Some (P,F,u)) \<longleftrightarrow>
    (\<exists>P. finite_source_extension_context E pu pr Q=Some P)"
    by (simp only: finite_extend_source_native_total)
  show ?thesis using present
    by (cases "finite_extend_source_native E pu pr Q"; cases "finite_source_extension_context E pu pr Q") auto
qed

theorem finite_extend_source_native_admitted:
  assumes result: "finite_extend_source_native E pu pr Q=Some (P,F,u)"
  shows "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    and "finite_mapped_native_extension E P Q pu pr (decode_finite_system P) id"
    and "finite_extend_mapped_native E P Q id=Some (F,u)"
proof -
  have ready: "finite_source_extension_context E pu pr Q=Some P"
    using result by (simp only: finite_extend_source_native_conditions; blast)
  show "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using ready by (simp only: finite_source_extension_context_correct; blast)
  show "finite_mapped_native_extension E P Q pu pr (decode_finite_system P) id"
    by (rule finite_source_extension_profile[OF ready])
  show "finite_extend_mapped_native E P Q id=Some (F,u)"
    using result by (simp only: finite_extend_source_native_conditions; blast)
qed

locale finite_source_native_run =
  fixes E F :: "local_address option finite_artifact_environment"
    and pu u :: "local_address option" and pr :: local_address
    and P Q :: "local_address option finite_native_system"
  assumes result: "finite_extend_source_native E pu pr Q=Some (P,F,u)"
begin

sublocale extension: finite_mapped_native_extension E P Q pu pr "decode_finite_system P" id
  by (rule finite_extend_source_native_admitted(2)[OF result])

lemma construction: "finite_extend_mapped_native E P Q id=Some (F,u)"
  by (rule finite_extend_source_native_admitted(3)[OF result])

lemmas correct = extension.correct[OF construction]

end

text \<open>
  The operation receives the actual source environment, selector and complete
  proposed target. It recovers every source field, checks target formation and
  complete preservation of old definitions, then uses the existing placement
  and construction. Every success establishes all premises of that constructor's
  universal contract, including whole-source correspondence. Its result theorem
  therefore supplies complete target meaning and preservation of every original
  artifact and outgoing binding without an additional source-model assumption.

  The target uses the recovered source's private coordinate types. Exact old
  fields are preserved; automatic placement fixes every old definition site and
  allocates fresh sites for additions. Arbitrary external alpha models are not
  inputs to this operation. Construction and admission of development decisions
  and the complete retained cycle remain separate requirements.
\<close>

end
