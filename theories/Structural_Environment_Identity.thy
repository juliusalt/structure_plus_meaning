theory Structural_Environment_Identity
  imports Structural_Artifact_Identity Structural_Word_Collections
begin

definition structural_placed_artifact_code ::
  "(local_address option\<times>finite_exact_artifact)\<Rightarrow>nat list" where
  "structural_placed_artifact_code row=structural_words_code
    [structural_optional_word (fst row),structural_artifact_code (snd row)]"

lemma structural_placed_artifact_code_injective:
  "structural_placed_artifact_code x=structural_placed_artifact_code y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: structural_placed_artifact_code_def structural_words_code_injective
    structural_optional_word_injective structural_artifact_code_injective)

definition structural_binding_code ::
  "((local_address option\<times>local_address)\<times>local_address option)\<Rightarrow>nat list" where
  "structural_binding_code row=(case row of ((u,r),v) \<Rightarrow>
    structural_words_code [structural_optional_word u,r,structural_optional_word v])"

lemma structural_binding_code_injective:
  "structural_binding_code x=structural_binding_code y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: structural_binding_code_def structural_words_code_injective
    structural_optional_word_injective split: prod.splits)

definition structural_environment_code ::
  "local_address option finite_artifact_environment\<Rightarrow>nat list" where
  "structural_environment_code E=structural_words_code [
    structural_fset_code structural_placed_artifact_code (finite_environment_artifacts E),
    structural_fset_code structural_binding_code (finite_environment_bindings E)]"

theorem structural_environment_code_injective:
  "structural_environment_code E=structural_environment_code F \<longleftrightarrow> E=F"
proof -
  have fields: "structural_environment_code E=structural_environment_code F \<longleftrightarrow>
    finite_environment_artifacts E=finite_environment_artifacts F \<and>
    finite_environment_bindings E=finite_environment_bindings F"
    by (simp add: structural_environment_code_def structural_words_code_injective
      structural_fset_code_injective[where encode=structural_placed_artifact_code,
        OF structural_placed_artifact_code_injective]
      structural_fset_code_injective[where encode=structural_binding_code, OF structural_binding_code_injective])
  show ?thesis by (simp only: fields; cases E; cases F) simp
qed

export_code structural_environment_code checking SML

text \<open>
  Every placement carries its complete artifact. Every binding retains its
  source use, occurrence address and destination use. Ambiguous placements,
  malformed artifacts and dangling bindings remain represented. Complete
  environment identity does not require formation and proves no reading,
  allocation, policy or admission condition.
\<close>

end
