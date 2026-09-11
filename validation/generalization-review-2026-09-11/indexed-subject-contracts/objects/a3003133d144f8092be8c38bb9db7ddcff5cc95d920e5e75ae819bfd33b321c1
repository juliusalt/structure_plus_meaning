theory RRA_Generation_Transport
  imports RRA_Generation_Dependencies RRA_Fresh_Uses
begin

section \<open>Renaming uses preserves the recursively recovered core\<close>

lemma generation_fields_use_renaming:
  assumes fields: "generation_fields_at E u r l M p c" and injective: "inj h"
  shows "generation_fields_at (rename_environment h E) (h u) r l M p c"
proof -
  have ef: "environment_formed E" using generation_fields_formed[OF fields] by blast
  have ff: "environment_formed (rename_environment h E)"
    by (rule environment_renaming_formed[OF ef injective])
  show ?thesis using fields ff
    by (simp add: generation_fields_at_def artifact_at_renamed_use[OF injective]
        anchored_at_use_renaming[OF injective])
qed

theorem generation_at_use_renaming:
  assumes source: "generation_at E u r G" and injective: "inj h"
  shows "generation_at (rename_environment h E) (h u) r G"
  using source
proof (induction rule: generation_at.induct)
  case (generation u root l M p c g)
  have fields: "generation_fields_at (rename_environment h E) (h u) root l M p c"
    by (rule generation_fields_use_renaming[OF generation.hyps(1) injective])
  have refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
    (\<exists>v a. located_at (rename_environment h E) (h u) d v a \<and>
      generation_at (rename_environment h E) v a (g s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d) \<in> M"
    obtain v a where loc: "located_at E u d v a"
      and child: "generation_at (rename_environment h E) (h v) a (g s)"
      using generation.IH edge by blast
    have moved: "located_at (rename_environment h E) (h u) d (h v) a"
      using loc by (simp only: located_at_use_renaming[OF injective])
    show "\<exists>v a. located_at (rename_environment h E) (h u) d v a \<and>
      generation_at (rename_environment h E) v a (g s)" using moved child by blast
  qed
  show ?case by (rule generation_at.generation[OF fields generation.hyps(2) refs])
qed

section \<open>A finite family of presentations can coexist\<close>

theorem finite_generation_presentations_together:
  assumes fin: "finite P"
    and each: "\<forall>G\<in>P. \<exists>E :: local_address option artifact_environment.
      \<exists>u r. generation_at E u r G"
  shows "\<exists>E :: local_address option artifact_environment.
    environment_formed E \<and> (\<forall>G\<in>P. \<exists>u r. generation_at E u r G)"
  using fin each
proof (induction P rule: finite_induct)
  case empty
  let ?E = "artifact_family_environment {} (\<lambda>_ :: local_address option. empty_artifact)"
  have formed: "environment_formed ?E" by (rule artifact_family_formed) auto
  show ?case using formed by blast
next
  case (insert G P)
  have rest: "\<forall>H\<in>P. \<exists>E :: local_address option artifact_environment.
    \<exists>u r. generation_at E u r H" using insert.prems by blast
  obtain E :: "local_address option artifact_environment" where ef: "environment_formed E"
    and old: "\<forall>H\<in>P. \<exists>u r. generation_at E u r H"
    using insert.IH[OF rest] by blast
  obtain F :: "local_address option artifact_environment" and u r
    where new: "generation_at F u r G" using insert.prems by blast
  have ff: "environment_formed F" by (rule generation_at_environment_formed[OF new])
  obtain H h where hf: "environment_formed H" and injective: "inj h"
    and left: "environment_included E H"
    and right: "environment_included (rename_environment h F) H"
    using disjoint_environment_extension[OF ef ff] by blast
  have retained: "\<forall>K\<in>P. \<exists>v a. generation_at H v a K"
    using old generation_at_included[OF _ left hf] by blast
  have renamed: "generation_at (rename_environment h F) (h u) r G"
    by (rule generation_at_use_renaming[OF new injective])
  have added: "generation_at H (h u) r G"
    by (rule generation_at_included[OF renamed right hf])
  show ?case using hf retained added by blast
qed

text \<open>
  The recovered exact targets and cores are unchanged by an injective map of
  use occurrences. Every recursive citation follows the mapped original use.
  Finite composition therefore retains all component readings, including
  components with equal artifact values and different binding scopes.
\<close>

end
