theory Structural_Artifact_Identity
  imports Structural_Word_Lists Factor_Executable_Artifact_Values
begin

definition structural_pair_code where
  "structural_pair_code pair=structural_words_code [fst pair,snd pair]"

definition structural_triple_code where
  "structural_triple_code triple=(case triple of (x,y,z) \<Rightarrow> structural_words_code [x,y,z])"

lemma structural_pair_code_injective:
  "structural_pair_code p=structural_pair_code q \<longleftrightarrow> p=q"
  by (cases p; cases q) (simp add: structural_pair_code_def structural_words_code_injective)

lemma structural_triple_code_injective:
  "structural_triple_code p=structural_triple_code q \<longleftrightarrow> p=q"
  by (cases p; cases q) (simp add: structural_triple_code_def structural_words_code_injective split: prod.splits)

definition structural_artifact_rows :: "artifact_value_rows\<Rightarrow>nat list" where
  "structural_artifact_rows rows=(case rows of (A,E,B,F) \<Rightarrow> structural_words_code [
    structural_words_code A,structural_words_code (map structural_triple_code E),
    structural_words_code (map structural_pair_code B),structural_words_code (map structural_pair_code F)])"

lemma structural_artifact_rows_injective:
  "structural_artifact_rows p=structural_artifact_rows q \<longleftrightarrow> p=q"
  by (cases p; cases q) (simp add: structural_artifact_rows_def structural_words_code_injective
    structural_map_injective[where encode=structural_pair_code, OF structural_pair_code_injective]
    structural_map_injective[where encode=structural_triple_code, OF structural_triple_code_injective]
    split: prod.splits)

definition structural_artifact_code where
  "structural_artifact_code R=structural_artifact_rows (finite_artifact_rows R)"

theorem structural_artifact_code_injective:
  "structural_artifact_code R=structural_artifact_code S \<longleftrightarrow> R=S"
  by (simp only: structural_artifact_code_def structural_artifact_rows_injective finite_artifact_rows_injective)

fun structural_target_code where
  "structural_target_code (Finite_Whole R)=structural_words_code [structural_artifact_code R]"
| "structural_target_code (Finite_Anchor R r)=structural_words_code [structural_artifact_code R,r]"

theorem structural_target_code_injective:
  "structural_target_code p=structural_target_code q \<longleftrightarrow> p=q"
  by (cases p; cases q) (simp_all add: structural_words_code_injective structural_artifact_code_injective)

text \<open>
  The existing complete artifact rows retain carrier, incidence, every counted
  occurrence and every functional binding. Word framing preserves all of them
  and distinguishes whole artifacts from anchored targets. Injectivity does
  not require formation and does not reject alternative source enumerations.
\<close>

end
