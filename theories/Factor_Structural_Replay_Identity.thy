theory Factor_Structural_Replay_Identity
  imports Factor_Digit_Replay_Families Structural_Environment_Identity
    RRA_Structural_Generation_Checking Finite_Reader_Identity_Maps
begin

fun structural_replay_value_code :: "bounded_replay_value\<Rightarrow>nat list" where
  "structural_replay_value_code None=structural_words_code []"
| "structural_replay_value_code (Some ((n,E),u,G,J,C))=structural_words_code [
    [n],structural_environment_code E,structural_optional_word u,structural_generation_code G,
    structural_environment_code J,structural_artifact_code C]"

lemma structural_replay_value_code_injective:
  "structural_replay_value_code x=structural_replay_value_code y \<longleftrightarrow> x=y"
  by (cases x; cases y) (auto simp: structural_words_code_injective structural_environment_code_injective
    structural_optional_word_injective structural_generation_code_injective structural_artifact_code_injective
    split: prod.splits)

definition structural_replay_row where
  "structural_replay_row row=(fst row,map_option (structural_fset_code structural_replay_value_code) (snd row))"

lemma structural_replay_row_injective:
  "structural_replay_row x=structural_replay_row y \<longleftrightarrow> x=y"
  by (cases x; cases y) (simp add: structural_replay_row_def
    optional_identity_map_injective[where encode="structural_fset_code structural_replay_value_code",
      OF structural_fset_code_injective[OF structural_replay_value_code_injective]])

declare digit_replay_inspect_def[code del]

lemma digit_replay_inspect_structural_code [code]:
  "digit_replay_inspect (result,reference,causes) f=finite_reader_inspect
    (fimage structural_replay_value_code result,fimage structural_replay_value_code reference) f"
  by (simp only: finite_reader_inspect_identity_map[OF structural_replay_value_code_injective]
    digit_replay_inspect_def case_prod_conv)

declare digit_replay_family_inspect_def[code del]

lemma digit_replay_family_inspect_structural_code [code]:
  "digit_replay_family_inspect (result,reference,covered,causes) f=(covered \<and>
    finite_reader_inspect (fimage structural_replay_row result,fimage structural_replay_row reference) f)"
  by (simp only: finite_reader_inspect_identity_map[OF structural_replay_row_injective]
    digit_replay_family_inspect_def case_prod_conv)

text \<open>
  The complete optional result retains the allocation head, every resulting
  artifact and binding, record use, original generation core, judgment
  environment and quotation artifact. Whole family rows retain the original
  certificate and every optional position. Exact injective maps change only
  comparison representation. All original meanings, observers and candidate
  construction equations remain the same; physical cost is still a separate
  obligation.
\<close>

end
