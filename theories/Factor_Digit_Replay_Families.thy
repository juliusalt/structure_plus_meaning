theory Factor_Digit_Replay_Families
  imports Factor_Digit_Replay_Methods Factor_Required_History_Methods
begin

type_synonym digit_replay_result_row =
  "required_history_certificate option\<times>bounded_replay_value fset option"

definition digit_replay_family_reference where
  "digit_replay_family_reference subjects=fimage (\<lambda>(key,input).
    (key,map_option digit_replay_reference input)) subjects"

definition digit_replay_family_prepare where
  "digit_replay_family_prepare subjects=fimage (\<lambda>(key,input).
    (key,map_option digit_replay_context input)) subjects"

definition digit_replay_family_change where
  "digit_replay_family_change (m::nat) results=(if m=16 then {||}
    else if m=17 then fimage (\<lambda>(key,result). (None,result)) results else results)"

definition digit_replay_family_prepared where
  "digit_replay_family_prepared m prepared=digit_replay_family_change m
    (fimage (\<lambda>(key,input). (key,map_option
      (\<lambda>(X,reference,variants). digit_replay_prepared m X variants) input)) prepared)"

definition digit_replay_family_method where
  "digit_replay_family_method m subjects=digit_replay_family_change m
    (fimage (\<lambda>(key,input). (key,map_option (digit_replay_method m) input)) subjects)"

lemma digit_replay_family_prepared_exact:
  "digit_replay_family_prepared m (digit_replay_family_prepare subjects)=digit_replay_family_method m subjects"
  by (simp only: digit_replay_family_prepared_def digit_replay_family_prepare_def digit_replay_family_method_def
    digit_replay_context_def digit_replay_prepared_exact fimage_fimage option.map_comp comp_def
    case_prod_unfold fst_conv snd_conv)

theorem digit_replay_family_correct_methods:
  assumes method: "m\<in>{0,1}"
  shows "digit_replay_family_method m subjects=digit_replay_family_reference subjects"
proof -
  have operation: "digit_replay_method m=digit_replay_reference"
    by (rule ext; rule digit_replay_correct_methods[OF method])
  show ?thesis using method by (auto simp: digit_replay_family_method_def
    digit_replay_family_reference_def digit_replay_family_change_def operation)
qed

definition digit_replay_family_condition where
  "digit_replay_family_condition f method subjects=(
    (\<exists>c X. (c,Some X) |\<in>| literal_replay_family literal_replay_seed 0 \<and> literal_replay_holds X) \<and>
    relation_reader_condition (\<lambda>row. row |\<in>| digit_replay_family_reference subjects) f (method subjects))"

definition digit_replay_family_context where
  "digit_replay_family_context subjects=(subjects,literal_replay_covered literal_replay_seed,
    digit_replay_family_prepare subjects,digit_replay_family_reference subjects)"

definition digit_replay_family_assessment where
  "digit_replay_family_assessment m context=(case context of (subjects,covered,prepared,reference) \<Rightarrow>
    (digit_replay_family_prepared m prepared,reference,covered,
      fimage (\<lambda>(key,input). (key,map_option (digit_replay_assessment m) input)) prepared))"

definition digit_replay_family_inspect ::
  "(digit_replay_result_row fset\<times>digit_replay_result_row fset\<times>bool\<times>'a)\<Rightarrow>nat\<Rightarrow>bool" where
  "digit_replay_family_inspect assessment f=(case assessment of (result,reference,covered,causes) \<Rightarrow>
    covered \<and> finite_reader_inspect (result,reference) f)"

theorem digit_replay_family_assessment_exact:
  "digit_replay_family_inspect (digit_replay_family_assessment m (digit_replay_family_context subjects)) f=
    digit_replay_family_condition f (digit_replay_family_method m) subjects"
  by (simp only: digit_replay_family_inspect_def digit_replay_family_assessment_def
    digit_replay_family_context_def case_prod_conv digit_replay_family_prepared_exact
    literal_replay_covered_exact digit_replay_family_condition_def finite_reader_inspect_exact[OF refl])

text \<open>
  Every certificate key, unavailable replay request, unavailable prepared state,
  refused operation and complete successful result retains its own position.
  Coverage requires an actually valid original literal replay. Whole-family
  comparison additionally exposes deleted rows and altered certificate keys.
  Per-input reports retain the actual suboperation results and original cause
  diagnostics before any whole-family deletion or key change.
\<close>

end
