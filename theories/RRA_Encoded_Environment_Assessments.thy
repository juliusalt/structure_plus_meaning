theory RRA_Encoded_Environment_Assessments
  imports RRA_Encoded_Environment_Methods
begin

definition encoded_environment_loaded_view where
  "encoded_environment_loaded_view use_code slot_code use_decode slot_decode X=(case X of (A,B,op) \<Rightarrow>
    encoded_environment_view use_decode slot_decode (encoded_environment_rows use_code slot_code A B))"

context environment_key_codec
begin

lemma loaded_view_exact:
  "encoded_environment_loaded_view use_code slot_code use_decode slot_decode (A,B,op)=
    finite_enumerated_environment A B"
  by (simp only: encoded_environment_loaded_view_def case_prod_conv; rule view_representation; rule rows_exact)

end

definition codec_environment_raw_view where
  "codec_environment_raw_view (m::nat) X=(if m=11 then
    encoded_environment_loaded_view digit_use_path digit_address_path read_digit_use_path read_digit_address_path X
    else if m=13 then encoded_environment_loaded_view
      (digit_use_path \<circ> map_option (map (\<lambda>n. n mod 256))) digit_address_path read_digit_use_path read_digit_address_path X
    else if m=14 then encoded_environment_loaded_view digit_use_path
      (digit_address_path \<circ> map (\<lambda>n. n mod 256)) read_digit_use_path read_digit_address_path X
    else if m=15 then encoded_environment_loaded_view digit_use_path digit_address_path
      (read_digit_use_path \<circ> butlast) read_digit_address_path X
    else encoded_environment_loaded_view use_binary_path address_binary_path decode_use_binary_path decode_address_binary_path X)"

lemma codec_environment_raw_view_correct:
  "m\<in>{0,1,11,12} \<Longrightarrow> codec_environment_raw_view m (A,B,op)=finite_enumerated_environment A B"
  by (auto simp: codec_environment_raw_view_def digit_environment.loaded_view_exact unary_environment.loaded_view_exact)

definition codec_environment_full_candidate where
  "codec_environment_full_candidate m=(codec_environment_method m,codec_environment_raw_view m)"

definition codec_environment_full_condition where
  "codec_environment_full_condition (f::nat) candidate X=(if f=2 then (case X of (A,B,op) \<Rightarrow>
    decode_finite_environment (snd candidate X)=decode_finite_environment (finite_enumerated_environment A B))
    else environment_update_condition f (fst candidate) X)"

definition codec_environment_full_context where
  "codec_environment_full_context X=(case X of (A,B,op) \<Rightarrow>
    (codec_environment_context X,finite_enumerated_environment A B))"

definition codec_environment_full_assess where
  "codec_environment_full_assess m context=(case context of ((X,reference),original) \<Rightarrow>
    ((codec_environment_method m X,reference),(codec_environment_raw_view m X,original)))"

type_synonym codec_environment_full_report =
  "(local_address option finite_artifact_environment fset\<times>local_address option finite_artifact_environment fset)\<times>
    local_address option finite_artifact_environment\<times>local_address option finite_artifact_environment"

definition codec_environment_full_inspect :: "codec_environment_full_report\<Rightarrow>nat\<Rightarrow>bool" where
  "codec_environment_full_inspect report f=(if f=2 then fst (snd report)=snd (snd report)
    else environment_update_inspect (fst report) f)"

lemma codec_environment_previous_assessment:
  "fst (codec_environment_full_assess m (codec_environment_full_context X))=
    codec_environment_assessment m (codec_environment_context X)"
  by (cases X) (simp add: codec_environment_full_assess_def codec_environment_full_context_def
    codec_environment_assessment_def codec_environment_context_def)

lemma codec_environment_previous_inspection:
  "f\<in>{0,1} \<Longrightarrow> codec_environment_full_inspect report f=environment_update_inspect (fst report) f"
  by (auto simp: codec_environment_full_inspect_def)

lemma codec_environment_full_assessment_exact:
  "codec_environment_full_inspect (codec_environment_full_assess m (codec_environment_full_context X)) f=
    codec_environment_full_condition f (codec_environment_full_candidate m) X"
proof (cases "f=2")
  case True
  obtain A B op where shape: "X=(A,B,op)" by (cases X) auto
  show ?thesis
    by (simp only: shape True codec_environment_full_inspect_def codec_environment_full_assess_def
      codec_environment_full_context_def codec_environment_full_condition_def codec_environment_full_candidate_def
      codec_environment_context_def case_prod_conv fst_conv snd_conv if_True HOL.simp_thms
      decode_finite_environment_injective)
next
  case False
  show ?thesis
    by (simp only: codec_environment_full_inspect_def codec_environment_full_condition_def
      codec_environment_full_candidate_def False if_False fst_conv codec_environment_previous_assessment
      codec_environment_assessment_exact)
qed

text \<open>
  The raw index and guarded update are separate components of the same actual
  candidate. Raw representation covers every original row, including unformed
  inputs that a valid update must reject. The prior update result and both of
  its original conditions are recovered exactly from the extended assessment.
\<close>

end
