theory RRA_Encoded_Environment_Methods
  imports RRA_Encoded_Environment_References Binary_Counted_Relation_Stores
begin

definition codec_environment_method where
  "codec_environment_method (m::nat) X=(if m=11 then
    encoded_environment_update_method digit_use_path digit_address_path read_digit_use_path read_digit_address_path X
    else if m=12 then encoded_environment_update_method use_binary_path address_binary_path
      decode_use_binary_path decode_address_binary_path X
    else if m=13 then encoded_environment_update_method
      (digit_use_path \<circ> map_option (map (\<lambda>n. n mod 256))) digit_address_path read_digit_use_path read_digit_address_path X
    else if m=14 then encoded_environment_update_method digit_use_path
      (digit_address_path \<circ> map (\<lambda>n. n mod 256)) read_digit_use_path read_digit_address_path X
    else if m=15 then encoded_environment_update_method digit_use_path digit_address_path
      (read_digit_use_path \<circ> butlast) read_digit_address_path X
    else environment_update_method m X)"

theorem codec_environment_correct_methods:
  "m\<in>{0,1,11,12} \<Longrightarrow> codec_environment_method m X=environment_update_reference X"
  by (auto simp: codec_environment_method_def environment_update_correct_methods
    digit_environment.update_method_exact unary_environment.update_method_exact)

definition codec_environment_context where
  "codec_environment_context X=(X,environment_update_reference X)"

definition codec_environment_assessment where
  "codec_environment_assessment m context=(case context of (X,reference) \<Rightarrow> (codec_environment_method m X,reference))"

lemma codec_environment_assessment_exact:
  "environment_update_inspect (codec_environment_assessment m (codec_environment_context X)) f=
    environment_update_condition f (codec_environment_method m) X"
  by (simp only: environment_update_inspect_def codec_environment_assessment_def codec_environment_context_def
    case_prod_conv environment_update_condition_def finite_reader_inspect_exact[OF environment_update_reference_exact])

definition codec_environment_previous_case :: "nat\<Rightarrow>environment_update_subject" where
  "codec_environment_previous_case w=(let A=finite_payload_syntax [7];B=finite_payload_syntax [8] in
    if w=16 then ([(Some [0],A)],[],Install_Artifact (Some [256]) B)
    else if w=17 then ([(Some [256],A)],[],Install_Binding (Some [256]) [] (Some [256]))
    else if w=18 then ([(Some [300],A)],[],Install_Artifact (Some [301]) B)
    else if w=19 then ([(Some (replicate 128 0),A)],[],Install_Artifact (Some [1]) B)
    else environment_update_case w)"

definition codec_environment_case :: "nat\<Rightarrow>environment_update_subject" where
  "codec_environment_case w=(if w=20 then ([(None,finite_payload_syntax [7])],
      [((None,[256]),None)],Install_Artifact (Some []) (finite_payload_syntax [8]))
    else if w=21 then ([(None,finite_payload_syntax [7])],
      [((None,[0]),None),((None,[256]),Some [])],Install_Binding None [] None)
    else codec_environment_previous_case w)"

lemma codec_environment_previous_cases:
  "w<20 \<Longrightarrow> codec_environment_case w=codec_environment_previous_case w"
  by (simp add: codec_environment_case_def)

definition encoded_artifact_path_report where
  "encoded_artifact_path_report use_code slot_code use_decode slot_decode A B u R=(let
    I=encoded_environment_rows use_code slot_code A B;key=use_code u;tree=indexed_artifact_store I;
    inserted=counted_relation_store_insert (key,R) tree
    in (key,counted_store_lookup tree key,snd inserted,relation_store_lookup (fst inserted) key,
      encoded_environment_view use_decode slot_decode (I\<lparr>indexed_artifact_store:=fst inserted\<rparr>)))"

lemma encoded_counted_artifact_insertion:
  "I\<lparr>indexed_artifact_store:=fst (counted_relation_store_insert (use_code u,R)
      (indexed_artifact_store I))\<rparr>=encoded_insert_artifact use_code I u R"
  by (simp add: counted_relation_store_insert_exact encoded_insert_artifact_def)

definition codec_environment_path_comparison where
  "codec_environment_path_comparison n=(let A=[(None,finite_payload_syntax [7])];B=[];u=Some [n];R=finite_payload_syntax [8]
    in (encoded_artifact_path_report use_binary_path address_binary_path decode_use_binary_path decode_address_binary_path A B u R,
        encoded_artifact_path_report digit_use_path digit_address_path read_digit_use_path read_digit_address_path A B u R))"

text \<open>
  The original update reference, conditions, eleven old methods and sixteen
  cases are reused unchanged. Exact encoded methods and encoding faults enter
  the same comparison on actual complete environments. The path report executes
  the actual insertion and retains its full resulting environment, old bucket,
  new bucket and both traversal counts. It does not count only an unrelated
  fixed key. These reports do not yet represent a cached allocation history.
\<close>

end
