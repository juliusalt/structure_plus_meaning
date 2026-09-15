theory RRA_Use_Codec_Methods
  imports RRA_Use_Codec_Observations
begin

definition read_unchecked_digit_natural where
  "read_unchecked_digit_natural source=map_option
    (\<lambda>(bs,rest). (natural_binary_value bs,rest)) (read_delimited_bit_word source)"

fun read_unchecked_digit_use where
  "read_unchecked_digit_use []=None"
| "read_unchecked_digit_use (False#source)=(if source=[] then Some None else None)"
| "read_unchecked_digit_use (True#source)=map_option Some
    (read_prefix_word read_unchecked_digit_natural source)"

definition use_codec_method :: "nat\<Rightarrow>use_codec" where
  "use_codec_method m=(if m=0 then (use_binary_path,decode_use_binary_path)
    else if m=1 then (digit_use_path,read_digit_use_path)
    else if m=2 then (digit_use_path \<circ> map_option (map (\<lambda>n. n mod 256)),read_digit_use_path)
    else if m=3 then ((\<lambda>u. case u of None \<Rightarrow> digit_use_path (Some [])
      | Some word \<Rightarrow> digit_use_path (Some word)),read_digit_use_path)
    else if m=4 then (digit_use_path,read_digit_use_path \<circ> butlast)
    else if m=5 then (digit_use_path,read_unchecked_digit_use)
    else if m=6 then ((\<lambda>_. []),(\<lambda>_. None))
    else if m=7 then (digit_use_path,(\<lambda>_. None))
    else if m=8 then (rev \<circ> digit_use_path,read_digit_use_path)
    else (rev \<circ> digit_use_path,read_digit_use_path \<circ> rev))"

theorem use_codec_correct_semantics:
  "m\<in>{0,1,9} \<Longrightarrow> f\<in>{0,1,2} \<Longrightarrow>
    use_codec_condition f (use_codec_method m) X"
  by (cases X)
    (auto simp: use_codec_condition_def use_codec_method_def inj_on_def
      One_nat_def split: if_splits; metis rev_rev_ident)

theorem use_codec_digit_budget:
  "m\<in>{1,9} \<Longrightarrow> use_codec_condition 3 (use_codec_method m) X"
  by (cases X)
    (auto simp: use_codec_condition_def use_codec_method_def One_nat_def
      intro: digit_use_path_budget)

end
