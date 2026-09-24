theory RRA_Digit_Natural_Paths
  imports Natural_Binary_Digits Delimited_Bit_Words
begin

definition digit_natural_path where
  "digit_natural_path n=delimited_bit_word (natural_binary_digits n)"

definition read_digit_natural_path where
  "read_digit_natural_path source=(case read_delimited_bit_word source of None \<Rightarrow> None
    | Some (bs,rest) \<Rightarrow> let n=natural_binary_value bs in
      if natural_binary_digits n=bs then Some (n,rest) else None)"

lemma digit_natural_path_nonempty [simp]: "digit_natural_path n\<noteq>[]"
  by (simp add: digit_natural_path_def)

lemma read_digit_natural_path_encoded [simp]:
  "read_digit_natural_path (digit_natural_path n@rest)=Some (n,rest)"
  by (simp add: read_digit_natural_path_def digit_natural_path_def Let_def)

theorem read_digit_natural_path_exact:
  "read_digit_natural_path source=Some (n,rest) \<longleftrightarrow> source=digit_natural_path n@rest"
  by (auto simp: read_digit_natural_path_def digit_natural_path_def Let_def
    read_delimited_bit_word_exact delimited_bit_word_cancel split: option.splits if_splits)

lemma digit_natural_path_cancel:
  "digit_natural_path m@xs=digit_natural_path n@ys \<longleftrightarrow> m=n \<and> xs=ys"
  by (simp add: digit_natural_path_def delimited_bit_word_cancel)

lemma digit_natural_path_length:
  "length (digit_natural_path n)=2*length (natural_binary_digits n)+1"
  by (simp add: digit_natural_path_def delimited_bit_word_length)

theorem digit_natural_path_bound:
  "n<2^k \<Longrightarrow> length (digit_natural_path n)\<le>2*k+1"
  using natural_binary_digits_bound by (simp add: digit_natural_path_length)

text \<open>
  Actual binary digits carry the natural coordinate. A separate prefix code
  keeps its endpoint explicit. The inverse checks the canonical digit word and
  preserves every remaining path position. The bound concerns path length;
  arithmetic and decoding cost, word composition and store adoption require
  their separate accounts.
\<close>

end
