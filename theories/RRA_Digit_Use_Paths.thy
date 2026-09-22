theory RRA_Digit_Use_Paths
  imports RRA_Digit_Natural_Paths Prefix_Code_Words RRA_Binary_Use_Paths
begin

interpretation digit_words: prefix_word_code digit_natural_path read_digit_natural_path
  by (unfold_locales) (simp_all add: read_digit_natural_path_exact)

definition digit_address_path where
  "digit_address_path word=prefix_word_encoding digit_natural_path word"

definition read_digit_address_path where
  "read_digit_address_path source=read_prefix_word read_digit_natural_path source"

theorem read_digit_address_path_exact [simp]:
  "read_digit_address_path source=Some word \<longleftrightarrow> source=digit_address_path word"
  by (simp add: read_digit_address_path_def digit_address_path_def digit_words.read_exact)

lemma digit_address_path_injective [simp]:
  "digit_address_path xs=digit_address_path ys \<longleftrightarrow> xs=ys"
  by (simp add: digit_address_path_def digit_words.encoding_injective)

fun digit_use_path :: "local_address option\<Rightarrow>bool list" where
  "digit_use_path None=[False]"
| "digit_use_path (Some word)=True#digit_address_path word"

fun read_digit_use_path :: "bool list\<Rightarrow>local_address option option" where
  "read_digit_use_path []=None"
| "read_digit_use_path (False#source)=(if source=[] then Some None else None)"
| "read_digit_use_path (True#source)=map_option Some (read_digit_address_path source)"

theorem read_digit_use_path_exact [simp]:
  "read_digit_use_path source=Some u \<longleftrightarrow> source=digit_use_path u"
proof (cases source)
  case Nil
  then show ?thesis by (cases u) simp_all
next
  case (Cons bit rest)
  then show ?thesis by (cases bit; cases u) auto
qed

lemma digit_use_path_injective [simp]:
  "digit_use_path u=digit_use_path v \<longleftrightarrow> u=v"
  by (cases u; cases v) auto

lemma digit_address_path_length:
  "length (digit_address_path word)=sum_list (map (\<lambda>n. 2*length (natural_binary_digits n)+1) word)"
  by (induction word) (simp_all add: digit_address_path_def digit_natural_path_length)

lemma digit_single_use_path_length:
  "length (digit_use_path (Some [n]))=2*length (natural_binary_digits n)+2"
  by (simp add: digit_address_path_length)

text \<open>
  Every original optional natural use word has an exact injective path and
  complete inverse. None, a present empty word and every tuple boundary remain
  distinct. The generic prefix-word construction is reused at this first word
  composition. No byte bound is introduced by the path representation.
\<close>

end
