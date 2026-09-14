theory RRA_Binary_Path_Decoding
  imports RRA_Binary_Use_Paths
begin

fun decode_address_binary_path where
  "decode_address_binary_path []=Some []"
| "decode_address_binary_path (False#path)=map_option (Cons 0) (decode_address_binary_path path)"
| "decode_address_binary_path (True#path)=(case decode_address_binary_path path of
    Some (n#ns) \<Rightarrow> Some (Suc n#ns) | _ \<Rightarrow> None)"

lemma decode_address_natural_prefix:
  "decode_address_binary_path (natural_binary_path n @ path)=
    map_option (Cons n) (decode_address_binary_path path)"
  by (induction n) (auto split: option.splits)

lemma decode_address_encoded [simp]:
  "decode_address_binary_path (address_binary_path word)=Some word"
  by (induction word) (simp_all add: decode_address_natural_prefix)

lemma decode_address_binary_path_sound:
  "decode_address_binary_path path=Some word \<Longrightarrow> path=address_binary_path word"
proof (induction path arbitrary: word)
  case Nil
  then show ?case by simp
next
  case (Cons b path)
  then show ?case by (cases b) (auto split: option.splits list.splits)
qed

theorem decode_address_binary_path_exact [simp]:
  "decode_address_binary_path path=Some word \<longleftrightarrow> path=address_binary_path word"
  using decode_address_binary_path_sound by auto

fun decode_use_binary_path :: "bool list \<Rightarrow> local_address option option" where
  "decode_use_binary_path []=None"
| "decode_use_binary_path (False#path)=(if path=[] then Some None else None)"
| "decode_use_binary_path (True#path)=map_option Some (decode_address_binary_path path)"

theorem decode_use_binary_path_exact [simp]:
  "decode_use_binary_path path=Some u \<longleftrightarrow> path=use_binary_path u"
proof (cases path)
  case Nil
  then show ?thesis by (cases u) simp_all
next
  case (Cons b rest)
  then show ?thesis by (cases b; cases u) auto
qed

text \<open>
  The decoder recognizes exactly the complete coordinate encoding, including
  absent uses, present empty words, and every natural component. A malformed
  path cannot acquire the meaning of another use or erase a tuple boundary.
\<close>

end
