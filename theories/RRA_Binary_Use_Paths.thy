theory RRA_Binary_Use_Paths
  imports RRA_Finite_Environments
begin

fun natural_binary_path where
  "natural_binary_path 0=[False]"
| "natural_binary_path (Suc n)=True#natural_binary_path n"

lemma natural_binary_path_nonempty [simp]: "natural_binary_path n\<noteq>[]"
  by (cases n) simp_all

lemma natural_binary_path_cancel:
  "natural_binary_path m @ xs=natural_binary_path n @ ys \<longleftrightarrow> m=n \<and> xs=ys"
  by (induction m arbitrary: n) (case_tac n; auto)+

fun address_binary_path where
  "address_binary_path []=[]"
| "address_binary_path (n#ns)=natural_binary_path n @ address_binary_path ns"

lemma address_binary_path_injective [simp]:
  "address_binary_path xs=address_binary_path ys \<longleftrightarrow> xs=ys"
  by (induction xs arbitrary: ys) (case_tac ys; auto simp: natural_binary_path_cancel)+

fun use_binary_path :: "local_address option \<Rightarrow> bool list" where
  "use_binary_path None=[False]"
| "use_binary_path (Some word)=True#address_binary_path word"

lemma use_binary_path_injective [simp]: "use_binary_path u=use_binary_path v \<longleftrightarrow> u=v"
  by (cases u; cases v) auto

lemma natural_binary_path_length: "length (natural_binary_path n)=Suc n"
  by (induction n) simp_all

lemma address_binary_path_length:
  "length (address_binary_path word)=sum_list (map Suc word)"
  by (induction word) (simp_all add: natural_binary_path_length)

text \<open>
  Every natural use word has an injective binary path. None and the empty
  present word remain different uses. The transparent unary component encoding
  imposes no byte restriction. Its exact path length is explicit and may grow
  with the chosen coordinates; it does not depend on the stored history.
\<close>

end
