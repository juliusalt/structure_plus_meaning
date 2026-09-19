theory Finite_Binary_Values
  imports Factor_Executable_Terms Natural_Binary_Digits
begin

section \<open>A bit path and a binary natural are one flat payload\<close>

definition finite_storage_path_value where
 "finite_storage_path_value path=Finite_Payload (map (\<lambda>b. if b then 1 else 0) path)"

lemma finite_storage_path_value_injective [intro]: "inj finite_storage_path_value"
proof -
 have digit: "inj (\<lambda>b. if b then (1::nat) else 0)" by (auto simp: inj_def)
 show ?thesis by (rule injI) (simp add: finite_storage_path_value_def inj_map_eq_map[OF digit])
qed

lemma finite_storage_path_value_formed [simp]: "finite_term_formed (finite_storage_path_value path)"
  by (auto simp: finite_storage_path_value_def octets_formed_def)

definition finite_binary_natural_value where
 "finite_binary_natural_value n=finite_storage_path_value (natural_binary_digits n)"

lemma finite_binary_natural_value_injective [intro]: "inj finite_binary_natural_value"
 by (rule injI) (simp add: finite_binary_natural_value_def inj_eq[OF finite_storage_path_value_injective])

lemma finite_binary_natural_value_formed [simp]: "finite_term_formed (finite_binary_natural_value n)"
  by (simp add: finite_binary_natural_value_def)

text \<open>A bit path is one flat native payload of its exact zero/one digits, and a natural is the
 path of its binary digits. The presentation is injective, its size is the number of digits, and
 its octets stay within the payload bound whatever the magnitude. It changes the presentation, not
 the path, the number or any reading. Presented storage notions and the candidates of native
 questions both use it.\<close>

end
