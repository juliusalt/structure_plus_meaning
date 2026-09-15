theory Natural_Binary_Digits
  imports Main "HOL-Library.Code_Target_Nat"
begin

function natural_binary_digits :: "nat\<Rightarrow>bool list" where
  "natural_binary_digits 0=[]"
| "natural_binary_digits (Suc n)=(Suc n mod 2=1)#natural_binary_digits (Suc n div 2)"
  by pat_completeness auto
termination by (relation "measure id") auto

fun natural_binary_value :: "bool list\<Rightarrow>nat" where
  "natural_binary_value []=0"
| "natural_binary_value (b#bs)=(if b then 1 else 0)+2*natural_binary_value bs"

lemma natural_binary_decomposition:
  "(n::nat)=(if n mod 2=1 then 1 else 0)+2*(n div 2)"
  by presburger

theorem natural_binary_value_digits [simp]:
  "natural_binary_value (natural_binary_digits n)=n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have smaller: "n div 2<n" using Suc by simp
    have recovered: "natural_binary_value (natural_binary_digits (n div 2))=n div 2"
      by (rule less.IH[OF smaller])
    show ?thesis using recovered natural_binary_decomposition[of n] by (simp add: Suc)
  qed
qed

lemma natural_binary_digits_injective [simp]:
  "natural_binary_digits m=natural_binary_digits n \<longleftrightarrow> m=n"
  by (metis natural_binary_value_digits)

theorem natural_binary_digits_bound:
  "n<2^k \<Longrightarrow> length (natural_binary_digits n)\<le>k"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note induction_hypothesis=Suc.IH
  have input_bound: "n<2^Suc k" by (rule Suc.prems)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have half: "n div 2<2^k" using input_bound by (simp add: power_Suc; presburger)
    have bound: "length (natural_binary_digits (n div 2))\<le>k"
      by (rule induction_hypothesis[OF half])
    show ?thesis using bound by (simp add: Suc)
  qed
qed

export_code natural_binary_digits natural_binary_value checking SML

end
