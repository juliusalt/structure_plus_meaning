theory Factor_Finite_Sequence_Reading
  imports Factor_Executable_Data_Values
begin

section \<open>Read exactly the original finite data sequence\<close>

fun finite_data_sequence_elements :: "finite_factor_term\<Rightarrow>finite_factor_term list option" where
  "finite_data_sequence_elements (Finite_Target a)=None"
| "finite_data_sequence_elements (Finite_Payload b)=(if b=[] then Some [] else None)"
| "finite_data_sequence_elements (Finite_Pair x y)=map_option (Cons x) (finite_data_sequence_elements y)"

lemma finite_data_sequence_elements_exact:
  "finite_data_sequence_elements t=Some xs \<longleftrightarrow> t=finite_data_sequence xs"
  by (induction t arbitrary: xs) (case_tac xs; auto split: option.splits)+

lemma finite_data_sequence_elements_decode:
  "finite_data_sequence_elements t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map decode_finite_term xs)"
  by (simp only: finite_data_sequence_elements_exact decode_finite_data_sequence[symmetric]
    decode_finite_term_injective)

lemma finite_data_sequence_elements_complete:
  assumes "decode_finite_term t=data_list_term xs"
  shows "\<exists>ys. finite_data_sequence_elements t=Some ys \<and> map decode_finite_term ys=xs"
  using assms
proof (induction t arbitrary: xs)
  case (Finite_Target a)
  then show ?case by (cases xs) auto
next
  case (Finite_Payload b)
  have fields: "b=[] \<and> xs=[]" using Finite_Payload.prems by (cases xs) auto
  show ?case by (rule exI[of _ "[]"]) (use fields in simp)
next
  case (Finite_Pair x y)
  obtain z zs where fields: "xs=z#zs" "decode_finite_term y=data_list_term zs"
    "decode_finite_term x=z" using Finite_Pair.prems by (cases xs) auto
  obtain ys where tail: "finite_data_sequence_elements y=Some ys" "map decode_finite_term ys=zs"
    using Finite_Pair.IH(2)[OF fields(2)] by blast
  show ?case by (rule exI[of _ "x#ys"]) (use fields tail in simp)
qed

lemma finite_data_sequence_elements_absent:
  "finite_data_sequence_elements t=None \<longleftrightarrow> \<not>(\<exists>xs. decode_finite_term t=data_list_term xs)"
proof
  assume none: "finite_data_sequence_elements t=None"
  show "\<not>(\<exists>xs. decode_finite_term t=data_list_term xs)"
  proof
    assume "\<exists>xs. decode_finite_term t=data_list_term xs"
    then obtain xs where shape: "decode_finite_term t=data_list_term xs" by blast
    obtain ys where "finite_data_sequence_elements t=Some ys"
      using finite_data_sequence_elements_complete[OF shape] by blast
    then show False using none by simp
  qed
next
  assume absent: "\<not>(\<exists>xs. decode_finite_term t=data_list_term xs)"
  show "finite_data_sequence_elements t=None"
  proof (cases "finite_data_sequence_elements t")
    case None
    then show ?thesis by simp
  next
    case (Some xs)
    have "decode_finite_term t=data_list_term (map decode_finite_term xs)"
      using Some by (simp only: finite_data_sequence_elements_decode)
    then show ?thesis using absent by blast
  qed
qed

end
