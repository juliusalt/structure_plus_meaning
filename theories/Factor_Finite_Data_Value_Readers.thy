theory Factor_Finite_Data_Value_Readers
  imports Factor_Executable_Data_Values Option_List_Maps
begin

fun finite_payload_value_read :: "finite_factor_term \<Rightarrow> octets option" where
  "finite_payload_value_read (Finite_Payload p)=Some p"
| "finite_payload_value_read (Finite_Pair x y)=None"
| "finite_payload_value_read (Finite_Target a)=None"

lemma finite_payload_value_read_exact:
  "finite_payload_value_read t=Some p \<longleftrightarrow> decode_finite_term t=Payload_Term p"
  by (cases t) simp_all

fun finite_data_list_read :: "finite_factor_term \<Rightarrow> finite_factor_term list option" where
  "finite_data_list_read (Finite_Payload p)=(if p=[] then Some [] else None)"
| "finite_data_list_read (Finite_Pair x y)=map_option (Cons x) (finite_data_list_read y)"
| "finite_data_list_read (Finite_Target a)=None"

lemma finite_data_list_read_sequence:
  "finite_data_list_read t=Some xs \<longleftrightarrow> t=finite_data_sequence xs"
  by (induction t arbitrary: xs) (case_tac xs; auto split: if_splits)+

theorem finite_data_list_read_exact:
  "finite_data_list_read t=Some xs \<longleftrightarrow>
    decode_finite_term t=data_list_term (map decode_finite_term xs)"
  by (simp only: finite_data_list_read_sequence decode_finite_term_injective[symmetric]
    decode_finite_data_sequence)

lemma finite_data_list_read_complete:
  assumes source: "decode_finite_term t=data_list_term xs"
  obtains ys where "finite_data_list_read t=Some ys" "map decode_finite_term ys=xs"
proof -
  have "\<exists>ys. t=finite_data_sequence ys \<and> map decode_finite_term ys=xs"
    using source
  proof (induction xs arbitrary: t)
    case Nil
    then show ?case by (cases t) auto
  next
    case (Cons x xs)
    obtain a b where shape: "t=Finite_Pair a b" and head: "decode_finite_term a=x"
      and tail: "decode_finite_term b=data_list_term xs"
      using Cons.prems by (cases t) auto
    obtain ys where body: "b=finite_data_sequence ys" "map decode_finite_term ys=xs"
      using Cons.IH[OF tail] by blast
    show ?case by (rule exI[of _ "a#ys"]) (simp add: shape head body)
  qed
  then show ?thesis using that by (simp only: finite_data_list_read_sequence; blast)
qed

definition finite_data_list_values where
  "finite_data_list_values read t=(case finite_data_list_read t of None \<Rightarrow> None
    | Some xs \<Rightarrow> those (map read xs))"

lemma finite_data_list_values_result:
  "finite_data_list_values read t=Some ys \<longleftrightarrow>
    (\<exists>xs. finite_data_list_read t=Some xs \<and> list_all2 (\<lambda>x y. read x=Some y) xs ys)"
  by (auto simp: finite_data_list_values_def those_map_result split: option.splits)

lemma finite_data_list_values_exact:
  "finite_data_list_values read t=Some ys \<longleftrightarrow>
    (\<exists>xs. decode_finite_term t=data_list_term (map decode_finite_term xs) \<and>
      list_all2 (\<lambda>x y. read x=Some y) xs ys)"
  by (simp only: finite_data_list_values_result finite_data_list_read_exact)

theorem finite_data_list_values_present:
  assumes element: "\<And>v a. read v=Some a \<longleftrightarrow> P a (decode_finite_term v)"
  shows "finite_data_list_values read t=Some xs \<longleftrightarrow>
    (\<exists>us. decode_finite_term t=data_list_term us \<and> list_all2 P xs us)"
proof -
  have entries: "list_all2 (\<lambda>v a. read v=Some a) vs xs \<longleftrightarrow>
    list_all2 P xs (map decode_finite_term vs)" for vs
    by (auto simp: element list_all2_conv_all_nth)
  show ?thesis
  proof
    assume result: "finite_data_list_values read t=Some xs"
    obtain vs where source: "decode_finite_term t=data_list_term (map decode_finite_term vs)"
      and rows: "list_all2 (\<lambda>v a. read v=Some a) vs xs"
      using result by (simp only: finite_data_list_values_exact; blast)
    show "\<exists>us. decode_finite_term t=data_list_term us \<and> list_all2 P xs us"
      using source rows by (simp only: entries; blast)
  next
    assume "\<exists>us. decode_finite_term t=data_list_term us \<and> list_all2 P xs us"
    then obtain us where source: "decode_finite_term t=data_list_term us"
      and rows: "list_all2 P xs us" by blast
    obtain vs where parsed: "finite_data_list_read t=Some vs"
      and decoded: "map decode_finite_term vs=us"
      by (rule finite_data_list_read_complete[OF source])
    have related: "list_all2 (\<lambda>v a. read v=Some a) vs xs"
      using rows by (simp only: entries decoded)
    show "finite_data_list_values read t=Some xs"
      using parsed related by (simp only: finite_data_list_values_result; blast)
  qed
qed

theorem finite_data_list_values_encoded:
  assumes element: "\<And>v a. read v=Some a \<longleftrightarrow> decode_finite_term v=code a"
  shows "finite_data_list_values read t=Some ys \<longleftrightarrow>
    decode_finite_term t=data_list_term (map code ys)"
proof -
  have reference: "finite_data_list_values read t=Some ys \<longleftrightarrow>
    (\<exists>us. decode_finite_term t=data_list_term us \<and> list_all2 (\<lambda>a v. v=code a) ys us)"
    by (rule finite_data_list_values_present) (rule element)
  show ?thesis by (simp only: reference list_all2_function; auto)
qed

export_code finite_payload_value_read finite_data_list_read finite_data_list_values checking SML

text \<open>
  The list reader recovers the actual sequence, including repeated elements.
  Element interpretation uses the existing strict optional traversal. These
  operations do not supply collection distinctness or artifact formation;
  their callers must retain the independently required checks.
\<close>

end
