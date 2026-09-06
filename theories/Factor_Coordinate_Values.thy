theory Factor_Coordinate_Values
  imports Factor_Self_Contained_Terms
begin

section \<open>Exact finite coordinates as data\<close>

fun natural_data_term :: "nat \<Rightarrow> factor_term" where
  "natural_data_term 0=Payload_Term []"
| "natural_data_term (Suc n)=Pair_Term (Payload_Term []) (natural_data_term n)"

lemma natural_data_term_injective: "inj natural_data_term"
proof -
  have "natural_data_term n=natural_data_term m \<longleftrightarrow> n=m" for n m
    by (induction n arbitrary: m) (case_tac m; auto)+
  then show ?thesis by (auto simp: inj_def)
qed

lemma natural_data_term_formed [simp]: "term_formed (natural_data_term n)"
  by (induction n) (auto simp: octets_formed_def)

lemma natural_data_term_self_contained [simp]: "self_contained_term (natural_data_term n)"
  by (induction n) auto

fun use_data_term :: "local_address option \<Rightarrow> factor_term" where
  "use_data_term None=Payload_Term []"
| "use_data_term (Some a)=
    Pair_Term (data_list_term (map natural_data_term a)) (Payload_Term [])"

lemma use_data_term_injective: "inj use_data_term"
  by (rule injI; rename_tac u v; case_tac u; case_tac v)
     (auto simp: data_list_term_injective injective_mapped_lists[OF natural_data_term_injective])

lemma use_data_term_formed [simp]: "term_formed (use_data_term u)"
  by (cases u) (auto simp: data_list_term_formed octets_formed_def)

lemma use_data_term_self_contained [simp]: "self_contained_term (use_data_term u)"
  by (cases u) (auto simp: data_list_term_self_contained)

definition site_data_term :: "local_address option \<Rightarrow> local_address \<Rightarrow> factor_term" where
  "site_data_term u r=Pair_Term (use_data_term u) (Payload_Term r)"

lemma site_data_term_eq [simp]:
  "site_data_term u r=site_data_term v s \<longleftrightarrow> u=v \<and> r=s"
  by (auto simp: site_data_term_def dest: injD[OF use_data_term_injective])

lemma site_data_term_formed [simp]:
  "term_formed (site_data_term u r)\<longleftrightarrow>octets_formed r"
  by (simp add: site_data_term_def)

lemma site_data_term_self_contained [simp]: "self_contained_term (site_data_term u r)"
  by (simp add: site_data_term_def)

text \<open>
  This is the common finite data representation of an optional coordinate.
  Environment-use coordinates and optional occurrence addresses use the same
  representation. The representation alone assigns neither role to a value.
\<close>

end
