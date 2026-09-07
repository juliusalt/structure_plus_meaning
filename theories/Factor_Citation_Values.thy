theory Factor_Citation_Values
  imports Factor_Coordinate_Values
begin

section \<open>Independent optional slot and target-address operands\<close>

fun citation_data_term :: "citation \<Rightarrow> factor_term" where
  "citation_data_term (Local a)=Pair_Term (optional_payload_term None) (optional_payload_term (Some a))"
| "citation_data_term (External k a)=Pair_Term (optional_payload_term (Some k)) (optional_payload_term (Some a))"
| "citation_data_term Local_Whole=Pair_Term (optional_payload_term None) (optional_payload_term None)"
| "citation_data_term (External_Whole k)=Pair_Term (optional_payload_term (Some k)) (optional_payload_term None)"

lemma citation_data_term_injective: "inj citation_data_term"
  by (rule injI; rename_tac c d; case_tac c; case_tac d) auto

lemma citation_data_term_formed [simp]:
  "term_formed (citation_data_term c) \<longleftrightarrow> citation_projection_formed c"
  by (cases c) (auto simp: octets_formed_def)

lemma citation_data_term_self_contained [simp]: "self_contained_term (citation_data_term c)"
  by (cases c) auto

lemma citation_data_local_fields:
  "citation_data_term c=Pair_Term (Payload_Term []) (data_list_term [a]) \<longleftrightarrow>
    (\<exists>b. a=Payload_Term b \<and> c=Local b)"
  by (cases c) auto

lemma citation_data_external_fields:
  assumes "citation_data_term c=Pair_Term (data_list_term [k]) a"
  shows "\<exists>s. k=Payload_Term s \<and> citation_slots c={s}"
  using assms by (cases c) auto

lemma citation_data_external_shape:
  assumes "citation_slots c\<noteq>{}"
  shows "\<exists>s a. citation_data_term c=Pair_Term (data_list_term [Payload_Term s]) a \<and> citation_slots c={s}"
  using assms by (cases c) auto

lemma citation_data_slot_shape:
  "\<exists>Ss a. citation_data_term c=Pair_Term (data_list_term (map Payload_Term Ss)) a \<and>
    distinct Ss \<and> set Ss=citation_slots c"
proof (cases c)
  case (Local r)
  then show ?thesis by (rule_tac x="[]" in exI) auto
next
  case (External k r)
  then show ?thesis by (rule_tac x="[k]" in exI) auto
next
  case Local_Whole
  then show ?thesis by (rule_tac x="[]" in exI) auto
next
  case (External_Whole k)
  then show ?thesis by (rule_tac x="[k]" in exI) auto
qed

lemma citation_data_slot_fields:
  assumes "citation_data_term c=Pair_Term s a"
  shows "\<exists>Ss. s=data_list_term (map Payload_Term Ss) \<and> distinct Ss \<and> set Ss=citation_slots c"
  using citation_data_slot_shape[of c] assms by auto

lemma citation_data_formed_at:
  assumes read: "citation_at R r c I"
  shows "term_formed (citation_data_term c)"
proof -
  have formed: "exact_formed R" and raw: "raw_citation_at R r c I"
    using read by (auto simp: citation_at_def)
  have fields: "\<forall>(p,x)\<in>headed_incidence (object_structure R) r.
    octets_formed p \<and> octets_formed x"
    using formed by (auto simp: exact_formed_def object_formed_def rra_formed_def)
  have literal: "octets_formed v" if "payload_at R d v" for d v
  proof -
    have member: "v\<in>basis_values (object_data R)"
      using payload_at_binding[OF that] by (auto simp: basis_values_def intro: rev_image_eqI)
    show ?thesis using formed member by (auto simp: exact_formed_def)
  qed
  show ?thesis using raw fields
    by (cases rule: raw_citation_at.cases) (auto simp: octets_formed_def dest: literal)
qed

text \<open>
  The first operand is the optional local slot, and the second is the
  optional target address. Absence and a present empty address remain
  distinct. Both use the same zero-or-one payload list; their positions
  supply their roles. No citation constructor name is attached as data.

  This is the recovered citation value, not its containing artifact or
  its interior. Native grammar checking retains those boundaries separately.
  The optional target address is also the occurrence field of exact target
  data, so an ordinary clause can preserve its opaque value.
\<close>

end
