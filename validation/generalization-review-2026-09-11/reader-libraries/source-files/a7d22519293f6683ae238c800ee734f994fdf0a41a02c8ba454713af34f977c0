theory Factor_Artifact_Values
  imports Factor_Self_Contained_Terms
begin

section \<open>Complete exact artifact values as self-contained terms\<close>

definition address_pair_data ::
  "(local_address\<times>octets) \<Rightarrow> factor_term" where
  "address_pair_data z = Pair_Term (Payload_Term (fst z)) (Payload_Term (snd z))"

definition incidence_data ::
  "(local_address\<times>local_address\<times>local_address) \<Rightarrow> factor_term" where
  "incidence_data z =
    Pair_Term (Payload_Term (fst z)) (address_pair_data (snd z))"

lemma address_pair_data_injective: "inj address_pair_data"
  by (rule injI) (auto simp: address_pair_data_def)

lemma incidence_data_injective: "inj incidence_data"
  by (rule injI) (auto simp: incidence_data_def address_pair_data_def)

definition artifact_data_term ::
  "local_address list \<Rightarrow> (local_address\<times>local_address\<times>local_address) list \<Rightarrow>
    (local_address\<times>octets) list \<Rightarrow> (local_address\<times>octets) list \<Rightarrow> factor_term" where
  "artifact_data_term A E B F =
    Pair_Term (data_list_term (map Payload_Term A))
      (Pair_Term (data_list_term (map incidence_data E))
        (Pair_Term (data_list_term (map address_pair_data B))
          (data_list_term (map address_pair_data F))))"

lemma artifact_data_term_exact:
  "artifact_data_term A E B F=artifact_data_term A' E' B' F' \<longleftrightarrow>
    A=A' \<and> E=E' \<and> B=B' \<and> F=F'"
proof -
  have injective: "inj Payload_Term" by (rule injI) simp
  show ?thesis
    by (simp add: artifact_data_term_def data_list_term_injective
      injective_mapped_lists[OF injective]
      injective_mapped_lists[OF incidence_data_injective]
      injective_mapped_lists[OF address_pair_data_injective])
qed

lemma artifact_data_term_self_contained:
  "self_contained_term (artifact_data_term A E B F)"
  by (simp add: artifact_data_term_def data_list_term_self_contained
    incidence_data_def address_pair_data_def)

lemma artifact_data_term_formed:
  assumes enumeration: "artifact_enumeration R A E B F"
  shows "term_formed (artifact_data_term A E B F)"
proof -
  let ?U = "rra_carrier (object_structure R)"
  let ?D = "object_data R"
  have rf: "exact_formed R" and atoms: "set A=?U"
    and edges: "set E=rra_incidence (object_structure R)"
    and bags: "set B=bag_support ?D"
    and fun_entries: "set F=functional_bindings ?D"
    using artifact_enumeration_material[OF enumeration] by auto
  have addresses: "\<forall>a\<in>?U. octets_formed a"
    and values_formed: "\<forall>v\<in>basis_values ?D. octets_formed v"
    and shape: "rra_formed (object_structure R)" and data: "basis_formed ?U ?D"
    using rf by (auto simp: exact_formed_def object_formed_def)
  have edge_fields: "\<And>e a b. (e,a,b)\<in>set E \<Longrightarrow>
    octets_formed e \<and> octets_formed a \<and> octets_formed b"
    using addresses shape edges by (auto simp: rra_formed_def)
  have attachment_fields: "\<And>a v. (a,v)\<in>set B \<union> set F \<Longrightarrow>
    octets_formed a \<and> octets_formed v"
  proof -
    fix a v assume member: "(a,v)\<in>set B \<union> set F"
    have inside: "(a,v)\<in>bag_support ?D \<union> functional_bindings ?D"
      using member bags fun_entries by simp
    have address: "a\<in>?U" using inside data by (auto simp: basis_formed_def)
    have datum: "v\<in>basis_values ?D"
      using imageI[OF inside, of snd] by (simp add: basis_values_def)
    show "octets_formed a \<and> octets_formed v"
      using addresses values_formed address datum by blast
  qed
  show ?thesis using addresses atoms edge_fields attachment_fields
    by (auto simp: artifact_data_term_def data_list_term_formed
      incidence_data_def address_pair_data_def split: prod.splits; blast)
qed

definition artifact_value_presents ::
  "exact_artifact \<Rightarrow> factor_term \<Rightarrow> bool" where
  "artifact_value_presents R t \<longleftrightarrow>
    (\<exists>A E B F. artifact_enumeration R A E B F \<and> t=artifact_data_term A E B F)"

lemma artifact_value_presents_formed:
  assumes "artifact_value_presents R t"
  shows "exact_formed R \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F"
    and encoded: "t=artifact_data_term A E B F"
    using assms unfolding artifact_value_presents_def by blast
  show ?thesis using artifact_enumeration_material(1)[OF enumeration]
    artifact_data_term_formed[OF enumeration] artifact_data_term_self_contained encoded by simp
qed

theorem artifact_value_presents_total:
  assumes "exact_formed R"
  shows "\<exists>t. artifact_value_presents R t"
  using artifact_enumeration_exists[OF assms]
  unfolding artifact_value_presents_def by blast

theorem artifact_value_presents_unique:
  assumes first: "artifact_value_presents R t" and second: "artifact_value_presents S t"
  shows "R=S"
proof -
  obtain A E B F where left: "artifact_enumeration R A E B F" "t=artifact_data_term A E B F"
    using first unfolding artifact_value_presents_def by blast
  obtain A' E' B' F' where right: "artifact_enumeration S A' E' B' F'"
    "t=artifact_data_term A' E' B' F'"
    using second unfolding artifact_value_presents_def by blast
  have same: "A=A' \<and> E=E' \<and> B=B' \<and> F=F'"
    using left(2) right(2) artifact_data_term_exact by blast
  show ?thesis using left(1) right(1) same by (simp add: artifact_enumeration_def)
qed

section \<open>Recovery depends on the containing artifact alone\<close>

definition artifact_value_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow>
    local_address set \<Rightarrow> bool" where
  "artifact_value_quoted_at C r R I \<longleftrightarrow>
    (\<exists>t. artifact_value_presents R t \<and> self_contained_quoted_at C r t I)"

theorem artifact_value_quoted_unique:
  assumes first: "artifact_value_quoted_at C r R I"
    and second: "artifact_value_quoted_at C r S J"
  shows "R=S \<and> I=J"
proof -
  obtain t where left: "artifact_value_presents R t" "self_contained_quoted_at C r t I"
    using first unfolding artifact_value_quoted_at_def by blast
  obtain v where right: "artifact_value_presents S v" "self_contained_quoted_at C r v J"
    using second unfolding artifact_value_quoted_at_def by blast
  have same: "t=v \<and> I=J" by (rule self_contained_quoted_unique[OF left(2) right(2)])
  have presented: "artifact_value_presents S t" using right(1) same by simp
  show ?thesis using artifact_value_presents_unique[OF left(1) presented] same by blast
qed

theorem artifact_value_quoted_total:
  assumes formed: "exact_formed R"
  shows "\<exists>C I. exact_formed C \<and> artifact_value_quoted_at C [] R I \<and>
    rra_carrier (object_structure C)=I"
proof -
  obtain t where present: "artifact_value_presents R t"
    using artifact_value_presents_total[OF formed] by blast
  have tf: "term_formed t" and closed: "self_contained_term t"
    using artifact_value_presents_formed[OF present] by auto
  have quote: "self_contained_quoted_at (term_syntax t) [] t (term_syntax_interior t)"
    and source: "exact_formed (term_syntax t)"
    and complete: "rra_carrier (object_structure (term_syntax t))=term_syntax_interior t"
    using self_contained_quotation_total[OF tf closed] by auto
  have read: "artifact_value_quoted_at (term_syntax t) [] R (term_syntax_interior t)"
    using present quote unfolding artifact_value_quoted_at_def by blast
  show ?thesis
    by (rule exI[of _ "term_syntax t"], rule exI[of _ "term_syntax_interior t"])
       (use source read complete in blast)
qed

lemma artifact_value_quoted_in_environment:
  assumes read: "artifact_value_quoted_at C r R I"
    and ef: "environment_formed E" and source: "artifact_at E u C"
  shows "\<exists>t. artifact_value_presents R t \<and> term_quoted_at E u r t I {}"
proof -
  obtain t where present: "artifact_value_presents R t"
    and quote: "self_contained_quoted_at C r t I"
    using read unfolding artifact_value_quoted_at_def by blast
  have native: "term_quoted_at E u r t I {}"
    by (rule self_contained_quoted_in_environment[OF quote ef source])
  show ?thesis using present native by blast
qed

text \<open>
  This profile presents an exact artifact as data: every original address,
  every ordered incidence triple, every counted attachment occurrence, and
  every functional attachment. Repetition in the counted list preserves
  multiplicity. The three set-like fields have no repeated entry and admit
  every complete order. Original addresses and opaque values remain exact.

  The value can be recovered from a complete native quotation without any
  external binding. Different outer environments therefore cannot change the
  recovered artifact. This is a representation theorem, not a new truth rule
  or a quotient of exact artifacts under structural isomorphism.
\<close>

end
