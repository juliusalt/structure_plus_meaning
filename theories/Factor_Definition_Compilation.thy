theory Factor_Definition_Compilation
  imports Factor_Definition_Encoding
begin

section \<open>Compiling an arbitrary complete identified clause family\<close>

lemma schema_family_variant_from_lists:
  assumes lengths: "length os=length Ss" "length ss=length As"
    and distinct: "distinct ss" and injective: "inj_on h (set os)" and rekey: "map h os=ss"
    and variants: "\<forall>i<length Ss. schema_alpha_variant (Ss!i) (As!i)"
  shows "schema_family_variant h (set (zip os Ss)) (set (zip ss As))"
proof -
  have same_length: "length ss=length os" using arg_cong[OF rekey, of length] by simp
  have domain: "rel_dom (set (zip ss As))=h ` rel_dom (set (zip os Ss))"
    using arg_cong[OF rekey, of set]
    by (simp only: zip_domain[OF lengths(1)] zip_domain[OF lengths(2)] set_map)
  have entries: "\<exists>A. (h c,A)\<in>set (zip ss As) \<and> schema_alpha_variant S A"
    if member: "(c,S)\<in>set (zip os Ss)" for c S
  proof -
    obtain i where index: "i<length os" "i<length Ss" "c=os!i" "S=Ss!i"
      using member by (auto simp: in_set_zip)
    have key: "h c=ss!i" using rekey index(1,3) by (metis nth_map)
    have target: "(h c,As!i)\<in>set (zip ss As)"
      using index(1) lengths(2) same_length key by (auto simp: in_set_zip)
    have alpha: "schema_alpha_variant S (As!i)" using variants index(2,4) by blast
    show ?thesis using target alpha by blast
  qed
  have functional: "single_valued (set (zip ss As))" by (rule single_valued_zip[OF distinct])
  show ?thesis using injective domain entries functional
    by (simp add: schema_family_variant_def zip_domain[OF lengths(1)])
qed

theorem definition_compilation_total:
  fixes p :: "'a term_pattern"
    and Cs :: "('c \<times> ('a,'s,local_address option definition_site) factor_schema) set"
  assumes pf: "pattern_formed p" and fin: "finite Cs" and sv: "single_valued Cs"
    and formed: "\<forall>S\<in>rel_ran Cs. schema_formed S"
    and addresses: "\<forall>S\<in>rel_ran Cs. \<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
  shows "\<exists>R f h D L C. exact_formed R \<and> bag_count (object_data R) = (\<lambda>_. 0) \<and>
    [] \<in> rra_carrier (object_structure R) \<and> inj_on f (pattern_variables p) \<and>
    schema_family_variant h Cs D \<and> reference_table_formed L C \<and>
    rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R) \<and>
    rel_ran C = (\<Union>S\<in>rel_ran Cs. schema_dependencies S) \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_definition_at E u [] (rename_pattern f p) D)"
proof -
  obtain os :: "'c list" and Ss :: "('a,'s,local_address option definition_site) factor_schema list" where enumeration:
    "length os = length Ss" "distinct os" "set (zip os Ss) = Cs"
    using finite_functional_list[OF fin sv] by metis
  have source_range: "rel_ran Cs = set Ss" using zip_range[OF enumeration(1)] enumeration(3) by simp
  have all_formed: "\<forall>S\<in>set Ss. schema_formed S" using formed source_range by simp
  have all_addresses: "\<forall>S\<in>set Ss. \<forall>d\<in>schema_dependencies S. octets_formed (snd d)"
    using addresses source_range by simp
  obtain R :: exact_artifact and f :: "'a \<Rightarrow> local_address" and ss :: "local_address list"
    and As :: "local_address option native_schema list" and L :: "(local_address \<times> exact_artifact) set"
    and C :: "(local_address \<times> local_address option definition_site) set" where built:
    "exact_formed R" "bag_count (object_data R) = (\<lambda>_. 0)" "[] \<in> rra_carrier (object_structure R)"
    "inj_on f (pattern_variables p)" "length ss = length Ss" "distinct ss" "length As = length Ss"
    "\<forall>i<length Ss. schema_alpha_variant (Ss!i) (As!i)"
    "reference_table_formed L C" "rel_dom L \<union> rel_dom C \<subseteq> rra_carrier (object_structure R)"
    "rel_ran C = (\<Union>S\<in>set Ss. schema_dependencies S)"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_definition_at E u [] (rename_pattern f p) (set (zip ss As))"
    using definition_list_syntax_total[OF pf all_formed all_addresses] by metis
  have lengths: "length os = length ss" using enumeration(1) built(5) by simp
  obtain h where rekey: "inj_on h (set os)" "map h os = ss"
    using distinct_list_rekey[OF lengths enumeration(2) built(6)] by metis
  let ?D = "set (zip ss As)"
  have dl: "length ss = length As" using built(5,7) by simp
  have family: "schema_family_variant h Cs ?D"
    using schema_family_variant_from_lists[OF enumeration(1) dl built(6) rekey built(8)] enumeration(3) by simp
  have range: "rel_ran C = (\<Union>S\<in>rel_ran Cs. schema_dependencies S)" using built(11) source_range by simp
  show ?thesis by (rule exI[of _ R], rule exI[of _ f], rule exI[of _ h], rule exI[of _ ?D],
      rule exI[of _ L], rule exI[of _ C]) (use built(1-4,9,10,12) family range in blast)
qed

text \<open>
  Source clause identifiers are injectively mapped to the complete native
  family sockets. Every output clause has a source clause, and every source
  clause has its corresponding output. The correspondence preserves the full
  dependency set and all rule instances. Enumeration is a proof choice and
  introduces no ordering requirement on the source family.
\<close>

end
