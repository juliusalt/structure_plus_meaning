theory Factor_Slot_Observations
  imports Factor_Material_Instantiation Factor_Presentation_Dependencies
begin

section \<open>Finite substitutions witness syntax without imposing truth\<close>

lemma finite_scope_has_bindings:
  assumes "finite V"
  shows "\<exists>xs :: ('a\<times>factor_term) list. distinct xs \<and> term_bindings_formed V (set xs)"
proof -
  let ?B="image (\<lambda>a. (a,Payload_Term [])) V"
  obtain xs where rows: "distinct xs" "set xs=?B"
    using finite_distinct_list[of ?B] assms by auto
  have table: "term_bindings_formed V (set xs)"
    using assms by (auto simp: rows term_bindings_formed_def single_valued_def rel_dom_def octets_formed_def)
  show ?thesis using rows(1) table by blast
qed

lemma selected_payload_list:
  assumes formed: "term_formed (data_list_term (map Payload_Term xs))"
  shows "selected_data_member t (data_list_term (map Payload_Term xs)) \<longleftrightarrow>
    (\<exists>a\<in>set xs. t=Payload_Term a)"
  using formed by (auto simp: selected_data_member_exact data_list_term_injective data_list_term_formed)

lemma pattern_slot_observation:
  assumes quote: "pattern_quoted_at E u (set Vs) r p I K"
    and source: "environment_value_presents E e"
    and scope: "distinct Vs" "\<forall>a\<in>set Vs. octets_formed a"
    and slot: "k\<in>K"
  obtains b t w i ks where
    "(55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      b (Payload_Term r) t w i ks)\<in>positive_meaning pattern_instantiation_system"
    "selected_data_member (Payload_Term k) ks"
proof -
  obtain xs where bindings: "distinct xs" "term_bindings_formed (set Vs) (set xs)"
    using finite_scope_has_bindings[of "set Vs"] by auto
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))
      \<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use scope bindings in blast)
  obtain Us Is Ks where order: "distinct Us" "distinct Is" "distinct Ks"
    and sets: "set Us=pattern_variables p" "set Is=I" "set Ks=K"
    using finite_distinct_list[of "pattern_variables p"] finite_distinct_list[of I]
      finite_distinct_list[of K] pattern_quoted_boundary[OF quote] by auto
  have formed: "pattern_formed p" "pattern_variables p\<subseteq>set Vs"
    using pattern_quoted_formed[OF quote] by auto
  obtain t where inst: "pattern_instance (set xs) p t"
    using scoped_pattern_has_one_instance[OF bindings(2) formed] by blast
  have reading: "(55,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) t (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning pattern_instantiation_system"
    by (rule pattern_instantiation_complete[OF quote source table refl order sets inst])
  have slots_formed: "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]] by auto
  have member: "selected_data_member (Payload_Term k) (data_list_term (map Payload_Term Ks))"
    using slot sets(3) by (simp add: selected_payload_list[OF slots_formed])
  show thesis by (rule that[OF reading member])
qed

lemma scoped_slot_observation:
  assumes quote: "scoped_pattern_at E u r p I K"
    and source: "environment_value_presents E e" and slot: "k\<in>K"
  obtains b t i ks where
    "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r) b t i ks)
      \<in>positive_meaning scoped_instantiation_system"
    "selected_data_member (Payload_Term k) ks"
proof -
  obtain xs where bindings: "distinct xs" "term_bindings_formed (pattern_variables p) (set xs)"
    using finite_scope_has_bindings[of "pattern_variables p"] by auto
  obtain Is Ks where order: "distinct Is" "distinct Ks" and sets: "set Is=I" "set Ks=K"
    using finite_distinct_list[of I] finite_distinct_list[of K] scoped_pattern_formed[OF quote] by blast
  obtain t where reading: "(56,scoped_instantiation_argument e (use_data_term u) (Payload_Term r)
      (binding_rows_term xs) t (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning scoped_instantiation_system"
    using scoped_instantiation_total[OF quote source bindings(2,1) order sets] by blast
  have slots_formed: "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]] by auto
  have member: "selected_data_member (Payload_Term k) (data_list_term (map Payload_Term Ks))"
    using slot sets(2) by (simp add: selected_payload_list[OF slots_formed])
  show thesis by (rule that[OF reading member])
qed

lemma prospective_slot_observation:
  assumes call: "prospective_call_at E u (set Vs) r d p I K"
    and source: "environment_value_presents E e"
    and scope: "distinct Vs" "\<forall>a\<in>set Vs. octets_formed a"
    and slot: "k\<in>K"
  obtains b d' t w i ks where
    "(57,prospective_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      b (Payload_Term r) d' t w i ks)\<in>positive_meaning prospective_instantiation_system"
    "selected_data_member (Payload_Term k) ks"
proof -
  obtain xs where bindings: "distinct xs" "term_bindings_formed (set Vs) (set xs)"
    using finite_scope_has_bindings[of "set Vs"] by auto
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))
      \<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use scope bindings in blast)
  obtain Us Is Ks where order: "distinct Us" "distinct Is" "distinct Ks"
    and sets: "set Us=pattern_variables p" "set Is=I" "set Ks=K"
    using finite_distinct_list[of "pattern_variables p"] finite_distinct_list[of I]
      finite_distinct_list[of K] prospective_call_formed[OF call] by auto
  obtain du da where site: "d=(du,da)" by (cases d)
  have actual: "prospective_call_at E u (set Vs) r (du,da) p I K" using call by (simp only: site)
  obtain t where reading:
    "(57,prospective_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) (site_data_term du da) t (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning prospective_instantiation_system"
    using prospective_instantiation_total[OF actual source table order sets] by blast
  have slots_formed: "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]] by auto
  have member: "selected_data_member (Payload_Term k) (data_list_term (map Payload_Term Ks))"
    using slot sets(3) by (simp add: selected_payload_list[OF slots_formed])
  show thesis by (rule that[OF reading member])
qed

lemma material_slot_observation:
  assumes material: "native_material_at E u (set Vs) r M I K"
    and source: "environment_value_presents E e"
    and scope: "distinct Vs" "\<forall>a\<in>set Vs. octets_formed a"
    and slot: "k\<in>K"
  obtains b s a d c f w i ks where
    "(62,material_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      b (Payload_Term r) s a d c f w i ks)\<in>positive_meaning material_instantiation_system"
    "selected_data_member (Payload_Term k) ks"
proof -
  obtain xs where bindings: "distinct xs" "term_bindings_formed (set Vs) (set xs)"
    using finite_scope_has_bindings[of "set Vs"] by auto
  have table: "(52,Pair_Term (data_list_term (map Payload_Term Vs)) (binding_rows_term xs))
      \<in>positive_meaning binding_admission_system"
    by (simp only: binding_admission_on_values) (use scope bindings in blast)
  obtain Us Is Ks where order: "distinct Us" "distinct Is" "distinct Ks"
    and sets: "set Us=material_variables M" "set Is=I" "set Ks=K"
    using finite_distinct_list[of "material_variables M"] finite_distinct_list[of I]
      finite_distinct_list[of K] native_material_formed[OF material] by auto
  have actual: "native_material_at E u (set Vs) r M (set Is) (set Ks)"
    using material by (simp only: sets)
  obtain s a d c f where reading:
    "(62,material_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) s a d c f (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning material_instantiation_system"
    using material_instantiation_total[OF source table actual order sets(1)] by blast
  have slots_formed: "term_formed (data_list_term (map Payload_Term Ks))"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]] by auto
  have member: "selected_data_member (Payload_Term k) (data_list_term (map Payload_Term Ks))"
    using slot sets(3) by (simp add: selected_payload_list[OF slots_formed])
  show thesis by (rule that[OF reading member])
qed

section \<open>Family selection follows the complete actual endpoint relation\<close>

lemma family_endpoint_observation:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and source: "artifact_value_presents R a"
  shows "(\<exists>rows s. (32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system \<and>
      selected_data_member (Pair_Term s t) rows) \<longleftrightarrow>
    (\<exists>k. t=Payload_Term k \<and> k\<in>family_endpoints E u r)"
proof
  assume "\<exists>rows s. (32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system \<and>
    selected_data_member (Pair_Term s t) rows"
  then obtain rows s xs where reading: "rows=data_list_term (map address_pair_data xs)"
    "family_at R r (set xs)" and selected: "selected_data_member (Pair_Term s t) rows"
    by (auto simp: family_admission_at_source[OF source])
  have member: "Pair_Term s t\<in>set (map address_pair_data xs)"
    using selected by (auto simp: reading(1) selected_data_member_exact data_list_term_injective)
  obtain p k where row: "(p,k)\<in>set xs" "t=Payload_Term k"
    using member by (auto simp: address_pair_data_def)
  have endpoint: "k\<in>family_endpoints E u r"
    using row(1) by (auto simp: family_endpoints_from_read[OF ef art reading(2)] rel_ran_def)
  show "\<exists>k. t=Payload_Term k \<and> k\<in>family_endpoints E u r" using row(2) endpoint by blast
next
  assume "\<exists>k. t=Payload_Term k \<and> k\<in>family_endpoints E u r"
  then obtain k S M where parts: "t=Payload_Term k" "artifact_at E u S" "family_at S r M" "k\<in>rel_ran M"
    by (auto simp: family_endpoints_def)
  have same: "S=R" by (rule environment_artifact_unique[OF ef parts(2) art])
  have family: "family_at R r M" using parts(3) by (simp only: same)
  obtain xs where order: "distinct xs" "set xs=M"
    using finite_distinct_list[OF family_socket_graph_finite[OF family]] by blast
  have reading: "(32,rooted_rows_argument a (Payload_Term r) (data_list_term (map address_pair_data xs)))
      \<in>positive_meaning family_admission_system"
    using family order by (simp add: family_admission_rows[OF source])
  obtain p where row: "(p,k)\<in>set xs" using parts(4) order(2) by (auto simp: rel_ran_def)
  have data: "data_elements (map address_pair_data xs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF reading]]
    by (auto simp: data_list_term_formed address_pair_data_def)
  have encoded_member: "Pair_Term (Payload_Term p) (Payload_Term k)\<in>set (map address_pair_data xs)"
    by (simp only: set_map, rule image_eqI[OF _ row]) (simp add: address_pair_data_def)
  have selected: "selected_data_member (Pair_Term (Payload_Term p) t) (data_list_term (map address_pair_data xs))"
    by (rule iffD2[OF selected_data_member_exact], rule exI[of _ "map address_pair_data xs"])
      (use data encoded_member parts(1) in auto)
  show "\<exists>rows s. (32,rooted_rows_argument a (Payload_Term r) rows)\<in>positive_meaning family_admission_system \<and>
    selected_data_member (Pair_Term s t) rows" using reading selected by blast
qed

text \<open>
  Every finite declared scope has a complete formed substitution. The existing
  readers therefore expose every slot of a recognized pattern, prospective
  call, or material record without requiring a true call or a satisfied
  material equation. Substitutions and instantiated outputs remain private
  existence witnesses. Family selection uses an actual complete family.
\<close>

end
