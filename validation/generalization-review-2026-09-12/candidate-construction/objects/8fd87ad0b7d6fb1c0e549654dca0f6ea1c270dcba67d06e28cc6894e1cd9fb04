theory Factor_Fragment_Enumerations
  imports Factor_Fragment_Presentations
begin

section \<open>Restriction keeps exactly the indicated source rows\<close>

abbreviation incidence_inside ::
  "local_address set \<Rightarrow> (local_address\<times>local_address\<times>local_address) \<Rightarrow> bool" where
  "incidence_inside A z \<equiv> fst z\<in>A \<and> fst (snd z)\<in>A \<and> snd (snd z)\<in>A"

lemma artifact_enumeration_coordinates:
  assumes "artifact_enumeration R A E B F"
  shows "\<forall>a\<in>set A. octets_formed a"
    "\<forall>z\<in>set E. incidence_coordinates_formed z"
    "\<forall>z\<in>set B. octets_formed (fst z) \<and> octets_formed (snd z)"
    "\<forall>z\<in>set F. octets_formed (fst z) \<and> octets_formed (snd z)"
  using artifact_data_term_formed[OF assms]
  by (auto simp: artifact_data_term_def data_list_term_formed incidence_data_def address_pair_data_def)

lemma exact_restriction_formed:
  assumes "exact_formed R"
  shows "exact_formed (restrict_object R A)"
  using assms restrict_object_formed basis_values_restrict
  by (auto simp: exact_formed_def restrict_object_def restrict_structure_def internal_incidence_def
    dest: basis_values_restrictD)

theorem artifact_enumeration_restriction:
  assumes source: "artifact_enumeration R A E B F"
  shows "artifact_enumeration (restrict_object R X)
    (filter (\<lambda>a. a\<in>X) A) (filter (incidence_inside X) E)
    (filter (\<lambda>z. fst z\<in>X) B) (filter (\<lambda>z. fst z\<in>X) F)"
proof -
  let ?U="rra_carrier (object_structure R)"
  have rf: "exact_formed R" and atoms: "set A=?U"
    and edges: "set E=rra_incidence (object_structure R)"
    and bags: "count_list B=bag_count (object_data R)"
    and frows: "set F=functional_bindings (object_data R)"
    using artifact_enumeration_material[OF source] by auto
  have bf: "basis_formed ?U (object_data R)"
    and sf: "rra_formed (object_structure R)"
    using rf by (auto simp: exact_formed_def object_formed_def)
  have edge_atoms: "incidence_inside ?U z" if "z\<in>set E" for z
  proof -
    obtain r p x where shape: "z=(r,p,x)" by (cases z) auto
    show ?thesis using that edges sf by (auto simp: shape rra_formed_def)
  qed
  have attachment_atoms: "fst z\<in>?U" if "z\<in>set F" for z
    using that frows bf by (auto simp: basis_formed_def)
  have outside: "count_list B (a,v)=0" if "a\<notin>?U" for a v
    using count_outside_carrier[OF bf that, of v] by (simp only: bags)
  have counts: "count_list (filter (\<lambda>z. fst z\<in>X) B) av=
      (if fst av\<in>?U\<inter>X then count_list B av else 0)" for av
    using outside[of "fst av" "snd av"]
    by (simp add: count_mset[symmetric])
  have restricted_structure: "object_structure (restrict_object R X)=
      \<lparr>rra_carrier=set (filter (\<lambda>a. a\<in>X) A), rra_incidence=set (filter (incidence_inside X) E)\<rparr>"
    using atoms edges edge_atoms
    by (auto simp: restrict_object_def restrict_structure_def internal_incidence_def rra_identity)
  have basis: "object_data (restrict_object R X)=
      \<lparr>bag_count=count_list (filter (\<lambda>z. fst z\<in>X) B),
        functional_bindings=set (filter (\<lambda>z. fst z\<in>X) F)\<rparr>"
    using counts bags frows attachment_atoms
    by (auto simp: restrict_object_def restrict_basis_def basis_identity fun_eq_iff)
  have recovered: "restrict_object R X=enumerated_artifact
      (filter (\<lambda>a. a\<in>X) A) (filter (incidence_inside X) E)
      (filter (\<lambda>z. fst z\<in>X) B) (filter (\<lambda>z. fst z\<in>X) F)"
    using restricted_structure basis by (simp add: exact_identity_iff enumerated_artifact_def)
  show ?thesis using source recovered exact_restriction_formed[OF rf, of X]
    by (auto simp: artifact_enumeration_def)
qed

lemma fragment_material_enumeration:
  assumes "artifact_enumeration (fragment_source G) A E B F"
  shows "artifact_enumeration (fragment_material G)
    (filter (\<lambda>a. a\<in>fragment_selection G) A) (filter (incidence_inside (fragment_selection G)) E)
    (filter (\<lambda>z. fst z\<in>fragment_selection G) B) (filter (\<lambda>z. fst z\<in>fragment_selection G) F)"
  using artifact_enumeration_restriction[OF assms, of "fragment_selection G"]
  by (simp only: fragment_material_def)

lemma fragment_remainder_enumeration:
  assumes source: "artifact_enumeration (fragment_source G) A E B F"
  shows "artifact_enumeration (fragment_remainder G)
    (filter (\<lambda>a. a\<notin>fragment_selection G) A) (filter (incidence_inside (- fragment_selection G)) E)
    (filter (\<lambda>z. fst z\<notin>fragment_selection G) B) (filter (\<lambda>z. fst z\<notin>fragment_selection G) F)"
proof -
  let ?R="fragment_source G"
  let ?U="rra_carrier (object_structure ?R)"
  have carrier: "?U\<inter>(?U-fragment_selection G)=?U\<inter>(-fragment_selection G)" by blast
  have same: "restrict_object ?R (fragment_omission G)=restrict_object ?R (- fragment_selection G)"
    by (simp only: fragment_omission_def restrict_object_def restrict_structure_def carrier)
  show ?thesis using artifact_enumeration_restriction[OF source, of "- fragment_selection G"]
    by (simp only: fragment_remainder_def same Compl_iff)
qed

lemma fragment_material_value_at_selection:
  assumes formed: "fragment_formed G"
    and source: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c"
  shows "artifact_value_presents (fragment_material G)
    (artifact_fields_term c
      (data_list_term (map incidence_data (filter (incidence_inside (fragment_selection G)) E)))
      (data_list_term (map address_pair_data (filter (\<lambda>z. fst z\<in>fragment_selection G) B)))
      (data_list_term (map address_pair_data (filter (\<lambda>z. fst z\<in>fragment_selection G) F))))"
proof -
  obtain X where chosen: "distinct X" "set X=fragment_selection G" "c=data_list_term (map Payload_Term X)"
    using selection by (auto simp: payload_set_enumerations)
  have same: "set X=set (filter (\<lambda>a. a\<in>fragment_selection G) A)"
    using chosen(2) formed artifact_enumeration_material(2)[OF source]
    by (auto simp: fragment_formed_def)
  have enumeration: "artifact_enumeration (fragment_material G) X
      (filter (incidence_inside (fragment_selection G)) E)
      (filter (\<lambda>z. fst z\<in>fragment_selection G) B)
      (filter (\<lambda>z. fst z\<in>fragment_selection G) F)"
    using fragment_material_enumeration[OF source] chosen(1) same
    by (auto simp: artifact_enumeration_def enumerated_artifact_def)
  show ?thesis using enumeration
    by (auto simp: artifact_value_presents_def artifact_data_term_def chosen(3))
qed

lemma fragment_selection_compared:
  assumes source: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c"
  shows "(6,Pair_Term (data_list_term (map Payload_Term (filter (\<lambda>a. a\<in>fragment_selection G) A))) c)
      \<in>positive_meaning bag_comparison_system \<longleftrightarrow> fragment_formed G"
proof -
  have rf: "exact_formed (fragment_source G)" and atoms: "set A=rra_carrier (object_structure (fragment_source G))"
    and distinct: "distinct A" and addresses: "\<forall>a\<in>set A. octets_formed a"
    using source artifact_enumeration_material[OF source]
    by (auto simp: artifact_enumeration_def exact_formed_def)
  have present: "payload_set_presents (set A\<inter>fragment_selection G)
      (data_list_term (map Payload_Term (filter (\<lambda>a. a\<in>fragment_selection G) A)))"
    by (rule data_collection_presents_map) (use distinct addresses in auto)
  have equal: "payload_set_presents (set A\<inter>fragment_selection G) c \<longleftrightarrow>
      set A\<inter>fragment_selection G=fragment_selection G"
  proof
    assume present: "payload_set_presents (set A\<inter>fragment_selection G) c"
    show "set A\<inter>fragment_selection G=fragment_selection G" by (rule payload_set_unique[OF present selection])
  next
    assume same: "set A\<inter>fragment_selection G=fragment_selection G"
    show "payload_set_presents (set A\<inter>fragment_selection G) c" using selection by (simp only: same)
  qed
  have comparison: "(6,Pair_Term
      (data_list_term (map Payload_Term (filter (\<lambda>a. a\<in>fragment_selection G) A))) c)
      \<in>positive_meaning bag_comparison_system \<longleftrightarrow>
      set A\<inter>fragment_selection G=fragment_selection G"
    using payload_set_comparison[OF present, of c] equal by blast
  have selected: "set A\<inter>fragment_selection G=fragment_selection G \<longleftrightarrow>
      fragment_selection G\<subseteq>rra_carrier (object_structure (fragment_source G))"
    using atoms by blast
  show ?thesis using comparison selected payload_set_formed[OF selection] rf
    unfolding fragment_formed_def by blast
qed

lemma fragment_omission_enumeration:
  assumes source: "artifact_enumeration (fragment_source G) A E B F"
  shows "payload_set_presents (fragment_omission G)
    (data_list_term (map Payload_Term (filter (\<lambda>a. a\<notin>fragment_selection G) A)))"
  using source artifact_enumeration_material[OF source]
  by (auto simp: payload_set_enumerations fragment_omission_def artifact_enumeration_def exact_formed_def
    intro!: exI[of _ "filter (\<lambda>a. a\<notin>fragment_selection G) A"])

lemma fragment_boundary_enumeration:
  assumes source: "artifact_enumeration (fragment_source G) A E B F"
  shows "incidence_set_presents (fragment_boundary G)
    (data_list_term (map incidence_data
      (filter (\<lambda>z. \<not>incidence_inside (fragment_selection G) z \<and>
        \<not>incidence_inside (- fragment_selection G) z) E)))"
proof -
  have rf: "exact_formed (fragment_source G)" and edges: "set E=rra_incidence (object_structure (fragment_source G))"
    and distinct: "distinct E" using source artifact_enumeration_material[OF source]
    by (auto simp: artifact_enumeration_def)
  have coords: "incidence_coordinates_formed z" if "z\<in>set E" for z
    using artifact_enumeration_coordinates(2)[OF source] that by blast
  have chosen: "set (filter (\<lambda>z. \<not>incidence_inside (fragment_selection G) z \<and>
      \<not>incidence_inside (- fragment_selection G) z) E)=fragment_boundary G"
    using edges by (auto simp: fragment_boundary_def crossing_incidence_def
      touching_incidence_def internal_incidence_def; blast)
  show ?thesis by (rule data_collection_presents_map)
    (use distinct chosen coords in auto)
qed

text \<open>
  Each restricted field is a filter of the complete source enumeration. The
  counted attachment list keeps every occurrence at every retained atom, so its
  count is exactly the original count or zero. Functional attachments and
  incidence retain their existing set conditions.

  The remainder keeps incidence whose three coordinates lie outside the
  selection. Crossing incidence is neither wholly selected nor wholly omitted.
  Every source row therefore has its original structural role, including rows
  that connect the selected and omitted material.
\<close>

end
