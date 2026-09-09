theory Factor_Fragment_Clauses
  imports Factor_Context_Filters Factor_Fragment_Enumerations Factor_Artifact_Difference
begin

section \<open>Membership and its complement retain their complete payload context\<close>

definition fragment_payload_inside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_payload_inside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
    {(0,1,(Pattern_Variable 0)),
     (1,5,(Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 2))))}"

definition fragment_payload_outside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_payload_outside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))
    {(0,1,(Pattern_Variable 0)),
     (1,1,(data_list_pattern [(Pattern_Variable 1)])),
     (2,132,(Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 0)))}"

definition fragment_attachment_inside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_attachment_inside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 2)))
    {(0,189,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))),
     (1,1,(data_list_pattern [(Pattern_Variable 2)]))}"

definition fragment_attachment_outside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_attachment_outside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 2)))
    {(0,190,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))),
     (1,1,(data_list_pattern [(Pattern_Variable 2)]))}"

definition fragment_incidence_inside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_incidence_inside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))
    {(0,189,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))),
     (1,189,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 2))),
     (2,189,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 3)))}"

definition fragment_incidence_outside_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_incidence_outside_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))
    {(0,190,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))),
     (1,190,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 2))),
     (2,190,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 3)))}"

definition fragment_incidence_alternative_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "fragment_incidence_alternative_schema selected i=data_rule
    (Pattern_Pair (Pattern_Variable 0)
      (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))
    (insert (0,selected,Pattern_Pair (Pattern_Variable 0) (Pattern_Variable (Suc i)))
      ({(1,1,data_list_pattern [Pattern_Variable 1]),
        (2,1,data_list_pattern [Pattern_Variable 2]),
        (3,1,data_list_pattern [Pattern_Variable 3])} -
       {(Suc i,1,data_list_pattern [Pattern_Variable (Suc i)])}))"

section \<open>Complete source admission and the four independent projections\<close>

definition fragment_admission_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_admission_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4))
    {(0,11,(Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))),
     (1,197,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 5)))),
     (2,6,(Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 4)))}"

definition fragment_material_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_material_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,205,(Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4))),
     (1,11,(Pattern_Variable 5)),
     (2,201,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 6)))),
     (3,199,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 7)))),
     (4,199,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 8)))),
     (5,7,(Pattern_Pair (Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))) (Pattern_Variable 5)))}"

definition fragment_remainder_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_remainder_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,205,(Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4))),
     (1,11,(Pattern_Variable 5)),
     (2,198,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 6)))),
     (3,202,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 7)))),
     (4,200,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 8)))),
     (5,200,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 9)))),
     (6,7,(Pattern_Pair (Pattern_Pair (Pattern_Variable 6) (Pattern_Pair (Pattern_Variable 7) (Pattern_Pair (Pattern_Variable 8) (Pattern_Variable 9)))) (Pattern_Variable 5)))}"

definition fragment_omission_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_omission_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,205,(Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4))),
     (1,198,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 6)))),
     (2,6,(Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 5)))}"

definition fragment_boundary_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_boundary_schema=data_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4)) (Pattern_Variable 5))
    {(0,205,(Pattern_Pair (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3)))) (Pattern_Variable 4))),
     (1,203,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 6)))),
     (2,204,(Pattern_Pair (Pattern_Variable 4) (Pattern_Pair (Pattern_Variable 6) (Pattern_Variable 7)))),
     (3,6,(Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 5)))}"

definition fragment_report_schema :: "(nat,nat,nat) factor_schema" where
  "fragment_report_schema=data_rule
    (Pattern_Pair (Pattern_Variable 0) (Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 3))))
    {(0,206,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1))),
     (1,209,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 2))),
     (2,207,(Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 3)))}"

lemmas fragment_schema_defs = fragment_payload_inside_schema_def
  fragment_payload_outside_schema_def
  fragment_attachment_inside_schema_def
  fragment_attachment_outside_schema_def
  fragment_incidence_inside_schema_def
  fragment_incidence_outside_schema_def
  fragment_admission_schema_def
  fragment_material_schema_def
  fragment_remainder_schema_def
  fragment_omission_schema_def
  fragment_boundary_schema_def
  fragment_report_schema_def
  fragment_incidence_alternative_schema_def

definition fragment_clause_family :: "nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "fragment_clause_family d=
    (if d=189 then {(0,fragment_payload_inside_schema)}
    else if d=190 then {(0,fragment_payload_outside_schema)}
    else if d=191 then {(0,fragment_attachment_inside_schema)}
    else if d=192 then {(0,fragment_attachment_outside_schema)}
    else if d=193 then {(0,fragment_incidence_inside_schema)}
    else if d=194 then {(0,fragment_incidence_alternative_schema 190 0),(1,fragment_incidence_alternative_schema 190 1),(2,fragment_incidence_alternative_schema 190 2)}
    else if d=195 then {(0,fragment_incidence_outside_schema)}
    else if d=196 then {(0,fragment_incidence_alternative_schema 189 0),(1,fragment_incidence_alternative_schema 189 1),(2,fragment_incidence_alternative_schema 189 2)}
    else if d=197 then context_filter_clauses 1 189 190 197
    else if d=198 then context_filter_clauses 1 190 189 198
    else if d=199 then context_filter_clauses 1 191 192 199
    else if d=200 then context_filter_clauses 1 192 191 200
    else if d=201 then context_filter_clauses 1 193 194 201
    else if d=202 then context_filter_clauses 1 195 196 202
    else if d=203 then context_filter_clauses 1 194 193 203
    else if d=204 then context_filter_clauses 1 196 195 204
    else if d=205 then {(0,fragment_admission_schema)}
    else if d=206 then {(0,fragment_material_schema)}
    else if d=207 then {(0,fragment_remainder_schema)}
    else if d=208 then {(0,fragment_omission_schema)}
    else if d=209 then {(0,fragment_boundary_schema)}
    else if d=210 then {(0,fragment_report_schema)}
    else {})"

section \<open>The actual callees determine the least base program\<close>

definition fragment_group_system :: "(nat,nat,nat,nat) schema_system" where
  "fragment_group_system=\<lparr>
    system_interfaces={(d,Pattern_Variable 0) |d. d\<in>{189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210}},
    system_clauses={((d,c),S). d\<in>{189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210} \<and> (c,S)\<in>fragment_clause_family d}\<rparr>"

lemma fragment_group_definitions [simp]:
  "system_definitions fragment_group_system={189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210}"
  by (auto simp: fragment_group_system_def system_definitions_def rel_dom_def)

lemma fragment_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces fragment_group_system \<longleftrightarrow>
    d\<in>system_definitions fragment_group_system \<and> p=Pattern_Variable 0"
  by (simp only: fragment_group_definitions; auto simp: fragment_group_system_def)

lemma fragment_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses fragment_group_system \<longleftrightarrow>
    d\<in>system_definitions fragment_group_system \<and> (c,S)\<in>fragment_clause_family d"
  by (simp only: fragment_group_definitions; auto simp: fragment_group_system_def)

lemma fragment_group_formed_over:
  "schema_system_formed_over {1,5,6,7,11,132} fragment_group_system"
proof -
  have family_finite: "finite (fragment_clause_family d)" for d
    by (simp add: fragment_clause_family_def context_filter_clauses_def)
  have family_functional: "single_valued (fragment_clause_family d)" for d
    by (auto simp: fragment_clause_family_def context_filter_clauses_def single_valued_def
      split: if_splits)
  have family_formed: "schema_formed S \<and>
      schema_dependencies S\<subseteq>{1,5,6,7,11,132}\<union>system_definitions fragment_group_system"
    if "(c,S)\<in>fragment_clause_family d" for c S d
    using that by (auto simp: fragment_clause_family_def fragment_schema_defs
      context_filter_clauses_def context_filter_nil_schema_def context_filter_keep_schema_def
      context_filter_drop_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def split: if_splits)
  show ?thesis
    by (rule schema_system_formed_over_families[where
        D="system_definitions fragment_group_system" and p="\<lambda>_. Pattern_Variable 0"
        and C=fragment_clause_family])
      (use family_finite family_functional family_formed in
        \<open>simp_all only: fragment_group_definitions; auto simp: fragment_group_system_def\<close>)+
qed

lemma fragment_external_dependencies:
  "system_external_dependencies fragment_group_system={1,5,6,7,11,132}"
proof -
  have bounded: "system_external_dependencies fragment_group_system\<subseteq>{1,5,6,7,11,132}"
    by (rule system_external_dependencies_boundary[OF fragment_group_formed_over])
  have reached: "e\<in>system_external_dependencies fragment_group_system"
    if "((d,c),S)\<in>system_clauses fragment_group_system" "e\<in>schema_dependencies S"
      "e\<notin>system_definitions fragment_group_system" for d c S e
  proof -
    have member: "e\<in>(\<Union>row\<in>system_clauses fragment_group_system. schema_dependencies (snd row))"
      by (rule UN_I[OF that(1)]) (use that(2) in simp)
    show ?thesis using member that(3) by (simp only: system_external_dependencies_clauses Diff_iff; blast)
  qed
  have payload: "1\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=189 and c=0 and S=fragment_payload_inside_schema])
      (auto simp: fragment_clause_family_def fragment_payload_inside_schema_def schema_dependencies_def rel_ran_image)
  have selection: "5\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=189 and c=0 and S=fragment_payload_inside_schema])
      (auto simp: fragment_clause_family_def fragment_payload_inside_schema_def schema_dependencies_def rel_ran_image)
  have comparison: "6\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=205 and c=0 and S=fragment_admission_schema])
      (auto simp: fragment_clause_family_def fragment_admission_schema_def schema_dependencies_def rel_ran_image)
  have artifact_comparison: "7\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=206 and c=0 and S=fragment_material_schema])
      (auto simp: fragment_clause_family_def fragment_material_schema_def schema_dependencies_def rel_ran_image)
  have artifact_admission: "11\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=205 and c=0 and S=fragment_admission_schema])
      (auto simp: fragment_clause_family_def fragment_admission_schema_def schema_dependencies_def rel_ran_image)
  have absence: "132\<in>system_external_dependencies fragment_group_system"
    by (rule reached[where d=190 and c=0 and S=fragment_payload_outside_schema])
      (auto simp: fragment_clause_family_def fragment_payload_outside_schema_def schema_dependencies_def rel_ran_image)
  show ?thesis using bounded payload selection comparison artifact_comparison artifact_admission absence by blast
qed

definition fragment_base_system :: "(nat,nat,nat,nat) schema_system" where
  "fragment_base_system=rooted_system artifact_difference_base_system
    (system_external_dependencies fragment_group_system)"

lemma fragment_base_formed [simp]: "schema_system_formed fragment_base_system"
  by (simp only: fragment_base_system_def; rule rooted_system_formed[OF artifact_difference_base_formed])

lemma fragment_base_subdomain:
  "system_definitions fragment_base_system\<subseteq>system_definitions artifact_difference_base_system"
  by (simp only: fragment_base_system_def; rule rooted_system_subdomain)

lemma fragment_base_roots:
  "{1,5,6,7,11,132}\<subseteq>system_definitions fragment_base_system"
  unfolding fragment_base_system_def fragment_external_dependencies
  by (rule rooted_system_roots[OF artifact_difference_base_formed]) auto

lemma fragment_base_call:
  "schema_call_formed fragment_base_system d t \<longleftrightarrow>
    d\<in>system_definitions fragment_base_system \<and> term_formed t"
proof -
  have roots: "system_external_dependencies fragment_group_system\<subseteq>
      system_definitions artifact_difference_base_system"
    by (simp only: fragment_external_dependencies; auto)
  have definitions: "system_definitions fragment_base_system=
      system_definition_closure artifact_difference_base_system
        (system_external_dependencies fragment_group_system)"
    unfolding fragment_base_system_def
    by (rule rooted_system_definitions[OF artifact_difference_base_formed roots])
  have inside: "d\<in>system_definition_closure artifact_difference_base_system
      (system_external_dependencies fragment_group_system) \<Longrightarrow>
      d\<in>system_definitions artifact_difference_base_system"
    using fragment_base_subdomain by (simp only: definitions; blast)
  have calls: "schema_call_formed fragment_base_system d t \<longleftrightarrow>
      d\<in>system_definition_closure artifact_difference_base_system
        (system_external_dependencies fragment_group_system) \<and>
      schema_call_formed artifact_difference_base_system d t"
    by (simp only: fragment_base_system_def rooted_system_calls[OF artifact_difference_base_formed])
  show ?thesis by (simp only: calls definitions artifact_difference_base_call; use inside in blast)
qed

lemma fragment_base_least:
  assumes "{1,5,6,7,11,132}\<subseteq>U" "system_dependency_closed artifact_difference_base_system U"
  shows "system_definitions fragment_base_system\<subseteq>U"
  unfolding fragment_base_system_def fragment_external_dependencies
  by (rule rooted_system_least[OF artifact_difference_base_formed _ assms]) auto

interpretation fragment_group: positive_definition_group fragment_base_system fragment_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed fragment_base_system" by simp
  show "schema_system_formed_over (system_definitions fragment_base_system) fragment_group_system"
    by (rule schema_system_formed_over_mono[OF fragment_group_formed_over fragment_base_roots])
  show "system_definitions fragment_base_system\<inter>system_definitions fragment_group_system={}"
    using fragment_base_subdomain by auto
qed

definition fragment_system :: "(nat,nat,nat,nat) schema_system" where
  "fragment_system=system_union fragment_base_system fragment_group_system"

lemma fragment_system_formed [simp]: "schema_system_formed fragment_system"
  using fragment_group.formed by (simp only: fragment_system_def)

lemma fragment_definitions [simp]:
  "system_definitions fragment_system=system_definitions fragment_base_system\<union>system_definitions fragment_group_system"
  by (simp add: fragment_system_def)

lemma fragment_call:
  "schema_call_formed fragment_system d t \<longleftrightarrow>
    d\<in>system_definitions fragment_system \<and> term_formed t"
  unfolding fragment_system_def
  by (rule fragment_group.variable_calls[OF fragment_base_call fragment_group_interfaces])

lemma fragment_clause:
  assumes "d\<in>system_definitions fragment_group_system"
  shows "((d,c),S)\<in>system_clauses fragment_system \<longleftrightarrow> (c,S)\<in>fragment_clause_family d"
  using fragment_group.no_old_clause[OF assms, of c S] assms by (simp add: fragment_system_def)

lemma fragment_previous_meaning:
  assumes "d\<in>{1,5,6,7,11,132}"
  shows "(d,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_difference_base_system"
proof -
  have member: "d\<in>system_definitions fragment_base_system" using fragment_base_roots assms by blast
  have inside: "d\<in>system_definition_closure artifact_difference_base_system
      (system_external_dependencies fragment_group_system)"
    using member by (auto simp: fragment_base_system_def rooted_system_def)
  show ?thesis using fragment_group.old_meaning[OF member, of t]
    rooted_system_meaning[OF artifact_difference_base_formed,
      where roots="system_external_dependencies fragment_group_system" and d=d and t=t] inside
    by (simp only: fragment_system_def fragment_base_system_def; blast)
qed

lemma fragment_bag_meaning:
  assumes "d\<in>{1,5,6}"
  shows "(d,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using fragment_previous_meaning[of d t]
    system_union_agree_right_locality(2)[OF artifact_identity_system_formed bag_difference_system_formed
      artifact_bag_difference_agreement, of d t]
    bag_difference_bag_meaning[of d t] assms
  by (auto simp: artifact_difference_base_system_def)

lemma fragment_components:
  "(1,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>A. payload_set_presents A t)"
  "(5,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(6,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(7,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (7,t)\<in>positive_meaning artifact_comparison_system"
  "(11,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
  "(132,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (132,t)\<in>positive_meaning data_absence_system"
proof -
  show "(1,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>A. payload_set_presents A t)"
    using fragment_bag_meaning[of 1 t] bag_comparison_old_meaning[of 1 t]
      data_comparison_payloads[of t] payload_set_admission[of t] by auto
  show "(5,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and "(6,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
    using fragment_bag_meaning[of 5 t] fragment_bag_meaning[of 6 t] by auto
  have identity: "(d,t)\<in>positive_meaning artifact_difference_base_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning artifact_identity_system" if "d\<in>{7,11}" for d
    using system_union_agree_left_locality(2)[OF artifact_identity_system_formed bag_difference_system_formed
      artifact_bag_difference_agreement, of d t] that by (auto simp: artifact_difference_base_system_def)
  show "(7,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (7,t)\<in>positive_meaning artifact_comparison_system"
    using fragment_previous_meaning[of 7 t] identity[of 7] artifact_identity_old_meaning[of 7 t] by auto
  show "(11,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
    using fragment_previous_meaning[of 11 t] identity[of 11] artifact_identity_admission[of t] by auto
  show "(132,t)\<in>positive_meaning fragment_system \<longleftrightarrow> (132,t)\<in>positive_meaning data_absence_system"
    using fragment_previous_meaning[of 132 t]
      system_union_agree_right_locality(2)[OF artifact_identity_system_formed bag_difference_system_formed
        artifact_bag_difference_agreement, of 132 t] bag_difference_old_meaning[of 132 t]
    by (auto simp: artifact_difference_base_system_def)
qed

text \<open>
  Twenty-two ordinary definitions expose explicit membership, complementary
  finite filters, fragment admission, and the four derived projections. A
  combined report calls the three structural projections at exactly the same
  source. Its full carrier and source data are never replaced by output claims.

  Only the least closure of the group's six actual external callees is
  retained from the prior programs. Every retained interface and clause stays
  complete. Positive recursion uses the existing least meaning, with no new
  material observation, discriminator, or truth primitive.
\<close>

end
