theory Factor_Artifact_Admission
  imports Factor_Material_Data_Projection
begin

section \<open>Complete material observation determines the supplied artifact data\<close>

definition artifact_projection_material :: "nat material_pattern" where
  "artifact_projection_material=
    \<lparr>material_source=Pattern_Variable 0, material_atoms=Pattern_Variable 1,
      material_edges=Pattern_Variable 2, material_counts=Pattern_Variable 3,
      material_functions=Pattern_Variable 4\<rparr>"

definition artifact_projection_schema :: "(nat,nat,nat) factor_schema" where
  "artifact_projection_schema=
    \<lparr>schema_conclusion=Pattern_Pair (Pattern_Variable 0)
        (Pattern_Pair (Pattern_Variable 5) (Pattern_Pair (Pattern_Variable 6)
          (Pattern_Pair (Pattern_Variable 7) (Pattern_Variable 8)))),
      schema_premises=
        {(0,0,Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 5)),
         (1,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 2) (Pattern_Variable 6))),
         (2,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 3) (Pattern_Variable 7))),
         (3,9,Pattern_Pair (Pattern_Variable 1) (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 8)))},
      schema_material_premises={(4,artifact_projection_material)}\<rparr>"

definition artifact_projection_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_projection_system=add_view_definition material_data_system 10 data_x {(0,artifact_projection_schema)}"

interpretation artifact_projection_view: positive_view material_data_system 10 data_x "{(0,artifact_projection_schema)}"
  by (rule positive_view.intro)
    (auto simp: artifact_projection_schema_def artifact_projection_material_def schema_formed_def
      material_pattern_formed_def material_fields_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma artifact_projection_system_formed [simp]: "schema_system_formed artifact_projection_system"
  using artifact_projection_view.formed by (simp only: artifact_projection_system_def)

lemma artifact_projection_definitions [simp]:
  "system_definitions artifact_projection_system={0,1,2,3,4,5,6,7,8,9,10}"
  by (auto simp: artifact_projection_system_def)

lemma artifact_projection_call:
  "schema_call_formed artifact_projection_system 10 t \<longleftrightarrow> term_formed t"
  using artifact_projection_view.view_call[of t] by (simp add: artifact_projection_system_def)

lemma artifact_projection_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9}"
  shows "(d,t)\<in>positive_meaning artifact_projection_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning material_data_system"
  using artifact_projection_view.old_meaning[of d t] assms by (simp add: artifact_projection_system_def)

lemma artifact_projection_clause [simp]:
  "((10,c),S)\<in>system_clauses artifact_projection_system \<longleftrightarrow> c=0 \<and> S=artifact_projection_schema"
  using artifact_projection_view.no_old_clause[of c S] by (auto simp: artifact_projection_system_def)

theorem artifact_projection_sound:
  assumes holds: "(10,t)\<in>positive_meaning artifact_projection_system"
  shows "\<exists>R x. t=Pair_Term (Target_Term (Whole_Artifact R)) x \<and> artifact_value_presents R x"
proof -
  have consequence: "(10,t)\<in>schema_consequences artifact_projection_system (positive_meaning artifact_projection_system)"
    using holds positive_meaning_unfold[of artifact_projection_system] by blast
  obtain c S v where clause: "((10,c),S)\<in>system_clauses artifact_projection_system"
    and head: "t=evaluate_pattern v (schema_conclusion S)"
    and material: "\<forall>s M. (s,M)\<in>schema_material_premises S \<longrightarrow> evaluate_material_satisfaction v M"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning artifact_projection_system"
    using consequence by (auto simp: schema_consequences_material_valuation)
  have schema: "S=artifact_projection_schema" using clause by simp
  have observation: "material_observation (v 0) (v 1) (v 2) (v 3) (v 4)"
    using material by (simp add: schema artifact_projection_schema_def artifact_projection_material_def)
  have children:
    "(0,Pair_Term (v 1) (v 5))\<in>positive_meaning material_data_system"
    "(9,material_projection_argument (v 1) (v 2) (v 6))\<in>positive_meaning material_data_system"
    "(9,material_projection_argument (v 1) (v 3) (v 7))\<in>positive_meaning material_data_system"
    "(9,material_projection_argument (v 1) (v 4) (v 8))\<in>positive_meaning material_data_system"
    using support artifact_projection_old_meaning[of 0] artifact_projection_old_meaning[of 9]
    by (auto simp: schema artifact_projection_schema_def)
  obtain R A E B F where enumeration: "artifact_enumeration R A E B F"
    and fields: "v 0=Target_Term (Whole_Artifact R)"
      "v 1=enumeration_term (map (atom_term R) A)"
      "v 2=enumeration_term (map (incidence_term R) E)"
      "v 3=enumeration_term (map (attachment_term R) B)"
      "v 4=enumeration_term (map (attachment_term R) F)"
    using observation unfolding material_observation_def by blast
  have formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    using artifact_enumeration_material[OF enumeration] by auto
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have outputs: "v 5=data_list_term (map Payload_Term A)"
    "v 6=data_list_term (map incidence_data E)"
    "v 7=data_list_term (map address_pair_data B)"
    "v 8=data_list_term (map address_pair_data F)"
    using children material_data_carrier[OF formed inside, of "v 5"]
      material_projection_incidence_list[OF formed atoms artifact_enumeration_terms_formed(2)[OF enumeration], of "v 6"]
      material_projection_attachment_list[OF formed atoms artifact_enumeration_terms_formed(3)[OF enumeration], of "v 7"]
      material_projection_attachment_list[OF formed atoms artifact_enumeration_terms_formed(4)[OF enumeration], of "v 8"]
    by (auto simp: fields[simplified])
  have presented: "artifact_value_presents R (artifact_fields_term (v 5) (v 6) (v 7) (v 8))"
    using enumeration outputs by (auto simp: artifact_value_presents_def artifact_data_term_def)
  show ?thesis using head fields(1) presented
    by (auto simp: schema artifact_projection_schema_def)
qed

theorem artifact_projection_complete:
  assumes present: "artifact_value_presents R t"
  shows "(10,Pair_Term (Target_Term (Whole_Artifact R)) t)\<in>positive_meaning artifact_projection_system"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F" and shape: "t=artifact_data_term A E B F"
    using present unfolding artifact_value_presents_def by blast
  let ?s="Target_Term (Whole_Artifact R)"
  let ?a="enumeration_term (map (atom_term R) A)"
  let ?e="enumeration_term (map (incidence_term R) E)"
  let ?b="enumeration_term (map (attachment_term R) B)"
  let ?f="enumeration_term (map (attachment_term R) F)"
  let ?da="data_list_term (map Payload_Term A)"
  let ?de="data_list_term (map incidence_data E)"
  let ?db="data_list_term (map address_pair_data B)"
  let ?df="data_list_term (map address_pair_data F)"
  have formed: "exact_formed R" and atoms: "set A=rra_carrier (object_structure R)"
    using artifact_enumeration_material[OF enumeration] by auto
  have inside: "set A\<subseteq>rra_carrier (object_structure R)" using atoms by simp
  have observation: "material_observation ?s ?a ?e ?b ?f"
    using enumeration by (simp only: material_observation_exact)
  have terms: "term_formed ?s" "term_formed ?a" "term_formed ?e" "term_formed ?b" "term_formed ?f"
    "term_formed ?da" "term_formed ?de" "term_formed ?db" "term_formed ?df"
    using material_observation_formed[OF observation] artifact_data_term_formed[OF enumeration]
    by (auto simp: artifact_data_term_def)
  have projections: "(0,Pair_Term ?a ?da)\<in>positive_meaning material_data_system"
    "(9,material_projection_argument ?a ?e ?de)\<in>positive_meaning material_data_system"
    "(9,material_projection_argument ?a ?b ?db)\<in>positive_meaning material_data_system"
    "(9,material_projection_argument ?a ?f ?df)\<in>positive_meaning material_data_system"
    by (simp_all add: material_data_carrier[OF formed inside]
      material_projection_incidence_list[OF formed atoms terms(3)]
      material_projection_attachment_list[OF formed atoms terms(4)]
      material_projection_attachment_list[OF formed atoms terms(5)])
  have lifted: "(0,Pair_Term ?a ?da)\<in>positive_meaning artifact_projection_system"
    "(9,material_projection_argument ?a ?e ?de)\<in>positive_meaning artifact_projection_system"
    "(9,material_projection_argument ?a ?b ?db)\<in>positive_meaning artifact_projection_system"
    "(9,material_projection_argument ?a ?f ?df)\<in>positive_meaning artifact_projection_system"
    using projections artifact_projection_old_meaning[of 0] artifact_projection_old_meaning[of 9] by auto
  let ?v="\<lambda>i::nat. if i=0 then ?s else if i=1 then ?a else if i=2 then ?e else if i=3 then ?b
    else if i=4 then ?f else if i=5 then ?da else if i=6 then ?de else if i=7 then ?db else ?df"
  have result: "(10,evaluate_pattern ?v (schema_conclusion artifact_projection_schema))
    \<in>positive_meaning artifact_projection_system"
    by (rule material_positive_valuation_step[where c=0])
      (use terms observation lifted in \<open>auto simp: artifact_projection_schema_def artifact_projection_material_def
        schema_variables_def material_variables_def material_fields_def artifact_projection_call\<close>)
  show ?thesis using result by (simp add: shape artifact_projection_schema_def artifact_data_term_def)
qed

theorem artifact_projection_exact:
  "(10,t)\<in>positive_meaning artifact_projection_system \<longleftrightarrow>
    (\<exists>R x. t=Pair_Term (Target_Term (Whole_Artifact R)) x \<and> artifact_value_presents R x)"
  using artifact_projection_sound artifact_projection_complete by blast

corollary artifact_projection_at_source:
  "(10,Pair_Term (Target_Term (Whole_Artifact R)) t)\<in>positive_meaning artifact_projection_system
    \<longleftrightarrow> artifact_value_presents R t"
  by (auto simp: artifact_projection_exact)

section \<open>Artifact admission and admitted equality are distinct definitions\<close>

definition artifact_admission_schema :: "(nat,nat,nat) factor_schema" where
  "artifact_admission_schema=data_rule data_x {(0,10,Pattern_Pair data_y data_x)}"

definition artifact_admission_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_admission_system=add_view_definition artifact_projection_system 11 data_x {(0,artifact_admission_schema)}"

interpretation artifact_admission_view: positive_view artifact_projection_system 11 data_x "{(0,artifact_admission_schema)}"
  by (rule positive_view.intro)
    (auto simp: artifact_admission_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma artifact_admission_system_formed [simp]: "schema_system_formed artifact_admission_system"
  using artifact_admission_view.formed by (simp only: artifact_admission_system_def)

lemma artifact_admission_definitions [simp]:
  "system_definitions artifact_admission_system={0,1,2,3,4,5,6,7,8,9,10,11}"
  by (auto simp: artifact_admission_system_def)

lemma artifact_admission_call:
  "schema_call_formed artifact_admission_system 11 t \<longleftrightarrow> term_formed t"
  using artifact_admission_view.view_call[of t] by (simp add: artifact_admission_system_def)

lemma artifact_admission_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10}"
  shows "(d,t)\<in>positive_meaning artifact_admission_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_projection_system"
  using artifact_admission_view.old_meaning[of d t] assms by (simp add: artifact_admission_system_def)

lemma artifact_admission_clause [simp]:
  "((11,c),S)\<in>system_clauses artifact_admission_system \<longleftrightarrow> c=0 \<and> S=artifact_admission_schema"
  using artifact_admission_view.no_old_clause[of c S] by (auto simp: artifact_admission_system_def)

theorem artifact_admission_exact:
  "(11,t)\<in>positive_meaning artifact_admission_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
proof
  assume holds: "(11,t)\<in>positive_meaning artifact_admission_system"
  have consequence: "(11,t)\<in>schema_consequences artifact_admission_system (positive_meaning artifact_admission_system)"
    using holds positive_meaning_unfold[of artifact_admission_system] by blast
  obtain c S v where clause: "((11,c),S)\<in>system_clauses artifact_admission_system"
    and head: "t=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning artifact_admission_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=artifact_admission_schema" using clause by simp
  have child: "(10,Pair_Term (v 1) t)\<in>positive_meaning artifact_projection_system"
    using head support artifact_admission_old_meaning[of 10]
    by (auto simp: schema artifact_admission_schema_def)
  show "\<exists>R. artifact_value_presents R t" using child by (auto simp: artifact_projection_exact)
next
  assume "\<exists>R. artifact_value_presents R t"
  then obtain R where present: "artifact_value_presents R t" by blast
  have formed: "term_formed t" "term_formed (Target_Term (Whole_Artifact R))"
    using artifact_value_presents_formed[OF present] by auto
  have child: "(10,Pair_Term (Target_Term (Whole_Artifact R)) t)\<in>positive_meaning artifact_admission_system"
    using artifact_projection_complete[OF present] artifact_admission_old_meaning[of 10] by auto
  let ?v="\<lambda>i::nat. if i=0 then t else Target_Term (Whole_Artifact R)"
  have result: "(11,evaluate_pattern ?v (schema_conclusion artifact_admission_schema))\<in>positive_meaning artifact_admission_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed child in \<open>auto simp: artifact_admission_schema_def schema_variables_def artifact_admission_call\<close>)
  show "(11,t)\<in>positive_meaning artifact_admission_system" using result by (simp add: artifact_admission_schema_def)
qed

definition artifact_identity_schema :: "(nat,nat,nat) factor_schema" where
  "artifact_identity_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,11,data_x),(1,11,data_y),(2,7,Pattern_Pair data_x data_y)}"

definition artifact_identity_system :: "(nat,nat,nat,nat) schema_system" where
  "artifact_identity_system=add_view_definition artifact_admission_system 12 data_x {(0,artifact_identity_schema)}"

interpretation artifact_identity_view: positive_view artifact_admission_system 12 data_x "{(0,artifact_identity_schema)}"
  by (rule positive_view.intro)
    (auto simp: artifact_identity_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def)

lemma artifact_identity_system_formed [simp]: "schema_system_formed artifact_identity_system"
  using artifact_identity_view.formed by (simp only: artifact_identity_system_def)

lemma artifact_identity_definitions [simp]:
  "system_definitions artifact_identity_system={0,1,2,3,4,5,6,7,8,9,10,11,12}"
  by (auto simp: artifact_identity_system_def)

lemma artifact_identity_call:
  "schema_call_formed artifact_identity_system d t \<longleftrightarrow>
    d\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12} \<and> term_formed t"
proof -
  have previous: "schema_call_formed material_data_system d t \<longleftrightarrow>
    d\<in>system_definitions material_data_system \<and> term_formed t"
    by (simp add: material_data_call)
  have projection: "schema_call_formed artifact_projection_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_projection_system \<and> term_formed t"
    using added_variable_calls[OF material_data_system_formed
      artifact_projection_system_formed[unfolded artifact_projection_system_def] previous]
    by (simp only: artifact_projection_system_def[symmetric])
  have admission: "schema_call_formed artifact_admission_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_admission_system \<and> term_formed t"
    using added_variable_calls[OF artifact_projection_system_formed
      artifact_admission_system_formed[unfolded artifact_admission_system_def] projection]
    by (simp only: artifact_admission_system_def[symmetric])
  have result: "schema_call_formed artifact_identity_system d t \<longleftrightarrow>
    d\<in>system_definitions artifact_identity_system \<and> term_formed t"
    using added_variable_calls[OF artifact_admission_system_formed
      artifact_identity_system_formed[unfolded artifact_identity_system_def] admission]
    by (simp only: artifact_identity_system_def[symmetric])
  show ?thesis using result by simp
qed

lemma artifact_identity_previous_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7,8,9,10,11}"
  shows "(d,t)\<in>positive_meaning artifact_identity_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_admission_system"
  using artifact_identity_view.old_meaning[of d t] assms by (simp add: artifact_identity_system_def)

theorem artifact_identity_old_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6,7}"
  shows "(d,t)\<in>positive_meaning artifact_identity_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning artifact_comparison_system"
  using artifact_identity_previous_meaning[of d t] artifact_admission_old_meaning[of d t]
    artifact_projection_old_meaning[of d t] material_data_old_meaning[OF assms, of t] assms by auto

lemma artifact_identity_admission:
  "(11,t)\<in>positive_meaning artifact_identity_system \<longleftrightarrow> (\<exists>R. artifact_value_presents R t)"
  using artifact_identity_previous_meaning[of 11 t] artifact_admission_exact[of t] by auto

lemma artifact_identity_clause [simp]:
  "((12,c),S)\<in>system_clauses artifact_identity_system \<longleftrightarrow> c=0 \<and> S=artifact_identity_schema"
  using artifact_identity_view.no_old_clause[of c S] by (auto simp: artifact_identity_system_def)

theorem artifact_identity_exact:
  "(12,t)\<in>positive_meaning artifact_identity_system \<longleftrightarrow>
    (\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y)"
proof
  assume holds: "(12,t)\<in>positive_meaning artifact_identity_system"
  have consequence: "(12,t)\<in>schema_consequences artifact_identity_system (positive_meaning artifact_identity_system)"
    using holds positive_meaning_unfold[of artifact_identity_system] by blast
  obtain c S v where clause: "((12,c),S)\<in>system_clauses artifact_identity_system"
    and head: "t=evaluate_pattern v (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern v p)\<in>positive_meaning artifact_identity_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schema: "S=artifact_identity_schema" using clause by simp
  have first: "(11,v 0)\<in>positive_meaning artifact_identity_system"
    and second: "(11,v 1)\<in>positive_meaning artifact_identity_system"
    and compare: "(7,Pair_Term (v 0) (v 1))\<in>positive_meaning artifact_comparison_system"
    using support artifact_identity_old_meaning[of 7]
    by (auto simp: schema artifact_identity_schema_def)
  obtain R where left: "artifact_value_presents R (v 0)" using first by (auto simp: artifact_identity_admission)
  obtain T where right: "artifact_value_presents T (v 1)" using second by (auto simp: artifact_identity_admission)
  have same: "R=T" using compare artifact_comparison_exact[OF left right] by blast
  show "\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y"
    using head left right same by (auto simp: schema artifact_identity_schema_def)
next
  assume "\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y"
  then obtain R x y where shape: "t=Pair_Term x y"
    and left: "artifact_value_presents R x" and right: "artifact_value_presents R y" by blast
  have formed: "term_formed x" "term_formed y"
    using artifact_value_presents_formed[OF left] artifact_value_presents_formed[OF right] by auto
  have children: "(11,x)\<in>positive_meaning artifact_identity_system"
    "(11,y)\<in>positive_meaning artifact_identity_system"
    "(7,Pair_Term x y)\<in>positive_meaning artifact_identity_system"
    using left right artifact_identity_admission artifact_comparison_exact[OF left right]
      artifact_identity_old_meaning[of 7 "Pair_Term x y"] by auto
  let ?v="\<lambda>i::nat. if i=0 then x else y"
  have result: "(12,evaluate_pattern ?v (schema_conclusion artifact_identity_schema))\<in>positive_meaning artifact_identity_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use formed children in \<open>auto simp: artifact_identity_schema_def schema_variables_def artifact_identity_call\<close>)
  show "(12,t)\<in>positive_meaning artifact_identity_system" using result by (simp add: shape artifact_identity_schema_def)
qed

corollary admitted_artifact_comparison:
  assumes "artifact_value_presents R x" "artifact_value_presents S y"
  shows "(12,Pair_Term x y)\<in>positive_meaning artifact_identity_system \<longleftrightarrow> R=S"
  using assms artifact_value_presents_unique by (auto simp: artifact_identity_exact; blast)

lemma artifact_checking_exact:
  assumes "d\<in>{11,12}"
  shows "(d,t)\<in>positive_meaning artifact_identity_system \<longleftrightarrow>
    (d=11 \<and> (\<exists>R. artifact_value_presents R t)) \<or>
    (d=12 \<and> (\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y))"
  using assms by (auto simp: artifact_identity_admission artifact_identity_exact)

section \<open>One closed native program for all future admission and equality calls\<close>

theorem native_artifact_checking:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> inj_on g {11::nat,12} \<and>
    (\<forall>d\<in>{11,12}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow>
          (d=11 \<and> (\<exists>R. artifact_value_presents R t)) \<or>
          (d=12 \<and> (\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y)))))"
proof -
  obtain g :: "nat \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where injective: "inj_on g (system_definitions artifact_identity_system)"
    and closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions artifact_identity_system. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed artifact_identity_system d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning artifact_identity_system) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF artifact_identity_system_formed] by blast
  have sites: "inj_on g {11,12}" using injective by (auto simp: inj_on_def)
  show ?thesis
  proof (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ g], intro conjI ballI allI impI)
    show "closed_native_package_at E pu [] Q" by (rule closed)
    show "inj_on g {11,12}" by (rule sites)
  next
    fix d :: nat and t :: factor_term
    assume selected: "d\<in>{11,12}" and tf: "term_formed t"
    have member: "d\<in>system_definitions artifact_identity_system" using selected by auto
    obtain F au I K where parts: "environment_formed F" "environment_included E F" "au\<notin>environment_uses E"
      "native_package_at F pu [] Q" "native_application_at F au [] (g d) t I K"
      "native_package_environment F pu []=E"
      "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed artifact_identity_system d t"
      "native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning artifact_identity_system"
      using future[rule_format, OF member tf] by blast
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
      native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
      (native_positive_holds F pu [] au [] \<longleftrightarrow>
        (d=11 \<and> (\<exists>R. artifact_value_presents R t)) \<or>
        (d=12 \<and> (\<exists>R x y. t=Pair_Term x y \<and> artifact_value_presents R x \<and> artifact_value_presents R y)))"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
        (use parts tf member artifact_checking_exact[OF selected] in \<open>auto simp: artifact_identity_call\<close>)
  qed
qed

text \<open>
  The mixed projection clause has four distinct ordinary premise sockets and
  one complete material socket. Its nine variables include the entire source
  and every input and output field. The observation supplies an actual formed
  artifact and every table entry; the ordinary program derives exactly the
  existing self-contained data presentation. The admission clause supplies
  that source through its ordinary finite binder boundary.

  Admission and identity have exact contracts over all terms. Identity joins
  two admission calls with the earlier four-field comparison at a fresh
  definition. Every complete presentation order is accepted, and counted
  repetitions and original addresses remain exact. All earlier definitions
  retain their interfaces and meaning. The final system has thirteen
  definitions and twenty-six clauses.

  One closed native package has separate admission and identity sites and
  serves every future formed argument. Each actual application retains the
  canonical program environment. A witness artifact in a material operand
  contributes no active definitions. This establishes artifact-data admission;
  grammar admission, native derivation checking, reflection, and foundation
  amendment require their own explicit definitions and proofs.
\<close>

end
