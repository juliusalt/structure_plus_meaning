theory Factor_System_Relocation
  imports Factor_System_Renaming Factor_System_Alpha
begin

section \<open>Conjugate consequence operators under injective in_definitions relocation\<close>

lemma renamed_system_consequence_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "d \<in> system_definitions P" and support: "X \<subseteq> system_definitions P \<times> UNIV"
  shows "(g d,t) \<in> schema_consequences (rename_system g P) (map_prod g id ` X) \<longleftrightarrow>
    (d,t) \<in> schema_consequences P X"
proof -
  let ?Q = "rename_system g P"
  let ?Y = "{q\<in>X. schema_call_formed P (fst q) (snd q)}"
  have each_call: "\<And>e x. (e,x) \<in> X \<Longrightarrow>
    (schema_call_formed ?Q (g e) x \<longleftrightarrow> schema_call_formed P e x)"
    by (rule renamed_system_call[OF formed injective]) (use support in auto)
  have support_image: "{q\<in>map_prod g id ` X. schema_call_formed ?Q (fst q) (snd q)} = map_prod g id ` ?Y"
    using each_call by (auto simp: map_prod_def intro: rev_image_eqI)
  have bounded: "?Y \<subseteq> system_definitions P \<times> UNIV" using support by blast
  have each_rule: "\<And>c S. (c,S) \<in> system_clause_family P d \<Longrightarrow>
    (schema_rule_instance (rename_schema id id g S) (map_prod g id ` ?Y) t \<longleftrightarrow> schema_rule_instance S ?Y t)"
  proof -
    fix c S assume entry: "(c,S) \<in> system_clause_family P d"
    have sr: "S \<in> rel_ran (system_clause_family P d)" by (rule rel_ranI[OF entry])
    have deps: "schema_dependencies S \<subseteq> system_definitions P"
      using system_clause_family_dependencies[OF formed, of d] sr by blast
    show "schema_rule_instance (rename_schema id id g S) (map_prod g id ` ?Y) t \<longleftrightarrow> schema_rule_instance S ?Y t"
      by (rule schema_rule_instance_callee_image[OF injective deps bounded])
  qed
  have rules: "(\<exists>c S. (c,S) \<in> system_clause_family ?Q (g d) \<and>
      schema_rule_instance S (map_prod g id ` ?Y) t) \<longleftrightarrow>
    (\<exists>c S. (c,S) \<in> system_clause_family P d \<and> schema_rule_instance S ?Y t)"
    using each_rule by (simp only: renamed_system_clause_at[OF formed injective member]) blast
  show ?thesis by (simp only: schema_consequence_rule renamed_system_call[OF formed injective member] support_image rules)
qed

theorem renamed_system_consequences:
  fixes P :: "('a,'s,'d,'c) schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and support: "X \<subseteq> system_definitions P \<times> UNIV"
  shows "schema_consequences (rename_system g P) (map_prod g id ` X) = map_prod g id ` schema_consequences P X"
proof (rule set_eqI)
  fix call :: "'e \<times> factor_term"
  obtain e t where shape: "call=(e,t)" by (cases call)
  show "call \<in> schema_consequences (rename_system g P) (map_prod g id ` X) \<longleftrightarrow>
    call \<in> map_prod g id ` schema_consequences P X"
  proof
    assume member: "call \<in> schema_consequences (rename_system g P) (map_prod g id ` X)"
    have call: "schema_call_formed (rename_system g P) e t" using member shape by (simp add: schema_consequence_rule)
    have in_definitions: "e \<in> g ` system_definitions P"
      using schema_call_formed_target[OF call] by (simp add: renamed_system_definitions)
    obtain d where original: "d \<in> system_definitions P" "e=g d" using in_definitions by blast
    have target: "(g d,t) \<in> schema_consequences (rename_system g P) (map_prod g id ` X)"
      using member shape original(2) by simp
    have source: "(d,t) \<in> schema_consequences P X"
      using renamed_system_consequence_at[OF formed injective original(1) support] target by blast
    have mapped: "map_prod g id (d,t) \<in> map_prod g id ` schema_consequences P X" by (rule imageI[OF source])
    show "call \<in> map_prod g id ` schema_consequences P X" using mapped shape original(2) by simp
  next
    assume member: "call \<in> map_prod g id ` schema_consequences P X"
    obtain d x where original: "(d,x) \<in> schema_consequences P X" "call=(g d,x)"
      using member by (auto simp: map_prod_def)
    have call: "schema_call_formed P d x" using original(1) by (simp add: schema_consequence_rule)
    have in_definitions: "d \<in> system_definitions P" using schema_call_formed_target[OF call] by blast
    have target: "(g d,x) \<in> schema_consequences (rename_system g P) (map_prod g id ` X)"
      using renamed_system_consequence_at[OF formed injective in_definitions support] original(1) by blast
    show "call \<in> schema_consequences (rename_system g P) (map_prod g id ` X)" using target original(2) by simp
  qed
qed

theorem renamed_system_positive_meaning:
  fixes P :: "('a,'s,'d,'c) schema_system" and g :: "'d \<Rightarrow> 'e"
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
  shows "positive_meaning (rename_system g P) = map_prod g id ` positive_meaning P"
proof -
  let ?D = "system_definitions P"
  let ?Q = "rename_system g P"
  let ?B = "{(d,t). d\<in>?D \<and> (g d,t) \<in> positive_meaning ?Q}"
  have source_bound: "positive_meaning P \<subseteq> ?D \<times> UNIV"
  proof
    fix call :: "'d \<times> factor_term" assume member: "call \<in> positive_meaning P"
    obtain d t where shape: "call=(d,t)" by (cases call)
    have actual: "(d,t) \<in> positive_meaning P" using member shape by simp
    have call: "schema_call_formed P d t" by (rule positive_meaning_formed[OF actual])
    show "call \<in> ?D \<times> UNIV" using schema_call_formed_target[OF call] shape by auto
  qed
  have image_closed: "schema_consequences ?Q (map_prod g id ` positive_meaning P) \<subseteq> map_prod g id ` positive_meaning P"
    by (simp only: renamed_system_consequences[OF formed injective source_bound] positive_meaning_unfold[symmetric])
  have target_subset: "positive_meaning ?Q \<subseteq> map_prod g id ` positive_meaning P"
    by (rule positive_meaning_least[OF image_closed])
  have inverse_bound: "?B \<subseteq> ?D \<times> UNIV" by auto
  have mapped_inverse: "map_prod g id ` ?B \<subseteq> positive_meaning ?Q" by auto
  have consequence_subset: "schema_consequences ?Q (map_prod g id ` ?B) \<subseteq> schema_consequences ?Q (positive_meaning ?Q)"
    by (rule monoD[OF schema_consequences_mono mapped_inverse])
  have image_step: "map_prod g id ` schema_consequences P ?B \<subseteq> positive_meaning ?Q"
    using consequence_subset
    by (simp only: renamed_system_consequences[OF formed injective inverse_bound] positive_meaning_unfold[symmetric])
  have inverse_closed: "schema_consequences P ?B \<subseteq> ?B"
  proof
    fix call :: "'d \<times> factor_term" assume member: "call \<in> schema_consequences P ?B"
    obtain d t where shape: "call=(d,t)" by (cases call)
    have accepted: "schema_call_formed P d t" using member shape by (simp add: schema_consequence_rule)
    have in_definitions: "d \<in> ?D" using schema_call_formed_target[OF accepted] by blast
    have mapped: "map_prod g id call \<in> map_prod g id ` schema_consequences P ?B" by (rule imageI[OF member])
    have target: "(g d,t) \<in> positive_meaning ?Q" using image_step mapped shape by auto
    show "call \<in> ?B" using in_definitions target shape by simp
  qed
  have inverse_subset: "positive_meaning P \<subseteq> ?B" by (rule positive_meaning_least[OF inverse_closed])
  have source_subset: "map_prod g id ` positive_meaning P \<subseteq> positive_meaning ?Q"
    by (rule subset_trans[OF image_mono[OF inverse_subset] mapped_inverse])
  show ?thesis using target_subset source_subset by blast
qed

text \<open>
  Relocation commutes with the independent positive consequence operator on
  support relations over the source definitions. Every least-fixed-point fact
  lies within that boundary. The two least fixed points therefore correspond
  exactly under the injective definition map, with argument terms unchanged.
\<close>

end
