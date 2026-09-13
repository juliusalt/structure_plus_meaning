theory Factor_System_Relocation
  imports Factor_System_Renaming Factor_System_Alpha Presentation_Closure
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
  let ?D="system_definitions P \<times> (UNIV::factor_term set)"
  let ?read="\<lambda>q::'d\<times>factor_term. \<lambda>p. p=map_prod g id q"
  have lift: "presented_set ?read X=image (map_prod g id) X" for X
    by (auto simp only: presented_set_def image_def)
  have boundary: "schema_consequences P X\<subseteq>?D" for X
  proof
    fix q assume member: "q\<in>schema_consequences P X"
    obtain d t where shape: "q=(d,t)" by (cases q)
    have call: "schema_call_formed P d t" using member shape by (simp add: schema_consequence_rule)
    show "q\<in>?D" using schema_call_formed_target[OF call] shape by auto
  qed
  have transported: "lfp (schema_consequences (rename_system g P)) =
    presented_set ?read (lfp (schema_consequences P))"
  proof (rule presented_least_fixed_point_on[where D="?D",
      OF schema_consequences_mono schema_consequences_mono])
    fix X assume "X\<subseteq>?D"
    show "schema_consequences P X\<subseteq>?D" by (rule boundary)
  next
    fix X assume support: "X\<subseteq>?D"
    show "schema_consequences (rename_system g P) (presented_set ?read X) =
      presented_set ?read (schema_consequences P X)"
      by (simp only: lift renamed_system_consequences[OF formed injective support])
  qed
  show ?thesis using transported by (simp only: positive_meaning_def lift)
qed

lemma renamed_system_meaning_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and member: "d\<in>system_definitions P"
  shows "(g d,t)\<in>positive_meaning (rename_system g P) \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof
  assume target: "(g d,t)\<in>positive_meaning (rename_system g P)"
  obtain e x where old: "(e,x)\<in>positive_meaning P" "g d=g e" "t=x"
    using target by (auto simp: renamed_system_positive_meaning[OF formed injective] map_prod_def)
  have site: "e\<in>system_definitions P"
    using schema_call_formed_target[OF positive_meaning_formed[OF old(1)]] by blast
  have same: "d=e" by (rule inj_onD[OF injective old(2) member site])
  show "(d,t)\<in>positive_meaning P" using old(1,3) same by simp
next
  assume "(d,t)\<in>positive_meaning P"
  then show "(g d,t)\<in>positive_meaning (rename_system g P)"
    by (auto simp: renamed_system_positive_meaning[OF formed injective] map_prod_def)
qed

lemma system_variant_renamed_meaning_at:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and variant: "system_alpha_variant (rename_system g P) Q" and member: "d\<in>system_definitions P"
  shows "(g d,t)\<in>positive_meaning Q \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  using renamed_system_meaning_at[OF formed injective member] system_alpha_positive_meaning[OF variant] by simp

lemma system_variant_renamed_meaning_source:
  assumes formed: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and variant: "system_alpha_variant (rename_system g P) Q"
  shows "positive_meaning P={(d,t). d\<in>system_definitions P \<and> (g d,t)\<in>positive_meaning Q}"
proof -
  have scope: "d\<in>system_definitions P" if "(d,t)\<in>positive_meaning P" for d t
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  show ?thesis using system_variant_renamed_meaning_at[OF formed injective variant] scope by auto
qed

text \<open>
  Relocation commutes with the independent positive consequence operator on
  support relations over the source definitions. Every least-fixed-point fact
  lies within that boundary. The general presentation fixed-point rule then
  gives exact correspondence under the injective definition map, with argument
  terms unchanged. Formation and the consequence equation are established here
  before that rule is applied.
\<close>

end
