theory Factor_Schema_Determination
  imports Factor_Pattern_Determination Factor_Premise_Instances
begin

section \<open>Complete instances retain every prospective pattern\<close>

lemma schema_premises_instances_determine:
  assumes injective: "inj_on f B"
    and first: "schema_instance S ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
      "schema_instance T ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
    and second: "schema_instance S ((\<lambda>a. (a,Target_Term k)) ` B) y W"
      "schema_instance T ((\<lambda>a. (a,Target_Term k)) ` B) y W"
  shows "schema_premises S=schema_premises T"
proof -
  let ?V="(\<lambda>a. (a,Payload_Term (f a))) ` B"
  let ?U="(\<lambda>a. (a,Target_Term k)) ` B"
  have inclusion: "schema_premises A\<subseteq>schema_premises D"
    if a: "schema_instance A ?V x Q" and d: "schema_instance D ?V x Q"
      and a': "schema_instance A ?U y W" and d': "schema_instance D ?U y W" for A D
  proof
    fix row assume member: "row\<in>schema_premises A"
    obtain s e p where shape: "row=(s,e,p)" by (cases row) auto
    have source: "(s,e,p)\<in>schema_premises A" using member shape by simp
    obtain t where left: "(s,e,t)\<in>Q" "pattern_instance ?V p t"
      using a source unfolding schema_instance_def schema_premise_instance_def by blast
    obtain q where right: "(s,e,q)\<in>schema_premises D" "pattern_instance ?V q t"
      using schema_instance_premise_iff[OF d, of s e t] left(1) by blast
    obtain u where left': "(s,e,u)\<in>W" "pattern_instance ?U p u"
      using a' source unfolding schema_instance_def schema_premise_instance_def by blast
    obtain r where right': "(s,e,r)\<in>schema_premises D" "pattern_instance ?U r u"
      using schema_instance_premise_iff[OF d', of s e u] left'(1) by blast
    have functional: "single_valued (schema_premises D)"
      using d by (simp add: schema_instance_def schema_formed_def)
    have same: "r=q" using single_valued_outputs[OF functional right'(1) right(1)] by simp
    have other: "pattern_instance ?U q u" using right'(2) same by simp
    have patterns: "p=q"
      by (rule pattern_instances_determine[OF injective left(2) right(2) left'(2) other])
    show "row\<in>schema_premises D" using right(1) shape patterns by simp
  qed
  show ?thesis using inclusion[OF first second] inclusion[OF first(2,1) second(2,1)] by blast
qed

section \<open>Material output rows retain their entire source syntax\<close>

lemma schema_material_instances_determine:
  assumes injective: "inj_on f B"
    and first: "schema_instance S ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
      "schema_instance T ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
    and second: "schema_instance S ((\<lambda>a. (a,Target_Term k)) ` B) y W"
      "schema_instance T ((\<lambda>a. (a,Target_Term k)) ` B) y W"
    and materials:
      "material_instance_relation ((\<lambda>a. (a,Payload_Term (f a))) ` B) (schema_material_premises S) =
       material_instance_relation ((\<lambda>a. (a,Payload_Term (f a))) ` B) (schema_material_premises T)"
      "material_instance_relation ((\<lambda>a. (a,Target_Term k)) ` B) (schema_material_premises S) =
       material_instance_relation ((\<lambda>a. (a,Target_Term k)) ` B) (schema_material_premises T)"
  shows "schema_material_premises S=schema_material_premises T"
proof -
  let ?V="(\<lambda>a. (a,Payload_Term (f a))) ` B"
  let ?U="(\<lambda>a. (a,Target_Term k)) ` B"
  have inclusion: "schema_material_premises A\<subseteq>schema_material_premises D"
    if a: "schema_instance A ?V x Q" and d: "schema_instance D ?V x Q"
      and a': "schema_instance A ?U y W"
      and v: "material_instance_relation ?V (schema_material_premises A) =
        material_instance_relation ?V (schema_material_premises D)"
      and u: "material_instance_relation ?U (schema_material_premises A) =
        material_instance_relation ?U (schema_material_premises D)" for A D
  proof
    fix row assume member: "row\<in>schema_material_premises A"
    obtain s M where shape: "row=(s,M)" by (cases row)
    have source: "(s,M)\<in>schema_material_premises A" using member shape by simp
    obtain x a e b g where left: "material_pattern_instance ?V M x a e b g"
      using schema_material_instance_boundary[OF a source] by blast
    have own_row: "(s,material_tuple x a e b g)\<in>material_instance_relation ?V (schema_material_premises A)"
      using source left by (auto simp: material_instance_relation_def; blast)
    have row: "(s,material_tuple x a e b g)\<in>material_instance_relation ?V (schema_material_premises D)"
      using own_row v by simp
    obtain N where right: "(s,N)\<in>schema_material_premises D"
      "material_pattern_instance ?V N x a e b g"
      using row by (auto simp: material_instance_relation_def material_tuple_def)
    obtain y a' e' b' g' where left': "material_pattern_instance ?U M y a' e' b' g'"
      using schema_material_instance_boundary[OF a' source] by blast
    have own_row': "(s,material_tuple y a' e' b' g')\<in>material_instance_relation ?U (schema_material_premises A)"
      using source left' by (auto simp: material_instance_relation_def; blast)
    have row': "(s,material_tuple y a' e' b' g')\<in>material_instance_relation ?U (schema_material_premises D)"
      using own_row' u by simp
    obtain L where right': "(s,L)\<in>schema_material_premises D"
      "material_pattern_instance ?U L y a' e' b' g'"
      using row' by (auto simp: material_instance_relation_def material_tuple_def)
    have functional: "single_valued (schema_material_premises D)"
      using d by (simp add: schema_instance_def schema_formed_def)
    have same: "L=N" by (rule single_valued_outputs[OF functional right'(1) right(1)])
    have other: "material_pattern_instance ?U N y a' e' b' g'" using right'(2) same by simp
    have patterns: "M=N"
      by (rule material_pattern_instances_determine[OF injective left right(2) left' other])
    show "row\<in>schema_material_premises D" using right(1) shape patterns by simp
  qed
  show ?thesis
    using inclusion[OF first second(1) materials]
      inclusion[OF first(2,1) second(2) materials(1)[symmetric] materials(2)[symmetric]] by blast
qed

section \<open>The complete schema follows from both readings\<close>

theorem schema_instances_determine:
  assumes injective: "inj_on f B"
    and first: "schema_instance S ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
      "schema_instance T ((\<lambda>a. (a,Payload_Term (f a))) ` B) x Q"
    and second: "schema_instance S ((\<lambda>a. (a,Target_Term k)) ` B) y W"
      "schema_instance T ((\<lambda>a. (a,Target_Term k)) ` B) y W"
    and materials:
      "material_instance_relation ((\<lambda>a. (a,Payload_Term (f a))) ` B) (schema_material_premises S) =
       material_instance_relation ((\<lambda>a. (a,Payload_Term (f a))) ` B) (schema_material_premises T)"
      "material_instance_relation ((\<lambda>a. (a,Target_Term k)) ` B) (schema_material_premises S) =
       material_instance_relation ((\<lambda>a. (a,Target_Term k)) ` B) (schema_material_premises T)"
  shows "S=T"
proof -
  have head: "schema_conclusion S=schema_conclusion T"
    using first second unfolding schema_instance_def
    by (blast intro: pattern_instances_determine[OF injective])
  have calls: "schema_premises S=schema_premises T"
    by (rule schema_premises_instances_determine[OF injective first second])
  have material: "schema_material_premises S=schema_material_premises T"
    by (rule schema_material_instances_determine[OF injective first second materials])
  show ?thesis using head calls material by (cases S; cases T) auto
qed

section \<open>Omitting material outputs loses information even over every substitution\<close>

theorem schema_instances_do_not_determine_material_patterns:
  "\<exists>S T :: (unit,unit,unit) factor_schema. S\<noteq>T \<and>
    schema_material_premises S={} \<and> schema_material_premises T\<noteq>{} \<and>
    schema_variables S=schema_variables T \<and>
    (\<forall>V t Q. schema_instance S V t Q \<longleftrightarrow> schema_instance T V t Q)"
proof -
  let ?p="Pattern_Variable ()"
  let ?M="\<lparr>material_source=?p,material_atoms=?p,material_edges=?p,
    material_counts=?p,material_functions=?p\<rparr>"
  let ?S="recognizer_schema ?p :: (unit,unit,unit) factor_schema"
  let ?T="\<lparr>schema_conclusion=?p,schema_premises={},schema_material_premises={((),?M)}\<rparr>
    :: (unit,unit,unit) factor_schema"
  show ?thesis
    by (rule exI[of _ ?S], rule exI[of _ ?T])
      (auto simp: recognizer_schema_def schema_instance_def schema_premise_instance_def
        schema_variables_def schema_formed_def material_variables_def material_fields_def
        material_pattern_formed_def single_valued_def rel_dom_def)
qed

text \<open>
  Every prospective socket retains its callee and instantiated argument.
  Functional source rows ensure that the two readings concern the same
  pattern at that socket. Every material socket similarly retains all five
  operands. Both complete relations are needed: conclusion and prospective
  outputs alone say nothing about an omitted material condition.

  The result is equality of the complete finite schema. It consequently
  applies to every later substitution, material equation, and prospective
  call, without enumerating future arguments. Instantiation imposes no truth
  requirement on either kind of premise. No schema operator, grammar branch,
  proof rule, or observation primitive is added.
\<close>

end
