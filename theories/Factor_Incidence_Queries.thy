theory Factor_Incidence_Queries
  imports Factor_Material_Meaning Factor_Compiled_Applications Factor_Structure
begin

section \<open>A selected incidence can head a complete material enumeration\<close>

lemma artifact_enumeration_incidence_first:
  assumes formed: "exact_formed R" and member: "e \<in> rra_incidence (object_structure R)"
  shows "\<exists>A E B F. artifact_enumeration R A (e#E) B F"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F"
    using artifact_enumeration_exists[OF formed] by blast
  have distinct: "distinct A" "distinct E" "distinct F"
    using enumeration by (auto simp: artifact_enumeration_def)
  have source: "set E = rra_incidence (object_structure R)"
    by (rule artifact_enumeration_material(3)[OF enumeration])
  have listed: "e \<in> set E" using member source by simp
  have new_distinct: "distinct (e # remove1 e E)" using distinct(2) by simp
  have same: "set E = set (e # remove1 e E)" using distinct(2) listed by auto
  have reordered: "artifact_enumeration R A (e # remove1 e E) B F"
    using artifact_enumeration_order[OF distinct(1,1,2) new_distinct distinct(3,3)
        refl same refl refl] enumeration by blast
  show ?thesis using reordered by blast
qed

theorem material_incidence_head:
  "(\<exists>a z b f. material_observation s a (Pair_Term x z) b f) \<longleftrightarrow>
    (\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
      s=Target_Term (Whole_Artifact R) \<and> x=incidence_term R e)"
proof
  assume observed: "\<exists>a z b f. material_observation s a (Pair_Term x z) b f"
  obtain R A E B F z where enumeration: "artifact_enumeration R A E B F"
    and source: "s=Target_Term (Whole_Artifact R)"
    and edge_terms: "Pair_Term x z = enumeration_term (map (incidence_term R) E)"
    using observed by (auto simp: material_observation_def)
  have nonempty: "E \<noteq> []" using edge_terms by auto
  obtain e es where list: "E=e#es" using nonempty by (cases E) auto
  have head: "x=incidence_term R e" using edge_terms list by simp
  have formed: "exact_formed R" by (rule artifact_enumeration_material(1)[OF enumeration])
  have member: "e \<in> rra_incidence (object_structure R)"
    using artifact_enumeration_material(3)[OF enumeration] list by auto
  show "\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
    s=Target_Term (Whole_Artifact R) \<and> x=incidence_term R e"
    using formed member source head by blast
next
  assume witness: "\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
    s=Target_Term (Whole_Artifact R) \<and> x=incidence_term R e"
  obtain R e where source: "exact_formed R" "e \<in> rra_incidence (object_structure R)"
    "s=Target_Term (Whole_Artifact R)" "x=incidence_term R e"
    using witness by blast
  obtain A E B F where enumeration: "artifact_enumeration R A (e#E) B F"
    using artifact_enumeration_incidence_first[OF source(1,2)] by blast
  have observed: "material_observation s
    (enumeration_term (map (atom_term R) A))
    (Pair_Term x (enumeration_term (map (incidence_term R) E)))
    (enumeration_term (map (attachment_term R) B))
    (enumeration_term (map (attachment_term R) F))"
    using material_observation_exact[of R A "e#E" B F] enumeration source(3,4) by simp
  show "\<exists>a z b f. material_observation s a (Pair_Term x z) b f" using observed by blast
qed

section \<open>One ordinary finite schema queries every future incidence\<close>

definition incidence_query_material :: "nat material_pattern" where
  "incidence_query_material =
    \<lparr>material_source=Pattern_Variable 0, material_atoms=Pattern_Variable 2,
     material_edges=Pattern_Pair (Pattern_Variable 1) (Pattern_Variable 3),
     material_counts=Pattern_Variable 4, material_functions=Pattern_Variable 5\<rparr>"

definition incidence_query_schema :: "(nat,unit,unit) factor_schema" where
  "incidence_query_schema =
    \<lparr>schema_conclusion=Pattern_Pair (Pattern_Variable 0) (Pattern_Variable 1),
     schema_premises={}, schema_material_premises={((),incidence_query_material)}\<rparr>"

definition incidence_query_system :: "(nat,unit,unit,unit) schema_system" where
  "incidence_query_system =
    \<lparr>system_interfaces={((),Pattern_Variable 0)},
     system_clauses={(((),()),incidence_query_schema)}\<rparr>"

lemma incidence_query_system_formed [simp]: "schema_system_formed incidence_query_system"
  by (auto simp: schema_system_formed_def incidence_query_system_def incidence_query_schema_def
      incidence_query_material_def material_pattern_formed_def material_fields_def schema_formed_def
      system_definitions_def schema_dependencies_def rel_dom_def rel_ran_def single_valued_def)

lemma incidence_query_variables:
  "schema_variables incidence_query_schema = {0,1,2,3,4,5}"
  by (auto simp: schema_variables_def incidence_query_schema_def incidence_query_material_def
      material_variables_def material_fields_def)

lemma incidence_query_admits_material:
  assumes observed: "material_observation s a (Pair_Term x z) b f"
  shows "((),Pair_Term s x) \<in> positive_meaning incidence_query_system"
proof -
  let ?V = "{(0,s),(1,x),(2,a),(3,z),(4,b),(5,f)}"
  have formed: "term_formed s" "term_formed x" "term_formed a" "term_formed z" "term_formed b" "term_formed f"
    using material_observation_formed[OF observed] by auto
  have bindings: "term_bindings_formed (schema_variables incidence_query_schema) ?V"
    using formed by (auto simp: incidence_query_variables term_bindings_formed_def single_valued_def rel_dom_def)
  have sf: "schema_formed incidence_query_schema"
    using incidence_query_system_formed by (simp add: schema_system_formed_def incidence_query_system_def)
  have inst: "schema_instance incidence_query_schema ?V (Pair_Term s x) {}"
    using sf bindings by (auto simp: schema_instance_def incidence_query_schema_def
        schema_premise_instance_def single_valued_def rel_dom_def)
  have material_inst: "material_pattern_instance ?V incidence_query_material s a (Pair_Term x z) b f"
    by (simp add: material_pattern_instance_def incidence_query_material_def)
  have material: "schema_material_satisfied incidence_query_schema ?V"
    using material_inst observed by (auto simp: schema_material_satisfied_def incidence_query_schema_def
        material_pattern_satisfied_def; blast)
  have call: "schema_call_formed incidence_query_system () (Pair_Term s x)"
    using formed by (simp only: schema_call_formed_def incidence_query_system_formed)
      (simp add: incidence_query_system_def)
  have admitted: "admitted_schema_instance incidence_query_system () () ?V (Pair_Term s x) {}"
    using call inst material by (auto simp: admitted_schema_instance_def incidence_query_system_def)
  show ?thesis by (rule positive_meaning_step[OF admitted]) simp
qed

lemma incidence_query_instance_sound:
  assumes inst: "schema_instance incidence_query_schema V t Q"
    and material: "schema_material_satisfied incidence_query_schema V"
  shows "\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
    t=Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)"
proof -
  have sv: "single_valued V"
    using inst by (simp add: schema_instance_def term_bindings_formed_def)
  obtain s x where conclusion: "t=Pair_Term s x" "(0,s) \<in> V" "(1,x) \<in> V"
    using inst by (auto simp: schema_instance_def incidence_query_schema_def)
  obtain y a es b f where fields: "material_pattern_instance V incidence_query_material y a es b f"
    and observed: "material_observation y a es b f"
    using material by (auto simp: schema_material_satisfied_def incidence_query_schema_def
        material_pattern_satisfied_def)
  obtain h z where heads: "(0,y) \<in> V" "(1,h) \<in> V" "es=Pair_Term h z"
    using fields by (auto simp: material_pattern_instance_def incidence_query_material_def)
  have same_source: "s=y" by (rule single_valued_outputs[OF sv conclusion(2) heads(1)])
  have same_head: "x=h" by (rule single_valued_outputs[OF sv conclusion(3) heads(2)])
  have complete: "\<exists>a z b f. material_observation s a (Pair_Term x z) b f"
    using observed heads(3) same_source same_head by blast
  show ?thesis using complete conclusion(1) by (simp only: material_incidence_head) blast
qed

theorem incidence_query_exact:
  "((),t) \<in> positive_meaning incidence_query_system \<longleftrightarrow>
    (\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
      t=Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e))"
proof
  assume holds: "((),t) \<in> positive_meaning incidence_query_system"
  obtain c V Q where admitted: "admitted_schema_instance incidence_query_system () c V t Q"
    using holds by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have inst: "schema_instance incidence_query_schema V t Q"
    and material: "schema_material_satisfied incidence_query_schema V"
    using admitted by (auto simp: admitted_schema_instance_def incidence_query_system_def)
  show "\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
    t=Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)"
    by (rule incidence_query_instance_sound[OF inst material])
next
  assume witness: "\<exists>R e. exact_formed R \<and> e \<in> rra_incidence (object_structure R) \<and>
    t=Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)"
  then obtain R e where source: "exact_formed R" "e \<in> rra_incidence (object_structure R)"
    "t=Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)" by blast
  have complete: "\<exists>a z b f. material_observation (Target_Term (Whole_Artifact R)) a
    (Pair_Term (incidence_term R e) z) b f"
    by (simp only: material_incidence_head) (use source(1,2) in blast)
  show "((),t) \<in> positive_meaning incidence_query_system"
    using complete incidence_query_admits_material source(3) by blast
qed

corollary incidence_query_at:
  "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)) \<in>
    positive_meaning incidence_query_system \<longleftrightarrow>
    exact_formed R \<and> e \<in> rra_incidence (object_structure R)"
proof
  assume holds: "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)) \<in>
    positive_meaning incidence_query_system"
  then show "exact_formed R \<and> e \<in> rra_incidence (object_structure R)"
    by (auto simp: incidence_query_exact dest: injD[OF incidence_term_injective])
next
  assume source: "exact_formed R \<and> e \<in> rra_incidence (object_structure R)"
  show "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R e)) \<in>
    positive_meaning incidence_query_system"
    by (simp only: incidence_query_exact)
       (rule exI[of _ R], rule exI[of _ e]; use source in blast)
qed

section \<open>The four source relations are observations at their actual field heads\<close>

lemma four_structure_fields:
  assumes four: "four_structure_at R r F" and fields: "record_at R r ps [cr,oh,eh,nh,bh]"
  shows "four_own F = headed_incidence (object_structure R) oh"
    "four_end F = headed_incidence (object_structure R) eh"
    "four_next F = headed_incidence (object_structure R) nh"
    "four_bind F = headed_incidence (object_structure R) bh"
proof -
  obtain qs c own e n b where source:
    "record_at R r qs [c,own,e,n,b]"
    "four_own F = headed_incidence (object_structure R) own"
    "four_end F = headed_incidence (object_structure R) e"
    "four_next F = headed_incidence (object_structure R) n"
    "four_bind F = headed_incidence (object_structure R) b"
    using four unfolding four_structure_at_def by blast
  have same: "own=oh" "e=eh" "n=nh" "b=bh"
    using record_at_unique[OF source(1) fields] by auto
  show "four_own F = headed_incidence (object_structure R) oh"
    "four_end F = headed_incidence (object_structure R) eh"
    "four_next F = headed_incidence (object_structure R) nh"
    "four_bind F = headed_incidence (object_structure R) bh"
    using source(2-5) same by simp_all
qed

theorem four_relation_queries:
  assumes formed: "exact_formed R" and four: "four_structure_at R r F"
    and fields: "record_at R r ps [cr,oh,eh,nh,bh]"
  shows "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R (oh,a,b))) \<in>
      positive_meaning incidence_query_system \<longleftrightarrow> (a,b) \<in> four_own F"
    "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R (eh,a,b))) \<in>
      positive_meaning incidence_query_system \<longleftrightarrow> (a,b) \<in> four_end F"
    "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R (nh,a,b))) \<in>
      positive_meaning incidence_query_system \<longleftrightarrow> (a,b) \<in> four_next F"
    "((),Pair_Term (Target_Term (Whole_Artifact R)) (incidence_term R (bh,a,b))) \<in>
      positive_meaning incidence_query_system \<longleftrightarrow> (a,b) \<in> four_bind F"
  by (simp_all add: incidence_query_at formed four_structure_fields[OF four fields] headed_incidence_def)

text \<open>
  One generic program observes every ternary incidence of every formed future
  artifact. Its material equation retains all atoms, all incidences, and both
  data components. Selecting the first incidence is an existentially chosen
  complete enumeration, never permission to omit the rest.

  The four source relations are recovered from the actual ordered field heads
  of their structural representation. The query uses those heads as ordinary
  arguments; no wrapper depth or relation-name dispatch selects an operation.
  Native compilation and future-application construction apply to this formed
  finite system without any new semantic branch.
\<close>

end
