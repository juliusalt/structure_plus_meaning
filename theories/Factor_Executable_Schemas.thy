theory Factor_Executable_Schemas
  imports Factor_Executable_Instances Factor_Schemas
begin

section \<open>Complete finite schema fields\<close>

definition decode_finite_call_pattern ::
  "('d \<times> 'a finite_term_pattern) \<Rightarrow> ('d \<times> 'a term_pattern)" where
  "decode_finite_call_pattern = map_prod id decode_finite_pattern"

definition decode_finite_call_term ::
  "('d \<times> finite_factor_term) \<Rightarrow> ('d \<times> factor_term)" where
  "decode_finite_call_term = map_prod id decode_finite_term"

lemma decode_finite_call_pair [simp]:
  "decode_finite_call_pattern (d,p) = (d,decode_finite_pattern p)"
  "decode_finite_call_term (d,t) = (d,decode_finite_term t)"
  by (simp_all add: decode_finite_call_pattern_def decode_finite_call_term_def)

lemma decode_finite_call_inj:
  "inj (decode_finite_call_pattern :: ('d \<times> 'a finite_term_pattern) \<Rightarrow> _)"
  "inj (decode_finite_call_term :: ('d \<times> finite_factor_term) \<Rightarrow> _)"
  by (auto simp: inj_def decode_finite_call_pattern_def decode_finite_call_term_def split: prod.splits)

record ('a,'s,'d) finite_factor_schema =
  finite_schema_conclusion :: "'a finite_term_pattern"
  finite_schema_premises :: "('s \<times> ('d \<times> 'a finite_term_pattern)) fset"
  finite_schema_materials :: "('s \<times> 'a finite_material_pattern) fset"

definition decode_finite_schema ::
  "('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d) factor_schema" where
  "decode_finite_schema S =
    \<lparr>schema_conclusion=decode_finite_pattern (finite_schema_conclusion S),
     schema_premises=map_relation_values decode_finite_call_pattern (fset (finite_schema_premises S)),
     schema_material_premises=map_relation_values decode_finite_material (fset (finite_schema_materials S))\<rparr>"

lemma decode_finite_schema_fields [simp]:
  "schema_conclusion (decode_finite_schema S) = decode_finite_pattern (finite_schema_conclusion S)"
  "schema_premises (decode_finite_schema S) =
    map_relation_values decode_finite_call_pattern (fset (finite_schema_premises S))"
  "schema_material_premises (decode_finite_schema S) =
    map_relation_values decode_finite_material (fset (finite_schema_materials S))"
  by (simp_all add: decode_finite_schema_def)

definition finite_schema_variables :: "('a,'s,'d) finite_factor_schema \<Rightarrow> 'a fset" where
  "finite_schema_variables S = finite_pattern_variables (finite_schema_conclusion S) |\<union>|
    ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_variables p) (finite_schema_premises S)) |\<union>|
    ffUnion (fimage (\<lambda>(s,M). finite_material_variables M) (finite_schema_materials S))"

definition finite_schema_dependencies :: "('a,'s,'d) finite_factor_schema \<Rightarrow> 'd fset" where
  "finite_schema_dependencies S = fimage (\<lambda>(s,d,p). d) (finite_schema_premises S)"

definition finite_schema_formed :: "('a,'s,'d) finite_factor_schema \<Rightarrow> bool" where
  "finite_schema_formed S \<longleftrightarrow>
    finite_pattern_formed (finite_schema_conclusion S) \<and>
    finite_relation_functional (finite_schema_premises S) \<and>
    fBall (finite_schema_premises S) (\<lambda>(s,d,p). finite_pattern_formed p) \<and>
    finite_relation_functional (finite_schema_materials S) \<and>
    fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||} \<and>
    fBall (finite_schema_materials S) (\<lambda>(s,M). finite_material_formed M)"

lemma finite_schema_variables_correct:
  "fset (finite_schema_variables S) = schema_variables (decode_finite_schema S)"
  by (auto simp: finite_schema_variables_def schema_variables_def fimage.rep_eq ffUnion.rep_eq
      map_relation_values_def finite_pattern_variables_correct finite_material_variables_correct
      split: prod.splits)

lemma finite_schema_dependencies_correct:
  "fset (finite_schema_dependencies S) = schema_dependencies (decode_finite_schema S)"
  by (auto simp: finite_schema_dependencies_def schema_dependencies_def rel_ran_def
      map_relation_values_def decode_finite_call_pattern_def fimage.rep_eq split: prod.splits; force)

lemma finite_schema_formed_correct:
  "finite_schema_formed S \<longleftrightarrow> schema_formed (decode_finite_schema S)"
proof -
  have inj: "inj (decode_finite_material :: 'a finite_material_pattern \<Rightarrow> _)"
    by (auto simp: inj_def)
  have calls: "(\<forall>s d p. (s,d,p) \<in>
      map_relation_values decode_finite_call_pattern (fset (finite_schema_premises S)) \<longrightarrow> pattern_formed p)
      \<longleftrightarrow> fBall (finite_schema_premises S) (\<lambda>(s,d,p). finite_pattern_formed p)"
    by (auto simp: finite_pattern_formed_correct decode_finite_call_pattern_def
        Ball_def split_paired_All)
  have materials: "(\<forall>s M. (s,M) \<in>
      map_relation_values decode_finite_material (fset (finite_schema_materials S)) \<longrightarrow> material_pattern_formed M)
      \<longleftrightarrow> fBall (finite_schema_materials S) (\<lambda>(s,M). finite_material_formed M)"
    by (auto simp: finite_material_formed_correct Ball_def split_paired_All)
  show ?thesis
    by (simp only: finite_schema_formed_def schema_formed_def decode_finite_schema_fields
        finite_pattern_formed_correct finite_relation_functional_correct
        map_relation_values_functional[OF decode_finite_call_inj(1)]
        map_relation_values_functional[OF inj] calls materials map_relation_values_domain)
       (simp add: map_relation_values_finite fset_inject[symmetric] fimage.rep_eq rel_dom_image)
qed

lemma decode_finite_schema_injective [simp]:
  "decode_finite_schema S = decode_finite_schema T \<longleftrightarrow> S=T"
proof -
  have inj: "inj (decode_finite_material :: 'a finite_material_pattern \<Rightarrow> _)"
    by (auto simp: inj_def)
  show ?thesis by (cases S; cases T)
    (simp add: decode_finite_schema_def
      map_relation_values_injective[OF decode_finite_call_inj(1)]
      map_relation_values_injective[OF inj] fset_inject)
qed

definition finite_schema_of ::
  "('a,'s,'d) factor_schema \<Rightarrow> ('a,'s,'d) finite_factor_schema" where
  "finite_schema_of S =
    \<lparr>finite_schema_conclusion=finite_pattern_of (schema_conclusion S),
     finite_schema_premises=Abs_fset (map_relation_values (map_prod id finite_pattern_of) (schema_premises S)),
     finite_schema_materials=Abs_fset (map_relation_values finite_material_of (schema_material_premises S))\<rparr>"

lemma decode_finite_schema_of:
  assumes formed: "schema_formed S"
  shows "decode_finite_schema (finite_schema_of S) = S"
proof -
  have finite: "finite (schema_premises S)" "finite (schema_material_premises S)"
    and conclusion: "pattern_formed (schema_conclusion S)"
    using formed by (auto simp: schema_formed_def)
  have premise: "\<And>s x. (s,x) \<in> schema_premises S \<Longrightarrow>
      decode_finite_call_pattern (map_prod id finite_pattern_of x) = x"
    using formed by (auto simp: schema_formed_def decode_finite_call_pattern_def
      decode_finite_pattern_of split: prod.splits)
  have material: "\<And>s M. (s,M) \<in> schema_material_premises S \<Longrightarrow>
      decode_finite_material (finite_material_of M) = M"
    using formed by (auto simp: schema_formed_def intro: decode_finite_material_of)
  have p: "map_relation_values decode_finite_call_pattern
      (map_relation_values (map_prod id finite_pattern_of) (schema_premises S)) = schema_premises S"
    by (rule map_relation_values_inverse, rule premise)
  have m: "map_relation_values decode_finite_material
      (map_relation_values finite_material_of (schema_material_premises S)) = schema_material_premises S"
    by (rule map_relation_values_inverse, rule material)
  have pf: "fset (Abs_fset (map_relation_values (map_prod id finite_pattern_of) (schema_premises S))) =
      map_relation_values (map_prod id finite_pattern_of) (schema_premises S)"
    by (rule Abs_fset_inverse) (simp add: finite)
  have mf: "fset (Abs_fset (map_relation_values finite_material_of (schema_material_premises S))) =
      map_relation_values finite_material_of (schema_material_premises S)"
    by (rule Abs_fset_inverse) (simp add: finite)
  show ?thesis
    by (rule factor_schema.equality)
      (simp_all add: decode_finite_schema_def finite_schema_of_def pf mf p m
        decode_finite_pattern_of[OF conclusion])
qed

theorem finite_schema_representation:
  assumes "schema_formed S"
  shows "\<exists>!C. finite_schema_formed C \<and> decode_finite_schema C=S"
  by (rule ex1I[of _ "finite_schema_of S"])
    (use assms decode_finite_schema_of[OF assms] in \<open>auto simp: finite_schema_formed_correct\<close>)

section \<open>Checking complete schema instances\<close>

definition decode_finite_premises ::
  "('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> ('s \<times> ('d \<times> factor_term)) set" where
  "decode_finite_premises Q = map_relation_values decode_finite_call_term (fset Q)"

definition finite_schema_premise_instance ::
  "('a,'s,'d) finite_factor_schema \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow>
    ('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_schema_premise_instance S V Q \<longleftrightarrow>
    finite_relation_functional Q \<and> fimage fst Q = fimage fst (finite_schema_premises S) \<and>
    fBall (finite_schema_premises S) (\<lambda>(s,d,p).
      fBex Q (\<lambda>(r,e,t). r=s \<and> e=d \<and> finite_pattern_instance V p t))"

lemma finite_schema_premise_instance_correct:
  "finite_schema_premise_instance S V Q \<longleftrightarrow>
    schema_premise_instance (decode_finite_schema S) (decode_finite_term_bindings V) (decode_finite_premises Q)"
proof -
  have instances: "(\<forall>s d p. (s,d,p) \<in>
      map_relation_values decode_finite_call_pattern (fset (finite_schema_premises S)) \<longrightarrow>
      (\<exists>t. (s,d,t) \<in> map_relation_values decode_finite_call_term (fset Q) \<and>
        pattern_instance (decode_finite_term_bindings V) p t)) \<longleftrightarrow>
      fBall (finite_schema_premises S) (\<lambda>(s,d,p).
        fBex Q (\<lambda>(r,e,t). r=s \<and> e=d \<and> finite_pattern_instance V p t))"
    by (auto simp: decode_finite_call_pattern_def decode_finite_call_term_def
        finite_pattern_instance_correct Ball_def Bex_def split_paired_All split_paired_Ex; blast)
  show ?thesis
    by (simp only: finite_schema_premise_instance_def schema_premise_instance_def
        decode_finite_schema_fields decode_finite_premises_def finite_relation_functional_correct
        map_relation_values_functional[OF decode_finite_call_inj(2)]
        map_relation_values_domain instances)
       (simp add: fset_inject[symmetric] fimage.rep_eq rel_dom_image)
qed

definition finite_schema_instance ::
  "('a,'s,'d) finite_factor_schema \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow>
    finite_factor_term \<Rightarrow> ('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_schema_instance S V t Q \<longleftrightarrow>
    finite_schema_formed S \<and> finite_term_bindings_formed (finite_schema_variables S) V \<and>
    finite_pattern_instance V (finite_schema_conclusion S) t \<and> finite_schema_premise_instance S V Q"

lemma finite_schema_instance_correct:
  "finite_schema_instance S V t Q \<longleftrightarrow>
    schema_instance (decode_finite_schema S) (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises Q)"
  by (simp add: finite_schema_instance_def schema_instance_def finite_schema_formed_correct
      finite_term_bindings_formed_correct finite_schema_variables_correct
      finite_pattern_instance_correct finite_schema_premise_instance_correct)

definition finite_schema_material_satisfied ::
  "('a,'s,'d) finite_factor_schema \<Rightarrow> ('a \<times> finite_factor_term) fset \<Rightarrow> bool" where
  "finite_schema_material_satisfied S V \<longleftrightarrow>
    fBall (finite_schema_materials S) (\<lambda>(s,M). finite_material_satisfied V M)"

lemma finite_schema_material_satisfied_correct:
  "finite_schema_material_satisfied S V \<longleftrightarrow>
    schema_material_satisfied (decode_finite_schema S) (decode_finite_term_bindings V)"
  by (auto simp: finite_schema_material_satisfied_def schema_material_satisfied_def
      finite_material_satisfied_correct Ball_def split_paired_All)

export_code finite_schema_formed finite_schema_instance finite_schema_material_satisfied checking SML

end
