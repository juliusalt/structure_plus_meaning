theory Factor_Finite_Payload_Literals
  imports Factor_Positive_Parametricity Factor_Executable_Systems Factor_Pattern_Programs Factor_Finite_System_Fields
begin

section \<open>The octets a finite program reads as structure\<close>

text \<open>
  The payloads a program states literally are exactly the octets it reads as structure
  (\<open>positive_meaning_unlisted_payloads\<close>). A finite program presents every pattern it states, so
  those payloads are computed by reading its patterns once; the computation is the original set on
  every finite program. It audits a program's use of octets without running it: an empty result
  means the program treats every octet as inert.
\<close>

fun finite_pattern_payloads :: "'a finite_term_pattern \<Rightarrow> octets fset" where
  "finite_pattern_payloads (Finite_Variable a) = {||}"
| "finite_pattern_payloads (Finite_Pattern_Target t) = {||}"
| "finite_pattern_payloads (Finite_Pattern_Payload v) = {|v|}"
| "finite_pattern_payloads (Finite_Pattern_Pair p q) =
    finite_pattern_payloads p |\<union>| finite_pattern_payloads q"

lemma finite_pattern_payloads_exact:
  "v |\<in>| finite_pattern_payloads p \<longleftrightarrow> Payload_Term v \<in> pattern_leaves (decode_finite_pattern p)"
  by (induction p) auto

definition finite_material_payloads :: "'a finite_material_pattern \<Rightarrow> octets fset" where
  "finite_material_payloads M=finite_pattern_payloads (finite_material_source M) |\<union>|
    finite_pattern_payloads (finite_material_atoms M) |\<union>| finite_pattern_payloads (finite_material_edges M) |\<union>|
    finite_pattern_payloads (finite_material_counts M) |\<union>| finite_pattern_payloads (finite_material_functions M)"

lemma finite_material_payloads_exact:
  "v |\<in>| finite_material_payloads M \<longleftrightarrow> Payload_Term v \<in> material_leaves (decode_finite_material M)"
  by (auto simp: finite_material_payloads_def material_leaves_def material_fields_def
    decode_finite_material_def finite_pattern_payloads_exact)

definition finite_schema_payloads :: "('a,'s,'d) finite_factor_schema \<Rightarrow> octets fset" where
  "finite_schema_payloads S=finite_pattern_payloads (finite_schema_conclusion S) |\<union>|
    ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_payloads p) (finite_schema_premises S)) |\<union>|
    ffUnion (fimage (\<lambda>(s,M). finite_material_payloads M) (finite_schema_materials S))"

lemma finite_schema_payloads_exact:
  "v |\<in>| finite_schema_payloads S \<longleftrightarrow> Payload_Term v \<in> schema_leaves (decode_finite_schema S)"
proof -
  have calls: "v |\<in>| ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_payloads p) (finite_schema_premises S)) \<longleftrightarrow>
    Payload_Term v \<in> (\<Union>(s,d,p)\<in>schema_premises (decode_finite_schema S). pattern_leaves p)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_pattern_payloads_exact decode_finite_call_pattern_def
      map_relation_values_def split: prod.splits; force)
  have materials: "v |\<in>| ffUnion (fimage (\<lambda>(s,M). finite_material_payloads M) (finite_schema_materials S)) \<longleftrightarrow>
    Payload_Term v \<in> (\<Union>(s,M)\<in>schema_material_premises (decode_finite_schema S). material_leaves M)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_material_payloads_exact map_relation_values_def
      split: prod.splits; force)
  show ?thesis using calls materials
    by (simp add: finite_schema_payloads_def schema_leaves_def finite_pattern_payloads_exact)
qed

definition finite_system_payloads :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> octets fset" where
  "finite_system_payloads P=
    ffUnion (fimage (\<lambda>(d,p). finite_pattern_payloads p) (finite_system_interfaces P)) |\<union>|
    ffUnion (fimage (\<lambda>(dc,S). finite_schema_payloads S) (finite_system_clauses P))"

theorem finite_system_payloads_exact:
  "fset (finite_system_payloads P)=system_payloads (decode_finite_system P)"
proof -
  have interfaces: "\<And>v. v |\<in>| ffUnion (fimage (\<lambda>(d,p). finite_pattern_payloads p) (finite_system_interfaces P)) \<longleftrightarrow>
    Payload_Term v \<in> (\<Union>(d,p)\<in>system_interfaces (decode_finite_system P). pattern_leaves p)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_pattern_payloads_exact map_relation_values_def
      split: prod.splits; force)
  have clauses: "\<And>v. v |\<in>| ffUnion (fimage (\<lambda>(dc,S). finite_schema_payloads S) (finite_system_clauses P)) \<longleftrightarrow>
    Payload_Term v \<in> (\<Union>(dc,S)\<in>system_clauses (decode_finite_system P). schema_leaves S)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_schema_payloads_exact map_relation_values_def
      split: prod.splits; force)
  show ?thesis
  proof (rule set_eqI)
    fix v
    have "v |\<in>| finite_system_payloads P \<longleftrightarrow>
      v |\<in>| ffUnion (fimage (\<lambda>(d,p). finite_pattern_payloads p) (finite_system_interfaces P)) \<or>
      v |\<in>| ffUnion (fimage (\<lambda>(dc,S). finite_schema_payloads S) (finite_system_clauses P))"
      by (simp add: finite_system_payloads_def)
    also have "\<dots> \<longleftrightarrow> Payload_Term v \<in> system_leaves (decode_finite_system P)"
      unfolding interfaces clauses system_leaves_def by (rule Un_iff[symmetric])
    finally show "v \<in> fset (finite_system_payloads P) \<longleftrightarrow> v \<in> system_payloads (decode_finite_system P)"
      by (simp add: system_payloads_def)
  qed
qed

text \<open>
  The payloads of a finite term are the octets it carries. A ground program recognizes each of its
  rows by an exact pattern of that row, so the octets such a program reads as structure are those
  of its rows: every octet of a row a decision is reflected into is read by that decision.
\<close>

text \<open>
  The payloads a term carries are the payload leaves of its exact pattern (@{text term_payloads}); a finite
  term carries exactly the payloads of the term it decodes to (@{text finite_term_payloads_term}), so the
  finite set and the abstract set are one notion.
\<close>

fun term_payloads :: "factor_term \<Rightarrow> octets set" where
  "term_payloads (Target_Term x)={}"
| "term_payloads (Payload_Term v)={v}"
| "term_payloads (Pair_Term x y)=term_payloads x \<union> term_payloads y"

lemma term_payloads_exact_pattern:
  "term_payloads t={v. Payload_Term v\<in>pattern_leaves (exact_term_pattern t)}"
  by (induction t) auto

fun finite_term_payloads :: "finite_factor_term \<Rightarrow> octets fset" where
  "finite_term_payloads (Finite_Target t) = {||}"
| "finite_term_payloads (Finite_Payload v) = {|v|}"
| "finite_term_payloads (Finite_Pair x y) = finite_term_payloads x |\<union>| finite_term_payloads y"

lemma finite_term_payloads_term:
  "fset (finite_term_payloads t)=term_payloads (decode_finite_term t)"
  by (induction t) auto

lemma finite_term_payloads_exact_pattern:
  "fset (finite_term_payloads t)={v. Payload_Term v \<in> pattern_leaves (exact_term_pattern (decode_finite_term t))}"
  by (subst finite_term_payloads_term) (rule term_payloads_exact_pattern)

text \<open>A renaming of sites changes no payload a schema or a program states.\<close>

lemma finite_rename_schema_payloads:
  "finite_schema_payloads (finite_rename_schema id id g S)=finite_schema_payloads S"
  by (simp add: finite_schema_payloads_def finite_rename_schema_def finite_material_payloads_def
    finite_rename_material_def finite_term_pattern.map_id fset.map_comp comp_def case_prod_unfold)

lemma finite_rename_system_payloads:
  "finite_system_payloads (finite_rename_system g P)=finite_system_payloads P"
  by (simp add: finite_system_payloads_def finite_rename_system_def fset.map_comp comp_def case_prod_unfold
    finite_rename_schema_payloads map_prod_def)

export_code finite_system_payloads finite_term_payloads checking SML

end
