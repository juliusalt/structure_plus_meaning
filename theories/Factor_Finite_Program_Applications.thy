theory Factor_Finite_Program_Applications
  imports Factor_Requested_Application_Readings Factor_Executable_Systems Factor_Inference_Development
    Inference_Embeddings
begin

section \<open>The complete original program supplies every requested rule\<close>

definition finite_program_applications where
  "finite_program_applications P D=ffUnion (fimage (\<lambda>(d,t).
    ffUnion (fimage (\<lambda>((e,c),S). if e=d then
      fimage (\<lambda>(x,V,H). (d,c,x,V,H))
        (ffilter (\<lambda>(x,V,H). finite_admitted_schema_instance P d c V x H)
          (finite_requested_schema_applications S t)) else {||}) (finite_system_clauses P))) D)"

lemma finite_program_application_member:
  "(d,c,t,V,H) |\<in>| finite_program_applications P D \<longleftrightarrow>
    (d,t) |\<in>| D \<and> finite_admitted_schema_instance P d c V t H \<and>
    (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses P \<and>
      (t,V,H) |\<in>| finite_requested_schema_applications S t)"
  using finite_requested_schema_application_sound(1)
  by (auto simp: finite_program_applications_def ffUnion.rep_eq fimage.rep_eq
    Bex_def split: prod.splits if_splits; force)

definition finite_program_head_covered where
  "finite_program_head_covered P D \<longleftrightarrow>
    fBall (finite_system_clauses P) (\<lambda>((d,c),S).
      d |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||})"

lemma finite_program_requested_head_covered:
  assumes covered: "finite_program_head_covered P D"
    and clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and demand: "(d,t) |\<in>| D"
  shows "finite_schema_head_missing S={||}"
proof -
  have key: "d |\<in>| fimage fst D" using demand by force
  show ?thesis
    using fbspec[OF covered[unfolded finite_program_head_covered_def] clause] key by simp
qed

lemma finite_program_application_complete:
  assumes inst: "admitted_schema_instance (decode_finite_system P) d c V (decode_finite_term t) H"
    and demand: "(d,t) |\<in>| D" and covered: "finite_program_head_covered P D"
  shows "\<exists>B G. (d,c,t,B,G) |\<in>| finite_program_applications P D \<and>
    decode_finite_term_bindings B=V \<and> decode_finite_premises G=H"
proof -
  obtain S where clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and schema: "schema_instance (decode_finite_schema S) V (decode_finite_term t) H"
    and material: "schema_material_satisfied (decode_finite_schema S) V"
    using inst by (auto simp: admitted_schema_instance_def)
  have scope: "finite_schema_head_missing S={||}"
    by (rule finite_program_requested_head_covered[OF covered clause demand])
  obtain B G where application: "(t,B,G) |\<in>| finite_requested_schema_applications S t"
    and fields: "decode_finite_term_bindings B=V" "decode_finite_premises G=H"
    using finite_requested_application_reading[OF schema material scope] by blast
  have checked: "finite_admitted_schema_instance P d c B t G"
    by (simp only: finite_admitted_schema_instance_correct fields; rule inst)
  show ?thesis by (rule exI[of _ B], rule exI[of _ G])
    (use demand checked clause application fields in \<open>auto simp: finite_program_application_member\<close>)
qed

theorem finite_program_application_exact:
  assumes covered: "finite_program_head_covered P D"
  shows "(d,c,t,V,H) |\<in>| finite_program_applications P D \<longleftrightarrow>
    (d,t) |\<in>| D \<and> finite_admitted_schema_instance P d c V t H"
proof
  assume "(d,c,t,V,H) |\<in>| finite_program_applications P D"
  then show "(d,t) |\<in>| D \<and> finite_admitted_schema_instance P d c V t H"
    by (simp only: finite_program_application_member; blast)
next
  assume fields: "(d,t) |\<in>| D \<and> finite_admitted_schema_instance P d c V t H"
  obtain S where clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and inst: "finite_schema_instance S V t H" and material: "finite_schema_material_satisfied S V"
    using fields by (auto simp: finite_admitted_schema_instance_def)
  have scope: "finite_schema_head_missing S={||}"
    by (rule finite_program_requested_head_covered[OF covered clause]) (use fields in blast)
  have requested: "(t,V,H) |\<in>| finite_requested_schema_applications S t"
    by (simp only: finite_requested_schema_applications_exact[OF scope] inst material)
  show "(d,c,t,V,H) |\<in>| finite_program_applications P D"
    using fields clause requested by (simp only: finite_program_application_member; blast)
qed

fun finite_program_application_rule where
  "finite_program_application_rule (d,c,t,V,H)=((d,t),H)"

definition finite_program_rule_table where
  "finite_program_rule_table P D=fimage finite_program_application_rule (finite_program_applications P D)"

lemma finite_program_rule_member:
  "((d,t),H) |\<in>| finite_program_rule_table P D \<longleftrightarrow>
    (\<exists>c V. (d,c,t,V,H) |\<in>| finite_program_applications P D)"
  by (auto simp: finite_program_rule_table_def fimage.rep_eq split: prod.splits; force)

lemma finite_program_rule_head:
  "(q,H) |\<in>| finite_program_rule_table P D \<Longrightarrow> q |\<in>| D"
  by (cases q) (auto simp: finite_program_rule_member finite_program_application_member)

lemma finite_program_rule_functional:
  assumes "(q,H) |\<in>| finite_program_rule_table P D"
  shows "single_valued (fset H)"
proof -
  obtain d t where shape: "q=(d,t)" by (cases q) auto
  obtain c V where checked: "finite_admitted_schema_instance P d c V t H"
    using assms by (auto simp: shape finite_program_rule_member finite_program_application_member)
  have inst: "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
    (decode_finite_term t) (decode_finite_premises H)"
    using checked by (simp only: finite_admitted_schema_instance_correct)
  show ?thesis using admitted_instance_formed[OF inst]
    by (simp add: decode_finite_premises_def map_relation_values_functional[OF decode_finite_call_inj(2)])
qed

theorem finite_program_rules_exact:
  assumes covered: "finite_program_head_covered P D"
  shows "embedded_inferences decode_finite_call_term (finite_inference_rules (finite_program_rule_table P D)) q H
    \<longleftrightarrow> schema_inference_rules (decode_finite_system P) q H \<and>
      q\<in>decode_finite_call_term ` fset D"
proof
  assume rule: "embedded_inferences decode_finite_call_term
    (finite_inference_rules (finite_program_rule_table P D)) q H"
  obtain d t G c V where fields: "q=(d,decode_finite_term t)" "H=decode_finite_premises G"
    and application: "(d,c,t,V,G) |\<in>| finite_program_applications P D"
    using rule by (auto simp: embedded_inferences_def finite_inference_rules_def
      finite_program_rule_member decode_finite_premises_def split_paired_Ex)
  have demand: "(d,t) |\<in>| D"
    and inst: "admitted_schema_instance (decode_finite_system P) d c
      (decode_finite_term_bindings V) (decode_finite_term t) (decode_finite_premises G)"
    using application by (auto simp: finite_program_application_member finite_admitted_schema_instance_correct)
  show "schema_inference_rules (decode_finite_system P) q H \<and> q\<in>decode_finite_call_term ` fset D"
    using demand inst by (auto simp: fields schema_inference_rules_def decode_finite_call_term_def map_prod_def)
next
  assume rule: "schema_inference_rules (decode_finite_system P) q H \<and>
    q\<in>decode_finite_call_term ` fset D"
  obtain d t where fields: "q=(d,decode_finite_term t)" and demand: "(d,t) |\<in>| D"
    using rule by (auto simp: decode_finite_call_term_def map_prod_def)
  obtain c V where inst:
    "admitted_schema_instance (decode_finite_system P) d c V (decode_finite_term t) H"
    using rule by (auto simp: fields schema_inference_rules_def)
  obtain B G where application: "(d,c,t,B,G) |\<in>| finite_program_applications P D"
    and decoded: "decode_finite_premises G=H"
    using finite_program_application_complete[OF inst demand covered] by blast
  have member: "((d,t),G) |\<in>| finite_program_rule_table P D"
    using application by (auto simp: finite_program_rule_member)
  have functional: "single_valued (fset G)" by (rule finite_program_rule_functional[OF member])
  show "embedded_inferences decode_finite_call_term
    (finite_inference_rules (finite_program_rule_table P D)) q H"
    unfolding embedded_inferences_def
    by (rule exI[of _ "(d,t)"], rule exI[of _ "fset G"])
      (use fields decoded member functional in
        \<open>auto simp: finite_inference_rules_def decode_finite_premises_def\<close>)
qed

export_code finite_program_applications finite_program_head_covered finite_program_rule_table checking SML

text \<open>
  The inputs are a complete program and actual requested calls. Every returned
  application retains its original clause, complete bindings and premise
  sockets, and passes the existing admitted-inst checker including material
  obligations and all call interfaces. Complete scope of each requested
  definition's clause heads makes the generated rules exhaustive for those
  calls. The application family is not a family of established conclusions.
\<close>

end
