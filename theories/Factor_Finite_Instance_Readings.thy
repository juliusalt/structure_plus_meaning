theory Factor_Finite_Instance_Readings
  imports Factor_Executable_Systems Factor_Instantiated_Premises
begin

definition finite_admitted_premise_readings where
  "finite_admitted_premise_readings P d c V t=fimage (\<lambda>((e,k),S). finite_instantiated_premises S V)
    (ffilter (\<lambda>((e,k),S). e=d \<and> k=c \<and>
      finite_admitted_schema_instance P d c V t (finite_instantiated_premises S V)) (finite_system_clauses P))"

theorem finite_admitted_premise_reading_exact:
  "H |\<in>| finite_admitted_premise_readings P d c V t \<longleftrightarrow>
    finite_admitted_schema_instance P d c V t H"
proof
  assume member: "H |\<in>| finite_admitted_premise_readings P d c V t"
  then show "finite_admitted_schema_instance P d c V t H"
    by (auto simp: finite_admitted_premise_readings_def)
next
  assume admitted: "finite_admitted_schema_instance P d c V t H"
  obtain S where clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and inst: "finite_schema_instance S V t H"
    using admitted by (auto simp: finite_admitted_schema_instance_def)
  have body: "finite_instantiated_premises S V=H" by (rule finite_instantiated_premises_exact[OF inst])
  show "H |\<in>| finite_admitted_premise_readings P d c V t"
    using clause admitted body by (auto simp: finite_admitted_premise_readings_def; force)
qed

theorem finite_admitted_premise_readings_correct:
  "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
    (decode_finite_term t) H \<longleftrightarrow>
    (\<exists>Q. Q |\<in>| finite_admitted_premise_readings P d c V t \<and> decode_finite_premises Q=H)"
proof
  assume admitted: "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
    (decode_finite_term t) H"
  obtain S where clause: "((d,c),S) |\<in>| finite_system_clauses P"
    and inst: "schema_instance (decode_finite_schema S) (decode_finite_term_bindings V) (decode_finite_term t) H"
    using admitted by (auto simp: admitted_schema_instance_def)
  have body: "decode_finite_premises (finite_instantiated_premises S V)=H"
    by (rule finite_instantiated_premises_correct[OF inst])
  have checked: "finite_admitted_schema_instance P d c V t (finite_instantiated_premises S V)"
    by (simp only: finite_admitted_schema_instance_correct body; rule admitted)
  show "\<exists>Q. Q |\<in>| finite_admitted_premise_readings P d c V t \<and> decode_finite_premises Q=H"
    using checked body by (simp only: finite_admitted_premise_reading_exact; blast)
next
  assume "\<exists>Q. Q |\<in>| finite_admitted_premise_readings P d c V t \<and> decode_finite_premises Q=H"
  then show "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
    (decode_finite_term t) H"
    by (simp only: finite_admitted_premise_reading_exact finite_admitted_schema_instance_correct; blast)
qed

text \<open>
  The actual source clause and complete supplied binding family determine
  every admitted premise relation. The reader is exact on all finite inputs
  and requires no head-coverage restriction. It reuses the existing complete
  premise instantiation and admitted-instance checks.
\<close>

end
