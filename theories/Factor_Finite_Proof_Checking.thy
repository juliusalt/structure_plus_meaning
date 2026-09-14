theory Factor_Finite_Proof_Checking
  imports Factor_Finite_Derivations Factor_Finite_Instance_Readings Factor_Executable_Readings
begin

primrec finite_checks_schema_proof ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'c) finite_schema_proof\<Rightarrow>'d\<Rightarrow>finite_factor_term\<Rightarrow>bool" where
  "finite_checks_schema_proof P (Schema_Proof c V B) d t=(finite_relation_functional B \<and>
    fBex (finite_admitted_premise_readings P d c V t) (\<lambda>H.
      fimage fst B=fimage fst H \<and>
      fBall (fimage (map_prod id (finite_checks_schema_proof P)) B) (\<lambda>(s,F).
        fBex H (\<lambda>(r,e,x). r=s \<and> F e x))))"

lemma finite_checks_schema_proof_node:
  "finite_checks_schema_proof P (Schema_Proof c V B) d t \<longleftrightarrow>
    finite_relation_functional B \<and> (\<exists>H. H |\<in>| finite_admitted_premise_readings P d c V t \<and>
      fimage fst B=fimage fst H \<and>
      (\<forall>s p. (s,p) |\<in>| B \<longrightarrow> (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)))"
  apply (simp only: finite_checks_schema_proof.simps fimage_pair_forall)
  by (auto simp: Bex_def split_paired_Ex)

theorem finite_checks_schema_proof_exact:
  "finite_checks_schema_proof P p d t \<longleftrightarrow>
    checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
proof (induction p arbitrary: d t)
  case (Schema_Proof c V B)
  have recursive: "finite_checks_schema_proof P p e x \<longleftrightarrow>
    checks_schema_proof (decode_finite_system P) (decode_finite_proof p) e (decode_finite_term x)"
    if "(s,p) |\<in>| B" for s p e x
    using Schema_Proof.IH that by (auto simp: Basic_BNFs.prod_set_defs)
  have child: "(\<exists>e x. (s,e,x)\<in>decode_finite_premises H \<and>
      checks_schema_proof (decode_finite_system P) (decode_finite_proof p) e x) \<longleftrightarrow>
    (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)"
    if member: "(s,p) |\<in>| B" for s p H
    apply (simp only: decode_finite_premises_value_member)
    using recursive[OF member] by blast
  have children: "(\<forall>s q. (s,q)\<in>fset (fimage (map_prod id decode_finite_proof) B) \<longrightarrow>
      (\<exists>e x. (s,e,x)\<in>decode_finite_premises H \<and>
        checks_schema_proof (decode_finite_system P) q e x)) \<longleftrightarrow>
    (\<forall>s p. (s,p) |\<in>| B \<longrightarrow>
      (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x))" for H
    using child by (simp only: decoded_proof_family_all; blast)
  show ?case
  proof
    assume checked: "finite_checks_schema_proof P (Schema_Proof c V B) d t"
    obtain H where reading: "H |\<in>| finite_admitted_premise_readings P d c V t"
      and fields: "finite_relation_functional B" "fimage fst B=fimage fst H"
        "\<forall>s p. (s,p) |\<in>| B \<longrightarrow>
          (\<exists>e x. (s,e,x) |\<in>| H \<and> finite_checks_schema_proof P p e x)"
      using checked by (simp only: finite_checks_schema_proof_node; blast)
    have inst: "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises H)"
      using reading by (simp only: finite_admitted_premise_reading_exact finite_admitted_schema_instance_correct)
    show "checks_schema_proof (decode_finite_system P) (decode_finite_proof (Schema_Proof c V B))
      d (decode_finite_term t)"
      apply (simp only: decode_finite_proof_node checks_schema_proof_node decode_finite_binding_set_values)
      apply (rule exI[of _ "decode_finite_premises H"])
      using inst fields by (simp only: decoded_proof_family_functional decoded_proof_family_domain
        decode_finite_premises_domain fset_inject children; blast)
  next
    assume checked: "checks_schema_proof (decode_finite_system P) (decode_finite_proof (Schema_Proof c V B))
      d (decode_finite_term t)"
    obtain H where inst: "admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
        (decode_finite_term t) H"
      and fields: "single_valued (fset (fimage (map_prod id decode_finite_proof) B))"
        "rel_dom (fset (fimage (map_prod id decode_finite_proof) B))=rel_dom H"
        "\<forall>s q. (s,q)\<in>fset (fimage (map_prod id decode_finite_proof) B) \<longrightarrow>
          (\<exists>e x. (s,e,x)\<in>H \<and> checks_schema_proof (decode_finite_system P) q e x)"
      using checked by (simp only: decode_finite_proof_node checks_schema_proof_node
        decode_finite_binding_set_values; blast)
    obtain Q where reading: "Q |\<in>| finite_admitted_premise_readings P d c V t"
      and decoded: "H=decode_finite_premises Q"
      using inst by (simp only: finite_admitted_premise_readings_correct; blast)
    show "finite_checks_schema_proof P (Schema_Proof c V B) d t"
      using reading fields by (simp only: finite_checks_schema_proof_node decoded
        decoded_proof_family_functional decoded_proof_family_domain decode_finite_premises_domain
        fset_inject children; blast)
  qed
qed

export_code finite_checks_schema_proof checking SML

text \<open>
  The executable checker recovers each complete premise relation from the
  original source clause, checks complete bindings and material conditions,
  and recursively checks the actual child at every required socket. Its exact
  condition is the existing proof checker for the complete decoded certificate,
  including malformed inputs. Construction and inspection remain independent.
\<close>

end
