theory Factor_Audit_Counterparts
  imports Factor_Inclusion_Admission_Counterparts Factor_Payload_Audit Factor_Executable_Definitions
    Factor_Finite_Closed_Installation
begin

text \<open>
  The payload audit's counterpart (DECISIONS.md "The native evaluator evaluates above an implemented base: the
  given's readers enter through counterparts exact to their native definitions", build C3). On a term the
  source-root reader reads (@{thm [source] finite_source_root_read_exact}) it asks whether some reading of the
  definition at the argument's environment, use and address (@{const finite_native_definition_readings})
  states no payload but the empty one (@{const finite_definition_payloads}); every other term it refuses. It is
  exact at every finite term to the audit's result relation, from the readings' correctness and completeness
  and the payloads' exactness, and so to site 505's positive meaning by @{thm [source] payload_audit_exact}.
\<close>

definition finite_payload_audit :: "finite_factor_term \<Rightarrow> bool" where
  "finite_payload_audit t=(case finite_source_root_read t of None \<Rightarrow> False
    | Some ((E,u),r) \<Rightarrow> fBex (finite_native_definition_readings E u r)
        (\<lambda>(p,F). finite_definition_payloads p F |\<subseteq>| {|[]|}))"

theorem finite_payload_audit_exact:
  "finite_payload_audit t \<longleftrightarrow> payload_audit_result (decode_finite_term t)"
proof
  assume holds: "finite_payload_audit t"
  obtain E u r where read: "finite_source_root_read t=Some ((E,u),r)"
    using holds by (cases "finite_source_root_read t") (auto simp: finite_payload_audit_def)
  obtain p F where reading: "(p,F) |\<in>| finite_native_definition_readings E u r"
      and payloads: "finite_definition_payloads p F |\<subseteq>| {|[]|}"
    using holds read by (auto simp: finite_payload_audit_def)
  obtain e where argument: "decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r)"
      and source: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp only: finite_source_root_read_exact)
  have defined: "native_definition_at (decode_finite_environment E) u r (decode_finite_pattern p)
      (map_relation_values decode_finite_schema (fset F))"
    using reading by (simp only: finite_native_definition_readings_correct)
  have "fset (finite_definition_payloads p F)\<subseteq>{[]}"
    using payloads by (simp add: less_eq_fset.rep_eq)
  then have "definition_payloads (decode_finite_pattern p) (map_relation_values decode_finite_schema (fset F))\<subseteq>{[]}"
    by (simp only: map_relation_values_def finite_definition_payloads_exact)
  then show "payload_audit_result (decode_finite_term t)"
    using argument source defined by blast
next
  assume "payload_audit_result (decode_finite_term t)"
  then obtain E e u r p C where argument: "decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r)"
      and source: "environment_value_presents E e" and defined: "native_definition_at E u r p C"
      and payloads: "definition_payloads p C\<subseteq>{[]}" by blast
  obtain G where decoded: "decode_finite_environment G=E" by (rule environment_value_presents_finite[OF source])
  have read: "finite_source_root_read t=Some ((G,u),r)"
    unfolding finite_source_root_read_exact using argument source decoded by blast
  obtain q F where reading: "(q,F) |\<in>| finite_native_definition_readings G u r"
      and pattern: "decode_finite_pattern q=p" and clauses: "map_relation_values decode_finite_schema (fset F)=C"
    using finite_native_definition_readings_complete[of G u r p C] defined decoded by blast
  have "definition_payloads (decode_finite_pattern q) (map_relation_values decode_finite_schema (fset F))\<subseteq>{[]}"
    using payloads pattern clauses by simp
  then have "fset (finite_definition_payloads q F)\<subseteq>{[]}"
    by (simp only: map_relation_values_def finite_definition_payloads_exact)
  then have stated: "finite_definition_payloads q F |\<subseteq>| {|[]|}" by (simp add: less_eq_fset.rep_eq)
  show "finite_payload_audit t"
    unfolding finite_payload_audit_def using read reading stated by (auto intro!: fBexI[where x="(q,F)"])
qed

corollary finite_payload_audit_meaning:
  "finite_payload_audit t \<longleftrightarrow> (505,decode_finite_term t)\<in>positive_meaning payload_audit_system"
  by (simp only: finite_payload_audit_exact payload_audit_exact)

section \<open>Controls\<close>

text \<open>
  A one-definition program whose single clause states one payload literal, installed as the extension of the
  empty program over the empty package selected in the empty environment. The audit at the installed
  definition, beside the payloads its readings state, which the relation's outcome is by the exactness above:
  the empty payload alone, and a nonempty literal.
\<close>

definition audit_control_program :: "octets \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "audit_control_program v=\<lparr>finite_system_interfaces={|(0,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),\<lparr>finite_schema_conclusion=Finite_Pattern_Payload v,
      finite_schema_premises={||},finite_schema_materials={||}\<rparr>)|}\<rparr>"

abbreviation audit_control_selection :: "local_address option finite_artifact_environment\<times>local_address option" where
  "audit_control_selection\<equiv>empty_package_selection"

definition audit_control_installed :: "octets \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option) option" where
  "audit_control_installed v=finite_extend_mapped_native (fst audit_control_selection) empty_installation_program
    (audit_control_program v) (\<lambda>_. (None,[]))"

abbreviation finite_source_root_term ::
    "local_address option finite_artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow> finite_factor_term" where
  "finite_source_root_term E d\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value E) (finite_use_data (fst d))) (Finite_Payload (snd d))"

definition audit_control_outcomes :: "octets \<Rightarrow> (bool\<times>octets fset fset) fset option" where
  "audit_control_outcomes v=(case audit_control_installed v of None \<Rightarrow> None
    | Some (K,w) \<Rightarrow> map_option (\<lambda>R. fimage (\<lambda>d. (finite_payload_audit (finite_source_root_term K d),
        fimage (\<lambda>(p,F). finite_definition_payloads p F) (finite_native_definition_readings K (fst d) (snd d))))
      (finite_system_definitions R)) (finite_native_source K w []))"

value "[(''505: the definition states the empty payload'', audit_control_outcomes []),
  (''505: the definition states the literal [1]'', audit_control_outcomes [1])]"

end
