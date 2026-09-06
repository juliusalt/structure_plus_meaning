theory Factor_Construction_Order_Audit
  imports Factor_Construction_Permission_Examples Factor_Encoding_Order_Audit
begin

section \<open>An order-sensitive definition fails unordered permission admission\<close>

definition order_audit_bases :: "(local_address \<times> exact_artifact) set" where
  "order_audit_bases = {([],empty_artifact),([0],empty_artifact)}"

abbreviation order_audit_claim :: factor_term where
  "order_audit_claim \<equiv> construction_claim_term [] order_audit_bases empty_source_construction empty_artifact"

definition reversed_base_claim :: factor_term where
  "reversed_base_claim = enumeration_term
    [artifact_list_term [],
     enumeration_term [Pair_Term (Payload_Term [0]) (Target_Term (Whole_Artifact empty_artifact)),
       Pair_Term (Payload_Term []) (Target_Term (Whole_Artifact empty_artifact))],
     finite_table_term Payload_Term construction_selection_term {},
     finite_table_term construction_atom_term Payload_Term {},
     Target_Term (Whole_Artifact empty_artifact)]"

lemma order_audit_construction:
  "source_constructs [] order_audit_bases empty_source_construction empty_artifact"
  by (rule source_constructs_empty)
     (auto simp: construction_sources_formed_def order_audit_bases_def single_valued_def)

lemma order_audit_coordinates:
  "construction_coordinates_formed order_audit_bases empty_source_construction"
  by (auto simp: construction_coordinates_formed_def order_audit_bases_def
    empty_source_construction_def octets_formed_def)

lemma reversed_base_claim_presents:
  "construction_claim_presents [] order_audit_bases empty_source_construction empty_artifact reversed_base_claim"
proof -
  let ?rows = "[([0],empty_artifact),([],empty_artifact)]"
  let ?row = "\<lambda>z. Pair_Term (Payload_Term (fst z)) (Target_Term (Whole_Artifact (snd z)))"
  let ?read = "table_entry_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T))"
  have base_rows: "finite_collection_presents ?read order_audit_bases (enumeration_term (map ?row ?rows))"
    by (rule finite_collection_presents_map[where f="?row" and xs="?rows"])
       (auto simp: order_audit_bases_def table_entry_presents_def)
  have bases: "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T))
    order_audit_bases (enumeration_term (map ?row ?rows))"
    using base_rows by (auto simp: finite_table_presents_def order_audit_bases_def single_valued_def)
  have selections: "finite_table_presents Payload_Term construction_selection_presents {}
    (finite_table_term Payload_Term construction_selection_term {})"
    by (rule finite_table_term_presents) (auto simp: single_valued_def)
  have origins: "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) {}
    (finite_table_term construction_atom_term Payload_Term {})"
    by (rule finite_table_term_presents) (auto simp: single_valued_def)
  show ?thesis using bases selections origins
    by (auto simp: construction_claim_presents_def reversed_base_claim_def empty_source_construction_def)
qed

lemma reversed_base_claim_different:
  "reversed_base_claim \<noteq> order_audit_claim"
proof -
  have sv: "single_valued order_audit_bases"
    by (auto simp: order_audit_bases_def single_valued_def)
  have left: "rel_value order_audit_bases []=empty_artifact"
    by (rule rel_value_eq[OF sv]) (simp add: order_audit_bases_def)
  have right: "rel_value order_audit_bases [0]=empty_artifact"
    by (rule rel_value_eq[OF sv]) (simp add: order_audit_bases_def)
  have domain: "rel_dom order_audit_bases={[],[0]}"
    by (auto simp: order_audit_bases_def rel_dom_def)
  show ?thesis
    by (simp add: reversed_base_claim_def construction_claim_term_def finite_table_term_def
      finite_table_rows_def domain left right empty_source_construction_def)
qed

definition order_sensitive_construction_program :: "(nat,unit,unit,unit) schema_system" where
  "order_sensitive_construction_program = recognizer_system 0 (exact_term_pattern order_audit_claim)"

lemma order_sensitive_construction_meaning:
  "((),order_audit_claim)\<in>positive_meaning order_sensitive_construction_program"
  "((),reversed_base_claim)\<notin>positive_meaning order_sensitive_construction_program"
proof -
  have tf: "term_formed order_audit_claim"
    by (rule construction_claim_formed[OF order_audit_construction order_audit_coordinates])
  have pf: "pattern_formed (exact_term_pattern order_audit_claim)" using tf by simp
  show "((),order_audit_claim)\<in>positive_meaning order_sensitive_construction_program"
    using recognizer_positive_meaning[OF pf, where a="0::nat" and t=order_audit_claim] tf
    by (simp add: order_sensitive_construction_program_def)
  show "((),reversed_base_claim)\<notin>positive_meaning order_sensitive_construction_program"
    using recognizer_positive_meaning[OF pf, where a="0::nat" and t=reversed_base_claim]
      reversed_base_claim_different by (simp add: order_sensitive_construction_program_def)
qed

theorem order_sensitive_construction_not_admitted:
  "\<not>construction_permission_invariant order_sensitive_construction_program ()"
proof
  assume invariant: "construction_permission_invariant order_sensitive_construction_program ()"
  have same: "((),order_audit_claim)\<in>positive_meaning order_sensitive_construction_program \<longleftrightarrow>
    ((),reversed_base_claim)\<in>positive_meaning order_sensitive_construction_program"
    by (rule construction_permission_invariantD(2)[OF invariant order_audit_construction
      order_audit_coordinates construction_claim_term_presents[OF order_audit_construction]
      reversed_base_claim_presents])
  show False using same order_sensitive_construction_meaning by blast
qed

theorem canonical_truth_alone_does_not_give_construction_permission:
  "((),order_audit_claim)\<in>positive_meaning order_sensitive_construction_program"
  "\<not>factor_constructs order_sensitive_construction_program ()
    [] order_audit_bases empty_source_construction empty_artifact"
  using order_sensitive_construction_meaning(1) order_sensitive_construction_not_admitted
  by (auto simp: factor_constructs_def)

theorem output_permission_has_an_accepted_account:
  "factor_constructs (recognizer_system 0 (construction_output_pattern empty_artifact)) ()
    [] order_audit_bases empty_source_construction empty_artifact"
  using construction_output_permission[OF empty_artifact_formed]
    order_audit_construction order_audit_coordinates by blast

text \<open>
  Both arguments present one valid account, including the same two unused base
  entries. One ordinary finite program accepts the canonical serialization and
  rejects the reversed serialization. The revised permission judgment rejects
  that program's admission for unordered construction accounts. The output
  recognizer is admitted and permits this account with either presentation.
\<close>

end
