theory Development_Given_Frames
  imports Development_Given_Installed_Declarations Factor_Native_Committed_Registrations
begin

text \<open>
  The frames declared beside the records (#603's, #607's, #679's, #681's, #758's and #760's), each discharged at its
  notion's system with its own record, are carried to the rooted readers by the transfer by agreement at the common
  definitions (@{text frames_agree_read_discharged}), as the records are. At the given's record each family is
  discharged record by record: at its own record by that discharge, at every other one vacuously, no other record
  holding a socket at a frame's key (the sites differ, and at 105 the two kept sockets stand at different clauses).
  The union of the families is the given's frames, relocated by the placement with the record.
\<close>

lemma given_frames_carried:
  assumes Pf: "schema_system_formed P" and agree: "systems_agree_on P guard_readers_system (system_definitions P)"
    and clauses: "\<And>e S s keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D \<Longrightarrow>
      \<exists>c. ((e,c),decode_finite_schema S) \<in> system_clauses P"
    and frames: "frames_discharged (positive_meaning P) D \<Phi>"
  shows "frames_discharged (positive_meaning given_rooted_readers_system) D \<Phi>"
proof -
  note chain = given_agreements[OF Pf agree]
  show ?thesis
  proof (rule frames_agree_read_discharged[OF Pf given_rooted_readers_formed chain(3) chain(4) _ frames])
    fix e S s keep Vp Vh d assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
      and d: "d \<in> schema_dependencies (decode_finite_schema S)"
    obtain c where "((e,c),decode_finite_schema S) \<in> system_clauses P" using clauses[OF m] by blast
    then have "d \<in> system_definitions P" using Pf d unfolding schema_system_formed_def by blast
    then show "d \<in> system_definitions P \<inter> system_definitions given_rooted_readers_system \<or>
        d \<notin> system_definitions given_rooted_readers_system" by blast
  qed
qed


lemma frames_foldr_discharged:
  "(\<And>\<Phi>. \<Phi> \<in> set \<Phi>s \<Longrightarrow> frames_discharged M D \<Phi>) \<Longrightarrow> frames_discharged M D (foldr (|\<union>|) \<Phi>s {||})"
proof (induction \<Phi>s)
  case Nil show ?case by (simp add: frames_discharged_def)
next
  case (Cons \<Phi> \<Phi>s)
  have "frames_discharged M D \<Phi>" using Cons.prems by simp
  moreover have "frames_discharged M D (foldr (|\<union>|) \<Phi>s {||})" by (rule Cons.IH) (use Cons.prems in simp)
  ultimately show ?case by (simp add: frames_union_discharged)
qed

lemma slot_sockets_distinct: "interface_slot_socket_schema \<noteq> schema_slot_row_schema"
  "schema_slot_row_schema \<noteq> interface_slot_socket_schema"
proof -
  have a: "\<exists>p. (2::nat,56::nat,p) |\<in>| finite_schema_premises interface_slot_socket_schema"
    by (simp add: interface_slot_socket_schema_def)
  have b: "\<not>(\<exists>p. (2::nat,56::nat,p) |\<in>| finite_schema_premises schema_slot_row_schema)"
    by (simp add: schema_slot_row_schema_def)
  show "interface_slot_socket_schema \<noteq> schema_slot_row_schema" "schema_slot_row_schema \<noteq> interface_slot_socket_schema"
    using a b by auto
qed


abbreviation given_rooted_meaning_at where
  "given_rooted_meaning_at \<equiv> positive_meaning given_rooted_readers_system"

lemma frames_list_discharged:
  "(\<And>D. D \<in> set Ds \<Longrightarrow> frames_discharged M D \<Phi>) \<Longrightarrow> frames_discharged M (declarations_list Ds) \<Phi>"
proof (induction Ds)
  case Nil show ?case by (simp add: frames_discharged_def no_declarations_def)
next
  case (Cons D Ds)
  have "frames_discharged M D \<Phi>" using Cons.prems by simp
  moreover have "frames_discharged M (declarations_list Ds) \<Phi>" by (rule Cons.IH) (use Cons.prems in simp)
  ultimately show ?case by (simp add: frames_declarations_union)
qed

lemma given_frames_lookup:
  "frames_discharged given_rooted_meaning_at given_plain_declarations lookup_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at lookup_declarations lookup_frames"
    by (rule given_frames_carried[OF artifact_lookup_system_formed guard_lookup_agreement _
    lookup_frames_discharged]) (auto simp: lookup_declarations_def lookup_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: lookup_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_identity:
  "frames_discharged given_rooted_meaning_at given_plain_declarations identity_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at identity_declarations identity_frames"
    by (rule given_frames_carried[OF artifact_identity_system_formed guard_identity_agreement _
    identity_frames_discharged]) (auto simp: identity_declarations_def identity_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: identity_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_comparison:
  "frames_discharged given_rooted_meaning_at given_plain_declarations comparison_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at comparison_declarations comparison_frames"
    by (rule given_frames_carried[OF artifact_comparison_system_formed guard_comparison_agreement _
    comparison_frames_discharged]) (auto simp: comparison_declarations_def comparison_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: comparison_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_headed:
  "frames_discharged given_rooted_meaning_at given_plain_declarations headed_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at headed_declarations headed_frames"
    by (rule given_frames_carried[OF headed_material_system_formed guard_headed_agreement _
    headed_frames_discharged]) (auto simp: headed_declarations_def headed_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: headed_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_family_rows:
  "frames_discharged given_rooted_meaning_at given_plain_declarations family_rows_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at family_rows_declarations family_rows_frames"
    by (rule given_frames_carried[OF family_admission_system_formed guard_family_agreement _
    family_rows_frames_discharged]) (auto simp: family_rows_declarations_def family_rows_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: family_rows_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_admission:
  "frames_discharged given_rooted_meaning_at given_plain_declarations admission_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at admission_declarations admission_frames"
    by (rule given_frames_carried[OF citation_admission_system_formed guard_citation_agreement _
    admission_frames_discharged]) (auto simp: admission_declarations_def external_socket_decoded citation_admission_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: admission_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_interpretation:
  "frames_discharged given_rooted_meaning_at given_plain_declarations interpretation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at interpretation_declarations interpretation_frames"
    by (rule given_frames_carried[OF citation_interpretation_system_formed
    guard_interpretation_agreement _ interpretation_frames_discharged]) (auto simp: interpretation_declarations_def interpretation_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: interpretation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_binder:
  "frames_discharged given_rooted_meaning_at given_plain_declarations binder_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at binder_declarations binder_frames"
    by (rule given_frames_carried[OF binder_admission_system_formed guard_binder_agreement _
    binder_frames_discharged]) (auto simp: binder_declarations_def binder_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: binder_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_quotation:
  "frames_discharged given_rooted_meaning_at given_plain_declarations quotation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at quotation_declarations quotation_frames"
    by (rule given_frames_carried[OF quotation_admission_system_formed guard_quotation_agreement _
    instantiation_notion_frames_discharged(1)]) (auto simp: quotation_declarations_def quotation_pair_socket_decoded quotation_admission_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: quotation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_instantiation:
  "frames_discharged given_rooted_meaning_at given_plain_declarations instantiation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at instantiation_declarations instantiation_frames"
    by (rule given_frames_carried[OF pattern_instantiation_system_formed
    guard_instantiation_agreement _ instantiation_notion_frames_discharged(2)]) (auto simp: instantiation_declarations_def instantiation_constant_socket_decoded instantiation_pair_socket_decoded pattern_instantiation_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: instantiation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_prospective:
  "frames_discharged given_rooted_meaning_at given_plain_declarations prospective_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at prospective_declarations prospective_frames"
    by (rule given_frames_carried[OF prospective_instantiation_system_formed
    guard_prospective_agreement _ instantiation_notion_frames_discharged(3)]) (auto simp: prospective_declarations_def prospective_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: prospective_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_vector:
  "frames_discharged given_rooted_meaning_at given_plain_declarations vector_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at vector_declarations vector_frames"
    by (rule given_frames_carried[OF vector_instantiation_system_formed
    guard_vector_instantiation_agreement _ schema_instantiation_notion_frames_discharged(1)]) (auto simp: vector_declarations_def vector_cons_socket_decoded vector_instantiation_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: vector_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_record:
  "frames_discharged given_rooted_meaning_at given_plain_declarations record_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at record_declarations record_frames"
    by (rule given_frames_carried[OF record_instantiation_system_formed
    guard_record_instantiation_agreement _ schema_instantiation_notion_frames_discharged(2)]) (auto simp: record_declarations_def record_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: record_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_material:
  "frames_discharged given_rooted_meaning_at given_plain_declarations material_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at material_declarations material_frames"
    by (rule given_frames_carried[OF material_instantiation_system_formed
    guard_material_instantiation_agreement _ schema_instantiation_notion_frames_discharged(3)]) (auto simp: material_declarations_def material_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: material_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_rows:
  "frames_discharged given_rooted_meaning_at given_plain_declarations premise_rows_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_rows_declarations premise_rows_frames"
    by (rule given_frames_carried[OF premise_rows_system_formed guard_premise_rows_agreement _
    schema_instantiation_notion_frames_discharged(4)]) (auto simp: premise_rows_declarations_def premise_call_socket_decoded premise_material_socket_decoded premise_rows_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_rows_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_family:
  "frames_discharged given_rooted_meaning_at given_plain_declarations premise_family_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_family_declarations premise_family_frames"
    by (rule given_frames_carried[OF premise_family_instantiation_system_formed
    guard_premise_family_agreement _ schema_instantiation_notion_frames_discharged(5)]) (auto simp: premise_family_declarations_def premise_family_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_family_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema:
  "frames_discharged given_rooted_meaning_at given_plain_declarations schema_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_declarations schema_frames"
    by (rule given_frames_carried[OF schema_instantiation_system_formed
    guard_schema_instantiation_agreement _ schema_instantiation_notion_frames_discharged(6)]) (auto simp: schema_declarations_def schema_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_interface_slot:
  "frames_discharged given_rooted_meaning_at given_plain_declarations interface_slot_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at interface_slot_declarations interface_slot_frames"
    by (rule given_frames_carried[OF definition_slot_reading_system_formed
    guard_definition_slot_agreement _ interface_slot_frames_discharged]) (auto simp: interface_slot_declarations_def interface_slot_socket_decoded definition_slot_reading_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: interface_slot_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema_family_socket:
  "frames_discharged given_rooted_meaning_at given_plain_declarations schema_family_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_family_socket_record schema_family_socket_frames"
    by (rule given_frames_carried[OF schema_family_admission_system_formed
    guard_schema_family_agreement _ schema_family_socket_frames_discharged]) (auto simp: schema_family_socket_record_def schema_family_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_family_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_callee_inclusion_socket:
  "frames_discharged given_rooted_meaning_at given_plain_declarations callee_inclusion_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at callee_inclusion_socket_record callee_inclusion_socket_frames"
    by (rule given_frames_carried[OF definition_callee_inclusion_system_formed
    guard_definition_callee_inclusion_agreement _ callee_inclusion_socket_frames_discharged]) (auto simp: callee_inclusion_socket_record_def callee_inclusion_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: callee_inclusion_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_payload_audit_socket:
  "frames_discharged given_rooted_meaning_at given_plain_declarations payload_audit_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at payload_audit_socket_record payload_audit_socket_frames"
    by (rule given_frames_carried[OF payload_audit_system_formed guard_audit_agreement _
    payload_audit_socket_frames_discharged]) (auto simp: payload_audit_socket_record_def payload_audit_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: payload_audit_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_clause_reading_row:
  "frames_discharged given_rooted_meaning_at given_plain_declarations clause_reading_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at clause_reading_row_record clause_reading_row_frames"
    by (rule given_frames_carried[OF definition_clause_reading_system_formed
    guard_clause_reading_agreement _ clause_reading_row_frames_discharged]) (auto simp: clause_reading_row_record_def clause_reading_row_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: clause_reading_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_slot_row:
  "frames_discharged given_rooted_meaning_at given_plain_declarations premise_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_slot_row_record premise_slot_row_frames"
    by (rule given_frames_carried[OF schema_slot_reading_system_formed
    guard_schema_slot_agreement _ premise_slot_row_frames_discharged]) (auto simp: premise_slot_row_record_def premise_slot_row_decoded schema_slot_reading_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema_slot_row:
  "frames_discharged given_rooted_meaning_at given_plain_declarations schema_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_slot_row_record schema_slot_row_frames"
    by (rule given_frames_carried[OF definition_slot_reading_system_formed
    guard_definition_slot_agreement _ schema_slot_row_frames_discharged]) (auto simp: schema_slot_row_record_def schema_slot_row_decoded definition_slot_reading_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_root_slot_row:
  "frames_discharged given_rooted_meaning_at given_plain_declarations root_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at root_slot_row_record root_slot_row_frames"
    by (rule given_frames_carried[OF package_slot_reading_system_formed
    guard_package_slot_agreement _ root_slot_row_frames_discharged]) (auto simp: root_slot_row_record_def root_slot_row_decoded package_slot_reading_clauses_def)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: root_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_application:
  "frames_discharged given_rooted_meaning_at given_plain_declarations application_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at application_declarations application_frames"
    by (rule given_frames_carried[OF application_reading_system_formed guard_application_reading_agreement _
    instantiation_notion_frames_discharged(4)]) (auto simp: application_declarations_def application_socket_decoded)
  show ?thesis unfolding given_plain_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: application_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemmas given_family_frames =
  given_frames_application
  given_frames_lookup
  given_frames_identity
  given_frames_comparison
  given_frames_headed
  given_frames_family_rows
  given_frames_admission
  given_frames_interpretation
  given_frames_binder
  given_frames_quotation
  given_frames_instantiation
  given_frames_prospective
  given_frames_vector
  given_frames_record
  given_frames_material
  given_frames_premise_rows
  given_frames_premise_family
  given_frames_schema
  given_frames_interface_slot
  given_frames_schema_family_socket
  given_frames_callee_inclusion_socket
  given_frames_payload_audit_socket
  given_frames_clause_reading_row
  given_frames_premise_slot_row
  given_frames_schema_slot_row
  given_frames_root_slot_row

text \<open>Each family beside its own record.\<close>

definition given_frame_families ::
    "((nat,nat,nat) resolution_declarations \<times> (nat,nat,nat) resolution_frames) list" where
  "given_frame_families = [(lookup_declarations,lookup_frames), (identity_declarations,identity_frames),
    (comparison_declarations,comparison_frames), (headed_declarations,headed_frames),
    (family_rows_declarations,family_rows_frames), (admission_declarations,admission_frames),
    (interpretation_declarations,interpretation_frames), (binder_declarations,binder_frames),
    (quotation_declarations,quotation_frames), (instantiation_declarations,instantiation_frames),
    (prospective_declarations,prospective_frames), (application_declarations,application_frames),
    (vector_declarations,vector_frames),
    (record_declarations,record_frames), (material_declarations,material_frames),
    (premise_rows_declarations,premise_rows_frames), (premise_family_declarations,premise_family_frames),
    (schema_declarations,schema_frames), (interface_slot_declarations,interface_slot_frames),
    (schema_family_socket_record,schema_family_socket_frames),
    (callee_inclusion_socket_record,callee_inclusion_socket_frames),
    (payload_audit_socket_record,payload_audit_socket_frames), (clause_reading_row_record,clause_reading_row_frames),
    (premise_slot_row_record,premise_slot_row_frames), (schema_slot_row_record,schema_slot_row_frames),
    (root_slot_row_record,root_slot_row_frames)]"

definition given_frames :: "(nat,nat,nat) resolution_frames" where
  "given_frames = foldr (|\<union>|) (map snd given_frame_families) {||}"

theorem given_frames_discharged:
  "frames_discharged (positive_meaning given_rooted_readers_system) given_plain_declarations given_frames"
  unfolding given_frames_def given_frame_families_def
  by (rule frames_foldr_discharged) (use given_family_frames in auto)

lemma frames_foldr_member: "x |\<in>| foldr (|\<union>|) \<Phi>s {||} \<longleftrightarrow> (\<exists>\<Phi>\<in>set \<Phi>s. x |\<in>| \<Phi>)"
  by (induction \<Phi>s) auto

lemma given_frame_families_own:
  assumes "(D,\<Phi>) \<in> set given_frame_families"
  shows "D \<in> set given_records"
    and "(e,S,s,C) |\<in>| \<Phi> \<Longrightarrow> (e,S,s) |\<in>| (\<lambda>(e,S,s,keep,Vp,Vh). (e,S,s)) |`| declared_sockets D"
  subgoal using assms unfolding given_frame_families_def by auto
  using assms by (auto simp: given_frame_families_def given_record_defs lookup_frames_def
    identity_frames_def comparison_frames_def headed_frames_def family_rows_frames_def admission_frames_def
    interpretation_frames_def binder_frames_def quotation_frames_def instantiation_frames_def prospective_frames_def application_frames_def
    vector_frames_def record_frames_def material_frames_def premise_rows_frames_def premise_family_frames_def
    schema_frames_def interface_slot_frames_def schema_family_socket_frames_def callee_inclusion_socket_frames_def
    payload_audit_socket_frames_def clause_reading_row_frames_def premise_slot_row_frames_def
    schema_slot_row_frames_def root_slot_row_frames_def)

section \<open>The frames relocated with the record\<close>

text \<open>
  Every frame of the given's frames stands at a socket of the given's record, so its site and its clause's callees
  stand in the rooted readers, on which the placement is injective; the frames are relocated with the record.
\<close>

lemma given_frames_at_sockets:
  assumes "(e,S,s,C) |\<in>| given_frames"
  shows "\<exists>keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_plain_declarations"
proof -
  obtain \<Phi> where \<Phi>: "\<Phi> \<in> set (map snd given_frame_families)" "(e,S,s,C) |\<in>| \<Phi>"
    using assms unfolding given_frames_def frames_foldr_member by blast
  then obtain D where D: "(D,\<Phi>) \<in> set given_frame_families" by auto
  obtain keep Vp Vh where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    using given_frame_families_own(2)[OF D \<Phi>(2)] by force
  then have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_plain_declarations"
    unfolding given_plain_declarations_records by (rule declarations_list_socket_member[OF given_frame_families_own(1)[OF D]])
  then show ?thesis by blast
qed

lemma given_frame_sites: "frame_sites given_frames \<subseteq> system_definitions given_rooted_readers_system"
proof
  fix x assume "x \<in> frame_sites given_frames"
  then obtain e S s C where f: "(e,S,s,C) |\<in>| given_frames" and x: "x = e \<or> x \<in> schema_dependencies (decode_finite_schema S)"
    unfolding frame_sites_def by auto
  obtain keep Vp Vh where sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_plain_declarations"
    using given_frames_at_sockets[OF f] by blast
  have e: "e \<in> system_definitions given_rooted_readers_system"
    using given_plain_declarations_sites declared_sites_members(4)[OF sock] by blast
  show "x \<in> system_definitions given_rooted_readers_system"
    using x e given_socket_reaches[OF sock e] by blast
qed

theorem given_placed_frames_discharged:
  "frames_discharged (positive_meaning (decode_finite_system given_placed_program))
    (declarations_relocated given_readers_placement given_plain_declarations)
    (frames_relocated given_readers_placement given_frames)"
proof -
  have Pf: "schema_system_formed (decode_finite_system finite_rooted_given_readers)"
    by (simp add: finite_rooted_given_readers_exact)
  have "system_definitions (decode_finite_system finite_rooted_given_readers) \<union> declared_sites given_plain_declarations \<union>
      frame_sites given_frames = system_definitions given_rooted_readers_system"
    using given_plain_declarations_sites given_frame_sites by (auto simp only: finite_rooted_given_readers_exact)
  then have inj: "inj_on given_readers_placement (system_definitions (decode_finite_system finite_rooted_given_readers) \<union>
      declared_sites given_plain_declarations \<union> frame_sites given_frames)"
    using given_readers_installation(3) by (simp only:)
  show ?thesis
    by (rule frames_relocated_discharged[OF Pf inj]) (simp add: finite_rooted_given_readers_exact given_frames_discharged)
qed

section \<open>The given's frames beside 48's narrowed frames\<close>

text \<open>
  The frames of the given's one record: the families' frames at the plain part and #609's frames at 48's narrowed
  sockets, joined at the record's keys (@{const frames_join}) and discharged by the join
  (@{thm [source] produced_join_frames}).
\<close>

definition given_narrowed_frames :: "(nat,nat,nat) resolution_frames" where
  "given_narrowed_frames = frames_join (resolution_declarations.truncate (union_produced given_union_sockets))
    given_frames given_union_frames"

theorem given_narrowed_frames_discharged:
  "narrowed_frames_discharged (positive_meaning given_rooted_readers_system)
    (narrowed_declarations.truncate given_declarations) given_narrowed_frames"
  unfolding given_declarations_def given_narrowed_frames_def
  by (rule produced_join_frames[OF given_frames_discharged]) (simp only: union_produced_fields given_union_rooted(2))

text \<open>
  R5f2's exchange at the given's rooted readers with the one record and its frames: the committed search there produces
  48's unions at the narrowed sockets (@{thm [source] finite_narrowed_commitment_exchanges}); the forms of R5f2 follow
  at the same premises.
\<close>

theorem given_narrowed_commitment_exchanges:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>"
    and only: "finite_registrations_premise_only \<kappa> finite_rooted_given_readers"
  shows "finite_commitment_exchanges (\<lambda>_. False) \<kappa>
    (finite_narrowed_commitment finite_rooted_given_readers m given_declarations given_narrowed_frames)
    finite_rooted_given_readers"
proof -
  have d: "narrowed_declarations_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
      (narrowed_declarations.truncate given_declarations) given_declarations_correspondence"
    using given_declarations_discharged(1) by (simp add: finite_rooted_given_readers_exact)
  have f: "narrowed_frames_discharged (positive_meaning (decode_finite_system finite_rooted_given_readers))
      (narrowed_declarations.truncate given_declarations) given_narrowed_frames"
    using given_narrowed_frames_discharged by (simp add: finite_rooted_given_readers_exact)
  show ?thesis
    by (rule finite_narrowed_commitment_exchanges[OF \<kappa> d f given_declarations_productions
      given_declarations_discharged(3) only])
qed

section \<open>The given's one record at every extension's installed program\<close>

text \<open>
  The one record (@{const given_declarations}: #611's plain record joined with 48's narrowed sockets and their
  productions) reaches an extension's installed program as #796's corollary carries a produced record
  (@{thm [source] finite_mapped_native_extension.committed_registrations_produced_relocated}): relocated by the
  placement (@{const produced_relocated}) and varied along the clause match to the program the native package reader
  returns (task 798, #782's Remains 2-5). Its premises are discharged once for every extension. At the numbered
  program the record's discharge, frames and productions are the rooted readers', carried by agreement. At the
  installed program: the sources agree where the record narrows, 48's callers, whose rooted clauses are told apart by
  their callees (@{text given_union_site_distinct}), so an installed clause there has one placed source
  (@{thm [source] varied_narrowings_agree_within}); the productions are 48's union registration at the relocated
  sites and the matched variables, answered from 48's and selection's meanings at the installed program alone
  (@{thm [source] union_at_registration_answers}, no equivalence of registration values between programs read); the
  static premise at the same sites (@{thm [source] narrowed_productions_declared_varied_within}).
\<close>

text \<open>A callee map and a clause match compose into one renaming.\<close>

lemma finite_rename_schema_callees_matched:
  "finite_rename_schema f h id (finite_rename_schema id id g S) = finite_rename_schema f h g S"
proof -
  have "decode_finite_schema (finite_rename_schema f h id (finite_rename_schema id id g S)) =
      decode_finite_schema (finite_rename_schema f h g S)"
    by (simp add: finite_rename_schema_correct rename_schema_composition)
  then show ?thesis by simp
qed

text \<open>The union registration relocated and varied is the registration at the relocated sites and matched variables.\<close>

lemma union_registration_varied_relocated:
  "registration_varied f T (registration_relocated g union_registration) =
    union_registration_at (g 48) (g 5) T (f 2) (f 0) (f 1)"
  by (simp add: registration_varied_def registration_relocated_def union_registration_def union_registration_at_def
    union_family_def union_family_at_def union_query_def union_query_at_def family_relocated_def query_relocated_def
    map_collection_family_def map_collection_query_def)

subsection \<open>48's callers: their rooted clauses are told apart by their callees\<close>

lemma given_union_site_clauses:
  "((50,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> quotation_admission_clauses"
  "((55,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> pattern_instantiation_clauses"
  "((57,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> {(0,prospective_instantiation_schema)}"
  "((60,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> vector_instantiation_clauses"
  "((63,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> premise_rows_clauses"
  "((48,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> {(0,data_union_schema)}"
proof -
  have at: "((e,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> ((e,c),S) \<in> system_clauses P"
    if formed: "schema_system_formed P" and agree: "systems_agree_on P guard_readers_system (system_definitions P)"
      and e: "e \<in> system_definitions P" "e \<in> system_definitions given_rooted_readers_system"
    for P :: "(nat,nat,nat,nat) schema_system" and e
    using given_agreements(3)[OF formed agree] e unfolding systems_agree_on_def by blast
  have r: "e \<in> system_definitions given_rooted_readers_system" if "e \<in> {48,50,55,57,60,63}" for e
    by (rule given_rooted_declared_sites) (use that in auto)
  have d: "50 \<in> system_definitions quotation_admission_system" "55 \<in> system_definitions pattern_instantiation_system"
    "57 \<in> system_definitions prospective_instantiation_system" "60 \<in> system_definitions vector_instantiation_system"
    "63 \<in> system_definitions premise_rows_system" "48 \<in> system_definitions data_union_system"
    by (simp_all add: pattern_instantiation_system_def prospective_instantiation_system_def
      vector_instantiation_system_def premise_rows_system_def)
  show "((50,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> quotation_admission_clauses"
    using at[OF quotation_admission_system_formed guard_quotation_agreement d(1) r[of 50]] by simp
  show "((55,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> pattern_instantiation_clauses"
    using at[OF pattern_instantiation_system_formed guard_instantiation_agreement d(2) r[of 55]] by simp
  show "((57,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> {(0,prospective_instantiation_schema)}"
    using at[OF prospective_instantiation_system_formed guard_prospective_agreement d(3) r[of 57]] by simp
  show "((60,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> vector_instantiation_clauses"
    using at[OF vector_instantiation_system_formed guard_vector_instantiation_agreement d(4) r[of 60]] by simp
  show "((63,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> premise_rows_clauses"
    using at[OF premise_rows_system_formed guard_premise_rows_agreement d(5) r[of 63]] by simp
  show "((48,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> (c,S) \<in> {(0,data_union_schema)}"
    using at[OF data_union_system_formed guard_union_agreement d(6) r[of 48]] by simp
qed

text \<open>
  At 48's callers two clauses of one definition of the rooted readers with the same callees are one clause: each
  pair of different clauses there differs in a callee. A match keeps the callees, so no installed clause at those
  sites is matched by two placed clauses.
\<close>

text \<open>Values told apart pairwise make a map injective on them; no equality of the values is decided.\<close>

lemma inj_on_two_values: "f a \<noteq> f b \<Longrightarrow> inj_on f {a,b}"
  unfolding inj_on_def by auto

lemma inj_on_three_values: "f a \<noteq> f b \<Longrightarrow> f a \<noteq> f c \<Longrightarrow> f b \<noteq> f c \<Longrightarrow> inj_on f {a,b,c}"
  unfolding inj_on_def by auto

lemma given_union_site_distinct:
  assumes e: "e \<in> {50,55,57,60,63}"
    and S: "((e,c),S) \<in> system_clauses given_rooted_readers_system"
    and S': "((e,c'),S') \<in> system_clauses given_rooted_readers_system"
    and deps: "schema_dependencies S = schema_dependencies S'"
  shows "S = S'"
proof -
  have q: "37 \<in> schema_dependencies quotation_payload_schema" "37 \<notin> schema_dependencies quotation_target_schema"
    "50 \<in> schema_dependencies quotation_pair_schema" "50 \<notin> schema_dependencies quotation_payload_schema"
    "50 \<notin> schema_dependencies quotation_target_schema"
    by (simp_all add: schema_dependencies_def rel_ran_image quotation_payload_schema_def quotation_target_schema_def
      quotation_pair_schema_def)
  have i: "42 \<in> schema_dependencies instantiation_variable_schema" "42 \<notin> schema_dependencies instantiation_constant_schema"
    "55 \<in> schema_dependencies instantiation_pair_schema" "55 \<notin> schema_dependencies instantiation_variable_schema"
    "55 \<notin> schema_dependencies instantiation_constant_schema"
    by (simp_all add: schema_dependencies_def rel_ran_image instantiation_schema_defs)
  have v: "60 \<in> schema_dependencies vector_instantiation_cons_schema"
    "60 \<notin> schema_dependencies vector_instantiation_nil_schema"
    by (simp_all add: schema_dependencies_def rel_ran_image vector_instantiation_cons_schema_def
      vector_instantiation_nil_schema_def)
  have p: "63 \<in> schema_dependencies premise_rows_call_schema" "63 \<in> schema_dependencies premise_rows_material_schema"
    "63 \<notin> schema_dependencies premise_rows_nil_schema" "62 \<in> schema_dependencies premise_rows_material_schema"
    "62 \<notin> schema_dependencies premise_rows_call_schema"
    by (simp_all add: schema_dependencies_def rel_ran_image premise_rows_nil_schema_def premise_rows_call_schema_def
      premise_rows_material_schema_def)
  have neq: "A \<noteq> B" if "x \<in> A" "x \<notin> B" for x :: nat and A B :: "nat set" using that by blast
  have qi: "inj_on schema_dependencies {quotation_payload_schema,quotation_target_schema,quotation_pair_schema}"
    by (rule inj_on_three_values[where f=schema_dependencies, OF neq[OF q(1,2)] not_sym[OF neq[OF q(3,4)]] not_sym[OF neq[OF q(3,5)]]])
  have ii: "inj_on schema_dependencies {instantiation_variable_schema,instantiation_constant_schema,
      instantiation_pair_schema}"
    by (rule inj_on_three_values[where f=schema_dependencies, OF neq[OF i(1,2)] not_sym[OF neq[OF i(3,4)]] not_sym[OF neq[OF i(3,5)]]])
  have vi: "inj_on schema_dependencies {vector_instantiation_nil_schema,vector_instantiation_cons_schema}"
    by (rule inj_on_two_values[where f=schema_dependencies, OF not_sym[OF neq[OF v(1,2)]]])
  have pi: "inj_on schema_dependencies {premise_rows_nil_schema,premise_rows_call_schema,premise_rows_material_schema}"
    by (rule inj_on_three_values[where f=schema_dependencies, OF not_sym[OF neq[OF p(1,3)]] not_sym[OF neq[OF p(2,3)]]
      not_sym[OF neq[OF p(4,5)]]])
  consider "e = 50" | "e = 55" | "e = 57" | "e = 60" | "e = 63" using e by blast
  then show ?thesis
  proof cases
    case 1
    have "S \<in> {quotation_payload_schema,quotation_target_schema,quotation_pair_schema}"
      "S' \<in> {quotation_payload_schema,quotation_target_schema,quotation_pair_schema}"
      using S S' unfolding 1 given_union_site_clauses(1) quotation_admission_clauses_def by auto
    then show ?thesis by (rule inj_onD[OF qi deps])
  next
    case 2
    have "S \<in> {instantiation_variable_schema,instantiation_constant_schema,instantiation_pair_schema}"
      "S' \<in> {instantiation_variable_schema,instantiation_constant_schema,instantiation_pair_schema}"
      using S S' unfolding 2 given_union_site_clauses(2) pattern_instantiation_clauses_def by auto
    then show ?thesis by (rule inj_onD[OF ii deps])
  next
    case 3
    show ?thesis using S S' unfolding 3 given_union_site_clauses(3) by simp
  next
    case 4
    have "S \<in> {vector_instantiation_nil_schema,vector_instantiation_cons_schema}"
      "S' \<in> {vector_instantiation_nil_schema,vector_instantiation_cons_schema}"
      using S S' unfolding 4 given_union_site_clauses(4) vector_instantiation_clauses_def by auto
    then show ?thesis by (rule inj_onD[OF vi deps])
  next
    case 5
    have "S \<in> {premise_rows_nil_schema,premise_rows_call_schema,premise_rows_material_schema}"
      "S' \<in> {premise_rows_nil_schema,premise_rows_call_schema,premise_rows_material_schema}"
      using S S' unfolding 5 given_union_site_clauses(5) premise_rows_clauses_def by auto
    then show ?thesis by (rule inj_onD[OF pi deps])
  qed
qed

subsection \<open>The union's facts at the one record\<close>

lemma given_union_sites:
  assumes "(e,S,s,keep,Vp,Vh) |\<in>| given_union_sockets"
  shows "e \<in> {50,55,57,60,63}"
  using assms by (auto simp: given_union_sockets_def quotation_union_sockets_def instantiation_union_sockets_def
    prospective_union_sockets_def vector_union_sockets_def premise_rows_union_sockets_def)


text \<open>A socket of the one record narrowed or producing is one of 48's, its class the union's and its production 48's.\<close>

lemma given_declarations_at_union:
  assumes m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    and n: "declared_narrowing given_declarations e S s \<noteq> (\<lambda>_. True) \<or> declared_production given_declarations e S s \<noteq> None"
  shows "(e,S,s,keep,Vp,Vh) |\<in>| given_union_sockets" "declared_narrowing given_declarations e S s = union_class"
    "declared_production given_declarations e S s = Some union_registration"
proof -
  have k: "socket_keyed (resolution_declarations.truncate (union_produced given_union_sockets)) e S s"
    using n unfolding given_declarations_def by (auto split: if_split_asm)
  show "(e,S,s,keep,Vp,Vh) |\<in>| given_union_sockets"
    using m k unfolding given_declarations_sockets socket_keyed_iff truncate_fields union_produced_simps by blast
  show "declared_narrowing given_declarations e S s = union_class"
    "declared_production given_declarations e S s = Some union_registration"
    using k unfolding given_declarations_def by simp_all
qed

lemma given_narrowed_frame_sites: "frame_sites given_narrowed_frames \<subseteq> system_definitions given_rooted_readers_system"
proof
  fix x assume "x \<in> frame_sites given_narrowed_frames"
  then obtain e S s C where f: "(e,S,s,C) |\<in>| given_frames \<or>
      socket_keyed (resolution_declarations.truncate (union_produced given_union_sockets)) e S s"
      and x: "x = e \<or> x \<in> schema_dependencies (decode_finite_schema S)"
    unfolding frame_sites_def given_narrowed_frames_def frames_join_def by auto
  show "x \<in> system_definitions given_rooted_readers_system"
    using f
  proof
    assume "(e,S,s,C) |\<in>| given_frames"
    then have "x \<in> frame_sites given_frames" using x unfolding frame_sites_def by auto
    then show ?thesis using given_frame_sites by blast
  next
    assume "socket_keyed (resolution_declarations.truncate (union_produced given_union_sockets)) e S s"
    then obtain keep Vp Vh where "(e,S,s,keep,Vp,Vh) |\<in>| given_union_sockets"
      unfolding socket_keyed_iff truncate_fields union_produced_simps by blast
    then have m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate given_declarations)"
      unfolding truncate_fields given_declarations_sockets by blast
    have "x \<in> declared_sites (resolution_declarations.truncate given_declarations)"
      using x declared_sites_members(4)[OF m] declared_sites_members(5)[OF m] by blast
    then show ?thesis using given_declarations_sites by blast
  qed
qed

text \<open>48 has one clause at the rooted readers, the union's.\<close>

lemma union_rooted_clause:
  "((48,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema union_schema"
  by (simp only: given_union_site_clauses(6) singleton_iff prod.inject union_schema_decoded)

context given_readers_extension
begin

subsection \<open>At the numbered program: the rooted readers' discharges carried by agreement\<close>

lemma rooted_in_Q: "d \<in> system_definitions given_rooted_readers_system \<Longrightarrow> d \<in> system_definitions (decode_finite_system Q)"
  by (rule subsetD[OF whole_agreement_definitions[OF agreement]])

lemma rooted_clauses_Q:
  assumes "d \<in> system_definitions given_rooted_readers_system"
  shows "((d,c),S) \<in> system_clauses (decode_finite_system Q) \<longleftrightarrow> ((d,c),S) \<in> system_clauses given_rooted_readers_system"
  using agreement assms unfolding systems_agree_on_def by auto

lemma rooted_shared:
  "systems_agree_on given_rooted_readers_system (decode_finite_system Q)
    (system_definitions given_rooted_readers_system \<inter> system_definitions (decode_finite_system Q))"
  by (rule systems_agree_on_subdomain[OF agreement Int_lower1])

lemma rooted_meaning_Q:
  assumes "d \<in> system_definitions given_rooted_readers_system"
  shows "(d,t) \<in> positive_meaning (decode_finite_system Q) \<longleftrightarrow> (d,t) \<in> positive_meaning given_rooted_readers_system"
  using positive_meaning_shared_definitions[OF given_rooted_readers_formed target_formed rooted_shared assms
    rooted_in_Q[OF assms]] by blast

lemma union_meanings_Q:
  "(48,t) \<in> positive_meaning (decode_finite_system Q) \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
  "(5,t) \<in> positive_meaning (decode_finite_system Q) \<longleftrightarrow> (5,t) \<in> positive_meaning bag_comparison_system"
proof -
  have r48: "48 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  show "(48,t) \<in> positive_meaning (decode_finite_system Q) \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
    using rooted_meaning_Q[OF r48] given_rooted_union_meanings(1)[of t] by (simp add: finite_rooted_given_readers_exact)
  show "(5,t) \<in> positive_meaning (decode_finite_system Q) \<longleftrightarrow> (5,t) \<in> positive_meaning bag_comparison_system"
    using rooted_meaning_Q[OF given_rooted_selection_site] given_rooted_union_meanings(2)[of t]
    by (simp add: finite_rooted_given_readers_exact)
qed

lemma given_declarations_sites_Q:
  "declared_sites (resolution_declarations.truncate given_declarations) \<subseteq> system_definitions (decode_finite_system Q)"
  using given_declarations_sites by (auto intro: rooted_in_Q)

lemma given_narrowed_frame_sites_Q: "frame_sites given_narrowed_frames \<subseteq> system_definitions (decode_finite_system Q)"
  using given_narrowed_frame_sites by (auto intro: rooted_in_Q)

text \<open>
  A produced record and its frames discharged at the rooted readers, with their sites there, are discharged at the
  numbered program by the agreement on the shared definitions; its productions at the numbered program, which read
  the record's own registrations, are the record's premise of the committed registrations. The given's record is its
  instance here (@{text given_declarations_discharged_Q}, @{text committed_registrations_Q}), the given's input
  record in @{text Development_Given_Installed_Productions}.
\<close>

lemma produced_record_discharged_Q:
  assumes discharged: "narrowed_declarations_discharged (positive_meaning given_rooted_readers_system)
      (narrowed_declarations.truncate ND) corr"
    and frames: "narrowed_frames_discharged (positive_meaning given_rooted_readers_system)
      (narrowed_declarations.truncate ND) \<Phi>"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions given_rooted_readers_system"
  shows "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate ND) corr"
    and "narrowed_frames_discharged (positive_meaning (decode_finite_system Q)) (narrowed_declarations.truncate ND) \<Phi>"
proof -
  have closed: "system_dependency_closed given_rooted_readers_system
      (system_definitions given_rooted_readers_system \<inter> system_definitions (decode_finite_system Q))"
    by (rule systems_agree_on_intersection_closed[OF given_rooted_readers_formed target_formed rooted_shared])
  have sites': "declared_sites (resolution_declarations.truncate (narrowed_declarations.truncate ND)) \<subseteq>
      system_definitions given_rooted_readers_system \<inter> system_definitions (decode_finite_system Q)"
    using sites by (auto intro: rooted_in_Q)
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate ND) corr"
    by (rule narrowed_declarations_agree_discharged[OF given_rooted_readers_formed target_formed rooted_shared closed
      sites' discharged])
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system Q)) (narrowed_declarations.truncate ND) \<Phi>"
    by (rule narrowed_frames_agree_discharged[OF given_rooted_readers_formed target_formed rooted_shared closed
      sites' frames])
qed

theorem produced_committed_registrations_Q:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and discharged: "narrowed_declarations_discharged (positive_meaning given_rooted_readers_system)
      (narrowed_declarations.truncate ND) corr"
    and frames: "narrowed_frames_discharged (positive_meaning given_rooted_readers_system)
      (narrowed_declarations.truncate ND) \<Phi>"
    and sites: "declared_sites (resolution_declarations.truncate ND) \<subseteq> system_definitions given_rooted_readers_system"
    and productions: "productions_discharged (positive_meaning (decode_finite_system Q)) Q m ND"
    and declared: "narrowed_productions_declared ND"
  shows "committed_registrations \<kappa> Q m ND \<Phi> corr"
  by (rule committed_registrations.intro[OF \<kappa> complete produced_record_discharged_Q[OF discharged frames sites]
    productions declared])

lemma given_declarations_discharged_Q:
  "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
    (narrowed_declarations.truncate given_declarations) given_declarations_correspondence"
  "narrowed_frames_discharged (positive_meaning (decode_finite_system Q))
    (narrowed_declarations.truncate given_declarations) given_narrowed_frames"
  "productions_discharged (positive_meaning (decode_finite_system Q)) Q m given_declarations"
proof -
  note carried = produced_record_discharged_Q[OF given_declarations_discharged(1) given_narrowed_frames_discharged
    given_declarations_sites]
  show "narrowed_declarations_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate given_declarations) given_declarations_correspondence"
    by (rule carried(1))
  show "narrowed_frames_discharged (positive_meaning (decode_finite_system Q))
      (narrowed_declarations.truncate given_declarations) given_narrowed_frames"
    by (rule carried(2))
  show "productions_discharged (positive_meaning (decode_finite_system Q)) Q m given_declarations"
    unfolding given_declarations_def by (rule produced_join_productions[OF union_productions_at[OF union_meanings_Q]])
qed

theorem committed_registrations_Q:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
  shows "committed_registrations \<kappa> Q m given_declarations given_narrowed_frames given_declarations_correspondence"
  by (rule produced_committed_registrations_Q[OF \<kappa> complete given_declarations_discharged(1)
    given_narrowed_frames_discharged given_declarations_sites given_declarations_discharged_Q(3)
    given_declarations_discharged(3)])

subsection \<open>The record relocated: 48's sockets at the placed sites\<close>

lemma relocated_injective:
  "inj_on installed_placement (declared_sites (resolution_declarations.truncate given_declarations))"
  by (rule inj_on_subset[OF installation(5) given_declarations_sites_Q])

lemma relocated_socket:
  assumes "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement given_declarations)"
  obtains e0 S0 where "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations" "e = installed_placement e0"
    "S = finite_rename_schema id id installed_placement S0"
  using assms by (auto simp: produced_relocated_def declarations_relocated_def)

lemma relocated_at_union:
  assumes m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement given_declarations)"
    and n: "declared_narrowing (produced_relocated installed_placement given_declarations) e S s \<noteq> (\<lambda>_. True) \<or>
      declared_production (produced_relocated installed_placement given_declarations) e S s \<noteq> None"
  shows "e \<in> installed_placement ` {50,55,57,60,63}" "Vp = join_view"
    "declared_narrowing (produced_relocated installed_placement given_declarations) e S s = union_class"
    "declared_production (produced_relocated installed_placement given_declarations) e S s =
      Some (registration_relocated installed_placement union_registration)"
proof -
  obtain e0 S0 where o: "(e0,S0,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations" "e = installed_placement e0"
      "S = finite_rename_schema id id installed_placement S0"
    by (rule relocated_socket[OF m])
  note k = produced_relocated_keys[OF relocated_injective o(1)]
  have n0: "declared_narrowing given_declarations e0 S0 s \<noteq> (\<lambda>_. True) \<or>
      declared_production given_declarations e0 S0 s \<noteq> None"
    using n[unfolded o(2,3)] k by simp
  note u = given_declarations_at_union[OF o(1) n0]
  show "e \<in> installed_placement ` {50,55,57,60,63}" using given_union_sites[OF u(1)] o(2) by blast
  show "Vp = join_view" by (rule given_union_socket_views[OF u(1)])
  show "declared_narrowing (produced_relocated installed_placement given_declarations) e S s = union_class"
    unfolding o(2,3) k(1) by (rule u(2))
  show "declared_production (produced_relocated installed_placement given_declarations) e S s =
      Some (registration_relocated installed_placement union_registration)"
    unfolding o(2,3) k(2) u(3) by simp
qed

lemma relocated_within:
  "narrowings_within (installed_placement ` {50,55,57,60,63}) (produced_relocated installed_placement given_declarations)"
  unfolding narrowings_within_def
proof (intro allI impI)
  fix e S s keep Vp Vh
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement given_declarations)"
    and out: "e \<notin> installed_placement ` {50,55,57,60,63}"
  show "declared_narrowing (produced_relocated installed_placement given_declarations) e S s = (\<lambda>_. True)"
  proof (rule ccontr)
    assume n: "declared_narrowing (produced_relocated installed_placement given_declarations) e S s \<noteq> (\<lambda>_. True)"
    show False by (rule notE[OF out relocated_at_union(1)[OF m disjI1[OF n]]])
  qed
qed

lemma relocated_declared: "narrowed_productions_declared (produced_relocated installed_placement given_declarations)"
  unfolding narrowed_productions_declared_def
proof (intro allI impI)
  fix e S s keep Vp Vh
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement given_declarations)"
    and n: "declared_narrowing (produced_relocated installed_placement given_declarations) e S s \<noteq> (\<lambda>_. True)"
  show "declared_production (produced_relocated installed_placement given_declarations) e S s \<noteq> None"
    using relocated_at_union(4)[OF m disjI1[OF n]] by simp
qed

subsection \<open>At the installed program: one source where the record narrows\<close>

theorem installed_union_sources:
  "finite_varied_sources_unique_at (installed_placement ` {50,55,57,60,63})
    (finite_rename_system installed_placement Q) installed_presentation"
  unfolding finite_varied_sources_unique_at_def
proof (intro allI impI)
  fix e c S c' S' c'' T f h f' h'
  assume e: "e \<in> installed_placement ` {50,55,57,60,63}"
    and S: "((e,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    and S': "((e,c'),S') |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    and T: "((e,c''),T) |\<in>| finite_system_clauses installed_presentation"
    and m: "finite_schema_match S T = Some (f,h)" and m': "finite_schema_match S' T = Some (f',h')"
  let ?g = installed_placement
  let ?Q = "decode_finite_system Q"
  obtain e0 where e0: "e0 \<in> {50,55,57,60,63}" "e = ?g e0" using e by blast
  have r0: "e0 \<in> system_definitions given_rooted_readers_system"
    by (rule given_rooted_declared_sites) (use e0(1) in auto)
  obtain d c0 S0 where o: "((d,c0),S0) |\<in>| finite_system_clauses Q" "e = ?g d"
      "S = finite_rename_schema id id ?g S0"
    using S by (auto simp: finite_rename_system_def)
  obtain d' c0' S0' where o': "((d',c0'),S0') |\<in>| finite_system_clauses Q" "e = ?g d'"
      "S' = finite_rename_schema id id ?g S0'"
    using S' by (auto simp: finite_rename_system_def)
  have Qc: "((d,c0),decode_finite_schema S0) \<in> system_clauses ?Q"
    "((d',c0'),decode_finite_schema S0') \<in> system_clauses ?Q"
    using o(1) o'(1) by (simp_all only: finite_system_clause_decoded)
  have dQ: "d \<in> system_definitions ?Q" "d' \<in> system_definitions ?Q"
    and depQ: "schema_dependencies (decode_finite_schema S0) \<subseteq> system_definitions ?Q"
      "schema_dependencies (decode_finite_schema S0') \<subseteq> system_definitions ?Q"
    using target_formed[unfolded schema_system_formed_def] Qc by blast+
  have dd: "d = e0" "d' = e0"
    by (rule inj_onD[OF installation(5)], use o(2) o'(2) e0(2) dQ rooted_in_Q[OF r0] in auto)+
  have rc: "((e0,c0),decode_finite_schema S0) \<in> system_clauses given_rooted_readers_system"
    "((e0,c0'),decode_finite_schema S0') \<in> system_clauses given_rooted_readers_system"
    using agreement Qc dd r0 unfolding systems_agree_on_def by auto
  have Sf: "finite_schema_formed S" "finite_schema_formed S'" and Tf: "finite_schema_formed T"
    using finite_system_clause_formed[OF installed_presentation_formed(2) S]
      finite_system_clause_formed[OF installed_presentation_formed(2) S']
      finite_system_clause_formed[OF installed_presentation_formed(1) T] by blast+
  have TS: "T = finite_rename_schema f h id S" "T = finite_rename_schema f' h' id S'"
    using finite_schema_match_exact(1)[OF Sf(1) Tf m] finite_schema_match_exact(1)[OF Sf(2) Tf m'] by blast+
  have "schema_dependencies (decode_finite_schema S) = schema_dependencies (decode_finite_schema S')"
  proof -
    have "schema_dependencies (decode_finite_schema T) = schema_dependencies (decode_finite_schema S)"
      "schema_dependencies (decode_finite_schema T) = schema_dependencies (decode_finite_schema S')"
      by (subst TS(1), simp add: finite_rename_schema_correct renamed_schema_dependencies)
        (subst TS(2), simp add: finite_rename_schema_correct renamed_schema_dependencies)
    then show ?thesis by simp
  qed
  then have "?g ` schema_dependencies (decode_finite_schema S0) = ?g ` schema_dependencies (decode_finite_schema S0')"
    unfolding o(3) o'(3) by (simp add: finite_rename_schema_correct renamed_schema_dependencies)
  then have deps0: "schema_dependencies (decode_finite_schema S0) = schema_dependencies (decode_finite_schema S0')"
    by (rule iffD1[OF inj_on_image_eq_iff[OF installation(5) depQ]])
  have "decode_finite_schema S0 = decode_finite_schema S0'"
    by (rule given_union_site_distinct[OF e0(1) rc deps0])
  then have "S0 = S0'" by (simp only: decode_finite_schema_injective)
  then show "S = S'" using o(3) o'(3) by (simp only:)
qed

theorem installed_agree:
  "varied_narrowings_agree (finite_rename_system installed_placement Q) installed_presentation
    (produced_relocated installed_placement given_declarations)"
  by (rule varied_narrowings_agree_within[OF installed_presentation_formed(2,1) installed_union_sources relocated_within])

subsection \<open>A site of one rooted clause: one placed clause, one installed clause, one source\<close>

text \<open>
  A site of the rooted readers whose clause family is the one clause of a finite schema has at the placed program the
  one clause of that schema relocated, at the installed program one clause, which that schema matches, and one source
  for every socket varied there. 48's clause is its instance here (@{text placed_union_clause},
  @{text installed_union_clause}); 37's and 12's are its instances in
  @{text Development_Given_Installed_Productions}. The five sites of 48's callers are not: each has several clauses,
  told apart by their callees (@{thm [source] installed_union_sources}).
\<close>

theorem installed_single_clause:
  assumes site: "d \<in> system_definitions given_rooted_readers_system"
    and one: "\<And>c S. ((d,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema X"
  shows "((installed_placement d,a),Z) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q) \<longleftrightarrow>
      a = 0 \<and> Z = finite_rename_schema id id installed_placement X"
    and "\<exists>c1 T1 f1 h1. ((installed_placement d,c1),T1) |\<in>| finite_system_clauses installed_presentation \<and>
      finite_schema_match (finite_rename_schema id id installed_placement X) T1 = Some (f1,h1) \<and>
      (\<forall>c T. ((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1)"
    and "finite_varied_sources_unique_at {installed_placement d} (finite_rename_system installed_placement Q)
      installed_presentation"
proof -
  have Qd: "((d,c),Y) |\<in>| finite_system_clauses Q \<longleftrightarrow> c = 0 \<and> Y = X" for c Y
  proof -
    have "((d,c),Y) |\<in>| finite_system_clauses Q \<longleftrightarrow>
        ((d,c),decode_finite_schema Y) \<in> system_clauses given_rooted_readers_system"
      by (simp only: finite_system_clause_decoded rooted_clauses_Q[OF site])
    also have "\<dots> \<longleftrightarrow> c = 0 \<and> decode_finite_schema Y = decode_finite_schema X" by (rule one)
    also have "\<dots> \<longleftrightarrow> c = 0 \<and> Y = X" by (simp only: decode_finite_schema_injective)
    finally show ?thesis .
  qed
  have placed: "((installed_placement d,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q) \<longleftrightarrow>
      c = 0 \<and> S = finite_rename_schema id id installed_placement X" for c S
  proof
    assume "((installed_placement d,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    then obtain d' c0 S0 where o: "((d',c0),S0) |\<in>| finite_system_clauses Q"
        "installed_placement d' = installed_placement d" "c = c0" "S = finite_rename_schema id id installed_placement S0"
      by (auto simp: finite_rename_system_def)
    have "d' \<in> system_definitions (decode_finite_system Q)"
      using target_formed[unfolded schema_system_formed_def] o(1)[unfolded finite_system_clause_decoded] by blast
    then have "d' = d" using inj_onD[OF installation(5) o(2)] rooted_in_Q[OF site] by blast
    then show "c = 0 \<and> S = finite_rename_schema id id installed_placement X" using o Qd by auto
  next
    assume "c = 0 \<and> S = finite_rename_schema id id installed_placement X"
    then show "((installed_placement d,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
      using fimageI[OF iffD2[OF Qd[of 0 X]],
        of "map_prod (map_prod installed_placement id) (finite_rename_schema id id installed_placement)"]
      by (simp add: finite_rename_system_def)
  qed
  show "((installed_placement d,a),Z) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q) \<longleftrightarrow>
      a = 0 \<and> Z = finite_rename_schema id id installed_placement X"
    by (rule placed)
  show "finite_varied_sources_unique_at {installed_placement d} (finite_rename_system installed_placement Q)
      installed_presentation"
    unfolding finite_varied_sources_unique_at_def
  proof (intro allI impI)
    fix e c S c' S' c'' T f h f' h'
    assume e: "e \<in> {installed_placement d}"
      and S: "((e,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
      and S': "((e,c'),S') |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    have "e = installed_placement d" using e by simp
    then show "S = S'" using S S' by (simp add: placed)
  qed
  show "\<exists>c1 T1 f1 h1. ((installed_placement d,c1),T1) |\<in>| finite_system_clauses installed_presentation \<and>
      finite_schema_match (finite_rename_schema id id installed_placement X) T1 = Some (f1,h1) \<and>
      (\<forall>c T. ((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1)"
  proof -
  let ?P = "decode_finite_system (finite_rename_system installed_placement Q)"
  let ?N = "decode_finite_system installed_presentation"
  let ?S = "finite_rename_schema id id installed_placement X"
  have pc: "((installed_placement d,0),?S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q)"
    by (simp add: placed)
  have pcd: "((installed_placement d,0),decode_finite_schema ?S) \<in> system_clauses ?P"
    by (rule iffD1[OF finite_system_clause_decoded pc])
  have alpha: "system_alpha_variant ?P ?N" by (rule installed_presentation_variant)
  have Pf: "schema_system_formed ?P" by (rule conjunct1[OF alpha[unfolded system_alpha_variant_def]])
  have Nf: "schema_system_formed ?N" by (rule conjunct1[OF conjunct2[OF alpha[unfolded system_alpha_variant_def]]])
  have Pc: "d \<in> system_definitions ?P \<and> schema_formed X \<and> schema_dependencies X \<subseteq> system_definitions ?P"
    if "((d,s),X) \<in> system_clauses ?P" for d s X
    by (rule Pf[unfolded schema_system_formed_def, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
      THEN conjunct2, rule_format, OF that])
  have Nc: "d \<in> system_definitions ?N \<and> schema_formed X \<and> schema_dependencies X \<subseteq> system_definitions ?N"
    if "((d,s),X) \<in> system_clauses ?N" for d s X
    by (rule Nf[unfolded schema_system_formed_def, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
      THEN conjunct2, rule_format, OF that])
  have defined: "installed_placement d \<in> system_definitions ?P" by (rule conjunct1[OF Pc[OF pcd]])
  obtain f k where fk: "inj_on f (pattern_variables (system_interface ?P (installed_placement d))) \<and>
      system_interface ?N (installed_placement d) = rename_pattern f (system_interface ?P (installed_placement d)) \<and>
      schema_family_variant k (system_clause_family ?P (installed_placement d))
        (system_clause_family ?N (installed_placement d))"
    using bspec[OF alpha[unfolded system_alpha_variant_def, THEN conjunct2, THEN conjunct2, THEN conjunct2] defined]
    by blast
  have family: "schema_family_variant k (system_clause_family ?P (installed_placement d))
      (system_clause_family ?N (installed_placement d))" by (rule conjunct2[OF conjunct2[OF fk]])
  have placed_only: "s = 0 \<and> W = decode_finite_schema ?S"
    if sW: "(s,W) \<in> system_clause_family ?P (installed_placement d)" for s W
  proof -
    have cl: "((installed_placement d,s),W) \<in> system_clauses ?P" using sW by (simp only: system_clause_member)
    have Wf: "schema_formed W" by (rule conjunct1[OF conjunct2[OF Pc[OF cl]]])
    have "((installed_placement d,s),finite_schema_of W) |\<in>|
        finite_system_clauses (finite_rename_system installed_placement Q)"
      unfolding finite_system_clause_decoded decode_finite_schema_of[OF Wf] by (rule cl)
    then have c: "s = 0 \<and> finite_schema_of W = ?S" by (simp only: placed)
    have "W = decode_finite_schema (finite_schema_of W)" by (rule decode_finite_schema_of[OF Wf, symmetric])
    also have "\<dots> = decode_finite_schema ?S" by (simp only: conjunct2[OF c])
    finally have w: "W = decode_finite_schema ?S" .
    show ?thesis using conjunct1[OF c] w by (rule conjI)
  qed
  have pf: "(0,decode_finite_schema ?S) \<in> system_clause_family ?P (installed_placement d)"
    using pcd by (simp only: system_clause_member)
  obtain T0 where T0: "(k 0,T0) \<in> system_clause_family ?N (installed_placement d)"
      "schema_alpha_variant (decode_finite_schema ?S) T0"
    using schema_family_variant_entry[OF family pf] by blast
  have T0c: "((installed_placement d,k 0),T0) \<in> system_clauses ?N" using T0(1) by (simp only: system_clause_member)
  have T0f: "schema_formed T0" by (rule conjunct1[OF conjunct2[OF Nc[OF T0c]]])
  have T1a: "((installed_placement d,k 0),finite_schema_of T0) |\<in>| finite_system_clauses installed_presentation"
    unfolding finite_system_clause_decoded decode_finite_schema_of[OF T0f] by (rule T0c)
  obtain T1 where T1: "((installed_placement d,k 0),T1) |\<in>| finite_system_clauses installed_presentation"
      "T0 = decode_finite_schema T1"
    by (rule that[OF T1a decode_finite_schema_of[OF T0f, symmetric]])
  have Sf: "finite_schema_formed ?S" by (rule finite_system_clause_formed[OF installed_presentation_formed(2) pc])
  have Tf: "finite_schema_formed T1" by (rule finite_system_clause_formed[OF installed_presentation_formed(1) T1(1)])
  have "finite_schema_match ?S T1 \<noteq> None"
    by (rule iffD2[OF finite_schema_match_exact(2)[OF Sf Tf]]) (simp only: T1(2)[symmetric] T0(2))
  then obtain f1 h1 where m: "finite_schema_match ?S T1 = Some (f1,h1)" by (metis not_None_eq surj_pair)
  have sv: "single_valued (system_clause_family ?N (installed_placement d))"
    by (rule system_clause_family_functional[OF Nf])
  have only: "c = k 0 \<and> T = T1"
    if "((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation" for c T
  proof -
    have cT: "(c,decode_finite_schema T) \<in> system_clause_family ?N (installed_placement d)"
      using that by (simp only: system_clause_member finite_system_clause_decoded)
    obtain s W where sW: "(s,W) \<in> system_clause_family ?P (installed_placement d)" "c = k s"
      using schema_family_variant_origin[OF family cT] by blast
    have c: "c = k 0" using sW(2) conjunct1[OF placed_only[OF sW(1)]] by (simp only:)
    have dT: "decode_finite_schema T = T0" using single_valued_outputs[OF sv cT[unfolded c] T0(1)] .
    have "decode_finite_schema T = decode_finite_schema T1" using dT T1(2) by (simp only:)
    then have "T = T1" by (simp only: decode_finite_schema_injective)
    then show ?thesis using c by (intro conjI)
  qed
  show ?thesis
  proof (intro exI conjI allI impI)
    show "((installed_placement d,k 0),T1) |\<in>| finite_system_clauses installed_presentation" by (rule T1(1))
    show "finite_schema_match ?S T1 = Some (f1,h1)" by (rule m)
    fix c T assume a: "((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation"
    show "c = k 0" by (rule conjunct1[OF only[OF a]])
    show "T = T1" by (rule conjunct2[OF only[OF a]])
  qed
  qed
qed

text \<open>
  A registration at the placed site of one rooted clause, whose schema is that clause relocated, varies to exactly one
  registration at the site's one installed clause: 48's (@{text relocated_carry_uniquely}) and 12's in
  @{text Development_Given_Installed_Productions} are its instances.
\<close>

lemma installed_single_registration:
  assumes site: "d \<in> system_definitions given_rooted_readers_system"
    and one: "\<And>c S. ((d,c),S) \<in> system_clauses given_rooted_readers_system \<longleftrightarrow> c = 0 \<and> S = decode_finite_schema X"
    and at: "registration_site R = installed_placement d"
      "registration_schema R = finite_rename_schema id id installed_placement X"
  obtains c1 T1 f1 h1 where "((installed_placement d,c1),T1) |\<in>| finite_system_clauses installed_presentation"
    "finite_schema_match (finite_rename_schema id id installed_placement X) T1 = Some (f1,h1)"
    "\<forall>c T. ((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1"
    "registrations_varied (finite_rename_system installed_placement Q) installed_presentation R =
      {|registration_varied f1 T1 R|}"
proof -
  let ?P = "finite_rename_system installed_placement Q"
  let ?S = "finite_rename_schema id id installed_placement X"
  have pc: "((installed_placement d,0),?S) |\<in>| finite_system_clauses ?P"
    by (simp add: installed_single_clause(1)[OF site one])
  obtain c1 T1 f1 h1 where u: "((installed_placement d,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match ?S T1 = Some (f1,h1)"
      "\<forall>c T. ((installed_placement d,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1"
    using installed_single_clause(2)[OF site one] by blast
  have "registrations_varied ?P installed_presentation R = {|registration_varied f1 T1 R|}"
  proof (rule fset_eqI)
    fix R'
    show "R' |\<in>| registrations_varied ?P installed_presentation R \<longleftrightarrow> R' |\<in>| {|registration_varied f1 T1 R|}"
    proof
      assume "R' |\<in>| registrations_varied ?P installed_presentation R"
      then obtain c c' T' f h where r: "((installed_placement d,c),?S) |\<in>| finite_system_clauses ?P"
          "((installed_placement d,c'),T') |\<in>| finite_system_clauses installed_presentation"
          "finite_schema_match ?S T' = Some (f,h)" "R' = registration_varied f T' R"
        unfolding registrations_varied_member at by blast
      have "c' = c1 \<and> T' = T1" by (rule u(3)[rule_format, OF r(2)])
      then show "R' |\<in>| {|registration_varied f1 T1 R|}" using r(3,4) u(2) by auto
    next
      assume "R' |\<in>| {|registration_varied f1 T1 R|}"
      then have R': "R' = registration_varied f1 T1 R" by simp
      show "R' |\<in>| registrations_varied ?P installed_presentation R"
        unfolding registrations_varied_member at using pc u(1,2) R' by blast
    qed
  qed
  then show ?thesis by (rule that[OF u(1) u(2) u(3)])
qed

subsection \<open>48's registration at the placed and installed programs\<close>

lemma placed_union_clause:
  "((installed_placement 48,c),S) |\<in>| finite_system_clauses (finite_rename_system installed_placement Q) \<longleftrightarrow>
    c = 0 \<and> S = finite_rename_schema id id installed_placement union_schema"
  by (rule installed_single_clause(1)[OF given_rooted_declared_sites union_rooted_clause]) simp

lemma installed_union_clause:
  "\<exists>c1 T1 f1 h1. ((installed_placement 48,c1),T1) |\<in>| finite_system_clauses installed_presentation \<and>
    finite_schema_match (finite_rename_schema id id installed_placement union_schema) T1 = Some (f1,h1) \<and>
    (\<forall>c T. ((installed_placement 48,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1)"
  by (rule installed_single_clause(2)[OF given_rooted_declared_sites union_rooted_clause]) simp

lemma relocated_carry_uniquely:
  "productions_carry_uniquely (finite_rename_system installed_placement Q) installed_presentation
    (produced_relocated installed_placement given_declarations)"
  unfolding productions_carry_uniquely_def
proof (intro allI impI)
  fix e S s keep Vp Vh R
  assume m: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (produced_relocated installed_placement given_declarations)"
    and p: "declared_production (produced_relocated installed_placement given_declarations) e S s = Some R"
  have R: "R = registration_relocated installed_placement union_registration"
    using relocated_at_union(4)[OF m disjI2] p by simp
  have site: "registration_site R = installed_placement 48"
    "registration_schema R = finite_rename_schema id id installed_placement union_schema"
    unfolding R by (simp_all add: union_registration_def)
  have r48: "48 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  obtain c1 T1 f1 h1 where "((installed_placement 48,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match (finite_rename_schema id id installed_placement union_schema) T1 = Some (f1,h1)"
      "\<forall>c T. ((installed_placement 48,c),T) |\<in>| finite_system_clauses installed_presentation \<longrightarrow> c = c1 \<and> T = T1"
      "registrations_varied (finite_rename_system installed_placement Q) installed_presentation R =
        {|registration_varied f1 T1 R|}"
    by (rule installed_single_registration[OF r48 union_rooted_clause site])
  then show "\<exists>R'. registrations_varied (finite_rename_system installed_placement Q) installed_presentation R = {|R'|}"
    by blast
qed

theorem installed_declared:
  "narrowed_productions_declared (produced_declarations_varied (finite_rename_system installed_placement Q)
    installed_presentation (produced_relocated installed_placement given_declarations))"
  by (rule narrowed_productions_declared_varied_within[OF installed_presentation_formed(2,1) installed_union_sources
    relocated_within relocated_declared relocated_carry_uniquely])

lemma union_meanings_installed:
  "(installed_placement 48,t) \<in> positive_meaning (decode_finite_system installed_presentation) \<longleftrightarrow>
    (48,t) \<in> positive_meaning data_union_system"
  "(installed_placement 5,t) \<in> positive_meaning (decode_finite_system installed_presentation) \<longleftrightarrow>
    (5,t) \<in> positive_meaning bag_comparison_system"
proof -
  have r48: "48 \<in> system_definitions given_rooted_readers_system" by (rule given_rooted_declared_sites) simp
  show "(installed_placement 48,t) \<in> positive_meaning (decode_finite_system installed_presentation) \<longleftrightarrow>
      (48,t) \<in> positive_meaning data_union_system"
    using installed_meaning[OF rooted_in_Q[OF r48]] union_meanings_Q(1)[of t]
    by (simp add: installed_presentation_exact(3))
  show "(installed_placement 5,t) \<in> positive_meaning (decode_finite_system installed_presentation) \<longleftrightarrow>
      (5,t) \<in> positive_meaning bag_comparison_system"
    using installed_meaning[OF rooted_in_Q[OF given_rooted_selection_site]] union_meanings_Q(2)[of t]
    by (simp add: installed_presentation_exact(3))
qed

theorem installed_productions:
  "productions_discharged (positive_meaning (decode_finite_system installed_presentation)) installed_presentation m
    (produced_declarations_varied (finite_rename_system installed_placement Q) installed_presentation
      (produced_relocated installed_placement given_declarations))"
  unfolding productions_discharged_def
proof (intro allI impI)
  let ?P = "finite_rename_system installed_placement Q"
  let ?D = "produced_relocated installed_placement given_declarations"
  fix e T t keep Vp Vh R'
  assume mem: "(e,T,t,keep,Vp,Vh) |\<in>| declared_sockets (produced_declarations_varied ?P installed_presentation ?D)"
    and p: "declared_production (produced_declarations_varied ?P installed_presentation ?D) e T t = Some R'"
  obtain S s c c' f h where ms: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets (resolution_declarations.truncate ?D)"
      "((e,c),S) |\<in>| finite_system_clauses ?P" "s \<in> schema_sockets (decode_finite_schema S)"
      "((e,c'),T) |\<in>| finite_system_clauses installed_presentation" "finite_schema_match S T = Some (f,h)" "t = h s"
    using mem[unfolded produced_declarations_varied_fields declarations_varied_sockets_member] by blast
  have m1: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets ?D" using ms(1) by simp
  have src: "(S,s) |\<in>| varied_socket_sources ?P installed_presentation (declared_sockets ?D) e T t"
    unfolding varied_socket_sources_member using m1 ms(2-6) by blast
  obtain R where R: "declared_production ?D e S s = Some R" "registrations_varied ?P installed_presentation R = {|R'|}"
    using production_varied_source[OF p[unfolded produced_declarations_varied_fields] src] by blast
  have pr: "declared_production ?D e S s \<noteq> None" using R(1) by simp
  note u = relocated_at_union[OF m1 disjI2[OF pr]]
  have Rr: "R = registration_relocated installed_placement union_registration" using u(4) R(1) by simp
  have site: "registration_site R = installed_placement 48"
    "registration_schema R = finite_rename_schema id id installed_placement union_schema"
    unfolding Rr by (simp_all add: union_registration_def)
  have "R' |\<in>| registrations_varied ?P installed_presentation R" using R(2) by simp
  then obtain c1 T1 f1 h1 where v: "((installed_placement 48,c1),T1) |\<in>| finite_system_clauses installed_presentation"
      "finite_schema_match (finite_rename_schema id id installed_placement union_schema) T1 = Some (f1,h1)"
      "R' = registration_varied f1 T1 R"
    unfolding registrations_varied_member site by blast
  have Sf: "finite_schema_formed (finite_rename_schema id id installed_placement union_schema)"
    by (rule finite_system_clause_formed[OF installed_presentation_formed(2), where e="installed_placement 48" and c=0])
      (simp add: placed_union_clause)
  have Tf: "finite_schema_formed T1" by (rule finite_system_clause_formed[OF installed_presentation_formed(1) v(1)])
  note mx = finite_schema_match_exact(1)[OF Sf Tf v(2)]
  have T1: "T1 = finite_rename_schema f1 h1 installed_placement union_schema"
    using mx finite_rename_schema_callees_matched by simp
  have vs: "schema_variables (decode_finite_schema (finite_rename_schema id id installed_placement union_schema)) =
      schema_variables data_union_schema"
    by (simp add: finite_rename_schema_correct renamed_schema_variables union_schema_decoded)
  have "{0,1,2} \<subseteq> schema_variables data_union_schema"
    by (auto simp: schema_variables_def data_union_schema_def)
  then have vars: "{0,1,2} \<subseteq>
      schema_variables (decode_finite_schema (finite_rename_schema id id installed_placement union_schema))"
    by (simp only: vs)
  have inj: "inj_on f1 {0,1,2}" by (rule inj_on_subset[OF conjunct1[OF mx] vars])
  have R'': "R' = union_registration_at (installed_placement 48) (installed_placement 5) T1 (f1 2) (f1 0) (f1 1)"
    unfolding v(3) Rr by (rule union_registration_varied_relocated)
  have K: "declared_narrowing (produced_declarations_varied ?P installed_presentation ?D) e T t = union_class"
    using narrowing_varied_source[OF installed_agree src] u(3) by (simp add: produced_declarations_varied_fields)
  show "head_registration Vp (registration_schema R') (registration_variable R') \<and>
      head_registration_produces (finite_collection_construction [R'] m) installed_presentation (registration_site R')
        (registration_schema R') (registration_variable R')
        (declared_narrowing (produced_declarations_varied ?P installed_presentation ?D) e T t) \<and>
      head_registration_answers (positive_meaning (decode_finite_system installed_presentation))
        (finite_collection_construction [R'] m) installed_presentation (registration_site R') (registration_schema R') Vp
        (registration_variable R')"
    unfolding R'' union_registration_at_fields K u(2) T1
    by (intro conjI union_variant_head_registration[OF inj] union_at_registration_produces
      union_at_registration_answers[OF union_meanings_installed(1) union_meanings_installed(2) union_variant_input])
qed

subsection \<open>The committed registrations at the installed program\<close>

definition installed_given_declarations where
  "installed_given_declarations = produced_declarations_varied (finite_rename_system installed_placement Q)
    installed_presentation (produced_relocated installed_placement given_declarations)"

definition installed_given_frames where
  "installed_given_frames = frames_varied (finite_rename_system installed_placement Q) installed_presentation
    (frames_relocated installed_placement given_narrowed_frames)"

definition installed_given_correspondence where
  "installed_given_correspondence = given_declarations_correspondence \<circ>
    inv_into (declared_sites (resolution_declarations.truncate given_declarations)) installed_placement"

theorem installed_committed_registrations:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
  shows "committed_registrations (installed_construction \<kappa>) installed_presentation m' installed_given_declarations
    installed_given_frames installed_given_correspondence"
  unfolding installed_given_declarations_def installed_given_frames_def installed_given_correspondence_def
    installed_construction_def
  using install.committed_registrations_produced_relocated[OF installed_built installed_presentation_read
    committed_registrations_Q[OF \<kappa> complete] given_declarations_sites_Q given_narrowed_frame_sites_Q
    installed_agree[unfolded installed_placement_def] installed_productions[unfolded installed_placement_def]
    installed_declared[unfolded installed_placement_def], folded installed_placement_def] .

theorem installed_committed_exact:
  assumes \<kappa>: "finite_witness_construction_formed \<kappa>" and complete: "finite_construction_complete \<kappa> Q"
    and resolution: "native_committed_resolution (installed_construction \<kappa>)
      (finite_narrowed_commitment installed_presentation m' installed_given_declarations installed_given_frames)
      installed_presentation R n = (T,A)"
  shows "fimage fst T = R"
    and "(q,Finite_Resolved C) |\<in>| T \<Longrightarrow> C \<noteq> {||} \<and>
      fBall C (\<lambda>p. finite_checks_schema_proof installed_presentation p (fst q) (snd q)) \<and>
      decode_finite_call_term q \<in> positive_meaning installed_program"
    and "(q,r) |\<in>| T \<Longrightarrow> finite_resolution_refutes r \<Longrightarrow> decode_finite_call_term q \<notin> positive_meaning installed_program"
    and "A = Some B \<Longrightarrow> schema_system_formed installed_program \<and>
      fset B = {q\<in>fset R. decode_finite_call_term q \<in> positive_meaning installed_program}"
  using native_committed_registrations_exact[OF installed_committed_registrations[OF \<kappa> complete] resolution,
    unfolded installed_presentation_exact(3)] by blast+

end

text \<open>
  The one record at the asked relation's installed guard (526 in the native course, #707) and at the first request's
  installed program (561 at the installation, #547, #399): committed with every complete construction of the numbered
  program; the plain record's carrying stands as @{thm [source] asked_installed_plain_declarations_discharged} and
  @{thm [source] first_request_installed_plain_declarations_discharged}.
\<close>

theorem asked_installed_declarations_discharged:
  assumes "finite_witness_construction_formed \<kappa>" "finite_construction_complete \<kappa> finite_asked_program"
  shows "committed_registrations (asked_extension.installed_construction \<kappa>) asked_installed_presentation m'
    asked_extension.installed_given_declarations asked_extension.installed_given_frames
    asked_extension.installed_given_correspondence"
  unfolding asked_installed_presentation_def by (rule asked_extension.installed_committed_registrations[OF assms])

theorem first_request_installed_declarations_discharged:
  assumes "finite_witness_construction_formed \<kappa>" "finite_construction_complete \<kappa> finite_first_request_program"
  shows "committed_registrations (first_request_extension.installed_construction \<kappa>) first_request_installed_presentation
    m' first_request_extension.installed_given_declarations first_request_extension.installed_given_frames
    first_request_extension.installed_given_correspondence"
  unfolding first_request_installed_presentation_def
  by (rule first_request_extension.installed_committed_registrations[OF assms])

end
