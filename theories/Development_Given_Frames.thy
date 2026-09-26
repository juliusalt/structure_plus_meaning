theory Development_Given_Frames
  imports Development_Given_Installed_Declarations
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
  have program: "systems_agree_on P given_program_system (system_definitions P)"
    by (rule whole_agreement_transitive[OF agree guard_program_agreement])
  have rooted: "systems_agree_on P given_rooted_readers_system
      (system_definitions P \<inter> system_definitions given_rooted_readers_system)"
    unfolding given_rooted_readers_system_def by (rule rooted_intersection_agreement[OF program])
  show ?thesis
  proof (rule frames_agree_read_discharged[OF Pf given_rooted_readers_formed rooted
      systems_agree_on_intersection_closed[OF Pf given_rooted_readers_formed rooted] _ frames])
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
  "frames_discharged given_rooted_meaning_at given_declarations lookup_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at lookup_declarations lookup_frames"
    by (rule given_frames_carried[OF artifact_lookup_system_formed guard_lookup_agreement _
    lookup_frames_discharged]) (auto simp: lookup_declarations_def lookup_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: lookup_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_identity:
  "frames_discharged given_rooted_meaning_at given_declarations identity_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at identity_declarations identity_frames"
    by (rule given_frames_carried[OF artifact_identity_system_formed guard_identity_agreement _
    identity_frames_discharged]) (auto simp: identity_declarations_def identity_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: identity_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_comparison:
  "frames_discharged given_rooted_meaning_at given_declarations comparison_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at comparison_declarations comparison_frames"
    by (rule given_frames_carried[OF artifact_comparison_system_formed guard_comparison_agreement _
    comparison_frames_discharged]) (auto simp: comparison_declarations_def comparison_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: comparison_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_headed:
  "frames_discharged given_rooted_meaning_at given_declarations headed_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at headed_declarations headed_frames"
    by (rule given_frames_carried[OF headed_material_system_formed guard_headed_agreement _
    headed_frames_discharged]) (auto simp: headed_declarations_def headed_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: headed_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_family_rows:
  "frames_discharged given_rooted_meaning_at given_declarations family_rows_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at family_rows_declarations family_rows_frames"
    by (rule given_frames_carried[OF family_admission_system_formed guard_family_agreement _
    family_rows_frames_discharged]) (auto simp: family_rows_declarations_def family_rows_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: family_rows_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_admission:
  "frames_discharged given_rooted_meaning_at given_declarations admission_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at admission_declarations admission_frames"
    by (rule given_frames_carried[OF citation_admission_system_formed guard_citation_agreement _
    admission_frames_discharged]) (auto simp: admission_declarations_def external_socket_decoded citation_admission_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: admission_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_interpretation:
  "frames_discharged given_rooted_meaning_at given_declarations interpretation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at interpretation_declarations interpretation_frames"
    by (rule given_frames_carried[OF citation_interpretation_system_formed
    guard_interpretation_agreement _ interpretation_frames_discharged]) (auto simp: interpretation_declarations_def interpretation_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: interpretation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_binder:
  "frames_discharged given_rooted_meaning_at given_declarations binder_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at binder_declarations binder_frames"
    by (rule given_frames_carried[OF binder_admission_system_formed guard_binder_agreement _
    binder_frames_discharged]) (auto simp: binder_declarations_def binder_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: binder_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_quotation:
  "frames_discharged given_rooted_meaning_at given_declarations quotation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at quotation_declarations quotation_frames"
    by (rule given_frames_carried[OF quotation_admission_system_formed guard_quotation_agreement _
    instantiation_notion_frames_discharged(1)]) (auto simp: quotation_declarations_def quotation_pair_socket_decoded quotation_admission_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: quotation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_instantiation:
  "frames_discharged given_rooted_meaning_at given_declarations instantiation_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at instantiation_declarations instantiation_frames"
    by (rule given_frames_carried[OF pattern_instantiation_system_formed
    guard_instantiation_agreement _ instantiation_notion_frames_discharged(2)]) (auto simp: instantiation_declarations_def instantiation_constant_socket_decoded instantiation_pair_socket_decoded pattern_instantiation_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: instantiation_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_prospective:
  "frames_discharged given_rooted_meaning_at given_declarations prospective_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at prospective_declarations prospective_frames"
    by (rule given_frames_carried[OF prospective_instantiation_system_formed
    guard_prospective_agreement _ instantiation_notion_frames_discharged(3)]) (auto simp: prospective_declarations_def prospective_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: prospective_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_vector:
  "frames_discharged given_rooted_meaning_at given_declarations vector_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at vector_declarations vector_frames"
    by (rule given_frames_carried[OF vector_instantiation_system_formed
    guard_vector_instantiation_agreement _ schema_instantiation_notion_frames_discharged(1)]) (auto simp: vector_declarations_def vector_cons_socket_decoded vector_instantiation_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: vector_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_record:
  "frames_discharged given_rooted_meaning_at given_declarations record_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at record_declarations record_frames"
    by (rule given_frames_carried[OF record_instantiation_system_formed
    guard_record_instantiation_agreement _ schema_instantiation_notion_frames_discharged(2)]) (auto simp: record_declarations_def record_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: record_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_material:
  "frames_discharged given_rooted_meaning_at given_declarations material_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at material_declarations material_frames"
    by (rule given_frames_carried[OF material_instantiation_system_formed
    guard_material_instantiation_agreement _ schema_instantiation_notion_frames_discharged(3)]) (auto simp: material_declarations_def material_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: material_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_rows:
  "frames_discharged given_rooted_meaning_at given_declarations premise_rows_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_rows_declarations premise_rows_frames"
    by (rule given_frames_carried[OF premise_rows_system_formed guard_premise_rows_agreement _
    schema_instantiation_notion_frames_discharged(4)]) (auto simp: premise_rows_declarations_def premise_call_socket_decoded premise_material_socket_decoded premise_rows_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_rows_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_family:
  "frames_discharged given_rooted_meaning_at given_declarations premise_family_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_family_declarations premise_family_frames"
    by (rule given_frames_carried[OF premise_family_instantiation_system_formed
    guard_premise_family_agreement _ schema_instantiation_notion_frames_discharged(5)]) (auto simp: premise_family_declarations_def premise_family_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_family_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema:
  "frames_discharged given_rooted_meaning_at given_declarations schema_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_declarations schema_frames"
    by (rule given_frames_carried[OF schema_instantiation_system_formed
    guard_schema_instantiation_agreement _ schema_instantiation_notion_frames_discharged(6)]) (auto simp: schema_declarations_def schema_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_interface_slot:
  "frames_discharged given_rooted_meaning_at given_declarations interface_slot_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at interface_slot_declarations interface_slot_frames"
    by (rule given_frames_carried[OF definition_slot_reading_system_formed
    guard_definition_slot_agreement _ interface_slot_frames_discharged]) (auto simp: interface_slot_declarations_def interface_slot_socket_decoded definition_slot_reading_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: interface_slot_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema_family_socket:
  "frames_discharged given_rooted_meaning_at given_declarations schema_family_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_family_socket_record schema_family_socket_frames"
    by (rule given_frames_carried[OF schema_family_admission_system_formed
    guard_schema_family_agreement _ schema_family_socket_frames_discharged]) (auto simp: schema_family_socket_record_def schema_family_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_family_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_callee_inclusion_socket:
  "frames_discharged given_rooted_meaning_at given_declarations callee_inclusion_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at callee_inclusion_socket_record callee_inclusion_socket_frames"
    by (rule given_frames_carried[OF definition_callee_inclusion_system_formed
    guard_definition_callee_inclusion_agreement _ callee_inclusion_socket_frames_discharged]) (auto simp: callee_inclusion_socket_record_def callee_inclusion_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: callee_inclusion_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_payload_audit_socket:
  "frames_discharged given_rooted_meaning_at given_declarations payload_audit_socket_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at payload_audit_socket_record payload_audit_socket_frames"
    by (rule given_frames_carried[OF payload_audit_system_formed guard_audit_agreement _
    payload_audit_socket_frames_discharged]) (auto simp: payload_audit_socket_record_def payload_audit_socket_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: payload_audit_socket_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_clause_reading_row:
  "frames_discharged given_rooted_meaning_at given_declarations clause_reading_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at clause_reading_row_record clause_reading_row_frames"
    by (rule given_frames_carried[OF definition_clause_reading_system_formed
    guard_clause_reading_agreement _ clause_reading_row_frames_discharged]) (auto simp: clause_reading_row_record_def clause_reading_row_decoded)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: clause_reading_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_premise_slot_row:
  "frames_discharged given_rooted_meaning_at given_declarations premise_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at premise_slot_row_record premise_slot_row_frames"
    by (rule given_frames_carried[OF schema_slot_reading_system_formed
    guard_schema_slot_agreement _ premise_slot_row_frames_discharged]) (auto simp: premise_slot_row_record_def premise_slot_row_decoded schema_slot_reading_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: premise_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_schema_slot_row:
  "frames_discharged given_rooted_meaning_at given_declarations schema_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at schema_slot_row_record schema_slot_row_frames"
    by (rule given_frames_carried[OF definition_slot_reading_system_formed
    guard_definition_slot_agreement _ schema_slot_row_frames_discharged]) (auto simp: schema_slot_row_record_def schema_slot_row_decoded definition_slot_reading_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: schema_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_root_slot_row:
  "frames_discharged given_rooted_meaning_at given_declarations root_slot_row_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at root_slot_row_record root_slot_row_frames"
    by (rule given_frames_carried[OF package_slot_reading_system_formed
    guard_package_slot_agreement _ root_slot_row_frames_discharged]) (auto simp: root_slot_row_record_def root_slot_row_decoded package_slot_reading_clauses_def)
  show ?thesis unfolding given_declarations_records
    apply (rule frames_list_discharged)
    apply (simp only: list.set insert_iff empty_iff)
    apply (elim disjE)
    apply (simp_all only: own)
    apply (rule frames_apart_discharged; auto simp: root_slot_row_frames_def given_record_defs slot_sockets_distinct)+
    done
qed

lemma given_frames_application:
  "frames_discharged given_rooted_meaning_at given_declarations application_frames"
proof -
  have own: "frames_discharged given_rooted_meaning_at application_declarations application_frames"
    by (rule given_frames_carried[OF application_reading_system_formed guard_application_reading_agreement _
    instantiation_notion_frames_discharged(4)]) (auto simp: application_declarations_def application_socket_decoded)
  show ?thesis unfolding given_declarations_records
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
  "frames_discharged (positive_meaning given_rooted_readers_system) given_declarations given_frames"
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
  shows "\<exists>keep Vp Vh. (e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
proof -
  obtain \<Phi> where \<Phi>: "\<Phi> \<in> set (map snd given_frame_families)" "(e,S,s,C) |\<in>| \<Phi>"
    using assms unfolding given_frames_def frames_foldr_member by blast
  then obtain D where D: "(D,\<Phi>) \<in> set given_frame_families" by auto
  obtain keep Vp Vh where "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets D"
    using given_frame_families_own(2)[OF D \<Phi>(2)] by force
  then have "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    unfolding given_declarations_records by (rule declarations_list_socket_member[OF given_frame_families_own(1)[OF D]])
  then show ?thesis by blast
qed

lemma given_frame_sites: "frame_sites given_frames \<subseteq> system_definitions given_rooted_readers_system"
proof
  fix x assume "x \<in> frame_sites given_frames"
  then obtain e S s C where f: "(e,S,s,C) |\<in>| given_frames" and x: "x = e \<or> x \<in> schema_dependencies (decode_finite_schema S)"
    unfolding frame_sites_def by auto
  obtain keep Vp Vh where sock: "(e,S,s,keep,Vp,Vh) |\<in>| declared_sockets given_declarations"
    using given_frames_at_sockets[OF f] by blast
  have e: "e \<in> system_definitions given_rooted_readers_system"
    using given_declarations_sites declared_sites_members(4)[OF sock] by blast
  show "x \<in> system_definitions given_rooted_readers_system"
    using x e given_socket_reaches[OF sock e] by blast
qed

theorem given_placed_frames_discharged:
  "frames_discharged (positive_meaning (decode_finite_system given_placed_program))
    (declarations_relocated given_readers_placement given_declarations)
    (frames_relocated given_readers_placement given_frames)"
proof -
  have Pf: "schema_system_formed (decode_finite_system finite_rooted_given_readers)"
    by (simp add: finite_rooted_given_readers_exact)
  have "system_definitions (decode_finite_system finite_rooted_given_readers) \<union> declared_sites given_declarations \<union>
      frame_sites given_frames = system_definitions given_rooted_readers_system"
    using given_declarations_sites given_frame_sites by (auto simp only: finite_rooted_given_readers_exact)
  then have inj: "inj_on given_readers_placement (system_definitions (decode_finite_system finite_rooted_given_readers) \<union>
      declared_sites given_declarations \<union> frame_sites given_frames)"
    using given_readers_installation(3) by (simp only:)
  show ?thesis
    by (rule frames_relocated_discharged[OF Pf inj]) (simp add: finite_rooted_given_readers_exact given_frames_discharged)
qed

end
