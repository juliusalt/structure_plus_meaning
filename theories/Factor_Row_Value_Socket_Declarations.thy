theory Factor_Row_Value_Socket_Declarations
  imports Factor_Artifact_Citation_Declarations Factor_Definition_Callee_Inclusion Factor_Payload_Audit
begin

text \<open>
  32's kept sockets whose rows 59 carries into a list consumer (DECISIONS.md, task 495's entry, its addition "The
  given's remaining producers: views, carriers and narrowed sockets", row 32, and correction (10) of "Committed choice,
  for refusals"): 71.0/1 (59 \<rightarrow> 70), 75.0/3 (59 \<rightarrow> 74) and 505.0/4 (59 \<rightarrow> 504, the payload audit's G4). Each is
  declared kept, 32 the producer at R6's identity view with its rows read as a bag, 59 a carrier from the rows to
  their values and the list consumer a carrier with no output, and framed at its carried set, 32's rows and 59's
  values. Each record and frame is discharged at the system where its clause stands, from the notions' contracts;
  no clause of any program changes.
\<close>

section \<open>A list checked element by element in a context keeps its answer under a permutation\<close>

text \<open>
  A context-list profile holds a list exactly when every element holds in the context
  (@{thm [source] context_list_profile.lists}): the answer reads the list's members only, so a permuted list is
  answered as the list is. Stated once for every profile; 70, 74 and 504 are its instances.
\<close>

context context_list_profile
begin

theorem list_bag_consumer:
  "consumer_discharged (positive_meaning P) list_site view_identity term_bag_transport"
  unfolding consumer_view_simps(1)[symmetric] consumer_discharged_argument consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "term_bag_transport y y'"
  then obtain ys ys' where y: "y = data_list_term ys" and y': "y' = data_list_term ys'" and m: "mset ys = mset ys'"
    by (auto simp: term_bag_transport_iff)
  show "(list_site,Pair_Term x y) \<in> positive_meaning P \<longleftrightarrow> (list_site,Pair_Term x y') \<in> positive_meaning P"
    by (simp only: y y' lists mset_eq_setD[OF m])
qed

end

section \<open>What the three sockets share\<close>

text \<open>
  32 answers a bag of rows at any system agreeing with its own at 32: R6's producer read through
  @{thm [source] family_rows_bag} (@{thm [source] binder_family_producer}), carried to the system. A list consumer
  becomes a carrier with no output (@{thm [source] consumer_discharged_carrier}).
\<close>

lemma family_rows_producer_at:
  fixes M :: "(nat \<times> factor_term) set"
  assumes site: "\<And>t. (32,t) \<in> M \<longleftrightarrow> (32,t) \<in> positive_meaning family_admission_system"
  shows "producer_discharged M 32 view_identity [snd (snd view_identity)] (\<lambda>_. row_bag_transport)"
proof -
  have eq: "\<And>t. (32,t) \<in> M \<longleftrightarrow> (32,t) \<in> positive_meaning binder_admission_system"
    using site binder_admission_components(2) by blast
  show ?thesis using binder_family_producer by (simp only: producer_discharged_site[OF eq])
qed

lemma row_values_carrier_at:
  fixes M :: "(nat \<times> factor_term) set"
  assumes site: "\<And>t. (59,t) \<in> M \<longleftrightarrow> (59,t) \<in> positive_meaning row_values_system"
  shows "carrier_discharged M 59 view_identity row_bag_transport term_bag_transport"
  using row_values_carrier by (simp only: carrier_discharged_site[OF site])

lemma list_consumer_carrier:
  assumes consumer: "consumer_discharged M' l view_identity term_bag_transport"
    and site: "\<And>t. (l,t) \<in> M \<longleftrightarrow> (l,t) \<in> M'"
  shows "carrier_discharged M l (consumer_carrier_view view_identity) (consumer_input view_identity term_bag_transport) (=)"
  using consumer consumer_discharged_site[of l M M', OF site]
    consumer_discharged_carrier[OF view_identity_formed term_bag_transport_sym, of M l] by blast

text \<open>The carriers of each socket: 59 at socket q, from the rows to their values, and the list consumer at r.\<close>

definition row_value_carriers :: "nat \<Rightarrow> nat \<Rightarrow> nat clause_carrier list" where
  "row_value_carriers q r = [(q,view_identity,row_bag_transport,term_bag_transport),
    (r,consumer_carrier_view view_identity,consumer_input view_identity term_bag_transport,(=))]"

lemmas row_value_listed_simps = socket_listed_simps row_value_carriers_def consumer_input_def view_identity_term
  pair_view_some insert_commute

section \<open>71.0/1: schema family admission, 59 \<rightarrow> 70\<close>

definition schema_family_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "schema_family_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))),
      (1,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 2)) (Finite_Variable 4)),
      (2,59,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)),
      (3,70,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 5))|},
    finite_schema_materials = {||}\<rparr>"

lemma schema_family_socket_decoded: "decode_finite_schema schema_family_socket_schema = schema_family_admission_schema"
  by (simp add: schema_family_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def schema_family_admission_schema_def)

theorem schema_family_socket_carried:
  "socket_carried (positive_meaning schema_family_admission_system) schema_family_socket_schema 1 True view_identity
    view_identity row_bag_transport (row_value_carriers 2 3)"
proof -
  let ?M = "positive_meaning schema_family_admission_system"
  have producer: "producer_discharged ?M 32 view_identity [snd (snd view_identity)] (\<lambda>_. row_bag_transport)"
    by (rule family_rows_producer_at[OF schema_family_admission_components(2)])
  have valued: "carrier_discharged ?M 59 view_identity row_bag_transport term_bag_transport"
    by (rule row_values_carrier_at[OF schema_family_admission_components(3)])
  have consumed: "carrier_discharged ?M 70 (consumer_carrier_view view_identity)
      (consumer_input view_identity term_bag_transport) (=)"
    by (rule list_consumer_carrier[OF schema_root_list_profile.list_bag_consumer schema_family_admission_components(4)])
  show ?thesis
    by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed producer, where \<sigma> = "\<lambda>_. 1"])
      (simp add: row_value_listed_simps schema_family_socket_schema_def valued consumed)
qed

theorem schema_family_socket_framed:
  "socket_framed (positive_meaning schema_family_admission_system) schema_family_socket_schema 1 True view_identity
    view_identity {4,5}"
  by (rule socket_framed_at_carried[OF schema_family_socket_carried])
    (simp add: row_value_listed_simps schema_family_socket_schema_def)

theorem schema_family_socket_discharged:
  "socket_discharged (positive_meaning schema_family_admission_system) schema_family_socket_schema 1 True view_identity
    view_identity"
  by (rule socket_discharged_carried[OF schema_family_socket_carried])

section \<open>75.0/3: definition callee inclusion, 59 \<rightarrow> 74\<close>

definition callee_inclusion_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "callee_inclusion_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,72,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
      (1,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 5))),
      (2,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 3))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 8))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 9)) (Finite_Pattern_Payload [])))),
      (3,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 9)) (Finite_Variable 10)),
      (4,59,Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 11)),
      (5,74,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))
        (Finite_Variable 11)),
      (6,47,Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 1))|},
    finite_schema_materials = {||}\<rparr>"

lemma callee_inclusion_socket_decoded:
  "decode_finite_schema callee_inclusion_socket_schema = definition_callee_inclusion_schema"
  by (simp add: callee_inclusion_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def definition_callee_inclusion_schema_def)

theorem callee_inclusion_socket_carried:
  "socket_carried (positive_meaning definition_callee_inclusion_system) callee_inclusion_socket_schema 3 True
    view_identity view_identity row_bag_transport (row_value_carriers 4 5)"
proof -
  let ?M = "positive_meaning definition_callee_inclusion_system"
  have producer: "producer_discharged ?M 32 view_identity [snd (snd view_identity)] (\<lambda>_. row_bag_transport)"
    by (rule family_rows_producer_at[OF definition_callee_inclusion_components(4)])
  have valued: "carrier_discharged ?M 59 view_identity row_bag_transport term_bag_transport"
    by (rule row_values_carrier_at[OF definition_callee_inclusion_components(5)])
  have consumed: "carrier_discharged ?M 74 (consumer_carrier_view view_identity)
      (consumer_input view_identity term_bag_transport) (=)"
    by (rule list_consumer_carrier[OF schema_callee_list_profile.list_bag_consumer
      definition_callee_inclusion_components(6)])
  show ?thesis
    by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed producer, where \<sigma> = "\<lambda>_. 1"])
      (simp add: row_value_listed_simps callee_inclusion_socket_schema_def valued consumed)
qed

theorem callee_inclusion_socket_framed:
  "socket_framed (positive_meaning definition_callee_inclusion_system) callee_inclusion_socket_schema 3 True
    view_identity view_identity {10,11}"
  by (rule socket_framed_at_carried[OF callee_inclusion_socket_carried])
    (simp add: row_value_listed_simps callee_inclusion_socket_schema_def)

theorem callee_inclusion_socket_discharged:
  "socket_discharged (positive_meaning definition_callee_inclusion_system) callee_inclusion_socket_schema 3 True
    view_identity view_identity"
  by (rule socket_discharged_carried[OF callee_inclusion_socket_carried])

section \<open>505.0/4: the payload audit (the guard's G4), 59 \<rightarrow> 504\<close>

definition payload_audit_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "payload_audit_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,72,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))),
      (1,500,Finite_Variable 3),
      (2,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 4))),
      (3,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 8)) (Finite_Pattern_Payload [])))),
      (4,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 8)) (Finite_Variable 9)),
      (5,59,Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 10)),
      (6,504,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 10))|},
    finite_schema_materials = {||}\<rparr>"

lemma payload_audit_socket_decoded: "decode_finite_schema payload_audit_socket_schema = payload_audit_schema"
  by (simp add: payload_audit_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def payload_audit_schema_def)

theorem payload_audit_socket_carried:
  "socket_carried (positive_meaning payload_audit_system) payload_audit_socket_schema 4 True view_identity
    view_identity row_bag_transport (row_value_carriers 5 6)"
proof -
  let ?M = "positive_meaning payload_audit_system"
  have producer: "producer_discharged ?M 32 view_identity [snd (snd view_identity)] (\<lambda>_. row_bag_transport)"
    by (rule family_rows_producer_at[OF payload_audit_components(4)])
  have valued: "carrier_discharged ?M 59 view_identity row_bag_transport term_bag_transport"
    by (rule row_values_carrier_at[OF payload_audit_components(5)])
  have consumed: "carrier_discharged ?M 504 (consumer_carrier_view view_identity)
      (consumer_input view_identity term_bag_transport) (=)"
    by (rule list_consumer_carrier[OF clause_family_payloads_profile.list_bag_consumer payload_audit_components(7)])
  show ?thesis
    by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed producer, where \<sigma> = "\<lambda>_. 1"])
      (simp add: row_value_listed_simps payload_audit_socket_schema_def valued consumed)
qed

theorem payload_audit_socket_framed:
  "socket_framed (positive_meaning payload_audit_system) payload_audit_socket_schema 4 True view_identity
    view_identity {9,10}"
  by (rule socket_framed_at_carried[OF payload_audit_socket_carried])
    (simp add: row_value_listed_simps payload_audit_socket_schema_def)

theorem payload_audit_socket_discharged:
  "socket_discharged (positive_meaning payload_audit_system) payload_audit_socket_schema 4 True view_identity
    view_identity"
  by (rule socket_discharged_carried[OF payload_audit_socket_carried])

section \<open>The records and their frames, each at the system where its clause stands\<close>

definition schema_family_socket_record :: "(nat,nat,nat) resolution_declarations" where
  "schema_family_socket_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(71,schema_family_socket_schema,1,True,view_identity,view_identity)|}\<rparr>"

definition callee_inclusion_socket_record :: "(nat,nat,nat) resolution_declarations" where
  "callee_inclusion_socket_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(75,callee_inclusion_socket_schema,3,True,view_identity,view_identity)|}\<rparr>"

definition payload_audit_socket_record :: "(nat,nat,nat) resolution_declarations" where
  "payload_audit_socket_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(505,payload_audit_socket_schema,4,True,view_identity,view_identity)|}\<rparr>"

definition schema_family_socket_frames :: "(nat,nat,nat) resolution_frames" where
  "schema_family_socket_frames = {|(71,schema_family_socket_schema,1,{|4,5|})|}"

definition callee_inclusion_socket_frames :: "(nat,nat,nat) resolution_frames" where
  "callee_inclusion_socket_frames = {|(75,callee_inclusion_socket_schema,3,{|10,11|})|}"

definition payload_audit_socket_frames :: "(nat,nat,nat) resolution_frames" where
  "payload_audit_socket_frames = {|(505,payload_audit_socket_schema,4,{|9,10|})|}"

theorem schema_family_socket_record_discharged:
  "declarations_discharged (positive_meaning schema_family_admission_system) schema_family_socket_record
    (\<lambda>d i. given_correspondence d)"
  using schema_family_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def schema_family_socket_record_def view_identity_formed)

theorem callee_inclusion_socket_record_discharged:
  "declarations_discharged (positive_meaning definition_callee_inclusion_system) callee_inclusion_socket_record
    (\<lambda>d i. given_correspondence d)"
  using callee_inclusion_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def callee_inclusion_socket_record_def
    view_identity_formed)

theorem payload_audit_socket_record_discharged:
  "declarations_discharged (positive_meaning payload_audit_system) payload_audit_socket_record
    (\<lambda>d i. given_correspondence d)"
  using payload_audit_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def payload_audit_socket_record_def view_identity_formed)

theorem schema_family_socket_frames_discharged:
  "frames_discharged (positive_meaning schema_family_admission_system) schema_family_socket_record
    schema_family_socket_frames"
  using schema_family_socket_framed
  by (auto simp: frames_discharged_def schema_family_socket_record_def schema_family_socket_frames_def)

theorem callee_inclusion_socket_frames_discharged:
  "frames_discharged (positive_meaning definition_callee_inclusion_system) callee_inclusion_socket_record
    callee_inclusion_socket_frames"
  using callee_inclusion_socket_framed
  by (auto simp: frames_discharged_def callee_inclusion_socket_record_def callee_inclusion_socket_frames_def)

theorem payload_audit_socket_frames_discharged:
  "frames_discharged (positive_meaning payload_audit_system) payload_audit_socket_record payload_audit_socket_frames"
  using payload_audit_socket_framed
  by (auto simp: frames_discharged_def payload_audit_socket_record_def payload_audit_socket_frames_def)

end
