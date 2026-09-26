theory Factor_Row_Selection_Socket_Declarations
  imports Factor_Root_Family_Declarations Factor_Row_Value_Socket_Declarations Factor_Definition_Clause_Reading
    Factor_Definition_Slot_Reading Factor_Package_Slot_Reading
begin

text \<open>
  32's kept sockets carried by 5 (DECISIONS.md "The native evaluator constructs the missing witnesses by resolution",
  its addition "The given's remaining producers: views, carriers and narrowed sockets", its table's row 32, and
  correction (10) of "Committed choice, for refusals"): at 81.0/3, 104.1/3, 105.1/2 and 119.0/1 the rows 32 returns
  are given to 5, which selects one row the clause fixes and returns the remainder, which no other goal holds. Each
  socket is kept, the head read at the identity view, as 83.0/1 is (@{thm [source] membership_socket_carried}); 32 is
  the producer at R6's identity view, its rows a bag (@{thm [source] family_rows_producer_at}) and 5 the carrier at
  @{const selection_view} (@{thm [source] selection_carrier}), each carried to the clause's system by its components,
  never proved again. Each socket is framed at its carried set, the set @{const carried_variables} computes from the
  clause, and declared with its frame at its notion's system. No clause of any program changes.
\<close>

section \<open>32's rows as a bag of terms, and 5 at a system\<close>

text \<open>
  32 answers a bag of rows at the clause's system (@{thm [source] family_rows_producer_at}), a bag of terms as 5's
  input reads it (@{thm [source] row_bag_transport_permuted}).
\<close>

lemma selection_carrier_at:
  assumes "\<And>t. (5,t) \<in> (M :: (nat \<times> factor_term) set) \<longleftrightarrow> (5,t) \<in> positive_meaning bag_comparison_system"
  shows "carrier_discharged M 5 selection_view selection_input term_bag_transport"
  using selection_carrier by (simp only: carrier_discharged_site[OF assms])

text \<open>The one carrier of each socket: 5 at the clause's key k, reading the selected row and 32's rows.\<close>

definition selection_carriers :: "nat \<Rightarrow> nat clause_carrier list" where
  "selection_carriers k = [(k,selection_view,selection_input,term_bag_transport)]"

lemmas row_selection_listed_simps = root_family_listed_simps selection_carriers_def selection_input_def
  row_bag_transport_permuted

section \<open>81.0/3: the definition clause reading\<close>

definition clause_reading_row_schema :: "(nat,nat,nat) finite_factor_schema" where
  "clause_reading_row_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    finite_schema_premises = {|(0,72,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 5))),
      (1,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 6))),
      (2,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 9))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 10)) (Finite_Pattern_Payload [])))),
      (3,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 10)) (Finite_Variable 11)),
      (4,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 12)))|},
    finite_schema_materials = {||}\<rparr>"

lemma clause_reading_row_decoded: "decode_finite_schema clause_reading_row_schema = definition_clause_reading_schema"
  by (simp add: clause_reading_row_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def definition_clause_reading_schema_def)

theorem clause_reading_row_carried:
  "socket_carried (positive_meaning definition_clause_reading_system) clause_reading_row_schema 3 True view_identity
    view_identity row_bag_transport (selection_carriers 4)"
  by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed
      family_rows_producer_at[OF definition_clause_reading_components(4)], where \<sigma> = "\<lambda>_. 1"])
    (simp add: row_selection_listed_simps clause_reading_row_schema_def
      selection_carrier_at[OF definition_clause_reading_components(5)])

lemma clause_reading_row_framed:
  "socket_framed (positive_meaning definition_clause_reading_system) clause_reading_row_schema 3 True view_identity
    view_identity {11,12}"
  by (rule socket_framed_at_carried[OF clause_reading_row_carried])
    (auto simp: row_selection_listed_simps clause_reading_row_schema_def)

theorem clause_reading_row_discharged:
  "socket_discharged (positive_meaning definition_clause_reading_system) clause_reading_row_schema 3 True
    view_identity view_identity"
  by (rule socket_framed_discharged[OF clause_reading_row_framed])

section \<open>104.1/3: the schema slot reading, its premise-slot clause\<close>

definition premise_slot_row_schema :: "(nat,nat,nat) finite_factor_schema" where
  "premise_slot_row_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 10))),
      (1,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 7))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 8))
            (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 9)) (Finite_Pattern_Payload []))))),
      (2,54,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 7)) (Finite_Variable 11)),
      (3,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 9)) (Finite_Variable 12)),
      (4,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 13) (Finite_Variable 14))
        (Finite_Pattern_Pair (Finite_Variable 12) (Finite_Variable 15))),
      (5,103,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 14) (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 3))))|},
    finite_schema_materials = {||}\<rparr>"

lemma premise_slot_row_decoded: "decode_finite_schema premise_slot_row_schema = schema_premise_slot_schema"
  by (simp add: premise_slot_row_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def schema_premise_slot_schema_def)

theorem premise_slot_row_carried:
  "socket_carried (positive_meaning schema_slot_reading_system) premise_slot_row_schema 3 True view_identity
    view_identity row_bag_transport (selection_carriers 4)"
  by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed
      family_rows_producer_at[OF schema_slot_reading_components(5)], where \<sigma> = "\<lambda>_. 1"])
    (simp add: row_selection_listed_simps premise_slot_row_schema_def
      selection_carrier_at[OF schema_slot_reading_components(6)])

lemma premise_slot_row_framed:
  "socket_framed (positive_meaning schema_slot_reading_system) premise_slot_row_schema 3 True view_identity
    view_identity {12,15}"
  by (rule socket_framed_at_carried[OF premise_slot_row_carried])
    (auto simp: row_selection_listed_simps premise_slot_row_schema_def)

theorem premise_slot_row_discharged:
  "socket_discharged (positive_meaning schema_slot_reading_system) premise_slot_row_schema 3 True
    view_identity view_identity"
  by (rule socket_framed_discharged[OF premise_slot_row_framed])

section \<open>105.1/2: the definition slot reading, its schema-slot clause\<close>

definition schema_slot_row_schema :: "(nat,nat,nat) finite_factor_schema" where
  "schema_slot_row_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 8))),
      (1,34,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 2))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 6))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 7)) (Finite_Pattern_Payload [])))),
      (2,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 7)) (Finite_Variable 9)),
      (3,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 11))
        (Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 12))),
      (4,104,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 11) (Finite_Variable 3)))|},
    finite_schema_materials = {||}\<rparr>"

lemma schema_slot_row_decoded: "decode_finite_schema schema_slot_row_schema = definition_schema_slot_schema"
  by (simp add: schema_slot_row_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def definition_schema_slot_schema_def)

theorem schema_slot_row_carried:
  "socket_carried (positive_meaning definition_slot_reading_system) schema_slot_row_schema 2 True view_identity
    view_identity row_bag_transport (selection_carriers 3)"
  by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed
      family_rows_producer_at[OF definition_slot_reading_components(3)], where \<sigma> = "\<lambda>_. 1"])
    (simp add: row_selection_listed_simps schema_slot_row_schema_def
      selection_carrier_at[OF definition_slot_reading_components(4)])

lemma schema_slot_row_framed:
  "socket_framed (positive_meaning definition_slot_reading_system) schema_slot_row_schema 2 True view_identity
    view_identity {9,12}"
  by (rule socket_framed_at_carried[OF schema_slot_row_carried])
    (auto simp: row_selection_listed_simps schema_slot_row_schema_def)

theorem schema_slot_row_discharged:
  "socket_discharged (positive_meaning definition_slot_reading_system) schema_slot_row_schema 2 True
    view_identity view_identity"
  by (rule socket_framed_discharged[OF schema_slot_row_framed])

section \<open>119.0/1: the package slot reading, its root-slot clause\<close>

definition root_slot_row_schema :: "(nat,nat,nat) finite_factor_schema" where
  "root_slot_row_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)))
      (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 4))),
      (1,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2)) (Finite_Variable 5)),
      (2,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 7))
        (Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 8))),
      (3,42,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 7)
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 10)) (Finite_Variable 11)))),
      (4,5,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 12)))|},
    finite_schema_materials = {||}\<rparr>"

lemma root_slot_row_decoded: "decode_finite_schema root_slot_row_schema = package_root_slot_schema"
  by (simp add: root_slot_row_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def package_root_slot_schema_def)

theorem root_slot_row_carried:
  "socket_carried (positive_meaning package_slot_reading_system) root_slot_row_schema 1 True view_identity
    view_identity row_bag_transport (selection_carriers 2)"
  by (rule socket_carried_listed[OF meaning_answers_formed view_identity_formed
      family_rows_producer_at[OF package_slot_reading_components(2)], where \<sigma> = "\<lambda>_. 1"])
    (simp add: row_selection_listed_simps root_slot_row_schema_def
      selection_carrier_at[OF package_slot_reading_components(3)])

lemma root_slot_row_framed:
  "socket_framed (positive_meaning package_slot_reading_system) root_slot_row_schema 1 True view_identity
    view_identity {5,8}"
  by (rule socket_framed_at_carried[OF root_slot_row_carried])
    (auto simp: row_selection_listed_simps root_slot_row_schema_def)

theorem root_slot_row_discharged:
  "socket_discharged (positive_meaning package_slot_reading_system) root_slot_row_schema 1 True
    view_identity view_identity"
  by (rule socket_framed_discharged[OF root_slot_row_framed])

section \<open>The records and their frames, each at the system where its clause stands\<close>

text \<open>
  Each record declares its socket kept, 32 read at the identity view and the head at the identity view; its frame is
  the carried set: 32's rows and 5's remainder. The records hold no producer and no consumer, so their correspondence
  is the given's (@{const given_correspondence}).
\<close>

definition clause_reading_row_record :: "(nat,nat,nat) resolution_declarations" where
  "clause_reading_row_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(81,clause_reading_row_schema,3,True,view_identity,view_identity)|}\<rparr>"

definition clause_reading_row_frames :: "(nat,nat,nat) resolution_frames" where
  "clause_reading_row_frames = {|(81,clause_reading_row_schema,3,{|11,12|})|}"

definition premise_slot_row_record :: "(nat,nat,nat) resolution_declarations" where
  "premise_slot_row_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(104,premise_slot_row_schema,3,True,view_identity,view_identity)|}\<rparr>"

definition premise_slot_row_frames :: "(nat,nat,nat) resolution_frames" where
  "premise_slot_row_frames = {|(104,premise_slot_row_schema,3,{|12,15|})|}"

definition schema_slot_row_record :: "(nat,nat,nat) resolution_declarations" where
  "schema_slot_row_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(105,schema_slot_row_schema,2,True,view_identity,view_identity)|}\<rparr>"

definition schema_slot_row_frames :: "(nat,nat,nat) resolution_frames" where
  "schema_slot_row_frames = {|(105,schema_slot_row_schema,2,{|9,12|})|}"

definition root_slot_row_record :: "(nat,nat,nat) resolution_declarations" where
  "root_slot_row_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(119,root_slot_row_schema,1,True,view_identity,view_identity)|}\<rparr>"

definition root_slot_row_frames :: "(nat,nat,nat) resolution_frames" where
  "root_slot_row_frames = {|(119,root_slot_row_schema,1,{|5,8|})|}"

theorem clause_reading_row_record_discharged:
  "declarations_discharged (positive_meaning definition_clause_reading_system) clause_reading_row_record
    (\<lambda>d i. given_correspondence d)"
  using clause_reading_row_discharged
  by (simp add: declarations_discharged_def declarations_formed_def clause_reading_row_record_def view_identity_formed)

theorem clause_reading_row_frames_discharged:
  "frames_discharged (positive_meaning definition_clause_reading_system) clause_reading_row_record
    clause_reading_row_frames"
  using clause_reading_row_framed
  by (auto simp: frames_discharged_def clause_reading_row_record_def clause_reading_row_frames_def)

theorem premise_slot_row_record_discharged:
  "declarations_discharged (positive_meaning schema_slot_reading_system) premise_slot_row_record
    (\<lambda>d i. given_correspondence d)"
  using premise_slot_row_discharged
  by (simp add: declarations_discharged_def declarations_formed_def premise_slot_row_record_def view_identity_formed)

theorem premise_slot_row_frames_discharged:
  "frames_discharged (positive_meaning schema_slot_reading_system) premise_slot_row_record premise_slot_row_frames"
  using premise_slot_row_framed
  by (auto simp: frames_discharged_def premise_slot_row_record_def premise_slot_row_frames_def)

theorem schema_slot_row_record_discharged:
  "declarations_discharged (positive_meaning definition_slot_reading_system) schema_slot_row_record
    (\<lambda>d i. given_correspondence d)"
  using schema_slot_row_discharged
  by (simp add: declarations_discharged_def declarations_formed_def schema_slot_row_record_def view_identity_formed)

theorem schema_slot_row_frames_discharged:
  "frames_discharged (positive_meaning definition_slot_reading_system) schema_slot_row_record schema_slot_row_frames"
  using schema_slot_row_framed
  by (auto simp: frames_discharged_def schema_slot_row_record_def schema_slot_row_frames_def)

theorem root_slot_row_record_discharged:
  "declarations_discharged (positive_meaning package_slot_reading_system) root_slot_row_record
    (\<lambda>d i. given_correspondence d)"
  using root_slot_row_discharged
  by (simp add: declarations_discharged_def declarations_formed_def root_slot_row_record_def view_identity_formed)

theorem root_slot_row_frames_discharged:
  "frames_discharged (positive_meaning package_slot_reading_system) root_slot_row_record root_slot_row_frames"
  using root_slot_row_framed
  by (auto simp: frames_discharged_def root_slot_row_record_def root_slot_row_frames_def)

end
