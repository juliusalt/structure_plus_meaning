theory Factor_Structural_Table_Contracts
  imports Factor_Structural_Table_Admission Factor_Compiled_Applications
begin

section \<open>Admission preserves every complete presentation\<close>

lemma piece_table_presentations_admitted:
  assumes "piece_family_presents payload_value_presents P p"
  shows "(213,p)\<in>positive_meaning structural_table_system"
  by (rule native_piece_families.presentation_boundary[OF assms])

lemma origin_table_presentations_admitted:
  assumes "origin_table_presents payload_value_presents q p"
  shows "(216,p)\<in>positive_meaning structural_table_system"
  by (rule native_origin_tables.presentation_boundary[OF assms])

theorem piece_table_native_total:
  assumes "piece_family_domain octets_formed P"
  shows "\<exists>p. piece_family_presents payload_value_presents P p \<and>
    (213,p)\<in>positive_meaning structural_table_system \<and> complete_data_quoted_at (term_syntax p) [] p"
proof -
  obtain p where read: "piece_family_presents payload_value_presents P p"
    using native_piece_families.total[OF assms] by blast
  have data: "term_formed p" "self_contained_term p"
    using piece_family_value_formed[OF read] by auto
  show ?thesis using read piece_table_presentations_admitted[OF read] complete_data_quotation_total[OF data] by blast
qed

theorem origin_table_native_total:
  assumes "origin_table_domain octets_formed q"
  shows "\<exists>p. origin_table_presents payload_value_presents q p \<and>
    (216,p)\<in>positive_meaning structural_table_system \<and> complete_data_quoted_at (term_syntax p) [] p"
proof -
  obtain p where read: "origin_table_presents payload_value_presents q p"
    using native_origin_tables.total[OF assms] by blast
  have data: "term_formed p" "self_contained_term p"
    using origin_table_value_formed[OF read] by auto
  show ?thesis using read origin_table_presentations_admitted[OF read] complete_data_quotation_total[OF data] by blast
qed

section \<open>Row identity does not identify its value\<close>

theorem equal_pieces_at_distinct_slots:
  assumes slots: "octets_formed s" "octets_formed t" "s\<noteq>t"
    and value_readings: "artifact_value_presents R p" "artifact_value_presents R q"
  shows "(213,data_list_term [Pair_Term (Payload_Term s) p,Pair_Term (Payload_Term t) q])
    \<in>positive_meaning structural_table_system"
proof -
  let ?P="\<lparr>piece_graph={(s,R),(t,R)}\<rparr>"
  have reading: "piece_family_presents payload_value_presents ?P
      (data_list_term [Pair_Term (Payload_Term s) p,Pair_Term (Payload_Term t) q])"
    unfolding piece_family_presents_def data_table_at_list
    by (rule exI[of _ "[(s,R),(t,R)]"])
      (use slots value_readings in \<open>auto simp: single_valued_def\<close>)
  show ?thesis by (rule piece_table_presentations_admitted[OF reading])
qed

theorem repeated_table_key_rejected:
  assumes "d\<in>{213,216}"
  shows "(d,data_list_term [Pair_Term k p,Pair_Term k q])\<notin>positive_meaning structural_table_system"
proof -
  have rejected: "(21,pair_list_term [(k,p),(k,q)])\<notin>positive_meaning keyed_list_system"
    by (simp only: keyed_list_exact pair_list_term_injective) simp
  show ?thesis using assms rejected
    by (auto simp: structural_piece_tables.exact structural_origin_tables.exact structural_table_components(3))
qed

theorem distinct_origins_may_share_a_destination:
  assumes addresses: "octets_formed s" "octets_formed a" "octets_formed t" "octets_formed b" "octets_formed c"
    and different: "(s,a)\<noteq>(t,b)"
  shows "(216,data_list_term [Pair_Term (address_pair_data (s,a)) (Payload_Term c),
    Pair_Term (address_pair_data (t,b)) (Payload_Term c)])\<in>positive_meaning structural_table_system"
proof -
  let ?q="{((s,a),c),((t,b),c)}"
  have reading: "origin_table_presents payload_value_presents ?q
      (data_list_term [Pair_Term (address_pair_data (s,a)) (Payload_Term c),
        Pair_Term (address_pair_data (t,b)) (Payload_Term c)])"
    unfolding data_table_at_list
    by (rule exI[of _ "[((s,a),c),((t,b),c)]"])
      (use addresses different in \<open>auto simp: address_pair_data_def single_valued_def\<close>)
  show ?thesis by (rule origin_table_presentations_admitted[OF reading])
qed

lemma empty_structural_tables_admitted:
  "(213,data_list_term [])\<in>positive_meaning structural_table_system"
  "(216,data_list_term [])\<in>positive_meaning structural_table_system"
proof -
  have pieces: "piece_family_presents payload_value_presents \<lparr>piece_graph={}\<rparr> (data_list_term [])"
    by (simp add: piece_family_presents_def data_table_empty)
  show "(213,data_list_term [])\<in>positive_meaning structural_table_system"
    by (rule piece_table_presentations_admitted[OF pieces])
  have origins: "origin_table_presents payload_value_presents {} (data_list_term [])" by (simp add: data_table_empty)
  show "(216,data_list_term [])\<in>positive_meaning structural_table_system"
    by (rule origin_table_presentations_admitted[OF origins])
qed

lemma empty_origins_do_not_cover_nonempty_pieces:
  assumes "copied_carrier P\<noteq>{}"
  shows "(216,data_list_term [])\<in>positive_meaning structural_table_system \<and>
    \<not>K2 \<lparr>assembly_pieces=P,assembly_origin={}\<rparr>"
  using assms empty_structural_tables_admitted(2)
  by (auto simp: K2_iff_complete_compatible_origins exact_map_def rel_dom_def)

section \<open>Every formed assembly has compatible admitted component tables\<close>

theorem assembly_complete_table_witnesses:
  assumes domain: "assembly_domain octets_formed W"
  shows "\<exists>p q. assembly_value_presents payload_value_presents W (Pair_Term p q) \<and>
    (213,p)\<in>positive_meaning structural_table_system \<and>
    (216,q)\<in>positive_meaning structural_table_system \<and>
    (\<forall>r. artifact_value_presents (assembly_output W) r \<longrightarrow>
      assembly_report_presents payload_value_presents W (Pair_Term (Pair_Term p q) r) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term (Pair_Term p q) r)) [] (Pair_Term (Pair_Term p q) r))"
proof -
  obtain t where source: "assembly_value_presents payload_value_presents W t"
    using presentation_class.total[OF assembly_value_presentation_class[OF payload_value_presentation_class] domain] by blast
  obtain p q where shape: "t=Pair_Term p q"
    and pieces: "piece_family_presents payload_value_presents (assembly_pieces W) p"
    and origins: "origin_table_presents payload_value_presents (assembly_origin W) q"
    using source by (auto simp: assembly_value_presents_def factor_pair_presents_def)
  have reports: "assembly_report_presents payload_value_presents W (Pair_Term (Pair_Term p q) r) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term (Pair_Term p q) r)) [] (Pair_Term (Pair_Term p q) r)"
    if result_read: "artifact_value_presents (assembly_output W) r" for r
  proof -
    have report: "assembly_report_presents payload_value_presents W (Pair_Term (Pair_Term p q) r)"
      using source result_read by (simp add: shape assembly_report_presents_def)
    have data: "term_formed (Pair_Term (Pair_Term p q) r)" "self_contained_term (Pair_Term (Pair_Term p q) r)"
      using assembly_report_formed[OF report] by auto
    show ?thesis using report complete_data_quotation_total[OF data] by blast
  qed
  show ?thesis using source shape piece_table_presentations_admitted[OF pieces]
    origin_table_presentations_admitted[OF origins] reports by blast
qed

section \<open>One fixed program supplies both table admissions\<close>

abbreviation structural_table_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "structural_table_result d t \<equiv> if d=213 then (\<exists>P. piece_family_presents payload_value_presents P t)
    else (\<exists>q. origin_table_presents payload_value_presents q t)"

lemma structural_table_operations_exact:
  assumes "d\<in>{213,216}"
  shows "(d,t)\<in>positive_meaning structural_table_system \<longleftrightarrow> structural_table_result d t"
  using assms by (auto simp: structural_piece_table_exact structural_origin_table_exact)

theorem native_structural_table_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {213::nat,216} \<and>
    (\<forall>d\<in>{213,216}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> structural_table_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{213,216}\<subseteq>system_definitions structural_table_system" by auto
  have calls: "schema_call_formed structural_table_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{213,216}" for d t using structural_table_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF structural_table_system_formed selected calls structural_table_operations_exact])
qed

text \<open>
  The two public entries are fixed before all future operands. They admit every
  complete piece or origin table and preserve the original program's complete
  scope, artifacts, and bindings. Equal piece values and shared destinations
  are admitted; duplicate source keys are rejected. Empty tables are admitted,
  while an empty origin table cannot cover a nonempty copied carrier.

  Every formed assembly has admitted component tables and every compatible
  complete report quotation. This supplies the table contracts needed for
  native gluing in Factor_Assembly_Contracts, which supplies complete K2
  admission and attachment transport. Construction permission and its global
  invariance remain separate obligations.
\<close>

end
