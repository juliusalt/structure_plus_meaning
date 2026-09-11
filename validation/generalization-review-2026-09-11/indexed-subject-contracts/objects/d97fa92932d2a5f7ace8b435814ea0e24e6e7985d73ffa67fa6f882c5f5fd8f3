theory Factor_Assembly_Presentations
  imports RRA_Assembly Factor_Table_Presentations Factor_Structural_Collections
begin

section \<open>Piece families retain their independent occurrence keys\<close>

abbreviation piece_family_domain :: "('s\<Rightarrow>bool) \<Rightarrow> 's exact_piece_family \<Rightarrow> bool" where
  "piece_family_domain D P \<equiv> piece_family_formed P \<and> (\<forall>s\<in>piece_slots P. D s)"

definition piece_family_presents ::
  "('s\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow> 's exact_piece_family \<Rightarrow> factor_term \<Rightarrow> bool" where
  "piece_family_presents K P t \<longleftrightarrow> data_table_presents K artifact_value_presents (piece_graph P) t"

lemma piece_graph_domain:
  "finite_table_domain D exact_formed (piece_graph P) \<longleftrightarrow> piece_family_domain D P"
  by (auto simp: piece_family_formed_def piece_slots_def rel_dom_def)

theorem piece_family_presentation_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (piece_family_presents K) (piece_family_domain D)
    (\<lambda>t. \<exists>P. piece_family_presents K P t)"
proof -
  have tables: "presentation_class (data_table_presents K artifact_value_presents)
      (finite_table_domain D exact_formed) (\<lambda>t. \<exists>Q. data_table_presents K artifact_value_presents Q t)"
    by (rule data_table_presentation_class[OF keys artifact_presentations.presentation_class_axioms])
  have observed: "presentation_class
      (\<lambda>P t. piece_family_domain D P \<and> data_table_presents K artifact_value_presents (piece_graph P) t)
      (piece_family_domain D)
      (\<lambda>t. \<exists>P. piece_family_domain D P \<and> data_table_presents K artifact_value_presents (piece_graph P) t)"
  proof (rule presentation_class_observations[OF tables])
    fix P assume "piece_family_domain D P"
    then show "finite_table_domain D exact_formed (piece_graph P)" by (simp only: piece_graph_domain; blast)
  next
    fix P Q assume "piece_family_domain D P" "piece_family_domain D Q" "piece_graph P=piece_graph Q"
    then show "P=Q" by (cases P; cases Q) auto
  qed
  have boundary: "piece_family_presents K P t \<Longrightarrow> piece_family_domain D P" for P t
    using presentation_class.subject_boundary[OF tables, of "piece_graph P" t]
    by (simp only: piece_family_presents_def piece_graph_domain; blast)
  have reading: "(piece_family_domain D P \<and> data_table_presents K artifact_value_presents (piece_graph P) t)
      \<longleftrightarrow> piece_family_presents K P t" for P t
    using boundary by (auto simp: piece_family_presents_def)
  show ?thesis using observed by (simp only: presentation_class_def reading)
qed

lemma piece_family_value_formed:
  assumes table: "piece_family_presents K P t"
    and keys: "\<And>s p. K s p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "term_formed t \<and> self_contained_term t"
proof (rule data_table_elements[OF table[unfolded piece_family_presents_def] keys])
  fix R p assume read: "artifact_value_presents R p"
  show "term_formed p \<and> self_contained_term p"
    using artifact_value_presents_formed[OF read] by blast
qed

section \<open>Origins are finite functions on copied occurrence addresses\<close>

abbreviation origin_table_presents ::
  "('s\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow>
    (('s\<times>local_address)\<times>local_address) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "origin_table_presents K \<equiv>
    data_table_presents (factor_pair_presents K payload_value_presents) payload_value_presents"

abbreviation origin_table_domain ::
  "('s\<Rightarrow>bool) \<Rightarrow> (('s\<times>local_address)\<times>local_address) set \<Rightarrow> bool" where
  "origin_table_domain D \<equiv> finite_table_domain (\<lambda>z. D (fst z) \<and> octets_formed (snd z)) octets_formed"

theorem origin_table_presentation_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (origin_table_presents K) (origin_table_domain D)
    (\<lambda>t. \<exists>q. origin_table_presents K q t)"
  by (rule data_table_presentation_class[OF factor_pair_class[OF keys payload_value_presentation_class]
    payload_value_presentation_class])

lemma origin_table_value_formed:
  assumes table: "origin_table_presents K q t"
    and keys: "\<And>s p. K s p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "term_formed t \<and> self_contained_term t"
  by (rule data_table_elements[OF table])
    (use keys in \<open>auto simp: factor_pair_presents_def\<close>)

section \<open>The full assembly boundary joins pieces and their actual origin map\<close>

abbreviation assembly_domain :: "('s\<Rightarrow>bool) \<Rightarrow> 's assembly_witness \<Rightarrow> bool" where
  "assembly_domain D W \<equiv> K2 W \<and> (\<forall>s\<in>piece_slots (assembly_pieces W). D s)"

lemma assembly_origin_domain:
  assumes formed: "assembly_domain D W"
  shows "origin_table_domain D (assembly_origin W)"
proof -
  have mapping: "exact_map (copied_carrier (assembly_pieces W))
      (rra_carrier (object_structure (assembly_output W))) (assembly_origin W)"
    and pieces: "piece_family_formed (assembly_pieces W)"
    and result: "exact_formed (assembly_output W)"
    using formed by (auto simp: K2_def)
  have coordinates: "D s \<and> octets_formed a \<and> octets_formed b"
    if "((s,a),b)\<in>assembly_origin W" for s a b
  proof -
    have source: "(s,a)\<in>copied_carrier (assembly_pieces W)"
      and target: "b\<in>rra_carrier (object_structure (assembly_output W))"
      using that mapping by (auto simp: exact_map_def rel_dom_def rel_ran_def)
    have slot: "s\<in>piece_slots (assembly_pieces W)"
      and atom: "a\<in>rra_carrier (object_structure (piece_at (assembly_pieces W) s))"
      using source by (auto simp: copied_carrier_def)
    have piece: "exact_formed (piece_at (assembly_pieces W) s)"
      by (rule piece_at_formed[OF pieces slot])
    show ?thesis using formed slot atom target piece result by (auto simp: exact_formed_def)
  qed
  show ?thesis using mapping coordinates by (auto simp: exact_map_def)
qed

definition assembly_value_presents ::
  "('s\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow> 's assembly_witness \<Rightarrow> factor_term \<Rightarrow> bool" where
  "assembly_value_presents K W t \<longleftrightarrow> K2 W \<and>
    factor_pair_presents (piece_family_presents K) (origin_table_presents K)
      (assembly_pieces W,assembly_origin W) t"

theorem assembly_value_presentation_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (assembly_value_presents K) (assembly_domain D)
    (\<lambda>t. \<exists>W. assembly_value_presents K W t)"
proof -
  have pieces: "presentation_class (piece_family_presents K) (piece_family_domain D)
      (\<lambda>t. \<exists>P. piece_family_presents K P t)"
    by (rule piece_family_presentation_class[OF keys])
  have origins: "presentation_class (origin_table_presents K) (origin_table_domain D)
      (\<lambda>t. \<exists>q. origin_table_presents K q t)"
    by (rule origin_table_presentation_class[OF keys])
  have pairs: "presentation_class (factor_pair_presents (piece_family_presents K) (origin_table_presents K))
      (\<lambda>z. piece_family_domain D (fst z) \<and> origin_table_domain D (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>P. piece_family_presents K P p) \<and>
        (\<exists>Q. origin_table_presents K Q q) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF pieces origins])
  have observed: "presentation_class
      (\<lambda>W t. assembly_domain D W \<and>
        factor_pair_presents (piece_family_presents K) (origin_table_presents K) (assembly_pieces W,assembly_origin W) t)
      (assembly_domain D)
      (\<lambda>t. \<exists>W. assembly_domain D W \<and>
        factor_pair_presents (piece_family_presents K) (origin_table_presents K) (assembly_pieces W,assembly_origin W) t)"
  proof (rule presentation_class_observations[OF pairs])
    fix W assume domain: "assembly_domain D W"
    show "piece_family_domain D (fst (assembly_pieces W,assembly_origin W)) \<and>
        origin_table_domain D (snd (assembly_pieces W,assembly_origin W))"
      using domain assembly_origin_domain[OF domain] by (simp add: K2_def)
  next
    fix W V assume "assembly_domain D W" "assembly_domain D V"
      "(assembly_pieces W,assembly_origin W)=(assembly_pieces V,assembly_origin V)"
    then show "W=V" by (cases W; cases V) auto
  qed
  have boundary: "assembly_value_presents K W t \<Longrightarrow> assembly_domain D W" for W t
    using presentation_class.subject_boundary[OF pieces]
    by (auto simp: assembly_value_presents_def factor_pair_presents_def)
  have reading: "(assembly_domain D W \<and>
      factor_pair_presents (piece_family_presents K) (origin_table_presents K) (assembly_pieces W,assembly_origin W) t)
      \<longleftrightarrow> assembly_value_presents K W t" for W t
    using boundary by (auto simp: assembly_value_presents_def)
  show ?thesis using observed by (simp only: presentation_class_def reading)
qed

lemma assembly_value_fields:
  "assembly_value_presents K W (Pair_Term p q) \<longleftrightarrow>
    K2 W \<and> piece_family_presents K (assembly_pieces W) p \<and> origin_table_presents K (assembly_origin W) q"
  by (simp add: assembly_value_presents_def)

lemma assembly_value_formed:
  assumes source: "assembly_value_presents K W t"
    and keys: "\<And>s p. K s p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where pieces: "piece_family_presents K (assembly_pieces W) p"
    and origins: "origin_table_presents K (assembly_origin W) q" and shape: "t=Pair_Term p q"
    using source by (auto simp: assembly_value_presents_def factor_pair_presents_def)
  have left: "term_formed p \<and> self_contained_term p"
    by (rule piece_family_value_formed[OF pieces keys])
  have right: "term_formed q \<and> self_contained_term q"
    by (rule origin_table_value_formed[OF origins keys])
  show ?thesis using left right by (simp only: shape term_formed.simps self_contained_term.simps)
qed

section \<open>The output is an intrinsic determined component\<close>

definition assembly_report_presents ::
  "('s\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow> 's assembly_witness \<Rightarrow> factor_term \<Rightarrow> bool" where
  "assembly_report_presents K W t \<longleftrightarrow>
    factor_pair_presents (assembly_value_presents K) artifact_value_presents (W,assembly_output W) t"

theorem assembly_report_presentation_class:
  assumes keys: "presentation_class K D A"
  shows "presentation_class (assembly_report_presents K) (assembly_domain D)
    (\<lambda>t. \<exists>W. assembly_report_presents K W t)"
proof -
  have sources: "presentation_class (assembly_value_presents K) (assembly_domain D)
      (\<lambda>t. \<exists>W. assembly_value_presents K W t)"
    by (rule assembly_value_presentation_class[OF keys])
  have pairs: "presentation_class (factor_pair_presents (assembly_value_presents K) artifact_value_presents)
      (\<lambda>z. assembly_domain D (fst z) \<and> exact_formed (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>W. assembly_value_presents K W p) \<and>
        (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF sources artifact_presentations.presentation_class_axioms])
  have observed: "presentation_class
      (\<lambda>W t. assembly_domain D W \<and>
        factor_pair_presents (assembly_value_presents K) artifact_value_presents (W,assembly_output W) t)
      (assembly_domain D)
      (\<lambda>t. \<exists>W. assembly_domain D W \<and>
        factor_pair_presents (assembly_value_presents K) artifact_value_presents (W,assembly_output W) t)"
    by (rule presentation_class_observations[OF pairs]) (auto simp: K2_def)
  have boundary: "assembly_report_presents K W t \<Longrightarrow> assembly_domain D W" for W t
    using presentation_class.subject_boundary[OF sources]
    by (auto simp: assembly_report_presents_def factor_pair_presents_def)
  have reading: "(assembly_domain D W \<and>
      factor_pair_presents (assembly_value_presents K) artifact_value_presents (W,assembly_output W) t)
      \<longleftrightarrow> assembly_report_presents K W t" for W t
    using boundary by (auto simp: assembly_report_presents_def)
  show ?thesis using observed by (simp only: presentation_class_def reading)
qed

lemma assembly_report_at_source:
  assumes source: "assembly_value_presents K W p"
  shows "assembly_report_presents K W (Pair_Term p q) \<longleftrightarrow>
    (\<exists>R. artifact_value_presents R q \<and> assembly_relation (assembly_pieces W) (assembly_origin W) R)"
  using source by (simp add: assembly_report_presents_def assembly_value_presents_def assembly_relation_iff)

lemma assembly_report_formed:
  assumes report: "assembly_report_presents K W t"
    and keys: "\<And>s p. K s p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where source: "assembly_value_presents K W p"
    and result_read: "artifact_value_presents (assembly_output W) q" and shape: "t=Pair_Term p q"
    using report by (auto simp: assembly_report_presents_def factor_pair_presents_def)
  have left: "term_formed p \<and> self_contained_term p" by (rule assembly_value_formed[OF source keys])
  have right: "term_formed q \<and> self_contained_term q"
    using artifact_value_presents_formed[OF result_read] by blast
  show ?thesis using left right by (simp only: shape term_formed.simps self_contained_term.simps)
qed

theorem assembly_report_quotation_class:
  assumes keys: "presentation_class K D A"
    and data: "\<And>s p. K s p \<Longrightarrow> term_formed p \<and> self_contained_term p"
  shows "presentation_class
    (composed_presentation (assembly_report_presents K) (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (assembly_domain D)
    (\<lambda>p. \<exists>t. (\<exists>W. assembly_report_presents K W t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
proof (rule complete_quotation_presentation_class[OF assembly_report_presentation_class[OF keys]])
  fix t assume "\<exists>W. assembly_report_presents K W t"
  then obtain W where report: "assembly_report_presents K W t" by blast
  show "term_formed t \<and> self_contained_term t" by (rule assembly_report_formed[OF report data])
qed

text \<open>
  The piece family remains a finite functional relation on arbitrary occurrence
  keys. A key class states its domain explicitly; taking the whole key domain
  covers every original piece family. Native byte keys are a later instance.
  Equal artifacts at different keys remain different piece occurrences.

  The assembly source stores only the existing pieces and origins. Its complete
  boundary is K2: every copied atom has one origin, every output atom has a
  source, incidence is transported, counted attachments are summed, and glued
  functional values agree. The report presents the determined output without
  adding it to the primitive witness. All component orders and admitted forms
  remain available. Complete quotation retains the actual whole report body.

  An admitted origin table alone need not cover a piece family or satisfy K2.
  The table readers and the full assembly relation have separate contracts.
  These mathematical classes add no native truth rule. The ordinary checking
  program in Factor_Assembly_Contracts implements their complete boundaries.
\<close>

end
