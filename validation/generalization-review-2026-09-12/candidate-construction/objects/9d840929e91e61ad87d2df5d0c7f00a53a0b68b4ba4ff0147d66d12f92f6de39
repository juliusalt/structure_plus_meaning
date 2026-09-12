theory Factor_Assembly_Admission
  imports Factor_Assembly_Folds Factor_Data_Set_Comparison_Contracts
begin

section \<open>The complete native report specializes the finite assembly criterion\<close>

theorem assembly_report_at_enumerations:
  assumes enumeration: "piece_family_enumeration P ss A E B F"
    and slots: "\<forall>s\<in>set ss. octets_formed s"
    and origin: "origin_table_presents payload_value_presents q p"
    and target: "artifact_enumeration R A' E' B' F'"
  shows "(230,Pair_Term (Pair_Term
      (pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)) p)
      (artifact_data_term A' E' B' F'))\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    assembly_relation P q R"
proof -
  interpret pieces: enumerated_piece_family P ss A E B F
    by (rule enumerated_piece_family.intro[OF enumeration])
  let ?pt="pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)"
  let ?parts="data_list_term (map (\<lambda>s. assembly_contribution_term q s (A s) (E s) (B s) (F s)) ss)"
  let ?ca="tagged_atom_list ss A"
  let ?ce="map (\<lambda>(r,p,x). (rel_value q r,rel_value q p,rel_value q x)) (tagged_incidence_list ss E)"
  let ?cb="pushed_attachment_list (rel_value q) (tagged_attachment_list ss B)"
  let ?cf="pushed_attachment_list (rel_value q) (tagged_attachment_list ss F)"
  let ?fields="artifact_list_fields (map address_pair_data ?ca) (map incidence_data ?ce)
      (map address_pair_data ?cb) (map address_pair_data ?cf)"
  let ?used="\<forall>s\<in>set ss.
      (\<forall>z\<in>set (E s). (s,fst z)\<in>rel_dom q \<and> (s,fst (snd z))\<in>rel_dom q \<and> (s,snd (snd z))\<in>rel_dom q) \<and>
      (\<forall>z\<in>set (B s)\<union>set (F s). (s,fst z)\<in>rel_dom q)"
  have piece_reading: "piece_family_presents payload_value_presents P ?pt"
    unfolding piece_table_enumerations
    by (rule exI[of _ ss], rule exI[of _ A], rule exI[of _ E], rule exI[of _ B], rule exI[of _ F])
      (use enumeration slots in simp)
  have result_reading: "artifact_value_presents R (artifact_data_term A' E' B' F')"
    unfolding artifact_value_presents_def
    by (rule exI[of _ A'], rule exI[of _ E'], rule exI[of _ B'], rule exI[of _ F'])
      (use target in simp)
  have admissions: "(213,?pt)\<in>positive_meaning assembly_checking_system"
    "(216,p)\<in>positive_meaning assembly_checking_system"
    "(11,artifact_data_term A' E' B' F')\<in>positive_meaning assembly_checking_system"
    using piece_reading origin result_reading
    by (auto simp only: assembly_piece_table_meaning assembly_origin_table_meaning assembly_artifact_meaning)
  obtain ks where table: "distinct ks" "set ks=rel_dom q" "single_valued q"
    "\<forall>k\<in>set ks. octets_formed (fst k) \<and> octets_formed (snd k) \<and> octets_formed (rel_value q k)"
    "p=pair_list_term (map (\<lambda>k. (address_pair_data k,Payload_Term (rel_value q k))) ks)"
    using origin by (simp only: origin_table_enumerations; blast)
  have finite: "finite q" using native_origin_tables.subject_boundary[OF origin] by auto
  have key_data: "data_elements (map address_pair_data ks)"
    and value_data: "data_elements (map Payload_Term (map (rel_value q) ks))"
    using table(4) by (auto simp: address_pair_data_def)
  have row_data: "term_formed (address_pair_data k) \<and> term_formed (Payload_Term (rel_value q k))"
    if "k\<in>set ks" for k
    using table(4) that by (simp add: address_pair_data_def)
  have keys: "(51,Pair_Term p u)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      u=data_list_term (map address_pair_data ks)" for u
    using indexed_row_projections(1)[where p=u and ks=ks, OF row_data]
    by (simp only: assembly_keys_meaning table(5))
  have vals: "(59,Pair_Term p u)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
      u=data_list_term (map Payload_Term (map (rel_value q) ks))" for u
    using indexed_row_projections(2)[where p=u and ks=ks, OF row_data]
    by (simp add: assembly_values_meaning table(5) map_map comp_def)
  have range: "set (map (rel_value q) ks)=rel_ran q"
    using arg_cong[OF single_valued_graph[OF table(3)], of rel_ran]
    by (simp add: graph_map_ran table(2))
  have result_data: "data_elements (map Payload_Term A')" "data_elements (map incidence_data E')"
    "data_elements (map address_pair_data B')" "data_elements (map address_pair_data F')"
    using artifact_data_term_formed[OF target]
    by (auto simp: artifact_data_term_def data_list_term_formed incidence_data_def address_pair_data_def)
  have payload_injective: "inj Payload_Term" by (rule injI) simp
  have criterion: "assembly_relation P q R \<longleftrightarrow>
      rel_dom q=set ?ca \<and> rel_ran q=set A' \<and> set E'=set ?ce \<and>
      count_list B'=count_list ?cb \<and> set F'=set ?cf"
    by (rule pieces.assembly_relation_at_enumeration[OF finite table(3) target])
  have enough: "?used" if "assembly_relation P q R"
    by (rule assembly_piece_coverage_suffices[OF enumeration])
      (use that criterion in blast)
  show ?thesis
  proof (cases "?used")
    case True
    have mapped: "(227,context_relation_argument p ?pt ?parts)\<in>positive_meaning assembly_checking_system"
      using True by (simp only: assembly_piece_list_at[OF origin enumeration slots]; blast)
    have folded: "(229,collection_join_argument (artifact_list_fields [] [] [] []) ?parts u)
        \<in>positive_meaning assembly_checking_system \<longleftrightarrow> u=?fields" for u
      by (rule assembly_piece_list_fold[OF origin enumeration slots mapped])
    have fold_result: "(229,collection_join_argument (artifact_list_fields [] [] [] []) ?parts ?fields)
        \<in>positive_meaning assembly_checking_system" by (simp only: folded)
    have fields_formed: "term_formed ?fields"
      using schema_call_formed_target[OF positive_meaning_formed[OF fold_result]] by simp
    have contribution_data: "data_elements (map address_pair_data ?ca)" "data_elements (map incidence_data ?ce)"
      "data_elements (map address_pair_data ?cb)" "data_elements (map address_pair_data ?cf)"
      using fields_formed by (auto simp: data_list_term_formed incidence_data_def address_pair_data_def)
    have mapped_at: "(227,context_relation_argument p ?pt u)\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> u=?parts" for u
      using True by (simp only: assembly_piece_list_at[OF origin enumeration slots]; blast)
    have carrier_check: "(219,Pair_Term (data_list_term (map address_pair_data ks))
        (data_list_term (map address_pair_data ?ca)))\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> rel_dom q=set ?ca"
      using key_data contribution_data(1)
      by (simp only: assembly_set_meaning data_set_comparison_mapped[OF address_pair_data_injective] table(2); blast)
    have range_check: "(219,Pair_Term (data_list_term (map Payload_Term (map (rel_value q) ks)))
        (data_list_term (map Payload_Term A')))\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> rel_ran q=set A'"
      using value_data result_data(1)
      by (simp only: assembly_set_meaning data_set_comparison_mapped[OF payload_injective] range; blast)
    have edges_check: "(219,Pair_Term (data_list_term (map incidence_data ?ce))
        (data_list_term (map incidence_data E')))\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> set E'=set ?ce"
      using contribution_data(2) result_data(2)
      by (simp only: assembly_set_meaning data_set_comparison_mapped[OF incidence_data_injective]; blast)
    have multiset_counts: "mset xs=mset ys \<longleftrightarrow> count_list xs=count_list ys"
      for xs ys :: "(local_address\<times>octets) list"
      by (simp only: multiset_eq_iff count_mset fun_eq_iff)
    have counts_check: "(6,Pair_Term (data_list_term (map address_pair_data ?cb))
        (data_list_term (map address_pair_data B')))\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> count_list B'=count_list ?cb"
    proof -
      have compared: "(6,Pair_Term (data_list_term (map address_pair_data ?cb))
          (data_list_term (map address_pair_data B')))\<in>positive_meaning assembly_checking_system
          \<longleftrightarrow> mset (map address_pair_data ?cb)=mset (map address_pair_data B')"
        using contribution_data(3) result_data(3)
        by (simp only: assembly_bag_meaning[of 6, simplified] bag_comparison_lists; blast)
      have encoded: "mset (map address_pair_data ?cb)=mset (map address_pair_data B')
          \<longleftrightarrow> mset ?cb=mset B'"
        by (rule injective_mapped_multisets[OF address_pair_data_injective])
      show ?thesis
        by (rule HOL.trans[OF compared], rule HOL.trans[OF encoded],
          rule HOL.trans[OF multiset_counts]) (rule eq_commute)
    qed
    have bindings_check: "(219,Pair_Term (data_list_term (map address_pair_data ?cf))
        (data_list_term (map address_pair_data F')))\<in>positive_meaning assembly_checking_system
        \<longleftrightarrow> set F'=set ?cf"
      using contribution_data(4) result_data(4)
      by (simp only: assembly_set_meaning data_set_comparison_mapped[OF address_pair_data_injective]; blast)
    note steps = admissions(1,2) admissions(3)[unfolded artifact_data_term_def]
      keys vals mapped_at folded[simplified data_list_term.simps]
      carrier_check range_check edges_check counts_check bindings_check
    show ?thesis
      apply (auto simp only: artifact_data_term_def[of A' E' B' F'] assembly_report_calls
        factor_term.inject steps criterion simp_thms)
      apply (rule exI[of _ "?pt"])
      apply (rule exI[of _ "p"])
      apply (rule exI[of _ "data_list_term (map Payload_Term A')"])
      apply (rule exI[of _ "data_list_term (map incidence_data E')"])
      apply (rule exI[of _ "data_list_term (map address_pair_data B')"])
      apply (rule exI[of _ "data_list_term (map address_pair_data F')"])
      apply (rule exI[of _ "?parts"])
      apply (rule exI[of _ "data_list_term (map address_pair_data ?ca)"])
      apply (rule exI[of _ "data_list_term (map incidence_data ?ce)"])
      apply (rule exI[of _ "data_list_term (map address_pair_data ?cb)"])
      apply (rule exI[of _ "data_list_term (map address_pair_data ?cf)"])
      apply (rule exI[of _ "data_list_term (map address_pair_data ks)"])
      apply (rule exI[of _ "data_list_term (map Payload_Term (map (rel_value q) ks))"])
      apply (simp only: steps factor_term.inject simp_thms)
      done
  next
    case False
    have rejected: "\<not>assembly_relation P q R" using False enough by blast
    have impossible: "(227,context_relation_argument p ?pt u)\<notin>positive_meaning assembly_checking_system" for u
      using False by (simp only: assembly_piece_list_at[OF origin enumeration slots]; blast)
    show ?thesis
      by (auto simp only: artifact_data_term_def[of A' E' B' F'] assembly_report_calls
        factor_term.inject impossible rejected simp_thms)
  qed
qed

theorem assembly_report_at_presentations:
  assumes pieces: "piece_family_presents payload_value_presents P p"
    and origins: "origin_table_presents payload_value_presents q t"
    and result_reading: "artifact_value_presents R r"
  shows "(230,Pair_Term (Pair_Term p t) r)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    assembly_relation P q R"
proof -
  obtain ss A E B F where source: "piece_family_enumeration P ss A E B F"
    "\<forall>s\<in>set ss. octets_formed s"
    "p=pair_list_term (map (\<lambda>s. (Payload_Term s,artifact_data_term (A s) (E s) (B s) (F s))) ss)"
    using pieces by (simp only: piece_table_enumerations; blast)
  obtain A' E' B' F' where target: "artifact_enumeration R A' E' B' F'"
    "r=artifact_data_term A' E' B' F'"
    using result_reading by (auto simp: artifact_value_presents_def)
  show ?thesis using assembly_report_at_enumerations[OF source(1,2) origins target(1)]
    by (simp only: source(3) target(2))
qed

section \<open>Admission is exact on every raw term\<close>

theorem assembly_report_exact:
  "(230,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>W. assembly_report_presents payload_value_presents W t)"
proof
  assume checked: "(230,t)\<in>positive_meaning assembly_checking_system"
  obtain p q a e b f where shape: "t=Pair_Term (Pair_Term p q) (artifact_fields_term a e b f)"
    and pieces: "(213,p)\<in>positive_meaning assembly_checking_system"
    and origins: "(216,q)\<in>positive_meaning assembly_checking_system"
    and result: "(11,artifact_fields_term a e b f)\<in>positive_meaning assembly_checking_system"
    using checked by (simp only: assembly_report_calls; blast)
  obtain P Q R where source: "piece_family_presents payload_value_presents P p"
    "origin_table_presents payload_value_presents Q q"
    "artifact_value_presents R (artifact_fields_term a e b f)"
    using pieces origins result
    by (simp only: assembly_piece_table_meaning assembly_origin_table_meaning assembly_artifact_meaning; blast)
  have assembled: "assembly_relation P Q R"
    using checked by (simp only: shape assembly_report_at_presentations[OF source])
  let ?W="\<lparr>assembly_pieces=P,assembly_origin=Q\<rparr>"
  have correspondence: "assembly_relation (assembly_pieces ?W) (assembly_origin ?W) R"
    using assembled by simp
  have witness: "K2 ?W" "R=assembly_output ?W"
    using correspondence by (simp only: assembly_relation_iff; blast)+
  show "\<exists>W. assembly_report_presents payload_value_presents W t"
    by (rule exI[of _ ?W])
      (use source witness in \<open>auto simp: shape assembly_report_presents_def assembly_value_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>W. assembly_report_presents payload_value_presents W t"
  then obtain W p q r where source: "K2 W"
    "piece_family_presents payload_value_presents (assembly_pieces W) p"
    "origin_table_presents payload_value_presents (assembly_origin W) q"
    "artifact_value_presents (assembly_output W) r"
    and shape: "t=Pair_Term (Pair_Term p q) r"
    by (auto simp: assembly_report_presents_def assembly_value_presents_def factor_pair_presents_def)
  show "(230,t)\<in>positive_meaning assembly_checking_system"
    by (simp only: shape assembly_report_at_presentations[OF source(2-4)] assembly_relation_iff)
      (use source(1) in simp)
qed

theorem assembly_source_exact:
  "(231,t)\<in>positive_meaning assembly_checking_system \<longleftrightarrow>
    (\<exists>W. assembly_value_presents payload_value_presents W t)"
proof -
  have result: "\<exists>r. artifact_value_presents (assembly_output W) r"
    if "assembly_value_presents payload_value_presents W t" for W
  proof -
    have formed: "exact_formed (assembly_output W)"
      using that by (auto simp: assembly_value_presents_def K2_def)
    show ?thesis by (rule artifact_presentations.total[OF formed])
  qed
  show ?thesis using result
    by (auto simp: assembly_source.exact assembly_report_exact assembly_report_presents_def factor_pair_presents_def; blast)
qed

theorem assembly_source_native_class:
  "presentation_class (assembly_value_presents payload_value_presents) (assembly_domain octets_formed)
    (\<lambda>t. (231,t)\<in>positive_meaning assembly_checking_system)"
  using assembly_value_presentation_class[OF payload_value_presentation_class]
  by (simp only: assembly_source_exact)

theorem assembly_report_native_class:
  "presentation_class (assembly_report_presents payload_value_presents) (assembly_domain octets_formed)
    (\<lambda>t. (230,t)\<in>positive_meaning assembly_checking_system)"
  using assembly_report_presentation_class[OF payload_value_presentation_class]
  by (simp only: assembly_report_exact)

text \<open>
  The proof takes the field lists from the actual supplied piece table. The
  origin projections likewise retain its actual rows. The finite assembly
  criterion then accounts for complete coverage, the range, incidence, every
  attachment count, and functional compatibility through output formation.

  Coverage includes unused carrier atoms. The traversals alone assert only
  the domains of their actual lookups; the full key comparison establishes
  the stronger condition. Shared destinations need not be injective, and
  repeated images are compared as sets except in the counted field.

  Both equivalences cover all raw terms, including malformed inputs. The
  source entry projects a complete report and admits exactly the original
  K2 source presentations. The report presents its intrinsic determined
  output without extending the primitive assembly witness.
\<close>

end
