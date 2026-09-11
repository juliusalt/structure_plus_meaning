theory Factor_Generation_Source_Admission
  imports Factor_Generation_Source_Equations Factor_Generation_Presentations RRA_Generation_Lists
begin

section \<open>Every expected core bounds only the proof of its child readings\<close>

theorem generation_core_report_on_values:
  assumes source: "environment_value_presents E e" and "value": "generation_value_presents G value"
  shows "(151,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
      \<in>positive_meaning generation_source_system \<longleftrightarrow> generation_at E u r G"
  using source "value"
proof (induction G arbitrary: E e u r "value" rule: measure_induct_rule[of size])
  case (less G)
  obtain l P p c where core: "G=Generation l P p c" by (cases G)
  obtain a ps b q where "values": "target_value_presents l a"
    "data_collection_presents generation_value_presents (fset P) ps"
    "target_value_presents p b" "target_value_presents c q"
    and shape: "value=generation_fields_term a ps b q"
    using less.prems(2) by (auto simp: core generation_value_presents_cases)
  obtain Gs gs where expected: "distinct Gs" "set Gs=fset P"
    "list_all2 generation_value_presents Gs gs" "ps=data_list_term gs"
    using "values"(2) by (auto simp: data_collection_presents_def)
  have context_formed: "term_formed (Pair_Term e (use_data_term u))"
    using environment_value_presents_formed[OF less.prems(1)] by simp
  have child_equation:
    "(149,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data row) h)
      \<in>positive_meaning generation_source_system \<longleftrightarrow> generation_child_at E u row H"
    if socket: "octets_formed (fst row)" and member: "H\<in>fset P" and presented: "generation_value_presents H h"
    for row H h
  proof -
    have smaller: "size H<size G"
      by (rule predecessor_size_decreases) (use member in \<open>simp add: core predecessor_edges_def\<close>)
    have recursive:
      "(151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term z)) h)
        \<in>positive_meaning generation_source_system \<longleftrightarrow> generation_at E v z H" for v z
      by (rule less.IH[OF smaller less.prems(1) presented])
    show ?thesis
      using socket by (cases row) (simp add: generation_child_value_at_source[OF less.prems(1)] recursive)
  qed
  have list_equation:
    "(150,context_relation_argument (Pair_Term e (use_data_term u))
      (data_list_term (map address_pair_data ms)) (data_list_term hs))
      \<in>positive_meaning generation_source_system \<longleftrightarrow> list_all2 (generation_child_at E u) ms Hs"
    if fields: "generation_fields_at E u r l (set ms) p c"
      and bounded: "set Hs\<subseteq>fset P"
      and presented: "list_all2 generation_value_presents Hs hs"
    for ms Hs hs
  proof -
    have addresses: "\<forall>row\<in>set ms. octets_formed (fst row)"
      using generation_fields_row_addresses[OF fields] by fastforce
    have first: "list_all2 (\<lambda>row t. t=address_pair_data row \<and> octets_formed (fst row))
        ms (map address_pair_data ms)"
      using addresses by (simp add: list_all2_function_restricted)
    have second: "list_all2 (\<lambda>H h. H\<in>fset P \<and> generation_value_presents H h) Hs hs"
      using presented bounded by (auto simp: list_all2_conv_all_nth)
    show ?thesis
      by (rule generation_child_values.readings[OF first second context_formed])
        (use child_equation in blast)
  qed
  show ?case
  proof
    assume holds: "(151,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
        \<in>positive_meaning generation_source_system"
    obtain m produced where calls:
      "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a m b q)
        \<in>positive_meaning generation_source_system"
      "(150,context_relation_argument (Pair_Term e (use_data_term u)) m produced)
        \<in>positive_meaning generation_source_system"
      "(145,Pair_Term produced ps)\<in>positive_meaning generation_value_system"
      using holds by (auto simp: shape generation_core_report_fields)
    obtain ms where rows: "m=data_list_term (map address_pair_data ms)" "distinct ms"
      "generation_fields_at E u r l (set ms) p c"
      using calls(1) by (simp only: generation_fields_on_values[OF less.prems(1) "values"(1,3,4)]) blast
    obtain hs where traversal: "produced=data_list_term hs"
      "list_all2 (\<lambda>x h. (149,context_relation_argument (Pair_Term e (use_data_term u)) x h)
        \<in>positive_meaning generation_source_system) (map address_pair_data ms) hs"
      using calls(2) by (auto simp: rows(1) generation_child_values.exact data_list_term_injective)
    have recovered: "\<forall>h\<in>set hs. \<exists>H. generation_value_presents H h"
      using list_all2_members[OF traversal(2)] generation_child_value_admitted by blast
    obtain Hs where presented: "list_all2 generation_value_presents Hs hs"
      using recovered by (simp only: list_all2_exists_left) blast
    have matching: "mset Hs=mset Gs"
      using calls(3) by (simp only: traversal(1) expected(4)
        generation_bags.comparison_readings[OF presented expected(3) generation_identity_contract.at])
    have separate: "distinct Hs" using mset_eq_imp_distinct_iff[OF matching] expected(1) by blast
    have range: "set Hs=fset P" using mset_eq_setD[OF matching] expected(2) by blast
    have children: "list_all2 (generation_child_at E u) ms Hs"
      using calls(2) list_equation[OF rows(3) _ presented] range
      by (simp only: rows(1) traversal(1); blast)
    have native: "generation_at E u r (Generation l P p c)"
      using separate range children by (simp only: generation_at_lists[OF rows(3,2) refl]) blast
    show "generation_at E u r G" using native by (simp only: core)
  next
    assume native: "generation_at E u r G"
    obtain M where fields: "generation_fields_at E u r l M p c"
      using native core by (cases rule: generation_at.cases) auto
    have finite: "finite M" using generation_fields_formed[OF fields] by blast
    obtain ms where rows: "distinct ms" "set ms=M" using finite_distinct_list[OF finite] by blast
    obtain Hs where children: "distinct Hs" "set Hs=fset P" "list_all2 (generation_child_at E u) ms Hs"
      using generation_at_to_lists[OF native fields rows] by (auto simp: core)
    have formed: "\<forall>H\<in>set Hs. generation_formed H"
      using generation_formed_fields[OF generation_at_formed[OF native]] children(2) by (simp add: core)
    have values_exist: "\<forall>H\<in>set Hs. \<exists>h. generation_value_presents H h"
      using formed generation_value_presents_total by blast
    obtain hs where reversed: "list_all2 (\<lambda>h H. generation_value_presents H h) hs Hs"
      using values_exist by (simp only: list_all2_exists_left) blast
    have presented: "list_all2 generation_value_presents Hs hs"
      using reversed by (auto simp: list_all2_conv_all_nth)
    have fields': "generation_fields_at E u r l (set ms) p c" using fields rows(2) by simp
    have traversal: "(150,context_relation_argument (Pair_Term e (use_data_term u))
        (data_list_term (map address_pair_data ms)) (data_list_term hs))\<in>positive_meaning generation_source_system"
      using children(2,3) list_equation[OF fields' _ presented] by blast
    have matching: "mset Hs=mset Gs"
      using children(1,2) expected(1,2) set_eq_iff_mset_eq_distinct by blast
    have bag: "(145,Pair_Term (data_list_term hs) ps)\<in>positive_meaning generation_value_system"
      using matching by (simp only: expected(4)
        generation_bags.comparison_readings[OF presented expected(3) generation_identity_contract.at])
    have value_admitted: "(139,value)\<in>positive_meaning generation_value_system"
      using less.prems(2) by (auto simp: generation_admission_exact)
    have fields_admitted: "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a
        (data_list_term (map address_pair_data ms)) b q)\<in>positive_meaning generation_source_system"
      using rows(1) fields' by (simp add: generation_fields_on_rows[OF less.prems(1) "values"(1,3,4)])
    show "(151,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
        \<in>positive_meaning generation_source_system"
      using value_admitted fields_admitted traversal bag by (auto simp: shape generation_core_report_fields)
  qed
qed

section \<open>All-term contracts admit exactly the existing source and report classes\<close>

corollary generation_core_report_at_source:
  assumes source: "environment_value_presents E e"
  shows "(151,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>G. generation_value_presents G value \<and> generation_at E u r G)"
  using generation_core_report_admitted generation_core_report_on_values[OF source]
  by blast

theorem generation_core_report_exact:
  "(151,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>z. generation_report_presents z t)"
proof
  assume holds: "(151,t)\<in>positive_meaning generation_source_system"
  obtain source "value" where shape: "t=Pair_Term source value"
    using holds by (auto simp: generation_core_report_fields)
  have report: "(151,Pair_Term source value)\<in>positive_meaning generation_source_system"
    using holds shape by simp
  obtain G where "value": "generation_value_presents G value" using generation_core_report_admitted[OF report] by blast
  obtain E e u r where source: "source=generation_source_term e (use_data_term u) (Payload_Term r)"
    "environment_value_presents E e" using generation_core_report_source[OF report] by blast
  have native: "generation_at E u r G"
    using report source(1) generation_core_report_on_values[OF source(2) "value"] by blast
  have root: "source_root_presents (E,(u,r)) source"
    using generation_context_formed[OF native] source by (auto simp: source_root_presents_fields)
  show "\<exists>z. generation_report_presents z t"
    by (rule exI[of _ "((E,(u,r)),G)"])
      (use root "value" native shape in \<open>auto simp: generation_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. generation_report_presents z t"
  then obtain E u r G source "value" where parts: "t=Pair_Term source value"
    "source_root_presents (E,(u,r)) source" "generation_value_presents G value" "generation_at E u r G"
    by (auto simp: generation_report_presents_def factor_pair_presents_def)
  obtain e where source: "source=generation_source_term e (use_data_term u) (Payload_Term r)"
    "environment_value_presents E e" using parts(2) by (auto simp: source_root_presents_fields)
  show "(151,t)\<in>positive_meaning generation_source_system"
    using parts(4) by (simp add: parts(1) source(1) generation_core_report_on_values[OF source(2) parts(3)])
qed

theorem generation_source_exact:
  "(152,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>z. generation_source_presents z t)"
proof
  assume "(152,t)\<in>positive_meaning generation_source_system"
  then show "\<exists>z. generation_source_presents z t"
    by (auto simp: generation_source_equation generation_core_report_exact
      generation_report_presents_def generation_source_presents_def factor_pair_presents_def)
next
  assume "\<exists>z. generation_source_presents z t"
  then obtain z where source: "source_root_presents (fst z) t" "generation_at_context (fst z) (snd z)"
    by (auto simp: generation_source_presents_def)
  obtain "value" where "value": "generation_value_presents (snd z) value"
    using generation_value_presents_total[OF generation_at_formed[OF source(2)]] by blast
  have report: "generation_report_presents z (Pair_Term t value)"
    using source "value" by (auto simp: generation_report_presents_def factor_pair_presents_def)
  show "(152,t)\<in>positive_meaning generation_source_system"
    using report by (simp only: generation_source_equation generation_core_report_exact) blast
qed

corollary generation_source_at_source:
  assumes source: "environment_value_presents E e"
  shows "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system
    \<longleftrightarrow> (\<exists>G. generation_at E u r G)"
proof
  assume "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
  then show "\<exists>G. generation_at E u r G"
    using environment_value_presents_unique[OF _ source]
    by (auto simp: generation_source_exact generation_source_presents_def source_root_presents_def
      dest: injD[OF use_data_term_injective])
next
  assume "\<exists>G. generation_at E u r G"
  then obtain G where native: "generation_at E u r G" by blast
  have presentation: "generation_source_presents ((E,(u,r)),G)
      (generation_source_term e (use_data_term u) (Payload_Term r))"
    using generation_context_formed[OF native] source native
    by (auto simp: generation_source_presents_def source_root_presents_fields)
  show "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
    using presentation by (auto simp: generation_source_exact)
qed

text \<open>
  The joint induction uses the size of the independently recovered expected
  core. Bag identity first accounts for every produced child occurrence and
  its multiplicity. Each resulting child belongs to the expected predecessor
  set and is strictly smaller. The local induction hypothesis therefore
  establishes the child's actual reading at its cited site.

  Generic sequence and multiset reading contracts transport those local
  equations. The existing generation rule is recovered through its complete
  socket-enumeration theorem. Completeness permits arbitrary source and
  expected-value presentations and independent predecessor enumerations.
  The exported all-term equations have no size bound and reject inputs
  outside the original source and report classes.
\<close>

end
