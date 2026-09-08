theory Factor_Generation_Predecessor_Admission
  imports Factor_Generation_Source_Admission
begin

section \<open>Child operation contracts retain their complete independent domains\<close>

abbreviation generation_child_value_result :: "factor_term \<Rightarrow> bool" where
  "generation_child_value_result t \<equiv> \<exists>E e u s d H h.
    t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) h \<and>
    environment_value_presents E e \<and> octets_formed s \<and> generation_value_presents H h \<and>
    generation_child_at E u (s,d) H"

theorem generation_child_value_exact:
  "(149,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_child_value_result t"
  using generation_core_report_at_source
  by (auto simp: generation_child_value_equation; blast)

abbreviation generation_child_row_result :: "factor_term \<Rightarrow> bool" where
  "generation_child_row_result t \<equiv> \<exists>E e u s d v a H row.
    t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) row \<and>
    environment_value_presents E e \<and> generation_predecessor_row_presents (s,(d,((v,a),H))) row \<and>
    located_at E u d v a \<and> generation_at E v a H"

theorem generation_child_row_exact:
  "(153,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_child_row_result t"
proof
  assume holds: "(153,t)\<in>positive_meaning generation_source_system"
  obtain E e u s d v a h where fields:
    "t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h)"
    "environment_value_presents E e" "octets_formed s" "located_at E u d v a"
    "(151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
      \<in>positive_meaning generation_source_system"
    using holds by (simp only: generation_child_row_equation) blast
  obtain H where child: "generation_value_presents H h" "generation_at E v a H"
    using fields(5) by (simp only: generation_core_report_at_source[OF fields(2)]) blast
  have call: "(44,citation_observation_argument e (use_data_term u) (Payload_Term d) (site_data_term v a))
      \<in>positive_meaning located_admission_system"
    using fields(4) by (simp add: located_admission_on_values[OF fields(2)])
  have coordinates: "octets_formed d" "octets_formed a"
    using schema_call_formed_target[OF positive_meaning_formed[OF call]] by auto
  have row: "generation_predecessor_row_presents (s,(d,((v,a),H)))
      (generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h)"
    using fields(3) coordinates child(1) by (auto simp: generation_predecessor_row_presents_fields)
  show "generation_child_row_result t" using fields(1,2,4) row child(2) by blast
next
  assume "generation_child_row_result t"
  then obtain E e u s d v a H row where parts:
    "t=context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (s,d)) row"
    "environment_value_presents E e" "generation_predecessor_row_presents (s,(d,((v,a),H))) row"
    "located_at E u d v a" "generation_at E v a H" by blast
  obtain h where "value": "row=generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h"
    "octets_formed s" "generation_value_presents H h"
    using parts(3) by (auto simp: generation_predecessor_row_presents_fields)
  have report: "(151,Pair_Term (generation_source_term e (use_data_term v) (Payload_Term a)) h)
      \<in>positive_meaning generation_source_system"
    using parts(5) by (simp add: generation_core_report_on_values[OF parts(2) "value"(3)])
  show "(153,t)\<in>positive_meaning generation_source_system"
    using parts(1,2,4) "value"(1,2) report by (auto simp: generation_child_row_equation)
qed

corollary generation_child_row_on_values:
  assumes source: "environment_value_presents E e"
    and "value": "generation_predecessor_row_presents (s,(d,((v,a),H))) row"
  shows "(153,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data (k,z)) row)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    k=s \<and> z=d \<and> located_at E u d v a \<and> generation_at E v a H"
proof -
  obtain h where fields: "row=generation_predecessor_row_term (Payload_Term s) (Payload_Term d) (site_data_term v a) h"
    "octets_formed s" "generation_value_presents H h"
    using "value" by (auto simp: generation_predecessor_row_presents_fields)
  show ?thesis using fields(2)
    by (auto simp: generation_child_row_at_source[OF source] fields(1)
      generation_core_report_on_values[OF source fields(3)])
qed

lemma generation_child_row_at_fields:
  assumes source: "environment_value_presents E e" and fields: "generation_fields_at E u r l M p c"
    and edge: "edge\<in>M" and "value": "generation_predecessor_row_presents row t"
  shows "(153,context_relation_argument (Pair_Term e (use_data_term u)) (address_pair_data edge) t)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    row\<in>generation_predecessor_rows E u r \<and> generation_predecessor_socket_row row=edge"
proof -
  obtain k z where edge_shape: "edge=(k,z)" by (cases edge)
  obtain s d v a H where row_shape: "row=(s,(d,((v,a),H)))"
    by (rule that[of "fst row" "fst (snd row)" "fst (fst (snd (snd row)))"
      "snd (fst (snd (snd row)))" "snd (snd (snd row))"]) simp
  have presented: "generation_predecessor_row_presents (s,(d,((v,a),H))) t" using "value" row_shape by simp
  show ?thesis using edge
    by (auto simp: edge_shape row_shape generation_child_row_on_values[OF source presented]
      generation_predecessor_rows_at_source_fields[OF fields])
qed

lemma generation_predecessor_row_lists:
  assumes source: "environment_value_presents E e"
    and fields: "generation_fields_at E u r l (set ms) p c"
    and rows: "list_all2 generation_predecessor_row_presents Rs qs"
  shows "(154,context_relation_argument (Pair_Term e (use_data_term u))
      (data_list_term (map address_pair_data ms)) (data_list_term qs))\<in>positive_meaning generation_source_system
    \<longleftrightarrow> list_all2 (\<lambda>edge row. row\<in>generation_predecessor_rows E u r \<and>
      generation_predecessor_socket_row row=edge) ms Rs"
proof -
  have first: "list_all2 (\<lambda>edge t. t=address_pair_data edge \<and> edge\<in>set ms) ms (map address_pair_data ms)"
    by (simp add: list_all2_function_restricted)
  have ctx_formed: "term_formed (Pair_Term e (use_data_term u))"
    using environment_value_presents_formed[OF source] by simp
  show ?thesis by (rule generation_child_rows.readings[OF first rows ctx_formed])
    (use generation_child_row_at_fields[OF source fields] in blast)
qed

section \<open>A report enumerates the whole actual predecessor relation\<close>

theorem generation_predecessor_report_on_source:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "(155,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u r) value"
proof
  let ?L="generation_predecessor_rows E u r"
  assume holds: "(155,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
      \<in>positive_meaning generation_source_system"
  obtain a m b q where calls:
    "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a m b q)\<in>positive_meaning generation_source_system"
    "(154,context_relation_argument (Pair_Term e (use_data_term u)) m value)\<in>positive_meaning generation_source_system"
    using holds by (auto simp: generation_predecessor_report_calls)
  obtain l ms p c where fields: "m=data_list_term (map address_pair_data ms)" "distinct ms"
    "generation_fields_at E u r l (set ms) p c"
    using calls(1) environment_value_presents_unique[OF _ source]
    by (auto simp: generation_fields_exact dest: injD[OF use_data_term_injective])
  obtain qs where traversal: "value=data_list_term qs"
    "list_all2 (\<lambda>x y. (153,context_relation_argument (Pair_Term e (use_data_term u)) x y)
      \<in>positive_meaning generation_source_system) (map address_pair_data ms) qs"
    using calls(2) by (auto simp: fields(1) generation_child_rows.exact data_list_term_injective)
  have recovered: "\<forall>q\<in>set qs. \<exists>row. generation_predecessor_row_presents row q"
    using list_all2_members[OF traversal(2)] by (auto simp: generation_child_row_exact; blast)
  obtain Rs where presented: "list_all2 generation_predecessor_row_presents Rs qs"
    using recovered by (simp only: list_all2_exists_left) blast
  have linked: "list_all2 (\<lambda>edge row. row\<in>?L \<and> generation_predecessor_socket_row row=edge) ms Rs"
    using calls(2) by (simp only: fields(1) traversal(1) generation_predecessor_row_lists[OF source fields(3) presented])
  have bounded: "set Rs\<subseteq>?L" using list_all2_members[OF linked] by blast
  have mapped: "map generation_predecessor_socket_row Rs=ms"
  proof (rule nth_equalityI)
    show "length (map generation_predecessor_socket_row Rs)=length ms"
      using list_all2_lengthD[OF linked] by simp
  next
    fix i assume index: "i<length (map generation_predecessor_socket_row Rs)"
    show "map generation_predecessor_socket_row Rs!i=ms!i"
      using linked index by (auto simp: list_all2_conv_all_nth)
  qed
  have mapped_distinct: "distinct (map generation_predecessor_socket_row Rs)"
    using fields(2) by (simp only: mapped)
  have separate: "distinct Rs" using mapped_distinct by (simp only: distinct_map; blast)
  have projection: "bij_betw generation_predecessor_socket_row ?L (set ms)"
    by (rule generation_predecessor_rows_projection[OF native fields(3)])
  have complete: "set Rs=?L"
  proof
    show "set Rs\<subseteq>?L" by (rule bounded)
    show "?L\<subseteq>set Rs"
    proof
      fix row assume member: "row\<in>?L"
      have edge: "generation_predecessor_socket_row row\<in>set ms"
        using projection member by (auto simp: bij_betw_def)
      obtain other where other: "other\<in>set Rs" "generation_predecessor_socket_row other=generation_predecessor_socket_row row"
        using edge mapped by auto
      have inside: "other\<in>?L" using bounded other(1) by blast
      have injective: "inj_on generation_predecessor_socket_row ?L" using projection by (simp add: bij_betw_def)
      have same: "other=row" by (rule inj_onD[OF injective other(2) inside member])
      show "row\<in>set Rs" using other(1) same by simp
    qed
  qed
  show "data_collection_presents generation_predecessor_row_presents ?L value"
    using separate complete presented traversal(1) by (auto simp: data_collection_presents_def)
next
  let ?L="generation_predecessor_rows E u r"
  assume presented: "data_collection_presents generation_predecessor_row_presents ?L value"
  obtain Rs qs where rows: "distinct Rs" "set Rs=?L" "list_all2 generation_predecessor_row_presents Rs qs"
    "value=data_list_term qs" using presented by (auto simp: data_collection_presents_def)
  obtain l M p c where fields: "generation_fields_at E u r l M p c"
    using native by (cases rule: generation_at.cases) blast
  have projection: "bij_betw generation_predecessor_socket_row ?L M"
    by (rule generation_predecessor_rows_projection[OF native fields])
  let ?ms="map generation_predecessor_socket_row Rs"
  have keys: "distinct ?ms" and domain: "set ?ms=M"
    using rows(1,2) projection by (auto simp: distinct_map bij_betw_def)
  have fields': "generation_fields_at E u r l (set ?ms) p c" using fields domain by simp
  have linked: "list_all2 (\<lambda>edge row. row\<in>?L \<and> generation_predecessor_socket_row row=edge) ?ms Rs"
    using rows(2) by (simp add: list_all2_map1 list_all2_same)
  have traversal: "(154,context_relation_argument (Pair_Term e (use_data_term u))
      (data_list_term (map address_pair_data ?ms)) value)\<in>positive_meaning generation_source_system"
    using linked by (simp only: rows(4) generation_predecessor_row_lists[OF source fields' rows(3)])
  obtain a b q where "values": "target_value_presents l a" "target_value_presents p b" "target_value_presents c q"
    using generation_fields_formed[OF fields] target_value_presents_total by blast
  have fields_admitted: "(148,generation_fields_argument e (use_data_term u) (Payload_Term r) a
      (data_list_term (map address_pair_data ?ms)) b q)\<in>positive_meaning generation_source_system"
    using keys fields' by (simp only: generation_fields_on_rows[OF source "values"]; blast)
  have source_admitted: "(152,generation_source_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning generation_source_system"
    using native by (auto simp: generation_source_at_source[OF source])
  show "(155,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) value)
      \<in>positive_meaning generation_source_system"
    using source_admitted fields_admitted traversal by (auto simp: generation_predecessor_report_calls)
qed

theorem generation_predecessor_report_exact:
  "(155,t)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (\<exists>z. generation_predecessor_report_presents z t)"
proof
  assume holds: "(155,t)\<in>positive_meaning generation_source_system"
  obtain source "value" where shape: "t=Pair_Term source value"
    and admitted: "(152,source)\<in>positive_meaning generation_source_system"
    using holds by (auto simp: generation_predecessor_report_calls)
  obtain E u r G where reading: "generation_source_presents ((E,(u,r)),G) source"
    using admitted by (auto simp: generation_source_exact)
  have native: "generation_at E u r G" using reading by (simp add: generation_source_presents_def)
  obtain e where input: "source=generation_source_term e (use_data_term u) (Payload_Term r)"
    "environment_value_presents E e"
    using reading by (auto simp: generation_source_presents_def source_root_presents_fields)
  have rows: "data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u r) value"
    using holds by (simp only: shape input(1) generation_predecessor_report_on_source[OF input(2) native])
  show "\<exists>z. generation_predecessor_report_presents z t"
    by (rule exI[of _ "(((E,(u,r)),G),generation_predecessor_rows E u r)"])
      (use reading rows shape in \<open>auto simp: generation_predecessor_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. generation_predecessor_report_presents z t"
  then obtain E u r G source "value" where fields: "t=Pair_Term source value"
    "generation_source_presents ((E,(u,r)),G) source"
    "data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u r) value"
    by (auto simp: generation_predecessor_report_presents_def factor_pair_presents_def)
  have native: "generation_at E u r G" using fields(2) by (simp add: generation_source_presents_def)
  obtain e where input: "source=generation_source_term e (use_data_term u) (Payload_Term r)"
    "environment_value_presents E e"
    using fields(2) by (auto simp: generation_source_presents_def source_root_presents_fields)
  show "(155,t)\<in>positive_meaning generation_source_system"
    using fields(3) by (simp only: fields(1) input(1) generation_predecessor_report_on_source[OF input(2) native])
qed

text \<open>
  The whole parent is admitted before its predecessor report. Its complete
  socket graph is in bijection with the actual predecessor rows. A report
  can enumerate those rows in any order; projecting that enumeration gives
  an admitted complete socket enumeration in the same order.

  The two traversal contracts retain every corresponding row and its actual
  source context. Exact child cores do not replace cited destinations. Empty
  reports still admit the parent and its empty predecessor family. Missing,
  repeated, and unrelated rows cannot satisfy the complete report class.
\<close>

end
