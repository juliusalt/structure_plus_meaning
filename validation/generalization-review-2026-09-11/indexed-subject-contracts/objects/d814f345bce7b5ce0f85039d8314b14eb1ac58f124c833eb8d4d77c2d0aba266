theory Factor_Generation_Read_Sites
  imports Factor_Generation_Dependency_Clauses Factor_Generation_Retention_Presentations
begin

section \<open>Each selected child is an actual predecessor destination\<close>

lemma generation_reported_child_site:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "(\<exists>rows s d h. (155,Pair_Term p rows)\<in>positive_meaning generation_source_system \<and>
      selected_data_member (generation_predecessor_row_term s d q h) rows) \<longleftrightarrow>
    (\<exists>v a. q=site_data_term v a \<and> ((u,r),(v,a))\<in>generation_request_edges E)"
proof -
  let ?L="generation_predecessor_rows E u r"
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have collections: "(155,Pair_Term p rows)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      data_collection_presents generation_predecessor_row_presents ?L rows" for rows
    using generation_predecessor_function.output[OF source, of rows] by simp
  have selected: "(\<forall>row\<in>?L. \<exists>t. selected_data_member t rows \<and> generation_predecessor_row_presents row t) \<and>
      (\<forall>t. selected_data_member t rows \<longrightarrow> (\<exists>row\<in>?L. generation_predecessor_row_presents row t))"
    if "data_collection_presents generation_predecessor_row_presents ?L rows" for rows
    by (rule data_collection_selection[OF that]) (use generation_predecessor_row_value_formed in blast)
  show ?thesis
  proof
    assume "\<exists>rows s d h. (155,Pair_Term p rows)\<in>positive_meaning generation_source_system \<and>
      selected_data_member (generation_predecessor_row_term s d q h) rows"
    then obtain rows s d h where report: "data_collection_presents generation_predecessor_row_presents ?L rows"
      and member: "selected_data_member (generation_predecessor_row_term s d q h) rows"
      by (simp only: collections) blast
    obtain row where row: "row\<in>?L" "generation_predecessor_row_presents row (generation_predecessor_row_term s d q h)"
      using selected[OF report] member by blast
    obtain x y v a H where shape: "row=(x,(y,((v,a),H)))"
      by (rule that[of "fst row" "fst (snd row)" "fst (fst (snd (snd row)))"
        "snd (fst (snd (snd row)))" "snd (snd (snd row))"]) simp
    have coordinate: "q=site_data_term v a"
      using row(2) by (auto simp: shape generation_predecessor_row_presents_fields)
    have edge: "((u,r),(v,a))\<in>generation_request_edges E"
      using row(1) by (simp only: generation_predecessor_request_relation[OF native])
        (use shape in blast)
    show "\<exists>v a. q=site_data_term v a \<and> ((u,r),(v,a))\<in>generation_request_edges E" using coordinate edge by blast
  next
    assume "\<exists>v a. q=site_data_term v a \<and> ((u,r),(v,a))\<in>generation_request_edges E"
    then obtain v a x y H where coordinate: "q=site_data_term v a" and member: "(x,(y,((v,a),H)))\<in>?L"
      by (simp only: generation_predecessor_request_relation[OF native]) blast
    have admitted: "(152,p)\<in>positive_meaning generation_source_system" using source by (auto simp: generation_source_exact)
    obtain rows where report: "(155,Pair_Term p rows)\<in>positive_meaning generation_source_system"
      using generation_predecessor_function.total[OF admitted] by blast
    have collection: "data_collection_presents generation_predecessor_row_presents ?L rows" using report by (simp only: collections)
    obtain t where chosen: "selected_data_member t rows" "generation_predecessor_row_presents (x,(y,((v,a),H))) t"
      using selected[OF collection] member by blast
    obtain h where shape: "t=generation_predecessor_row_term (Payload_Term x) (Payload_Term y) q h"
      using chosen(2) by (auto simp: generation_predecessor_row_presents_fields coordinate)
    show "\<exists>rows s d h. (155,Pair_Term p rows)\<in>positive_meaning generation_source_system \<and>
      selected_data_member (generation_predecessor_row_term s d q h) rows"
      using report chosen(1) shape by blast
  qed
qed

section \<open>The positive recursion is exactly predecessor reachability\<close>

abbreviation generation_read_site_result :: "factor_term \<Rightarrow> bool" where
  "generation_read_site_result t \<equiv> \<exists>E e u r G v a.
    t=Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v a) \<and>
    environment_value_presents E e \<and> generation_at E u r G \<and> (v,a)\<in>generation_read_sites E {(u,r)}"

lemma generation_read_site_start:
  assumes read: "(152,generation_source_term e u r)\<in>positive_meaning generation_source_system"
  shows "(169,Pair_Term (generation_source_term e u r) (Pair_Term u r))\<in>positive_meaning generation_retention_system"
proof -
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else r"
  have formed: "term_formed e" "term_formed u" "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  have result: "(169,evaluate_pattern ?h (schema_conclusion generation_read_site_root_schema))
      \<in>positive_meaning generation_retention_system"
    by (rule generation_retention_rule[where c=0])
      (use formed read in \<open>auto simp: generation_retention_group_clauses_def
        generation_read_site_root_schema_def schema_variables_def generation_retention_components\<close>)
  show ?thesis using result by (simp add: generation_read_site_root_schema_def)
qed

lemma generation_read_site_advance:
  assumes reached: "(169,Pair_Term (generation_source_term e u r) (Pair_Term w b))\<in>positive_meaning generation_retention_system"
    and report: "(155,Pair_Term (generation_source_term e w b) rows)\<in>positive_meaning generation_source_system"
    and selected: "(5,Pair_Term (generation_predecessor_row_term s d (Pair_Term v a) h) (Pair_Term rows rest))
      \<in>positive_meaning bag_comparison_system"
  shows "(169,Pair_Term (generation_source_term e u r) (Pair_Term v a))\<in>positive_meaning generation_retention_system"
proof -
  let ?f="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else if i=3 then v
    else if i=4 then a else if i=5 then w else if i=6 then b else if i=7 then rows
    else if i=8 then s else if i=9 then d else if i=10 then h else rest"
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed w" "term_formed b"
    "term_formed rows" "term_formed s" "term_formed d" "term_formed v" "term_formed a" "term_formed h" "term_formed rest"
    using schema_call_formed_target[OF positive_meaning_formed[OF reached]]
      schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  have result: "(169,evaluate_pattern ?f (schema_conclusion generation_read_site_step_schema))
      \<in>positive_meaning generation_retention_system"
    by (rule generation_retention_rule[where c=1])
      (use formed reached report selected in \<open>auto simp: generation_retention_group_clauses_def
        generation_read_site_step_schema_def schema_variables_def generation_retention_components\<close>)
  show ?thesis using result by (simp add: generation_read_site_step_schema_def)
qed

theorem generation_read_site_sound:
  assumes holds: "(169,t)\<in>positive_meaning generation_retention_system"
  shows "generation_read_site_result t"
proof -
  have invariant: "(169::nat)=169 \<longrightarrow> generation_read_site_result t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=169 \<longrightarrow> generation_read_site_result t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses generation_retention_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed generation_retention_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning generation_retention_system \<and>
        (e=169 \<longrightarrow> generation_read_site_result (evaluate_pattern h p))"
    show "d=169 \<longrightarrow> generation_read_site_result (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=169"
      then have cases: "S=generation_read_site_root_schema \<or> S=generation_read_site_step_schema" using clause by auto
      then show "generation_read_site_result (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=generation_read_site_root_schema"
        have read: "(152,generation_source_term (h 0) (h 1) (h 2))\<in>positive_meaning generation_source_system"
          using support by (auto simp: schema generation_read_site_root_schema_def generation_retention_components)
        obtain E u r G where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
          "h 2=Payload_Term r" "generation_at E u r G"
          using read by (auto simp: generation_source_exact generation_source_presentation_fields)
        have root: "(u,r)\<in>generation_read_sites E {(u,r)}"
          using generation_read_sites_roots[of "{(u,r)}" E] by blast
        show ?thesis using source root
          by (auto simp: schema generation_read_site_root_schema_def site_data_term_def)
      next
        assume schema: "S=generation_read_site_step_schema"
        have prior: "generation_read_site_result
            (Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (Pair_Term (h 5) (h 6)))"
          using support[rule_format, of 0 169
            "Pattern_Pair (generation_source_pattern data_x data_y data_z) (Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 6))"]
          by (simp add: schema generation_read_site_step_schema_def)
        obtain E u r G w b where source: "environment_value_presents E (h 0)" "h 1=use_data_term u"
          "h 2=Payload_Term r" "generation_at E u r G" "h 5=use_data_term w" "h 6=Payload_Term b"
          and site: "(w,b)\<in>generation_read_sites E {(u,r)}"
          using prior by (auto simp: site_data_term_def)
        have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E v a H)"
          using source(4) by auto
        obtain H where native: "generation_at E w b H" using generation_read_sites_have_cores[OF roots site] by blast
        have parent: "generation_source_presents ((E,(w,b)),H) (generation_source_term (h 0) (h 5) (h 6))"
          using source(1,5,6) native by (auto simp: generation_source_presentation_fields)
        have report: "(155,Pair_Term (generation_source_term (h 0) (h 5) (h 6)) (h 7))\<in>positive_meaning generation_source_system"
          and selection: "(5,Pair_Term (generation_predecessor_row_term (h 8) (h 9) (Pair_Term (h 3) (h 4)) (h 10))
            (Pair_Term (h 7) (h 11)))\<in>positive_meaning bag_comparison_system"
          using support by (auto simp: schema generation_read_site_step_schema_def generation_retention_components)
        obtain v a where coordinate: "Pair_Term (h 3) (h 4)=site_data_term v a"
          and edge: "((w,b),(v,a))\<in>generation_request_edges E"
          using generation_reported_child_site[OF parent, of "Pair_Term (h 3) (h 4)"] report selection by blast
        have reached: "(v,a)\<in>generation_read_sites E {(u,r)}" by (rule generation_read_sites_step[OF site edge])
        show ?thesis using source(1-4) coordinate reached
          by (auto simp: schema generation_read_site_step_schema_def)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem generation_read_site_complete:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
    and site: "(v,a)\<in>generation_read_sites E {(u,r)}"
  shows "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term v a))
    \<in>positive_meaning generation_retention_system"
proof -
  have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)" using native by auto
  have admitted: "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
    using native by (simp only: generation_source_at_source[OF source]) blast
  have start: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (site_data_term u r))
      \<in>positive_meaning generation_retention_system"
    using generation_read_site_start[OF admitted] by (simp only: site_data_term_def)
  have path: "((u,r),(v,a))\<in>(generation_request_edges E)\<^sup>*" using site by (simp add: generation_read_sites_def)
  have reached: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (definition_site_value z))
      \<in>positive_meaning generation_retention_system"
    if path: "((u,r),z)\<in>(generation_request_edges E)\<^sup>*" for z
    using path
  proof (induction rule: rtrancl_induct)
    case base
    show ?case using start by simp
  next
    case (step y z)
    obtain w b where y: "y=(w,b)" by (cases y)
    obtain x k where z: "z=(x,k)" by (cases z)
    have read_site: "(w,b)\<in>generation_read_sites E {(u,r)}"
      using step.hyps(1) y by (auto simp: generation_read_sites_def)
    obtain H where child: "generation_at E w b H" using generation_read_sites_have_cores[OF roots read_site] by blast
    have parent: "generation_source_presents ((E,(w,b)),H) (generation_source_term e (use_data_term w) (Payload_Term b))"
      using source child by (auto simp: generation_source_presentation_fields)
    have edge: "((w,b),(x,k))\<in>generation_request_edges E" using step.hyps(2) y z by simp
    obtain rows s d h rest where report:
      "(155,Pair_Term (generation_source_term e (use_data_term w) (Payload_Term b)) rows)\<in>positive_meaning generation_source_system"
      and selected: "(5,Pair_Term (generation_predecessor_row_term s d (site_data_term x k) h) (Pair_Term rows rest))
        \<in>positive_meaning bag_comparison_system"
      using generation_reported_child_site[OF parent, of "site_data_term x k"] edge by blast
    have prior: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r))
        (Pair_Term (use_data_term w) (Payload_Term b)))\<in>positive_meaning generation_retention_system"
      using step.IH by (simp add: y site_data_term_def)
    show ?case using generation_read_site_advance[OF prior report selected[unfolded site_data_term_def]]
      by (simp add: z site_data_term_def)
  qed
  show ?thesis using reached[OF path] by simp
qed

theorem generation_read_site_exact:
  "(169,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_read_site_result t"
  using generation_read_site_sound generation_read_site_complete by blast

corollary generation_read_site_at_source:
  assumes source: "environment_value_presents E e"
  shows "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>G v a. q=site_data_term v a \<and> generation_at E u r G \<and> (v,a)\<in>generation_read_sites E {(u,r)})"
proof
  assume holds: "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system"
  obtain F f v b G w a where shape: "Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q=
      Pair_Term (generation_source_term f (use_data_term v) (Payload_Term b)) (site_data_term w a)"
    and presented: "environment_value_presents F f"
    and native: "generation_at F v b G" and site: "(w,a)\<in>generation_read_sites F {(v,b)}"
    using generation_read_site_sound[OF holds] by blast
  have fields: "f=e" "v=u" "b=r" "q=site_data_term w a"
    using shape by (auto simp: inj_eq[OF use_data_term_injective])
  have actual: "environment_value_presents F e" using presented by (simp only: fields(1))
  have same: "F=E" by (rule environment_value_presents_unique[OF actual source])
  show "\<exists>G v a. q=site_data_term v a \<and> generation_at E u r G \<and> (v,a)\<in>generation_read_sites E {(u,r)}"
    using fields(4) native site by (simp only: same fields(2,3)) blast
next
  assume "\<exists>G v a. q=site_data_term v a \<and> generation_at E u r G \<and> (v,a)\<in>generation_read_sites E {(u,r)}"
  then obtain G v a where shape: "q=site_data_term v a" and native: "generation_at E u r G"
    and site: "(v,a)\<in>generation_read_sites E {(u,r)}" by blast
  show "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system"
    by (simp only: shape) (rule generation_read_site_complete[OF source native site])
qed

corollary generation_read_site_on_read:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "(169,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>v a. q=site_data_term v a \<and> (v,a)\<in>generation_read_sites E {(u,r)})"
  by (simp only: generation_read_site_at_source[OF source]) (use native in blast)

text \<open>
  Every recursive step consumes the source notion's complete predecessor
  contract. Selection recovers the actual cited destination, even when the
  child core has other presentations. The positive induction gives only
  reachable sites; path induction supplies every reachable site.

  The exact result has no path certificate, selected subgraph, or depth bound.
  Every environment presentation is supported at the same actual root. The
  root admission remains required even when no predecessor edge is followed.
\<close>

end
