theory Factor_Proof_Inclusion
  imports Factor_Proof_Retention Factor_Future_Applications
begin

section \<open>Existing proof readings survive formed environment extension\<close>

lemma site_citation_included:
  assumes cite: "site_citation_at E u r d I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "site_citation_at F u r d I K"
proof -
  obtain R c where source: "artifact_at E u R" "citation_at R r c I"
    "citation_location E u c (fst d) (snd d)" "K=citation_slots c"
    using cite by (auto simp: site_citation_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included source(1)])
  have loc: "citation_location F u c (fst d) (snd d)" by (rule included_location[OF included source(3)])
  show ?thesis using ff art loc source(2,4) by (auto simp: site_citation_at_def)
qed

lemma native_site_link_included:
  assumes link: "native_site_link_at E u r d e I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_site_link_at F u r d e I K"
proof -
  obtain R ps a b J A L B where parts: "artifact_at E u R" "record_at R r ps [a,b]"
    "site_citation_at E u a d J A" "site_citation_at E u b e L B"
    "insert r (set ps)\<inter>(J\<union>L)={}" "J\<inter>L={}"
    "I=insert r (set ps\<union>J\<union>L)" "K=A\<union>B" "I\<inter>K={}"
    using link by (auto simp: native_site_link_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have left: "site_citation_at F u a d J A" by (rule site_citation_included[OF parts(3) included ff])
  have right: "site_citation_at F u b e L B" by (rule site_citation_included[OF parts(4) included ff])
  show ?thesis using ff art left right parts(2,5-9) unfolding native_site_link_at_def by blast
qed

lemma native_binding_table_included:
  assumes table: "native_binding_table_at E u r V I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_binding_table_at F u r V I K"
proof (rule native_table_change_reader[OF table ff])
  fix R assume "artifact_at E u R"
  then show "artifact_at F u R" by (rule included_artifact[OF included])
next
  fix a q J A assume row: "native_application_at E u a (fst q) (snd q) J A" and "A\<subseteq>K"
  show "native_application_at F u a (fst q) (snd q) J A"
    by (rule native_application_included[OF row included ff])
next
  fix a q J A z L B
  assume first: "native_application_at F u a (fst q) (snd q) J A"
    and second: "native_application_at F u a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B" using native_application_unique[OF first second] by (auto intro: prod_eqI)
qed

lemma native_discharge_table_included:
  assumes table: "native_discharge_table_at E u r D I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_discharge_table_at F u r D I K"
proof (rule native_table_change_reader[OF table ff])
  fix R assume "artifact_at E u R"
  then show "artifact_at F u R" by (rule included_artifact[OF included])
next
  fix a q J A assume row: "native_site_link_at E u a (fst q) (snd q) J A" and "A\<subseteq>K"
  show "native_site_link_at F u a (fst q) (snd q) J A"
    by (rule native_site_link_included[OF row included ff])
next
  fix a q J A z L B
  assume first: "native_site_link_at F u a (fst q) (snd q) J A"
    and second: "native_site_link_at F u a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B" using native_site_link_unique[OF first second] by (auto intro: prod_eqI)
qed

lemma native_proof_node_included:
  assumes node: "native_proof_node_at E u r N D I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_proof_node_at F u r N D I K"
proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
  case (assertion R)
  have art: "artifact_at F u R" by (rule included_artifact[OF included]) (use assertion in simp)
  have rec: "record_at R r [] []" using assertion by simp
  have native: "native_proof_node_at F u r Schema_Assertion {} {r} {}"
    by (rule native_proof_node_at.assertion[OF ff art rec])
  show ?thesis using assertion native by simp
next
  case (inference R ps c b p d C A V B L D' J W)
  have source: "artifact_at E u R" and rec: "record_at R r ps [c,b,p]"
    and cite: "site_citation_at E u c d C A"
    and bindings: "native_binding_table_at E u b (fset V) B L"
    and discharges: "native_discharge_table_at E u p D' J W"
    and header: "insert r (set ps)\<inter>(C\<union>B\<union>J)={}"
    and cb: "C\<inter>B={}" and cj: "C\<inter>J={}" and bj: "B\<inter>J={}"
    and separate: "insert r (set ps\<union>C\<union>B\<union>J)\<inter>(A\<union>L\<union>W)={}"
    using inference by auto
  have art: "artifact_at F u R" by (rule included_artifact[OF included source])
  have cnew: "site_citation_at F u c d C A" by (rule site_citation_included[OF cite included ff])
  have bnew: "native_binding_table_at F u b (fset V) B L" by (rule native_binding_table_included[OF bindings included ff])
  have pnew: "native_discharge_table_at F u p D' J W" by (rule native_discharge_table_included[OF discharges included ff])
  have native: "native_proof_node_at F u r (Schema_Inference d V) D'
    (insert r (set ps\<union>C\<union>B\<union>J)) (A\<union>L\<union>W)"
    by (rule native_proof_node_at.inference[OF ff art rec cnew bnew pnew header cb cj bj separate])
  show ?thesis using inference native by simp
qed

theorem native_schema_graph_included:
  assumes graph: "native_schema_graph_at E root G" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_schema_graph_at F root G"
  unfolding native_schema_graph_at_def
proof (intro conjI allI impI)
  show "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  fix n N assume row: "(n,N)\<in>fset (graph_inferences G)"
  obtain I K where node: "native_proof_node_at E (fst n) (snd n) N (schema_graph_premises G n) I K"
    using native_schema_graph_entry[OF graph row] by blast
  show "\<exists>I K. native_proof_node_at F (fst n) (snd n) N (schema_graph_premises G n) I K"
    using native_proof_node_included[OF node included ff] by blast
qed

theorem native_graph_demands_included:
  assumes graph: "native_schema_graph_at E root G" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_graph_demands F G=native_graph_demands E G"
proof (rule native_graph_demands_preserved[OF graph])
  fix n N I K assume row: "(n,N)\<in>fset (graph_inferences G)"
    and node: "native_proof_node_at E (fst n) (snd n) N (schema_graph_premises G n) I K"
  show "native_proof_node_at F (fst n) (snd n) N (schema_graph_premises G n) I K"
    by (rule native_proof_node_included[OF node included ff])
qed

text \<open>
  Adding a formed environment extension preserves every existing proof
  reading and every demanded slot. Complete source families and unique
  destination readings exclude additional row interpretations. This
  preservation changes neither the graph nor any validity judgment.
\<close>

end
