theory Factor_Proof_Restriction
  imports Factor_Realization Factor_Application_Retention
begin

section \<open>Retaining the exact sources and slots of proof metadata\<close>

lemma site_citation_slots_bound:
  assumes "site_citation_at E u r d I K" "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain c where loc: "citation_location E u c (fst d) (snd d)" and slots: "K=citation_slots c"
    using assms(1) by (auto simp: site_citation_at_def)
  have member: "k \<in> citation_slots c" using assms(2) slots by simp
  show ?thesis by (rule located_citation_slots_bound[OF loc member])
qed

lemma site_citation_read_environment:
  assumes cite: "site_citation_at E u r d I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "site_citation_at (read_environment E U D) u r d I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R c where parts: "artifact_at E u R" "citation_at R r c I"
    "citation_location E u c (fst d) (snd d)" "K=citation_slots c"
    using cite by (auto simp: site_citation_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have demands: "\<forall>k\<in>citation_slots c. (u,k) \<in> D" using slots parts(4) by simp
  have location: "citation_location ?F u c (fst d) (snd d)"
    using read_environment_location[OF source demands] parts(3) by simp
  show ?thesis using ff art location parts(2,4) unfolding site_citation_at_def by blast
qed

lemma native_site_link_slots_bound:
  assumes link: "native_site_link_at E u r d e I K" and slot: "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain a b J A L B where parts: "site_citation_at E u a d J A" "site_citation_at E u b e L B" "K=A \<union> B"
    using link by (auto simp: native_site_link_at_def)
  show ?thesis using site_citation_slots_bound[OF parts(1)] site_citation_slots_bound[OF parts(2)] slot parts(3) by auto
qed

lemma native_site_link_read_environment:
  assumes link: "native_site_link_at E u r d e I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_site_link_at (read_environment E U D) u r d e I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps a b J A L B where parts: "artifact_at E u R" "record_at R r ps [a,b]"
    "site_citation_at E u a d J A" "site_citation_at E u b e L B"
    "insert r (set ps) \<inter> (J \<union> L) = {}" "J \<inter> L = {}"
    "I=insert r (set ps \<union> J \<union> L)" "K=A \<union> B" "I \<inter> K = {}"
    using link by (auto simp: native_site_link_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have left_slots: "\<forall>k\<in>A. (u,k) \<in> D" and right_slots: "\<forall>k\<in>B. (u,k) \<in> D"
    using slots parts(8) by auto
  have left: "site_citation_at ?F u a d J A" by (rule site_citation_read_environment[OF parts(3) boundary source left_slots])
  have right: "site_citation_at ?F u b e L B" by (rule site_citation_read_environment[OF parts(4) boundary source right_slots])
  show ?thesis using ff art left right parts(2,5-9) unfolding native_site_link_at_def by blast
qed

lemma native_binding_table_read_environment:
  assumes table: "native_binding_table_at E u r V I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_binding_table_at (read_environment E U D) u r V I K"
proof (rule native_table_change_reader[OF table read_environment_formed[OF boundary]])
  fix R assume "artifact_at E u R"
  then show "artifact_at (read_environment E U D) u R" using source by (simp add: read_environment_uses_def)
next
  fix a q J A assume row: "native_application_at E u a (fst q) (snd q) J A" and sub: "A \<subseteq> K"
  have demands: "\<forall>k\<in>A. (u,k) \<in> D" using slots sub by blast
  show "native_application_at (read_environment E U D) u a (fst q) (snd q) J A"
    by (rule native_application_read_environment[OF row boundary source demands])
next
  fix a q J A z L B
  assume first: "native_application_at (read_environment E U D) u a (fst q) (snd q) J A"
    and second: "native_application_at (read_environment E U D) u a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B" using native_application_unique[OF first second] by (cases q; cases z) auto
qed

lemma native_discharge_table_read_environment:
  assumes table: "native_discharge_table_at E u r Q I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_discharge_table_at (read_environment E U D) u r Q I K"
proof (rule native_table_change_reader[OF table read_environment_formed[OF boundary]])
  fix R assume "artifact_at E u R"
  then show "artifact_at (read_environment E U D) u R" using source by (simp add: read_environment_uses_def)
next
  fix a q J A assume row: "native_site_link_at E u a (fst q) (snd q) J A" and sub: "A \<subseteq> K"
  have demands: "\<forall>k\<in>A. (u,k) \<in> D" using slots sub by blast
  show "native_site_link_at (read_environment E U D) u a (fst q) (snd q) J A"
    by (rule native_site_link_read_environment[OF row boundary source demands])
next
  fix a q J A z L B
  assume first: "native_site_link_at (read_environment E U D) u a (fst q) (snd q) J A"
    and second: "native_site_link_at (read_environment E U D) u a (fst z) (snd z) L B"
  show "q=z \<and> J=L \<and> A=B" using native_site_link_unique[OF first second] by (cases q; cases z) auto
qed

lemma native_binding_table_slots_bound:
  assumes "native_binding_table_at E u r V I K" "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  by (rule native_table_slots_bound[OF assms]; rule native_application_slots_bound; assumption)

lemma native_discharge_table_slots_bound:
  assumes "native_discharge_table_at E u r Q I K" "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  by (rule native_table_slots_bound[OF assms]; rule native_site_link_slots_bound; assumption)

lemma native_proof_node_slots_bound:
  assumes node: "native_proof_node_at E u r N Q I K" and slot: "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
  case (assertion R)
  then show ?thesis using slot by simp
next
  case (inference R ps c b p d C A V B L Q' J W)
  have reference: "site_citation_at E u c d C A"
    and bindings: "native_binding_table_at E u b (fset V) B L"
    and discharges: "native_discharge_table_at E u p Q' J W"
    and ks: "K=A \<union> L \<union> W"
    using inference by auto
  show ?thesis using slot ks site_citation_slots_bound[OF reference]
    native_binding_table_slots_bound[OF bindings] native_discharge_table_slots_bound[OF discharges] by auto
qed

lemma native_proof_node_read_environment:
  assumes node: "native_proof_node_at E u r N Q I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_proof_node_at (read_environment E U D) u r N Q I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have arts: "\<And>R. artifact_at E u R \<Longrightarrow> artifact_at ?F u R"
    using source by (simp add: read_environment_uses_def)
  show ?thesis
  proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
    case (assertion R)
    have art: "artifact_at ?F u R" by (rule arts) (use assertion in simp)
    have frame: "record_at R r [] []" using assertion by simp
    show ?thesis using native_proof_node_at.assertion[OF ff art frame] assertion by simp
  next
    case (inference R ps c b p d C A V B L Q' J W)
    have art: "artifact_at ?F u R" by (rule arts) (use inference in simp)
    have frame: "record_at R r ps [c,b,p]" and reference: "site_citation_at E u c d C A"
      and bindings: "native_binding_table_at E u b (fset V) B L"
      and discharges: "native_discharge_table_at E u p Q' J W"
      and ks: "K=A \<union> L \<union> W"
      using inference by auto
    have ca: "\<forall>k\<in>A. (u,k) \<in> D" and bl: "\<forall>k\<in>L. (u,k) \<in> D" and dw: "\<forall>k\<in>W. (u,k) \<in> D"
      using slots ks by auto
    have cite: "site_citation_at ?F u c d C A" by (rule site_citation_read_environment[OF reference boundary source ca])
    have bind: "native_binding_table_at ?F u b (fset V) B L" by (rule native_binding_table_read_environment[OF bindings boundary source bl])
    have discharge: "native_discharge_table_at ?F u p Q' J W" by (rule native_discharge_table_read_environment[OF discharges boundary source dw])
    have head: "insert r (set ps) \<inter> (C \<union> B \<union> J) = {}"
      and cb: "C \<inter> B = {}" and cj: "C \<inter> J = {}" and bj: "B \<inter> J = {}"
      and sk: "insert r (set ps \<union> C \<union> B \<union> J) \<inter> (A \<union> L \<union> W) = {}"
      using inference by auto
    have result: "native_proof_node_at ?F u r (Schema_Inference d V) Q'
      (insert r (set ps \<union> C \<union> B \<union> J)) (A \<union> L \<union> W)"
      by (rule native_proof_node_at.inference[OF ff art frame cite bind discharge head cb cj bj sk])
    show ?thesis using result inference by simp
  qed
qed

end
