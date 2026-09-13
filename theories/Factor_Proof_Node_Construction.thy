theory Factor_Proof_Node_Construction
  imports Factor_Proof_Table_Copy Factor_Record_Syntax
begin

section \<open>Complete finite syntax for inference metadata\<close>

locale inference_node_syntax_construction =
  fixes d :: "local_address option definition_site"
    and V :: "(local_address option definition_site\<times>factor_term) fset"
    and D :: "(local_address option definition_site\<times>local_address option definition_site) set"
    and Rb Rp :: exact_artifact
    and Lb Lp :: "(local_address\<times>exact_artifact) set"
    and Cb Cp :: "(local_address\<times>local_address option definition_site) set"
    and Ib Kb Ip Kp :: "local_address set"
  assumes address: "octets_formed (snd d)"
    and b: "exact_formed Rb" "bag_count (object_data Rb)=(\<lambda>_. 0)"
      "[]\<in>rra_carrier (object_structure Rb)" "reference_table_formed Lb Cb"
      "rra_carrier (object_structure Rb)=Ib\<union>Kb" "Ib\<inter>Kb={}"
      "Kb=rel_dom Lb\<union>rel_dom Cb" "rel_ran Cb=rel_dom (fset V)"
      "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u Rb \<longrightarrow> syntax_references E u Lb Cb \<longrightarrow>
        native_binding_table_at E u [] (fset V) Ib Kb"
    and p: "exact_formed Rp" "bag_count (object_data Rp)=(\<lambda>_. 0)"
      "[]\<in>rra_carrier (object_structure Rp)" "reference_table_formed Lp Cp"
      "rra_carrier (object_structure Rp)=Ip\<union>Kp" "Ip\<inter>Kp={}"
      "Kp=rel_dom Lp\<union>rel_dom Cp" "rel_ran Cp=rel_dom D\<union>rel_ran D"
      "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u Rp \<longrightarrow> syntax_references E u Lp Cp \<longrightarrow>
        native_discharge_table_at E u [] D Ip Kp"
begin

abbreviation clause_syntax where "clause_syntax \<equiv> external_occurrence_syntax (snd d)"
abbreviation clause_interior :: "local_address set" where "clause_interior \<equiv> {[],[5]}"
abbreviation clause_slots :: "local_address set" where "clause_slots \<equiv> {[4]}"
abbreviation callees where "callees \<equiv> [{([4],d)},Cb,Cp]"
abbreviation literals where "literals \<equiv> [{},Lb,Lp]"
abbreviation interiors where "interiors \<equiv> [clause_interior,Ib,Ip]"
abbreviation slots where "slots \<equiv> [clause_slots,Kb,Kp]"
abbreviation artifacts where "artifacts \<equiv> [clause_syntax,Rb,Rp]"

lemma cf: "exact_formed clause_syntax" by (rule external_occurrence_syntax_formed[OF address])
lemma profile: "reference_table_formed {} {([4],d)}"
    by (rule reference_table_callees) (simp_all add: single_valued_def)
lemma cc: "rra_carrier (object_structure clause_syntax)=clause_interior\<union>clause_slots"
    by (auto simp: external_occurrence_syntax_def)
lemma cs: "clause_interior\<inter>clause_slots={}" by auto
lemma cd: "clause_slots=rel_dom ({} :: (local_address\<times>exact_artifact) set)\<union>rel_dom {([4],d)}"
    by (auto simp: rel_dom_def)
sublocale assembled: record_syntax_construction artifacts interiors slots literals callees
  proof (rule record_syntax_construction.intro)
    show "\<forall>R\<in>set artifacts. exact_formed R" using cf b(1) p(1) by simp
    show "\<forall>R\<in>set artifacts. bag_count (object_data R)=(\<lambda>_. 0)"
      using b(2) p(2) external_occurrence_syntax_properties(2) by simp
    show "\<forall>R\<in>set artifacts. []\<in>rra_carrier (object_structure R)"
      using b(3) p(3) external_occurrence_syntax_properties(1) by simp
    show "length interiors=length artifacts" "length slots=length artifacts"
      "length literals=length artifacts" "length callees=length artifacts" by simp_all
    show "\<forall>i<length artifacts. rra_carrier (object_structure (artifacts!i))=interiors!i\<union>slots!i"
      using cc b(5) p(5) by (auto simp: less_Suc_eq)
    show "\<forall>i<length artifacts. interiors!i\<inter>slots!i={}"
      using cs b(6) p(6) by (auto simp: less_Suc_eq)
    show "\<forall>i<length artifacts. slots!i=rel_dom (literals!i)\<union>rel_dom (callees!i)"
      using cd b(7) p(7) by (auto simp: less_Suc_eq)
    show "\<forall>i<length artifacts. reference_table_formed (literals!i) (callees!i)"
      using profile b(4) p(4) by (auto simp: less_Suc_eq)
  qed
lemma br: "rel_dom Lb\<union>rel_dom Cb\<subseteq>rra_carrier (object_structure Rb)" using b(5,7) by blast
lemma pr: "rel_dom Lp\<union>rel_dom Cp\<subseteq>rra_carrier (object_structure Rp)" using p(5,7) by blast
lemma bd: "rel_dom (fset V)\<subseteq>rel_ran Cb" using b(8) by simp
lemma pd: "rel_dom D\<union>rel_ran D\<subseteq>rel_ran Cp" using p(8) by simp
lemma cite_range: "rel_ran {([4],d)}={d}" by (auto simp: rel_ran_def)
lemma deps: "rel_ran assembled.callees=insert d (rel_dom (fset V)\<union>rel_dom D\<union>rel_ran D)"
    using assembled.reference_range by (simp add: cite_range b(8) p(8) Un_assoc)
lemma recover: "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u assembled.framed \<longrightarrow>
      syntax_references E u assembled.literals assembled.callees \<longrightarrow>
      native_proof_node_at E u [] (Schema_Inference d V) D assembled.interior assembled.slots"
  proof (intro allI impI)
    fix E u assume ef: "environment_formed E" and art: "artifact_at E u assembled.framed"
      and refs: "syntax_references E u assembled.literals assembled.callees"
    have caddr: "finite_addressing (rra_carrier (object_structure clause_syntax)) (syntax_branch 0)"
      using assembled.child_addressing[of 0] by simp
    have cread: "object_reads_agree (push_object (syntax_branch 0) clause_syntax) assembled.framed
      (image (syntax_branch 0) (rra_carrier (object_structure clause_syntax)))"
      using assembled.frame.record_child_reads[of 0] by simp
    have centry: "(syntax_branch 0 [4],d)\<in>assembled.callees"
      by (rule syntax_forest_table_member[where i=0]) simp_all
    have cite: "site_citation_at E u (syntax_branch 0 []) d (image (syntax_branch 0) clause_interior) {syntax_branch 0 [4]}"
      by (rule external_syntax_embedded_site[OF ef art address caddr cread refs centry])
    have baddr: "finite_addressing (rra_carrier (object_structure Rb)) (syntax_branch 1)"
      using assembled.child_addressing[of 1] by simp
    have bread: "object_reads_agree (push_object (syntax_branch 1) Rb) assembled.framed
      (image (syntax_branch 1) (rra_carrier (object_structure Rb)))"
      using assembled.frame.record_child_reads[of 1] by simp
    have brefs: "syntax_references E u (map_slot_keys (syntax_branch 1) Lb) (map_slot_keys (syntax_branch 1) Cb)"
      using assembled.child_references[OF refs, of 1] by simp
    have binding_read: "native_binding_table_at E u (syntax_branch 1 []) (fset V)
      (image (syntax_branch 1) Ib) (image (syntax_branch 1) Kb)"
      by (rule compiled_binding_table_embedded[OF b(1) br b(9)[rule_format] bd ef art
          syntax_branch_injective baddr bread brefs])
    have paddr: "finite_addressing (rra_carrier (object_structure Rp)) (syntax_branch 2)"
      using assembled.child_addressing[of 2] by simp
    have pread: "object_reads_agree (push_object (syntax_branch 2) Rp) assembled.framed
      (image (syntax_branch 2) (rra_carrier (object_structure Rp)))"
      using assembled.frame.record_child_reads[of 2] by simp
    have prefs: "syntax_references E u (map_slot_keys (syntax_branch 2) Lp) (map_slot_keys (syntax_branch 2) Cp)"
      using assembled.child_references[OF refs, of 2] by simp
    have discharge_read: "native_discharge_table_at E u (syntax_branch 2 []) D
      (image (syntax_branch 2) Ip) (image (syntax_branch 2) Kp)"
      by (rule compiled_discharge_table_embedded[OF p(1) pr p(9)[rule_format] pd ef art
          syntax_branch_injective paddr pread prefs])
    let ?C = "image (syntax_branch 0) clause_interior"
    let ?B = "image (syntax_branch 1) Ib"
    let ?P = "image (syntax_branch 2) Ip"
    let ?A = "{syntax_branch 0 [4]}"
    let ?L = "image (syntax_branch 1) Kb"
    let ?W = "image (syntax_branch 2) Kp"
    have rec: "record_at assembled.framed [] assembled.frame.ports
      [syntax_branch 0 [],syntax_branch 1 [],syntax_branch 2 []]"
      using assembled.frame.record_read by (simp add: upt_conv_Cons numeral_2_eq_2)
    have header: "insert [] (set assembled.frame.ports)\<inter>(?C\<union>?B\<union>?P)={}"
      using assembled.header_separate by (simp add: syntax_forest_three_positions Un_assoc)
    have cb: "?C\<inter>?B={}" using assembled.child_interiors_separate[of 0 1] by simp
    have cp: "?C\<inter>?P={}" using assembled.child_interiors_separate[of 0 2] by simp
    have bp: "?B\<inter>?P={}" using assembled.child_interiors_separate[of 1 2] by simp
    have separate: "insert [] (set assembled.frame.ports\<union>?C\<union>?B\<union>?P)\<inter>(?A\<union>?L\<union>?W)={}"
      using assembled.boundary by (simp add: syntax_forest_three_positions Un_assoc)
    have native: "native_proof_node_at E u [] (Schema_Inference d V) D
      (insert [] (set assembled.frame.ports\<union>?C\<union>?B\<union>?P)) (?A\<union>?L\<union>?W)"
      by (rule native_proof_node_at.inference[OF ef art rec cite binding_read discharge_read header cb cp bp separate])
    show "native_proof_node_at E u [] (Schema_Inference d V) D assembled.interior assembled.slots"
      using native by (simp add: syntax_forest_three_positions Un_assoc)
  qed
theorem total:
  "\<exists>R L C I K. exact_formed R \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
    []\<in>rra_carrier (object_structure R) \<and> reference_table_formed L C \<and>
    rra_carrier (object_structure R)=I\<union>K \<and> I\<inter>K={} \<and>
    K=rel_dom L\<union>rel_dom C \<and>
    rel_ran C=insert d (rel_dom (fset V)\<union>rel_dom D\<union>rel_ran D) \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_proof_node_at E u [] (Schema_Inference d V) D I K)"
proof -
  show ?thesis
    by (rule exI[of _ assembled.framed], rule exI[of _ assembled.literals], rule exI[of _ assembled.callees],
        rule exI[of _ assembled.interior], rule exI[of _ assembled.slots])
       (use assembled.frame.record_formed assembled.frame.record_counts assembled.frame.record_root
          assembled.reference_table assembled.carrier assembled.boundary assembled.reference_domain deps recover in blast)
qed

end

theorem inference_node_syntax_total:
  fixes d :: "local_address option definition_site"
    and V :: "(local_address option definition_site \<times> factor_term) fset"
    and D :: "(local_address option definition_site \<times> local_address option definition_site) set"
  assumes address: "octets_formed (snd d)" and bindings: "single_valued (fset V)"
    and terms: "\<forall>a t. (a,t)\<in>fset V \<longrightarrow> octets_formed (snd a) \<and> term_formed t"
    and dfinite: "finite D" and dfunctional: "single_valued D"
    and endpoints: "\<forall>s n. (s,n)\<in>D \<longrightarrow> octets_formed (snd s) \<and> octets_formed (snd n)"
  shows "\<exists>R L C I K. exact_formed R \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
    []\<in>rra_carrier (object_structure R) \<and> reference_table_formed L C \<and>
    rra_carrier (object_structure R)=I\<union>K \<and> I\<inter>K={} \<and>
    K=rel_dom L\<union>rel_dom C \<and>
    rel_ran C=insert d (rel_dom (fset V)\<union>rel_dom D\<union>rel_ran D) \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_proof_node_at E u [] (Schema_Inference d V) D I K)"
proof -
  obtain Rb Lb Cb Ib Kb where b:
    "exact_formed Rb" "bag_count (object_data Rb)=(\<lambda>_. 0)"
    "[]\<in>rra_carrier (object_structure Rb)" "reference_table_formed Lb Cb"
    "rra_carrier (object_structure Rb)=Ib\<union>Kb" "Ib\<inter>Kb={}"
    "Kb=rel_dom Lb\<union>rel_dom Cb" "rel_ran Cb=rel_dom (fset V)"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u Rb \<longrightarrow> syntax_references E u Lb Cb \<longrightarrow>
      native_binding_table_at E u [] (fset V) Ib Kb"
    using binding_table_syntax_total[OF finite_fset bindings terms] by blast
  obtain Rp Lp Cp Ip Kp where p:
    "exact_formed Rp" "bag_count (object_data Rp)=(\<lambda>_. 0)"
    "[]\<in>rra_carrier (object_structure Rp)" "reference_table_formed Lp Cp"
    "rra_carrier (object_structure Rp)=Ip\<union>Kp" "Ip\<inter>Kp={}"
    "Kp=rel_dom Lp\<union>rel_dom Cp" "rel_ran Cp=rel_dom D\<union>rel_ran D"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u Rp \<longrightarrow> syntax_references E u Lp Cp \<longrightarrow>
      native_discharge_table_at E u [] D Ip Kp"
    using discharge_table_syntax_total[OF dfinite dfunctional endpoints] by blast
  interpret construction: inference_node_syntax_construction d V D Rb Rp Lb Lp Cb Cp Ib Kb Ip Kp
    by (rule inference_node_syntax_construction.intro[OF address b p])
  show ?thesis by (rule construction.total)
qed

section \<open>An assertion has an explicit complete empty record\<close>

definition assertion_node_syntax :: exact_artifact where
  "assertion_node_syntax=record_wrapper (syntax_forest []) [] [] []"

theorem assertion_node_syntax_properties:
  "exact_formed assertion_node_syntax"
  "bag_count (object_data assertion_node_syntax)=(\<lambda>_. 0)"
  "rra_carrier (object_structure assertion_node_syntax)={[]}"
  "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u assertion_node_syntax \<longrightarrow>
    native_proof_node_at E u [] Schema_Assertion {} {[]} {}"
proof -
  interpret frame: syntax_family_construction "[]" by (rule syntax_family_construction.intro) simp_all
  have carrier: "rra_carrier (object_structure frame.record_framed)={[]}"
    by (simp add: record_wrapper_def attach_structure_def record_structure_def
      syntax_forest.simps empty_artifact_def family_ports_def)
  have rec: "record_at frame.record_framed [] [] []" using frame.record_read by (simp add: family_ports_def)
  have every: "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u frame.record_framed \<longrightarrow>
      native_proof_node_at E u [] Schema_Assertion {} {[]} {}"
    by (intro allI impI) (rule native_proof_node_at.assertion[OF _ _ rec]; assumption)
  have same: "assertion_node_syntax=frame.record_framed"
    by (simp add: assertion_node_syntax_def family_ports_def)
  show "exact_formed assertion_node_syntax"
    "bag_count (object_data assertion_node_syntax)=(\<lambda>_. 0)"
    "rra_carrier (object_structure assertion_node_syntax)={[]}"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u assertion_node_syntax \<longrightarrow>
      native_proof_node_at E u [] Schema_Assertion {} {[]} {}"
    using frame.record_formed frame.record_counts carrier every by (simp_all only: same)
qed

theorem assertion_node_syntax_total:
  "\<exists>R. exact_formed R \<and> bag_count (object_data R)=(\<lambda>_. 0) \<and>
    rra_carrier (object_structure R)={[]} \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow>
      native_proof_node_at E u [] Schema_Assertion {} {[]} {})"
  using assertion_node_syntax_properties by blast

text \<open>
  Each inference has an actual three-field record with a clause citation,
  complete bindings, and complete premise links. All reference requirements are
  exactly the cited clause, binding keys, premise sockets, and proof targets.
  The theorem supplies syntax before references are installed; its recovery
  statement uses the eventual environment's actual references. Assertions
  contain an explicit empty record. Neither constructor assumes proof validity.
\<close>

end
