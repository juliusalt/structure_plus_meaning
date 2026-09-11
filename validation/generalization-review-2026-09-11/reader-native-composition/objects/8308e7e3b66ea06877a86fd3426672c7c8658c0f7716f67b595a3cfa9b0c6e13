theory Factor_Proof_Tables
  imports Factor_Proof_Row_Copy Factor_Table_Syntax Factor_Proof_Metadata
begin

section \<open>Binding tables for arbitrary finite sets of formed assignments\<close>

locale binding_table_construction =
  fixes bs :: "(local_address option definition_site \<times> factor_term) list"
  assumes keys: "distinct (map fst bs)"
    and rows_formed: "\<forall>q\<in>set bs. octets_formed (snd (fst q)) \<and> term_formed (snd q)"
begin

sublocale table: table_syntax_construction bs
    "\<lambda>q. binding_row_syntax (snd (fst q)) (snd q)"
    "\<lambda>q. binding_row_interior (snd q)" "\<lambda>q. binding_row_slots (snd q)"
    "\<lambda>q. binding_row_literals (snd q)" "\<lambda>q. {([2,4],fst q)}"
  by (rule table_syntax_construction.intro[OF keys])
     (use rows_formed in \<open>auto intro: binding_row_formed binding_row_reference_table
       simp: binding_row_carrier binding_row_boundary binding_row_reference_domain\<close>)

theorem recovers:
  assumes ef: "environment_formed E" and art: "artifact_at E u table.framed"
    and refs: "syntax_references E u table.literals table.callees"
  shows "native_binding_table_at E u [] (set bs) table.table_interior table.table_slots"
proof -
  have row_reads: "\<forall>i<length bs. native_application_at E u (syntax_branch i [])
    (fst (bs!i)) (snd (bs!i)) (syntax_branch i ` binding_row_interior (snd (bs!i)))
      (syntax_branch i ` binding_row_slots (snd (bs!i)))"
  proof (intro allI impI)
    fix i assume index: "i < length bs"
    let ?q = "bs!i"
    let ?R = "binding_row_syntax (snd (fst ?q)) (snd ?q)"
    have row: "octets_formed (snd (fst ?q))" "term_formed (snd ?q)"
      using rows_formed nth_mem[OF index] by blast+
    have formed: "exact_formed ?R" by (rule binding_row_formed[OF row])
    have addressing: "finite_addressing (rra_carrier (object_structure ?R)) (syntax_branch i)"
      by (rule syntax_branch_addressing[OF formed])
    have reads: "object_reads_agree (push_object (syntax_branch i) ?R) table.framed
      (syntax_branch i ` rra_carrier (object_structure ?R))"
      using table.frame.child_reads[of i] index by simp
    have left: "map_slot_keys (syntax_branch i) (binding_row_literals (snd ?q)) \<subseteq> table.literals"
      using syntax_forest_table_child[of i "map (\<lambda>q. binding_row_literals (snd q)) bs"] index by simp
    have right: "map_slot_keys (syntax_branch i) {([2,4],fst ?q)} \<subseteq> table.callees"
      using syntax_forest_table_child[of i "map (\<lambda>q. {([2,4],fst q)}) bs"] index by simp
    have child_refs: "syntax_references E u (map_slot_keys (syntax_branch i) (binding_row_literals (snd ?q)))
      (map_slot_keys (syntax_branch i) {([2,4],fst ?q)})"
      by (rule syntax_references_mono[OF refs left right])
    show "native_application_at E u (syntax_branch i []) (fst ?q) (snd ?q)
      (syntax_branch i ` binding_row_interior (snd ?q)) (syntax_branch i ` binding_row_slots (snd ?q))"
      by (rule binding_row_embedded[OF row ef art syntax_branch_injective addressing reads child_refs])
  qed
  show ?thesis
    by (rule table.recovers[OF ef art row_reads])
       (auto dest: native_application_unique intro: prod_eqI)
qed

lemma reference_range: "rel_ran table.callees=rel_dom (set bs)"
  using table.reference_range by (auto simp: rel_ran_def rel_dom_def)

end

section \<open>Premise-link tables retain actual source and target sites\<close>

locale discharge_table_construction =
  fixes ds :: "(local_address option definition_site \<times> local_address option definition_site) list"
  assumes keys: "distinct (map fst ds)"
    and rows_formed: "\<forall>q\<in>set ds. octets_formed (snd (fst q)) \<and> octets_formed (snd (snd q))"
begin

sublocale table: table_syntax_construction ds
    "\<lambda>q. discharge_row_syntax (snd (fst q)) (snd (snd q))"
    "\<lambda>q. discharge_row_interior" "\<lambda>q. discharge_row_slots"
    "\<lambda>q. {}" "\<lambda>q. {([2,4],fst q),([3,4],snd q)}"
  by (rule table_syntax_construction.intro[OF keys])
     (use rows_formed in \<open>auto intro: discharge_row_formed
       simp: discharge_row_carrier discharge_row_boundary discharge_row_reference_table discharge_row_reference_domain\<close>)

theorem recovers:
  assumes ef: "environment_formed E" and art: "artifact_at E u table.framed"
    and refs: "syntax_references E u table.literals table.callees"
  shows "native_discharge_table_at E u [] (set ds) table.table_interior table.table_slots"
proof -
  have row_reads: "\<forall>i<length ds. native_site_link_at E u (syntax_branch i [])
    (fst (ds!i)) (snd (ds!i)) (syntax_branch i ` discharge_row_interior)
      (syntax_branch i ` discharge_row_slots)"
  proof (intro allI impI)
    fix i assume index: "i < length ds"
    let ?q = "ds!i"
    let ?R = "discharge_row_syntax (snd (fst ?q)) (snd (snd ?q))"
    have row: "octets_formed (snd (fst ?q))" "octets_formed (snd (snd ?q))"
      using rows_formed nth_mem[OF index] by blast+
    have formed: "exact_formed ?R" by (rule discharge_row_formed[OF row])
    have addressing: "finite_addressing (rra_carrier (object_structure ?R)) (syntax_branch i)"
      by (rule syntax_branch_addressing[OF formed])
    have reads: "object_reads_agree (push_object (syntax_branch i) ?R) table.framed
      (syntax_branch i ` rra_carrier (object_structure ?R))"
      using table.frame.child_reads[of i] index by simp
    have right: "map_slot_keys (syntax_branch i) {([2,4],fst ?q),([3,4],snd ?q)} \<subseteq> table.callees"
      using syntax_forest_table_child[of i "map (\<lambda>q. {([2,4],fst q),([3,4],snd q)}) ds"] index by simp
    have child_refs: "syntax_references E u {} (map_slot_keys (syntax_branch i) {([2,4],fst ?q),([3,4],snd ?q)})"
      by (rule syntax_references_mono[OF refs _ right]) simp
    show "native_site_link_at E u (syntax_branch i []) (fst ?q) (snd ?q)
      (syntax_branch i ` discharge_row_interior) (syntax_branch i ` discharge_row_slots)"
      by (rule discharge_row_embedded[OF row ef art syntax_branch_injective addressing reads child_refs])
  qed
  show ?thesis
    by (rule table.recovers[OF ef art row_reads])
       (auto dest: native_site_link_unique intro: prod_eqI)
qed

lemma reference_range: "rel_ran table.callees=rel_dom (set ds) \<union> rel_ran (set ds)"
proof -
  have each: "\<And>q. rel_ran {([2,4],fst q),([3,4],snd q)} = {fst q,snd q}"
    by (auto simp: rel_ran_def)
  have range: "rel_ran table.callees = (\<Union>q\<in>set ds. {fst q,snd q})"
    using table.reference_range by (simp only: each)
  show ?thesis unfolding range
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> (\<Union>q\<in>set ds. {fst q,snd q})"
    then show "x \<in> rel_dom (set ds) \<union> rel_ran (set ds)"
      by (auto simp: rel_dom_def rel_ran_def)
  next
    fix x assume "x \<in> rel_dom (set ds) \<union> rel_ran (set ds)"
    then obtain y where entry: "(x,y) \<in> set ds \<or> (y,x) \<in> set ds"
      by (auto simp: rel_dom_def rel_ran_def)
    have left: "(x,y) \<in> set ds \<Longrightarrow> x \<in> (\<Union>q\<in>set ds. {fst q,snd q})"
      by (rule UN_I[where a="(x,y)"]) auto
    have right: "(y,x) \<in> set ds \<Longrightarrow> x \<in> (\<Union>q\<in>set ds. {fst q,snd q})"
      by (rule UN_I[where a="(y,x)"]) auto
    show "x \<in> (\<Union>q\<in>set ds. {fst q,snd q})" using entry left right by blast
  qed
qed

end

section \<open>Finite functional tables admit a complete row enumeration\<close>

theorem binding_table_syntax_total:
  fixes V :: "(local_address option definition_site \<times> factor_term) set"
  assumes fin: "finite V" and sv: "single_valued V"
    and rows: "\<forall>d t. (d,t) \<in> V \<longrightarrow> octets_formed (snd d) \<and> term_formed t"
  shows "\<exists>R L C I K. exact_formed R \<and> bag_count (object_data R) = (\<lambda>_. 0) \<and>
    [] \<in> rra_carrier (object_structure R) \<and> reference_table_formed L C \<and>
    rra_carrier (object_structure R) = I \<union> K \<and> I \<inter> K = {} \<and>
    K=rel_dom L \<union> rel_dom C \<and> rel_ran C=rel_dom V \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_binding_table_at E u [] V I K)"
proof -
  obtain bs where enumeration: "set bs=V" "distinct (map fst bs)"
    using finite_keyed_enumeration[OF fin sv] by blast
  have formed: "\<forall>q\<in>set bs. octets_formed (snd (fst q)) \<and> term_formed (snd q)"
    using rows enumeration(1) by auto
  interpret construction: binding_table_construction bs
    by (rule binding_table_construction.intro[OF enumeration(2) formed])
  show ?thesis
    by (rule exI[of _ construction.table.framed], rule exI[of _ construction.table.literals],
        rule exI[of _ construction.table.callees], rule exI[of _ construction.table.table_interior],
        rule exI[of _ construction.table.table_slots])
       (use construction.table.frame.formed construction.table.frame.counts construction.table.frame.root
          construction.table.reference_table construction.table.carrier construction.table.boundary
          construction.table.reference_domain construction.reference_range construction.recovers enumeration(1) in auto)
qed

theorem discharge_table_syntax_total:
  fixes D :: "(local_address option definition_site \<times> local_address option definition_site) set"
  assumes fin: "finite D" and sv: "single_valued D"
    and rows: "\<forall>s n. (s,n) \<in> D \<longrightarrow> octets_formed (snd s) \<and> octets_formed (snd n)"
  shows "\<exists>R L C I K. exact_formed R \<and> bag_count (object_data R) = (\<lambda>_. 0) \<and>
    [] \<in> rra_carrier (object_structure R) \<and> reference_table_formed L C \<and>
    rra_carrier (object_structure R) = I \<union> K \<and> I \<inter> K = {} \<and>
    K=rel_dom L \<union> rel_dom C \<and> rel_ran C=rel_dom D \<union> rel_ran D \<and>
    (\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u R \<longrightarrow> syntax_references E u L C \<longrightarrow>
      native_discharge_table_at E u [] D I K)"
proof -
  obtain ds where enumeration: "set ds=D" "distinct (map fst ds)"
    using finite_keyed_enumeration[OF fin sv] by blast
  have formed: "\<forall>q\<in>set ds. octets_formed (snd (fst q)) \<and> octets_formed (snd (snd q))"
    using rows enumeration(1) by auto
  interpret construction: discharge_table_construction ds
    by (rule discharge_table_construction.intro[OF enumeration(2) formed])
  show ?thesis
    by (rule exI[of _ construction.table.framed], rule exI[of _ construction.table.literals],
        rule exI[of _ construction.table.callees], rule exI[of _ construction.table.table_interior],
        rule exI[of _ construction.table.table_slots])
       (use construction.table.frame.formed construction.table.frame.counts construction.table.frame.root
          construction.table.reference_table construction.table.carrier construction.table.boundary
          construction.table.reference_domain construction.reference_range construction.recovers enumeration(1) in auto)
qed

text \<open>
  Every finite functional assignment or premise-link relation has a native
  table, including the empty relation. Its actual sites are explicit references;
  term targets are separate literal requirements. Every physical position is
  accounted for by the recovered interior or reference slots. Construction
  assumes no derivability or truth.
\<close>

end
