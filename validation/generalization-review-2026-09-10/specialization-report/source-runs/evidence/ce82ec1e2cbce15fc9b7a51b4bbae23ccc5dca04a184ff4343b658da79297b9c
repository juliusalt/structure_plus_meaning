theory Factor_Presentation_Restriction
  imports Factor_Presentation_Dependencies
begin

section \<open>Retaining a pattern's complete source and literal boundary\<close>

lemma term_quoted_has_artifact:
  assumes "term_quoted_at E u r t I K"
  shows "\<exists>R. artifact_at E u R"
  using assms by (cases rule: term_quoted_at.cases) auto

lemma pattern_quoted_has_artifact:
  assumes "pattern_quoted_at E u V r p I K"
  shows "\<exists>R. artifact_at E u R"
  using assms by (cases rule: pattern_quoted_at.cases) (auto dest: term_quoted_has_artifact)

lemma term_quoted_read_environment:
  assumes quote: "term_quoted_at E u r t I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "term_quoted_at (read_environment E U D) u r t I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  show ?thesis using quote source slots
  proof (induction rule: term_quoted_at.induct)
    case (target u R r c I t)
    have art: "artifact_at ?F u R" using target.hyps(2) target.prems(1) by (simp add: read_environment_uses_def)
    have interp: "interpret_citation ?F u c t"
      using read_environment_citation[OF target.prems] target.hyps(5) by simp
    show ?case by (rule term_quoted_at.target[OF ff art target.hyps(3,4) interp])
  next
    case (pair u R r ps l q x L A y Q B)
    have art: "artifact_at ?F u R" using pair.hyps(2) pair.prems(1) by (simp add: read_environment_uses_def)
    have left_slots: "\<forall>k\<in>A. (u,k) \<in> D" and right_slots: "\<forall>k\<in>B. (u,k) \<in> D"
      using pair.prems(2) by auto
    have left: "term_quoted_at ?F u l x L A" by (rule pair.IH(1)[OF pair.prems(1) left_slots])
    have right: "term_quoted_at ?F u q y Q B" by (rule pair.IH(2)[OF pair.prems(1) right_slots])
    show ?case by (rule term_quoted_at.pair[OF ff art pair.hyps(3) left right pair.hyps(6-8)])
  next
    case (payload u R r v)
    have art: "artifact_at ?F u R"
      using payload.hyps(2) payload.prems(1) by (simp add: read_environment_uses_def)
    show ?case by (rule term_quoted_at.payload[OF ff art payload.hyps(3)])
  qed
qed

lemma pattern_quoted_read_environment:
  assumes quote: "pattern_quoted_at E u V r p I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "pattern_quoted_at (read_environment E U D) u V r p I K"
proof -
  let ?F = "read_environment E U D"
  obtain R where art: "artifact_at E u R" using pattern_quoted_has_artifact[OF quote] by blast
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have copied: "artifact_at ?F u R" using art source by (simp add: read_environment_uses_def)
  have reads: "object_reads_agree R R I"
    using pattern_quoted_carrier[OF quote art] by (auto simp: object_reads_agree_def)
  have literals: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values ?F u k"
    using slots read_environment_external_values[of u _ D E U] by auto
  show ?thesis by (rule pattern_quotation_embedding[OF quote art reads literals ff copied])
qed

lemma scoped_pattern_read_environment:
  assumes quote: "scoped_pattern_at E u r p I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "scoped_pattern_at (read_environment E U D) u r p I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps b q V J where parts:
    "artifact_at E u R" "record_at R r ps [b,q]" "binder_scope_at R b V"
    "pattern_quoted_at E u V q p J K" "V = pattern_variables p"
    "insert r (set ps) \<inter> (insert b V \<union> J) = {}" "insert b V \<inter> J = {}"
    "I = insert r (set ps \<union> insert b V \<union> J)" "I \<inter> K = {}"
    using quote by (auto simp: scoped_pattern_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have body: "pattern_quoted_at ?F u V q p J K"
    by (rule pattern_quoted_read_environment[OF parts(4) boundary source slots])
  show ?thesis using ff art body parts(2,3,5-9) unfolding scoped_pattern_at_def by blast
qed

lemma prospective_call_read_environment:
  assumes call: "prospective_call_at E u V r d p I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "prospective_call_at (read_environment E U D) u V r d p I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps c a cite C J A where parts:
    "artifact_at E u R" "record_at R r ps [c,a]" "citation_at R c cite C"
    "citation_location E u cite (fst d) (snd d)" "pattern_quoted_at E u V a p J A"
    "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
    "I = insert r (set ps \<union> C \<union> J)" "K = citation_slots cite \<union> A" "I \<inter> (K \<union> V) = {}"
    using call by (auto simp: prospective_call_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have cite_slots: "\<forall>k\<in>citation_slots cite. (u,k) \<in> D" and arg_slots: "\<forall>k\<in>A. (u,k) \<in> D"
    using slots parts(9) by auto
  have loc: "citation_location ?F u cite (fst d) (snd d)"
    using read_environment_location[OF source cite_slots] parts(4) by simp
  have arg: "pattern_quoted_at ?F u V a p J A"
    by (rule pattern_quoted_read_environment[OF parts(5) boundary source arg_slots])
  show ?thesis using ff art loc arg parts(2,3,6-10) unfolding prospective_call_at_def by blast
qed

section \<open>Every family member remains readable and contributes its slots\<close>

lemma prospective_family_read_environment:
  assumes family: "prospective_family_at E u V r Q" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>prospective_family_slots E u V r. (u,k) \<in> D"
  shows "prospective_family_at (read_environment E U D) u V r Q"
    and "prospective_family_slots (read_environment E U D) u V r = prospective_family_slots E u V r"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R M where parts: "artifact_at E u R" "family_at R r M" "finite Q" "single_valued Q"
    "rel_dom Q = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)"
    using family by (auto simp: prospective_family_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have copied_ends: "family_endpoints ?F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have each: "\<And>a d p I K. a \<in> rel_ran M \<Longrightarrow> prospective_call_at E u V a d p I K \<Longrightarrow>
    prospective_call_at ?F u V a d p I K"
  proof -
    fix a d p I K assume member: "a \<in> rel_ran M" and call: "prospective_call_at E u V a d p I K"
    have demanded: "\<forall>k\<in>K. (u,k) \<in> D"
      using slots member ends prospective_call_slots_of_read[OF call]
      by (auto simp: prospective_family_slots_def)
    show "prospective_call_at ?F u V a d p I K"
      by (rule prospective_call_read_environment[OF call boundary source demanded])
  qed
  have calls: "\<forall>s a. (s,a) \<in> M \<longrightarrow>
    (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at ?F u V a d p I K)"
  proof (intro allI impI)
    fix s a assume socket: "(s,a) \<in> M"
    obtain d p I K where call: "(s,d,p) \<in> Q" "prospective_call_at E u V a d p I K"
      using parts(6) socket by blast
    have member: "a \<in> rel_ran M" by (rule rel_ranI[OF socket])
    have copied: "prospective_call_at ?F u V a d p I K" by (rule each[OF member call(2)])
    show "\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at ?F u V a d p I K"
      using call(1) copied by blast
  qed
  show "prospective_family_at ?F u V r Q"
    using ff art parts(2-5) calls unfolding prospective_family_at_def by blast
  have same_slots: "\<And>a. a \<in> rel_ran M \<Longrightarrow> prospective_call_slots ?F u V a = prospective_call_slots E u V a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain d p I K where call: "prospective_call_at E u V a d p I K" using parts(6) socket by blast
    have copied: "prospective_call_at ?F u V a d p I K" by (rule each[OF member call])
    show "prospective_call_slots ?F u V a = prospective_call_slots E u V a"
      by (simp only: prospective_call_slots_of_read[OF copied] prospective_call_slots_of_read[OF call])
  qed
  show "prospective_family_slots ?F u V r = prospective_family_slots E u V r"
    by (simp add: prospective_family_slots_def ends copied_ends same_slots)
qed


lemma native_material_read_environment:
  assumes material: "native_material_at E u V r M I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_material_at (read_environment E U D) u V r M I K"
proof -
  let ?F = "read_environment E U D"
  obtain R where art: "artifact_at E u R"
    using material by (auto simp: native_material_at_def pattern_record_at_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have copied: "artifact_at ?F u R" using art source by (simp add: read_environment_uses_def)
  have literals: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values ?F u k"
    using slots read_environment_external_values[of u _ D E U] by auto
  show ?thesis by (rule native_material_reinterpretation[OF material art literals ff copied])
qed

lemma native_premise_read_environment:
  assumes read: "native_premise_at E u V r p I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_premise_at (read_environment E U D) u V r p I K"
  using read
proof (cases rule: native_premise_at.cases)
  case (call d q)
  have "prospective_call_at (read_environment E U D) u V r d q I K"
    by (rule prospective_call_read_environment[OF call(2) boundary source slots])
  then show ?thesis using call by auto
next
  case (material M)
  have "native_material_at (read_environment E U D) u V r M I K"
    by (rule native_material_read_environment[OF material(2) boundary source slots])
  then show ?thesis using material by auto
qed

lemma native_premise_family_read_environment:
  assumes family: "native_premise_family_at E u V r Q C" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>native_premise_family_slots E u V r. (u,k) \<in> D"
  shows "native_premise_family_at (read_environment E U D) u V r Q C"
    and "native_premise_family_slots (read_environment E U D) u V r = native_premise_family_slots E u V r"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R M where parts: "artifact_at E u R" "family_at R r M"
    "finite (socket_sum Q C)" "single_valued (socket_sum Q C)" "rel_dom (socket_sum Q C)=rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow>
      (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at E u V a p I K)"
    using family by (auto simp: native_premise_family_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have copied_ends: "family_endpoints ?F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have each: "\<And>a p I K. a \<in> rel_ran M \<Longrightarrow> native_premise_at E u V a p I K \<Longrightarrow>
    native_premise_at ?F u V a p I K"
  proof -
    fix a p I K assume member: "a \<in> rel_ran M" and read: "native_premise_at E u V a p I K"
    have demanded: "\<forall>k\<in>K. (u,k) \<in> D"
      using slots member ends native_premise_slots_of_read[OF read]
      by (auto simp: native_premise_family_slots_def)
    show "native_premise_at ?F u V a p I K"
      by (rule native_premise_read_environment[OF read boundary source demanded])
  qed
  have reads: "\<forall>s a. (s,a) \<in> M \<longrightarrow>
    (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at ?F u V a p I K)"
  proof (intro allI impI)
    fix s a assume socket: "(s,a) \<in> M"
    obtain p I K where read: "(s,p) \<in> socket_sum Q C" "native_premise_at E u V a p I K"
      using parts(6) socket by blast
    have member: "a \<in> rel_ran M" by (rule rel_ranI[OF socket])
    have copied: "native_premise_at ?F u V a p I K" by (rule each[OF member read(2)])
    show "\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at ?F u V a p I K"
      using read(1) copied by blast
  qed
  show "native_premise_family_at ?F u V r Q C"
    using ff art parts(2-5) reads unfolding native_premise_family_at_def by blast
  have same_slots: "\<And>a. a \<in> rel_ran M \<Longrightarrow>
    native_premise_slots ?F u V a = native_premise_slots E u V a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain p I K where read: "native_premise_at E u V a p I K" using parts(6) socket by blast
    have copied: "native_premise_at ?F u V a p I K" by (rule each[OF member read])
    show "native_premise_slots ?F u V a = native_premise_slots E u V a"
      by (simp only: native_premise_slots_of_read[OF copied] native_premise_slots_of_read[OF read])
  qed
  show "native_premise_family_slots ?F u V r = native_premise_family_slots E u V r"
    by (simp add: native_premise_family_slots_def ends copied_ends same_slots)
qed

lemma native_schema_read_environment:
  assumes schema: "native_schema_at E u r S" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>native_schema_slots E u r. (u,k) \<in> D"
  shows "native_schema_at (read_environment E U D) u r S"
    and "native_schema_slots (read_environment E U D) u r = native_schema_slots E u r"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps b c m V I K where parts:
    "artifact_at E u R" "record_at R r ps [b,c,m]" "binder_scope_at R b V"
    "pattern_quoted_at E u V c (schema_conclusion S) I K"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)" "V = schema_variables S"
    "insert r (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {}"
    "insert b V \<inter> I = {}" "b \<noteq> m" "m \<notin> I"
    using schema by (auto simp: native_schema_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have exposed: "native_schema_slots E u r = pattern_slots E u V c \<union> native_premise_family_slots E u V m"
    by (rule native_schema_slots_from_fields[OF ef parts(1-3)])
  have head_slots: "\<forall>k\<in>K. (u,k) \<in> D"
    using slots exposed pattern_slots_of_quote[OF parts(4)] by simp
  have body_slots: "\<forall>k\<in>native_premise_family_slots E u V m. (u,k) \<in> D"
    using slots exposed by simp
  have head: "pattern_quoted_at ?F u V c (schema_conclusion S) I K"
    by (rule pattern_quoted_read_environment[OF parts(4) boundary source head_slots])
  have body: "native_premise_family_at ?F u V m (schema_premises S) (schema_material_premises S)"
    and same_body: "native_premise_family_slots ?F u V m = native_premise_family_slots E u V m"
    by (rule native_premise_family_read_environment[OF parts(5) boundary source body_slots])+
  show "native_schema_at ?F u r S" unfolding native_schema_at_def
    by (rule conjI[OF ff], rule exI[of _ R], rule exI[of _ ps],
        rule exI[of _ b], rule exI[of _ c], rule exI[of _ m],
        rule exI[of _ V], rule exI[of _ I], rule exI[of _ K])
       (use art head body parts(2,3,6-10) in blast)
  have same_head: "pattern_slots ?F u V c = pattern_slots E u V c"
    by (simp only: pattern_slots_of_quote[OF head] pattern_slots_of_quote[OF parts(4)])
  show "native_schema_slots ?F u r = native_schema_slots E u r"
    by (simp only: native_schema_slots_from_fields[OF ff art parts(2,3)] exposed same_head same_body)
qed


lemma native_schema_family_read_environment:
  assumes family: "native_schema_family_at E u r C" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>native_schema_family_slots E u r. (u,k) \<in> D"
  shows "native_schema_family_at (read_environment E U D) u r C"
    and "native_schema_family_slots (read_environment E U D) u r = native_schema_family_slots E u r"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R M where parts: "artifact_at E u R" "family_at R r M" "finite C" "single_valued C"
    "rel_dom C = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at E u a S)"
    using family by (auto simp: native_schema_family_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have copied_ends: "family_endpoints ?F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have demanded: "\<And>a. a \<in> rel_ran M \<Longrightarrow> \<forall>k\<in>native_schema_slots E u a. (u,k) \<in> D"
    using slots ends by (auto simp: native_schema_family_slots_def)
  have reads: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at ?F u a S)"
  proof (intro allI impI)
    fix s a assume socket: "(s,a) \<in> M"
    obtain S where schema: "(s,S) \<in> C" "native_schema_at E u a S" using parts(6) socket by blast
    have member: "a \<in> rel_ran M" by (rule rel_ranI[OF socket])
    have copied: "native_schema_at ?F u a S"
      by (rule native_schema_read_environment(1)[OF schema(2) boundary source demanded[OF member]])
    show "\<exists>S. (s,S) \<in> C \<and> native_schema_at ?F u a S" using schema(1) copied by blast
  qed
  show "native_schema_family_at ?F u r C"
    using ff art parts(2-5) reads unfolding native_schema_family_at_def by blast
  have same_slots: "\<And>a. a \<in> rel_ran M \<Longrightarrow> native_schema_slots ?F u a = native_schema_slots E u a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain S where schema: "native_schema_at E u a S" using parts(6) socket by blast
    show "native_schema_slots ?F u a = native_schema_slots E u a"
      by (rule native_schema_read_environment(2)[OF schema boundary source demanded[OF member]])
  qed
  show "native_schema_family_slots ?F u r = native_schema_family_slots E u r"
    by (simp add: native_schema_family_slots_def ends copied_ends same_slots)
qed

theorem native_definition_read_environment:
  assumes defn: "native_definition_at E u r p C" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>native_definition_slots E u r. (u,k) \<in> D"
  shows "native_definition_at (read_environment E U D) u r p C"
    and "native_definition_slots (read_environment E U D) u r = native_definition_slots E u r"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    "insert r (set ps) \<inter> (I \<union> {m}) = {}" "m \<notin> I"
    using defn by (auto simp: native_definition_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have exposed: "native_definition_slots E u r = scoped_pattern_slots E u i \<union> native_schema_family_slots E u m"
    by (rule native_definition_slots_from_fields[OF ef parts(1,2)])
  have interface_slots: "\<forall>k\<in>K. (u,k) \<in> D"
    using slots exposed scoped_pattern_slots_of_quote[OF parts(3)] by simp
  have body_slots: "\<forall>k\<in>native_schema_family_slots E u m. (u,k) \<in> D" using slots exposed by simp
  have interface: "scoped_pattern_at ?F u i p I K"
    by (rule scoped_pattern_read_environment[OF parts(3) boundary source interface_slots])
  have body: "native_schema_family_at ?F u m C"
    and same_body: "native_schema_family_slots ?F u m = native_schema_family_slots E u m"
    by (rule native_schema_family_read_environment[OF parts(4) boundary source body_slots])+
  show "native_definition_at ?F u r p C"
    using ff art interface body parts(2,5,6) unfolding native_definition_at_def by blast
  have same_interface: "scoped_pattern_slots ?F u i = scoped_pattern_slots E u i"
    by (simp only: scoped_pattern_slots_of_quote[OF interface] scoped_pattern_slots_of_quote[OF parts(3)])
  show "native_definition_slots ?F u r = native_definition_slots E u r"
    by (simp only: native_definition_slots_from_fields[OF ff art parts(2)] exposed same_interface same_body)
qed

lemma native_root_family_read_environment:
  assumes family: "native_root_family_at E u r Q" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U"
    and slots: "requested_slots E ({u} \<times> family_endpoints E u r) \<subseteq> D"
  shows "native_root_family_at (read_environment E U D) u r Q"
proof -
  let ?F = "read_environment E U D"
  let ?Q = "{u} \<times> family_endpoints E u r"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R M where parts: "artifact_at E u R" "family_at R r M" "finite Q" "single_valued Q"
    "rel_dom Q = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at E u a (fst d) (snd d))"
    using family by (auto simp: native_root_family_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have reads: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at ?F u a (fst d) (snd d))"
  proof (intro allI impI)
    fix s a assume socket: "(s,a) \<in> M"
    obtain d where loc: "(s,d) \<in> Q" "located_at E u a (fst d) (snd d)" using parts(6) socket by blast
    have member: "a \<in> rel_ran M" by (rule rel_ranI[OF socket])
    have request: "(u,a) \<in> ?Q" using member ends by simp
    obtain S cite I where citation: "artifact_at E u S" "citation_at S a cite I"
      "citation_location E u cite (fst d) (snd d)"
      using loc(2) by (auto simp: located_at_def)
    have demanded: "\<forall>k\<in>citation_slots cite. (u,k) \<in> D"
      using requested_citation_slots[OF request citation(1,2)] slots by blast
    have relocated: "citation_location ?F u cite (fst d) (snd d)"
      using read_environment_location[OF source demanded] citation(3) by simp
    have copied: "artifact_at ?F u S" using citation(1) source by (simp add: read_environment_uses_def)
    have result: "located_at ?F u a (fst d) (snd d)"
      using copied citation(2) relocated unfolding located_at_def by blast
    show "\<exists>d. (s,d) \<in> Q \<and> located_at ?F u a (fst d) (snd d)" using loc(1) result by blast
  qed
  show ?thesis using ff art parts(2-5) reads unfolding native_root_family_at_def by blast
qed

end
