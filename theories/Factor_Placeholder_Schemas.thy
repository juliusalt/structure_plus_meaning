theory Factor_Placeholder_Schemas
  imports Factor_Placeholder_Fill Factor_Presentation
begin

section \<open>The syntax readers above terms at the placeholder fill\<close>

text \<open>
  Every reader here reads an address of its artifact's carrier, so its use does not hold the empty artifact:
  at the fill it reads the same artifact (@{text artifact_at_placeholder_fill_read}). Each reading at the fill
  is E's with its patterns, material patterns, schemas and definitions mapped by the parametricity map at the
  placeholder's leaf map (@{const map_pattern_leaves}, @{const map_material_leaves}, @{const map_schema_leaves}
  at @{term "placeholder_leaf R"}), every socket, clause key, callee site, interior and slot kept. The readings
  are carried forward for every formed R, R equal to an artifact E holds elsewhere or the empty artifact itself;
  each is exact where E reads, closed by the reader's own uniqueness at the fill and never by the map's
  injectivity.
\<close>

lemma artifact_at_placeholder_fill_read:
  assumes formed: "environment_formed E" and held: "artifact_at E u S"
    and address: "r\<in>rra_carrier (object_structure S)"
  shows "artifact_at (placeholder_fill E R) u S"
  using artifact_at_placeholder_fill_carried[OF formed held, of R] placeholder_artifact_kept[OF address] by simp

lemma artifact_at_placeholder_fill_record:
  assumes "environment_formed E" "artifact_at E u S" "record_at S r ps xs"
  shows "artifact_at (placeholder_fill E R) u S"
  using record_interior_in_carrier[OF assms(3)] by (intro artifact_at_placeholder_fill_read[OF assms(1,2), of r]) auto

lemma artifact_at_placeholder_fill_family:
  assumes "environment_formed E" "artifact_at E u S" "family_at S r M"
  shows "artifact_at (placeholder_fill E R) u S"
  using family_interior_in_carrier[OF assms(3)] by (intro artifact_at_placeholder_fill_read[OF assms(1,2), of r]) auto

lemma socket_sum_map_relation_values:
  "socket_sum (map_relation_values f Q) (map_relation_values g C)=
    map_relation_values (map_sum f g) (socket_sum Q C)"
  by (simp add: socket_sum_def map_relation_values_def image_Un image_image split_def)

section \<open>Patterns\<close>

lemma pattern_quoted_not_placeholder:
  assumes quote: "pattern_quoted_at E u V r p I K"
  shows "\<not>artifact_at E u empty_artifact"
proof
  assume "artifact_at E u empty_artifact"
  from pattern_quoted_carrier[OF quote this] pattern_quoted_boundary[OF quote] show False
    by (auto simp: empty_artifact_def)
qed

theorem pattern_quoted_placeholder_fill:
  assumes R_formed: "exact_formed R" and quote: "pattern_quoted_at E u V r p I K"
  shows "pattern_quoted_at (placeholder_fill E R) u V r (map_pattern_leaves (placeholder_leaf R) p) I K"
  using quote
proof (induction rule: pattern_quoted_at.induct)
  case (variable S r a I)
  have art: "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF variable.hyps(1,2), of R]
      placeholder_artifact_citation[OF variable.hyps(3)] by simp
  show ?case
    using pattern_quoted_at.variable[OF placeholder_fill_formed[OF variable.hyps(1) R_formed] art
        variable.hyps(3-5)]
    by simp
next
  case (target r t I K)
  have tq: "term_quoted_at (placeholder_fill E R) u r (Target_Term (placeholder_target R t)) I K"
    using term_quoted_placeholder_fill[OF R_formed target.hyps(1)] by simp
  show ?case using pattern_quoted_at.target[OF tq target.hyps(2)] by simp
next
  case (pair S r ps l q p L A s Q B)
  have art: "artifact_at (placeholder_fill E R) u S"
    by (rule artifact_at_placeholder_fill_record[OF pair.hyps(1,2,3)])
  show ?case
    using pattern_quoted_at.pair[OF placeholder_fill_formed[OF pair.hyps(1) R_formed] art pair.hyps(3)
        pair.IH pair.hyps(6-8)]
    by simp
next
  case (payload r v I K)
  have tq: "term_quoted_at (placeholder_fill E R) u r (Payload_Term v) I K"
    using term_quoted_placeholder_fill[OF R_formed payload.hyps(1)] by simp
  show ?case using pattern_quoted_at.payload[OF tq payload.hyps(2)] by simp
qed

corollary pattern_quoted_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and quote: "pattern_quoted_at E u V r p I K"
  shows "pattern_quoted_at (placeholder_fill E R) u V r q J W \<longleftrightarrow>
    q=map_pattern_leaves (placeholder_leaf R) p \<and> J=I \<and> W=K"
  using pattern_quoted_placeholder_fill[OF assms]
  by (auto dest: pattern_quoted_unique[OF pattern_quoted_placeholder_fill[OF assms]])

theorem scoped_pattern_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "scoped_pattern_at E u r p I K"
  shows "scoped_pattern_at (placeholder_fill E R) u r (map_pattern_leaves (placeholder_leaf R) p) I K"
proof -
  obtain S ps b q V J where S: "environment_formed E" "artifact_at E u S" "record_at S r ps [b,q]"
      "binder_scope_at S b V" "pattern_quoted_at E u V q p J K" "V=pattern_variables p"
      "insert r (set ps) \<inter> (insert b V \<union> J) = {}" "insert b V \<inter> J = {}"
      "I = insert r (set ps \<union> insert b V \<union> J)" "I \<inter> K = {}"
    by (insert read[unfolded scoped_pattern_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  have vars: "V=pattern_variables (map_pattern_leaves (placeholder_leaf R) p)" using S(6) by simp
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3,4,7-10) vars
    pattern_quoted_placeholder_fill[OF R_formed S(5)]
  show ?thesis unfolding scoped_pattern_at_def by (intro exI conjI) (fact facts)+
qed

corollary scoped_pattern_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "scoped_pattern_at E u r p I K"
  shows "scoped_pattern_at (placeholder_fill E R) u r q J W \<longleftrightarrow>
    q=map_pattern_leaves (placeholder_leaf R) p \<and> J=I \<and> W=K"
  using scoped_pattern_placeholder_fill[OF assms]
  by (auto dest: scoped_pattern_unique[OF scoped_pattern_placeholder_fill[OF assms]])

section \<open>Pattern vectors and material patterns\<close>

theorem pattern_vector_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "pattern_vector_at E u V rs ps I K"
  shows "pattern_vector_at (placeholder_fill E R) u V rs (map (map_pattern_leaves (placeholder_leaf R)) ps) I K"
  using read
proof (induction rule: pattern_vector_at.induct)
  case empty
  show ?case using pattern_vector_at.empty[OF placeholder_fill_formed[OF empty R_formed]] by simp
next
  case (cons r p A B rs ps I K)
  show ?case
    using pattern_vector_at.cons[OF pattern_quoted_placeholder_fill[OF R_formed cons.hyps(1)] cons.IH
        cons.hyps(3,4)]
    by simp
qed

corollary pattern_vector_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "pattern_vector_at E u V rs ps I K"
  shows "pattern_vector_at (placeholder_fill E R) u V rs qs J W \<longleftrightarrow>
    qs=map (map_pattern_leaves (placeholder_leaf R)) ps \<and> J=I \<and> W=K"
  using pattern_vector_placeholder_fill[OF assms]
  by (auto dest: pattern_vector_unique[OF pattern_vector_placeholder_fill[OF assms]])

lemma pattern_record_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "pattern_record_at E u V r ps I K"
  shows "pattern_record_at (placeholder_fill E R) u V r (map (map_pattern_leaves (placeholder_leaf R)) ps) I K"
proof -
  obtain S ports roots J where S: "environment_formed E" "artifact_at E u S" "record_at S r ports roots"
      "pattern_vector_at E u V roots ps J K" "insert r (set ports) \<inter> J = {}"
      "I=insert r (set ports \<union> J)" "I \<inter> (K \<union> V) = {}"
    by (insert read[unfolded pattern_record_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3,5-7)
    pattern_vector_placeholder_fill[OF R_formed S(4)]
  show ?thesis unfolding pattern_record_at_def by (intro exI conjI) (fact facts)+
qed

theorem native_material_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_material_at E u V r M I K"
  shows "native_material_at (placeholder_fill E R) u V r (map_material_leaves (placeholder_leaf R) M) I K"
  using pattern_record_placeholder_fill[OF R_formed read[unfolded native_material_at_def]]
  by (simp add: native_material_at_def)

corollary native_material_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_material_at E u V r M I K"
  shows "native_material_at (placeholder_fill E R) u V r N J W \<longleftrightarrow>
    N=map_material_leaves (placeholder_leaf R) M \<and> J=I \<and> W=K"
  using native_material_placeholder_fill[OF assms]
  by (auto dest: native_material_unique[OF native_material_placeholder_fill[OF assms]])

section \<open>Prospective calls and premises\<close>

theorem prospective_call_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "prospective_call_at E u V r d p I K"
  shows "prospective_call_at (placeholder_fill E R) u V r d (map_pattern_leaves (placeholder_leaf R) p) I K"
proof -
  obtain S ps c a cite C J A where S: "environment_formed E" "artifact_at E u S" "record_at S r ps [c,a]"
      "citation_at S c cite C" "citation_location E u cite (fst d) (snd d)"
      "pattern_quoted_at E u V a p J A"
      "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
      "I = insert r (set ps \<union> C \<union> J)" "K = citation_slots cite \<union> A" "I \<inter> (K \<union> V) = {}"
    by (insert read[unfolded prospective_call_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3,4,7-11)
    citation_location_placeholder_fill[OF S(1,5)] pattern_quoted_placeholder_fill[OF R_formed S(6)]
  show ?thesis unfolding prospective_call_at_def by (intro exI conjI) (fact facts)+
qed

corollary prospective_call_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "prospective_call_at E u V r d p I K"
  shows "prospective_call_at (placeholder_fill E R) u V r e q J W \<longleftrightarrow>
    e=d \<and> q=map_pattern_leaves (placeholder_leaf R) p \<and> J=I \<and> W=K"
  using prospective_call_placeholder_fill[OF assms]
  by (auto dest: prospective_call_unique[OF prospective_call_placeholder_fill[OF assms]])

theorem native_premise_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_premise_at E u V r p I K"
  shows "native_premise_at (placeholder_fill E R) u V r
    (map_sum (map_prod id (map_pattern_leaves (placeholder_leaf R))) (map_material_leaves (placeholder_leaf R)) p)
    I K"
  using read
proof cases
  case (call d q)
  then show ?thesis using prospective_call_placeholder_fill[OF R_formed, of E u V r d q I K] by simp
next
  case (material M)
  then show ?thesis using native_material_placeholder_fill[OF R_formed, of E u V r M I K] by simp
qed

corollary native_premise_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_premise_at E u V r p I K"
  shows "native_premise_at (placeholder_fill E R) u V r q J W \<longleftrightarrow>
    q=map_sum (map_prod id (map_pattern_leaves (placeholder_leaf R))) (map_material_leaves (placeholder_leaf R)) p \<and>
    J=I \<and> W=K"
  using native_premise_placeholder_fill[OF assms]
  by (auto dest: native_premise_unique[OF native_premise_placeholder_fill[OF assms]])

theorem native_premise_family_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_premise_family_at E u V r Q C"
  shows "native_premise_family_at (placeholder_fill E R) u V r
    (map_relation_values (map_prod id (map_pattern_leaves (placeholder_leaf R))) Q)
    (map_relation_values (map_material_leaves (placeholder_leaf R)) C)"
proof -
  let ?f="map_prod id (map_pattern_leaves (placeholder_leaf R))" and ?g="map_material_leaves (placeholder_leaf R)"
  let ?F="placeholder_fill E R" and ?h="map_sum ?f ?g"
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S r M"
      "finite (socket_sum Q C)" "single_valued (socket_sum Q C)" "rel_dom (socket_sum Q C)=rel_dom M"
      "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at E u V a p I K)"
    by (insert read[unfolded native_premise_family_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at ?F u S" by (rule artifact_at_placeholder_fill_family[OF S(1-3)])
  have fin: "finite (map_relation_values ?h (socket_sum Q C))" using S(4) by simp
  have sv: "single_valued (map_relation_values ?h (socket_sum Q C))"
    by (rule map_relation_values_single_valued[OF S(5)])
  have dom: "rel_dom (map_relation_values ?h (socket_sum Q C))=rel_dom M" using S(6) by simp
  have rows: "\<forall>s a. (s,a) \<in> M \<longrightarrow>
      (\<exists>p I K. (s,p) \<in> map_relation_values ?h (socket_sum Q C) \<and> native_premise_at ?F u V a p I K)"
  proof (intro allI impI)
    fix s a assume "(s,a) \<in> M"
    then obtain p I K where row: "(s,p) \<in> socket_sum Q C" "native_premise_at E u V a p I K" using S(7) by blast
    have "(s,?h p) \<in> map_relation_values ?h (socket_sum Q C)" using row(1) by auto
    then show "\<exists>p I K. (s,p) \<in> map_relation_values ?h (socket_sum Q C) \<and> native_premise_at ?F u V a p I K"
      using native_premise_placeholder_fill[OF R_formed row(2)] by blast
  qed
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3) fin sv dom rows
  show ?thesis unfolding native_premise_family_at_def socket_sum_map_relation_values
    by (intro exI conjI) (fact facts)+
qed

corollary native_premise_family_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_premise_family_at E u V r Q C"
  shows "native_premise_family_at (placeholder_fill E R) u V r W D \<longleftrightarrow>
    W=map_relation_values (map_prod id (map_pattern_leaves (placeholder_leaf R))) Q \<and>
    D=map_relation_values (map_material_leaves (placeholder_leaf R)) C"
  using native_premise_family_placeholder_fill[OF assms]
  by (auto dest: native_premise_family_unique[OF native_premise_family_placeholder_fill[OF assms]])

section \<open>Schemas, schema families and definitions\<close>

theorem native_schema_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_schema_at E u r S"
  shows "native_schema_at (placeholder_fill E R) u r (map_schema_leaves (placeholder_leaf R) S)"
proof -
  let ?F="placeholder_fill E R" and ?S="map_schema_leaves (placeholder_leaf R) S"
  obtain T ps b c m V I K where T: "environment_formed E" "artifact_at E u T" "record_at T r ps [b,c,m]"
      "binder_scope_at T b V" "pattern_quoted_at E u V c (schema_conclusion S) I K"
      "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
      "V = schema_variables S"
      "insert r (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {}"
      "insert b V \<inter> I = {}" "b \<noteq> m" "m \<notin> I"
    by (insert read[unfolded native_schema_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at ?F u T" by (rule artifact_at_placeholder_fill_record[OF T(1-3)])
  have conclusion: "pattern_quoted_at ?F u V c (schema_conclusion ?S) I K"
    using pattern_quoted_placeholder_fill[OF R_formed T(5)] by simp
  have family: "native_premise_family_at ?F u V m (schema_premises ?S) (schema_material_premises ?S)"
    using native_premise_family_placeholder_fill[OF R_formed T(6)] by simp
  have vars: "V = schema_variables ?S" using T(7) by simp
  note facts=placeholder_fill_formed[OF T(1) R_formed] art T(3,4,8-11) conclusion family vars
  show ?thesis unfolding native_schema_at_def by (intro exI conjI) (fact facts)+
qed

corollary native_schema_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_schema_at E u r S"
  shows "native_schema_at (placeholder_fill E R) u r T \<longleftrightarrow> T=map_schema_leaves (placeholder_leaf R) S"
  using native_schema_placeholder_fill[OF assms]
  by (auto dest: native_schema_unique[OF native_schema_placeholder_fill[OF assms]])

theorem native_schema_family_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_schema_family_at E u r C"
  shows "native_schema_family_at (placeholder_fill E R) u r
    (map_relation_values (map_schema_leaves (placeholder_leaf R)) C)"
proof -
  let ?F="placeholder_fill E R" and ?h="map_schema_leaves (placeholder_leaf R)"
  obtain S M where S: "environment_formed E" "artifact_at E u S" "family_at S r M" "finite C" "single_valued C"
      "rel_dom C = rel_dom M" "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>T. (s,T) \<in> C \<and> native_schema_at E u a T)"
    by (insert read[unfolded native_schema_family_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at ?F u S" by (rule artifact_at_placeholder_fill_family[OF S(1-3)])
  have fin: "finite (map_relation_values ?h C)" using S(4) by simp
  have sv: "single_valued (map_relation_values ?h C)" by (rule map_relation_values_single_valued[OF S(5)])
  have dom: "rel_dom (map_relation_values ?h C)=rel_dom M" using S(6) by simp
  have rows: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>T. (s,T) \<in> map_relation_values ?h C \<and> native_schema_at ?F u a T)"
  proof (intro allI impI)
    fix s a assume "(s,a) \<in> M"
    then obtain T where row: "(s,T) \<in> C" "native_schema_at E u a T" using S(7) by blast
    have "(s,?h T) \<in> map_relation_values ?h C" using row(1) by auto
    then show "\<exists>T. (s,T) \<in> map_relation_values ?h C \<and> native_schema_at ?F u a T"
      using native_schema_placeholder_fill[OF R_formed row(2)] by blast
  qed
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3) fin sv dom rows
  show ?thesis unfolding native_schema_family_at_def by (intro exI conjI) (fact facts)+
qed

corollary native_schema_family_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_schema_family_at E u r C"
  shows "native_schema_family_at (placeholder_fill E R) u r D \<longleftrightarrow>
    D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
  using native_schema_family_placeholder_fill[OF assms]
  by (auto dest: native_schema_family_unique[OF native_schema_family_placeholder_fill[OF assms]])

theorem native_definition_placeholder_fill:
  assumes R_formed: "exact_formed R" and read: "native_definition_at E u r p C"
  shows "native_definition_at (placeholder_fill E R) u r (map_pattern_leaves (placeholder_leaf R) p)
    (map_relation_values (map_schema_leaves (placeholder_leaf R)) C)"
proof -
  obtain S ps i m I K where S: "environment_formed E" "artifact_at E u S" "record_at S r ps [i,m]"
      "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
      "insert r (set ps) \<inter> (I \<union> {m}) = {}" "m \<notin> I"
    by (insert read[unfolded native_definition_at_def], elim conjE exE) (rule that; assumption)
  have art: "artifact_at (placeholder_fill E R) u S" by (rule artifact_at_placeholder_fill_record[OF S(1-3)])
  note facts=placeholder_fill_formed[OF S(1) R_formed] art S(3,6,7)
    scoped_pattern_placeholder_fill[OF R_formed S(4)] native_schema_family_placeholder_fill[OF R_formed S(5)]
  show ?thesis unfolding native_definition_at_def by (intro exI conjI) (fact facts)+
qed

corollary native_definition_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and read: "native_definition_at E u r p C"
  shows "native_definition_at (placeholder_fill E R) u r q D \<longleftrightarrow>
    q=map_pattern_leaves (placeholder_leaf R) p \<and> D=map_relation_values (map_schema_leaves (placeholder_leaf R)) C"
  using native_definition_placeholder_fill[OF assms]
  by (auto dest: native_definition_unique[OF native_definition_placeholder_fill[OF assms]])

end
