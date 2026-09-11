theory Factor_Presentation_Dependencies
  imports Factor_Packages RRA_Read_Environment
begin

section \<open>Compatible environment extension preserves recovered syntax\<close>

lemma term_quoted_included:
  assumes quote: "term_quoted_at E u r t I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "term_quoted_at F u r t I K"
  using quote
proof (induction rule: term_quoted_at.induct)
  case (target u R r c I t)
  have art: "artifact_at F u R" by (rule included_artifact[OF included target.hyps(2)])
  have interp: "interpret_citation F u c t" by (rule included_interpretation[OF included target.hyps(5)])
  show ?case by (rule term_quoted_at.target[OF formed art target.hyps(3,4) interp])
next
  case (pair u R r ps l q x L A y Q B)
  have art: "artifact_at F u R" by (rule included_artifact[OF included pair.hyps(2)])
  show ?case by (rule term_quoted_at.pair[OF formed art pair.hyps(3) pair.IH pair.hyps(6-8)])
next
  case (payload u R r v)
  have art: "artifact_at F u R" by (rule included_artifact[OF included payload.hyps(2)])
  show ?case by (rule term_quoted_at.payload[OF formed art payload.hyps(3)])
qed

lemma pattern_quoted_included:
  assumes quote: "pattern_quoted_at E u V r p I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "pattern_quoted_at F u V r p I K"
  using quote
proof (induction rule: pattern_quoted_at.induct)
  case (variable R r a I)
  have art: "artifact_at F u R" by (rule included_artifact[OF included variable.hyps(2)])
  show ?case by (rule pattern_quoted_at.variable[OF formed art variable.hyps(3-5)])
next
  case (target r t I K)
  have leaf: "term_quoted_at F u r (Target_Term t) I K"
    by (rule term_quoted_included[OF target.hyps(1) included formed])
  show ?case by (rule pattern_quoted_at.target[OF leaf target.hyps(2)])
next
  case (pair R r ps l q p L A s Q B)
  have art: "artifact_at F u R" by (rule included_artifact[OF included pair.hyps(2)])
  show ?case by (rule pattern_quoted_at.pair[OF formed art pair.hyps(3) pair.IH pair.hyps(6-8)])
next
  case (payload r v I K)
  have leaf: "term_quoted_at F u r (Payload_Term v) I K"
    by (rule term_quoted_included[OF payload.hyps(1) included formed])
  show ?case by (rule pattern_quoted_at.payload[OF leaf payload.hyps(2)])
qed

lemma scoped_pattern_included:
  assumes source: "scoped_pattern_at E u r p I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "scoped_pattern_at F u r p I K"
proof -
  obtain R ps b q V J where parts:
    "artifact_at E u R" "record_at R r ps [b,q]" "binder_scope_at R b V"
    "pattern_quoted_at E u V q p J K" "V = pattern_variables p"
    "insert r (set ps) \<inter> (insert b V \<union> J) = {}" "insert b V \<inter> J = {}"
    "I = insert r (set ps \<union> insert b V \<union> J)" "I \<inter> K = {}"
    using source by (auto simp: scoped_pattern_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have quote: "pattern_quoted_at F u V q p J K" by (rule pattern_quoted_included[OF parts(4) included formed])
  show ?thesis using formed art quote parts(2,3,5-9) unfolding scoped_pattern_at_def by blast
qed

lemma prospective_call_included:
  assumes source: "prospective_call_at E u V r d p I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "prospective_call_at F u V r d p I K"
proof -
  obtain R ps c a cite C J A where parts:
    "artifact_at E u R" "record_at R r ps [c,a]" "citation_at R c cite C"
    "citation_location E u cite (fst d) (snd d)" "pattern_quoted_at E u V a p J A"
    "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
    "I = insert r (set ps \<union> C \<union> J)" "K = citation_slots cite \<union> A" "I \<inter> (K \<union> V) = {}"
    using source by (auto simp: prospective_call_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have loc: "citation_location F u cite (fst d) (snd d)" by (rule included_location[OF included parts(4)])
  have quote: "pattern_quoted_at F u V a p J A" by (rule pattern_quoted_included[OF parts(5) included formed])
  show ?thesis using formed art loc quote parts(2,3,6-10) unfolding prospective_call_at_def by blast
qed

lemma prospective_family_included:
  assumes source: "prospective_family_at E u V r Q"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "prospective_family_at F u V r Q"
  using source formed included unfolding prospective_family_at_def
  by (meson included_artifact prospective_call_included)

lemma pattern_vector_included:
  assumes vector: "pattern_vector_at E u V rs ps I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "pattern_vector_at F u V rs ps I K"
  using vector
proof (induction rule: pattern_vector_at.induct)
  case empty
  show ?case by (rule pattern_vector_at.empty[OF formed])
next
  case (cons r p A B rs ps I K)
  have head: "pattern_quoted_at F u V r p A B"
    by (rule pattern_quoted_included[OF cons.hyps(1) included formed])
  show ?case by (rule pattern_vector_at.cons[OF head cons.IH cons.hyps(3,4)])
qed

lemma pattern_record_included:
  assumes source: "pattern_record_at E u V r ps I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "pattern_record_at F u V r ps I K"
proof -
  obtain R ports roots J where parts: "artifact_at E u R" "record_at R r ports roots"
    "pattern_vector_at E u V roots ps J K" "insert r (set ports) \<inter> J = {}"
    "I=insert r (set ports \<union> J)" "I \<inter> (K \<union> V) = {}"
    using source by (auto simp: pattern_record_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have vector: "pattern_vector_at F u V roots ps J K"
    by (rule pattern_vector_included[OF parts(3) included formed])
  show ?thesis using formed art vector parts(2,4-6) unfolding pattern_record_at_def by blast
qed

lemma native_material_included:
  assumes "native_material_at E u V r M I K" "environment_included E F" "environment_formed F"
  shows "native_material_at F u V r M I K"
  using assms unfolding native_material_at_def by (rule pattern_record_included)

lemma native_premise_included:
  assumes source: "native_premise_at E u V r p I K"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_premise_at F u V r p I K"
  using source
proof (cases rule: native_premise_at.cases)
  case (call d q)
  have "prospective_call_at F u V r d q I K"
    by (rule prospective_call_included[OF call(2) included formed])
  then show ?thesis using call by auto
next
  case (material M)
  have "native_material_at F u V r M I K"
    by (rule native_material_included[OF material(2) included formed])
  then show ?thesis using material by auto
qed

lemma native_premise_family_included:
  assumes source: "native_premise_family_at E u V r Q C"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_premise_family_at F u V r Q C"
  using source formed included unfolding native_premise_family_at_def
  by (meson included_artifact native_premise_included)

lemma native_schema_included:
  assumes source: "native_schema_at E u r S"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_schema_at F u r S"
proof -
  obtain R ps b c m V I K where parts:
    "artifact_at E u R" "record_at R r ps [b,c,m]" "binder_scope_at R b V"
    "pattern_quoted_at E u V c (schema_conclusion S) I K"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)" "V = schema_variables S"
    "insert r (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {}"
    "insert b V \<inter> I = {}" "b \<noteq> m" "m \<notin> I"
    using source by (auto simp: native_schema_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have quote: "pattern_quoted_at F u V c (schema_conclusion S) I K"
    by (rule pattern_quoted_included[OF parts(4) included formed])
  have body: "native_premise_family_at F u V m (schema_premises S) (schema_material_premises S)"
    by (rule native_premise_family_included[OF parts(5) included formed])
  show ?thesis unfolding native_schema_at_def
    by (rule conjI[OF formed], rule exI[of _ R], rule exI[of _ ps],
        rule exI[of _ b], rule exI[of _ c], rule exI[of _ m],
        rule exI[of _ V], rule exI[of _ I], rule exI[of _ K])
       (use art quote body parts(2,3,6-10) in blast)
qed

lemma native_schema_family_included:
  assumes source: "native_schema_family_at E u r C"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_schema_family_at F u r C"
  using source formed included unfolding native_schema_family_at_def
  by (meson included_artifact native_schema_included)

lemma native_definition_included:
  assumes source: "native_definition_at E u r p C"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_definition_at F u r p C"
  using source formed included unfolding native_definition_at_def
  by (meson included_artifact scoped_pattern_included native_schema_family_included)

lemma native_root_family_included:
  assumes source: "native_root_family_at E u r Q"
    and included: "environment_included E F" and formed: "environment_formed F"
  shows "native_root_family_at F u r Q"
  using source formed included unfolding native_root_family_at_def
  by (meson included_artifact included_located)

section \<open>Slots are derived from recognized pattern and call syntax\<close>

lemma interpreted_citation_slots_bound:
  assumes interp: "interpret_citation E u c t" and slot: "k \<in> citation_slots c"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using interp slot by (cases c) (auto simp: rel_dom_def binds_slot_def)

lemma located_citation_slots_bound:
  assumes loc: "citation_location E u c v a" and slot: "k \<in> citation_slots c"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using loc slot by (cases c) (auto simp: rel_dom_def binds_slot_def)

lemma term_quoted_slots_bound:
  assumes "term_quoted_at E u r t I K"
  shows "\<forall>k\<in>K. (u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (induction rule: term_quoted_at.induct)
    (auto intro: interpreted_citation_slots_bound)

lemma pattern_quoted_slots_bound:
  assumes "pattern_quoted_at E u V r p I K"
  shows "\<forall>k\<in>K. (u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (induction rule: pattern_quoted_at.induct)
    (auto dest: term_quoted_slots_bound)

definition pattern_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "pattern_slots E u V r = {k. \<exists>p I K. pattern_quoted_at E u V r p I K \<and> k \<in> K}"

lemma pattern_slots_of_quote:
  assumes quote: "pattern_quoted_at E u V r p I K"
  shows "pattern_slots E u V r = K"
proof -
  have unique: "\<And>q J W. pattern_quoted_at E u V r q J W \<Longrightarrow> W = K"
    using pattern_quoted_unique[OF _ quote] by blast
  show ?thesis using quote unique unfolding pattern_slots_def by blast
qed

definition scoped_pattern_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "scoped_pattern_slots E u r = {k. \<exists>p I K. scoped_pattern_at E u r p I K \<and> k \<in> K}"

lemma scoped_pattern_slots_of_quote:
  assumes quote: "scoped_pattern_at E u r p I K"
  shows "scoped_pattern_slots E u r = K"
proof -
  have unique: "\<And>q J W. scoped_pattern_at E u r q J W \<Longrightarrow> W = K"
    using scoped_pattern_unique[OF _ quote] by blast
  show ?thesis using quote unique unfolding scoped_pattern_slots_def by blast
qed

definition prospective_call_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "prospective_call_slots E u V r = {k. \<exists>d p I K. prospective_call_at E u V r d p I K \<and> k \<in> K}"

lemma prospective_call_slots_of_read:
  assumes call: "prospective_call_at E u V r d p I K"
  shows "prospective_call_slots E u V r = K"
proof -
  have unique: "\<And>e q J W. prospective_call_at E u V r e q J W \<Longrightarrow> W = K"
    using prospective_call_unique[OF _ call] by blast
  show ?thesis using call unique unfolding prospective_call_slots_def by blast
qed

lemma pattern_slots_bound:
  assumes "k \<in> pattern_slots E u V r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain p I K where quote: "pattern_quoted_at E u V r p I K" and slot: "k \<in> K"
    using assms unfolding pattern_slots_def by blast
  show ?thesis using pattern_quoted_slots_bound[OF quote] slot by blast
qed

lemma scoped_pattern_slots_bound:
  assumes "k \<in> scoped_pattern_slots E u r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain p I K where scoped: "scoped_pattern_at E u r p I K" and slot: "k \<in> K"
    using assms unfolding scoped_pattern_slots_def by blast
  obtain V q J where quote: "pattern_quoted_at E u V q p J K"
    using scoped by (auto simp: scoped_pattern_at_def)
  show ?thesis using pattern_quoted_slots_bound[OF quote] slot by blast
qed

lemma prospective_call_slots_bound:
  assumes "k \<in> prospective_call_slots E u V r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain d p I K where call: "prospective_call_at E u V r d p I K" and slot: "k \<in> K"
    using assms unfolding prospective_call_slots_def by blast
  obtain cite a J A where parts: "citation_location E u cite (fst d) (snd d)"
    "pattern_quoted_at E u V a p J A" "K = citation_slots cite \<union> A"
    using call by (auto simp: prospective_call_at_def)
  show ?thesis using slot located_citation_slots_bound[OF parts(1)]
    pattern_quoted_slots_bound[OF parts(2)] parts(3) by blast
qed

lemma pattern_vector_slots_bound:
  assumes "pattern_vector_at E u V rs ps I K"
  shows "\<forall>k\<in>K. (u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (induction rule: pattern_vector_at.induct) (auto dest: pattern_quoted_slots_bound)

lemma native_material_slots_bound:
  assumes material: "native_material_at E u V r M I K" and member: "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain roots J where vector: "pattern_vector_at E u V roots (material_fields M) J K"
    using material by (auto simp: native_material_at_def pattern_record_at_def)
  show ?thesis using pattern_vector_slots_bound[OF vector] member by blast
qed

definition native_premise_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "native_premise_slots E u V r = {k. \<exists>p I K. native_premise_at E u V r p I K \<and> k \<in> K}"

lemma native_premise_slots_of_read:
  assumes read: "native_premise_at E u V r p I K"
  shows "native_premise_slots E u V r = K"
proof -
  have unique: "\<And>q J W. native_premise_at E u V r q J W \<Longrightarrow> W=K"
    using native_premise_unique[OF _ read] by blast
  show ?thesis using read unique unfolding native_premise_slots_def by blast
qed

lemma native_premise_slots_bound:
  assumes "k \<in> native_premise_slots E u V r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain p I K where read: "native_premise_at E u V r p I K" and member: "k \<in> K"
    using assms unfolding native_premise_slots_def by blast
  show ?thesis using read
  proof (cases rule: native_premise_at.cases)
    case (call d q)
    have "k \<in> prospective_call_slots E u V r"
      using member call prospective_call_slots_of_read[OF call(2)] by simp
    then show ?thesis by (rule prospective_call_slots_bound)
  next
    case (material M)
    show ?thesis by (rule native_material_slots_bound[OF material(2)]) (use member material in simp)
  qed
qed

section \<open>Complete record and family traversal derives higher boundaries\<close>

definition family_endpoints ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "family_endpoints E u r = {a. \<exists>R M. artifact_at E u R \<and> family_at R r M \<and> a \<in> rel_ran M}"

lemma family_endpoints_from_read:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and family: "family_at R r M"
  shows "family_endpoints E u r = rel_ran M"
proof -
  have unique: "\<And>S N. artifact_at E u S \<Longrightarrow> family_at S r N \<Longrightarrow> N = M"
  proof -
    fix S N assume other: "artifact_at E u S" "family_at S r N"
    have same: "S = R" by (rule environment_artifact_unique[OF ef other(1) art])
    have raw: "family_at R r N" using other(2) same by simp
    show "N = M" by (rule family_at_unique[OF raw family])
  qed
  show ?thesis using art family unique unfolding family_endpoints_def by blast
qed

definition prospective_family_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "prospective_family_slots E u V r = (\<Union>a\<in>family_endpoints E u r. prospective_call_slots E u V a)"

definition native_premise_family_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "native_premise_family_slots E u V r = (\<Union>a\<in>family_endpoints E u r. native_premise_slots E u V a)"

lemma native_premise_family_slots_bound:
  assumes "k \<in> native_premise_family_slots E u V r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (auto simp: native_premise_family_slots_def dest: native_premise_slots_bound)

definition native_schema_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "native_schema_slots E u r = {k. \<exists>R ps b c m V.
    artifact_at E u R \<and> record_at R r ps [b,c,m] \<and> binder_scope_at R b V \<and>
    k \<in> pattern_slots E u V c \<union> native_premise_family_slots E u V m}"

definition native_schema_family_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "native_schema_family_slots E u r = (\<Union>a\<in>family_endpoints E u r. native_schema_slots E u a)"

definition native_definition_slots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "native_definition_slots E u r = {k. \<exists>R ps i m.
    artifact_at E u R \<and> record_at R r ps [i,m] \<and>
    k \<in> scoped_pattern_slots E u i \<union> native_schema_family_slots E u m}"

lemma prospective_family_slots_bound:
  assumes "k \<in> prospective_family_slots E u V r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (auto simp: prospective_family_slots_def dest: prospective_call_slots_bound)

lemma native_schema_slots_bound:
  assumes "k \<in> native_schema_slots E u r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (auto simp: native_schema_slots_def dest: pattern_slots_bound native_premise_family_slots_bound)

lemma native_schema_family_slots_bound:
  assumes "k \<in> native_schema_family_slots E u r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (auto simp: native_schema_family_slots_def dest: native_schema_slots_bound)

lemma native_definition_slots_bound:
  assumes "k \<in> native_definition_slots E u r"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
  using assms by (auto simp: native_definition_slots_def dest: scoped_pattern_slots_bound native_schema_family_slots_bound)

lemma native_schema_slots_from_fields:
  assumes ef: "environment_formed E" and art: "artifact_at E u R"
    and rec: "record_at R r ps [b,c,m]" and scope: "binder_scope_at R b V"
  shows "native_schema_slots E u r = pattern_slots E u V c \<union> native_premise_family_slots E u V m"
proof -
  have unique: "\<And>S qs x y z W. artifact_at E u S \<Longrightarrow> record_at S r qs [x,y,z] \<Longrightarrow>
    binder_scope_at S x W \<Longrightarrow> x = b \<and> y = c \<and> z = m \<and> W = V"
  proof -
    fix S qs x y z W assume other: "artifact_at E u S" "record_at S r qs [x,y,z]" "binder_scope_at S x W"
    have same: "S = R" by (rule environment_artifact_unique[OF ef other(1) art])
    have raw: "record_at R r qs [x,y,z]" using other(2) same by simp
    have fields: "x = b \<and> y = c \<and> z = m" using record_at_unique[OF raw rec] by auto
    have binders: "binder_scope_at R b W" using other(3) same fields by simp
    have vars: "W = V" by (rule binder_scope_unique[OF binders scope])
    show "x = b \<and> y = c \<and> z = m \<and> W = V" using fields vars by blast
  qed
  show ?thesis using art rec scope unique unfolding native_schema_slots_def by blast
qed

lemma native_definition_slots_from_fields:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and rec: "record_at R r ps [i,m]"
  shows "native_definition_slots E u r = scoped_pattern_slots E u i \<union> native_schema_family_slots E u m"
proof -
  have unique: "\<And>S qs j n. artifact_at E u S \<Longrightarrow> record_at S r qs [j,n] \<Longrightarrow> j = i \<and> n = m"
  proof -
    fix S qs j n assume other: "artifact_at E u S" "record_at S r qs [j,n]"
    have same: "S = R" by (rule environment_artifact_unique[OF ef other(1) art])
    have raw: "record_at R r qs [j,n]" using other(2) same by simp
    show "j = i \<and> n = m" using record_at_unique[OF raw rec] by auto
  qed
  show ?thesis using art rec unique unfolding native_definition_slots_def by blast
qed

text \<open>
  These boundaries follow the record fields, every family endpoint, and the
  slots returned by the pattern and call readers. They are projections of
  recognized syntax, not certificate-selected lists. A quoted literal retains
  its exact artifact value without recursively interpreting that artifact as
  a definition. Only prospective callees extend the definition traversal.
\<close>

end
