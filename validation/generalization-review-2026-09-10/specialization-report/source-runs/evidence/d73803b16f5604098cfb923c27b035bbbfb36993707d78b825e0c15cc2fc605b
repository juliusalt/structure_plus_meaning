theory Factor_Native_Transport
  imports Factor_Syntax_Boundaries Factor_Scoped_Transport Factor_Schema_Renaming
begin

section \<open>A structural copy with explicit literal and callee transport\<close>

fun map_native_premise ::
  "(local_address \<Rightarrow> local_address) \<Rightarrow> ('u definition_site \<Rightarrow> 'v definition_site) \<Rightarrow>
    'u native_premise \<Rightarrow> 'v native_premise" where
  "map_native_premise f g (Inl (d,p)) = Inl (g d,rename_pattern f p)"
| "map_native_premise f g (Inr M) = Inr (rename_material_pattern f M)"

lemma map_native_premise_left:
  "map_native_premise f g (Inl p) = Inl (g (fst p),rename_pattern f (snd p))"
  by (cases p) simp

lemma mapped_native_socket_sum:
  "socket_sum (map_socket_graph f g (rename_pattern f) Q)
      ((\<lambda>(s,M). (f s,rename_material_pattern f M)) ` C) =
    (\<lambda>(s,p). (f s,map_native_premise f g p)) ` socket_sum Q C"
  by (simp add: socket_sum_def map_socket_graph_def map_prod_def image_Un image_image split_def
      map_native_premise_left)

locale native_syntax_copy =
  fixes E :: "'u artifact_environment" and u :: 'u and R :: exact_artifact
    and F :: "'v artifact_environment" and w :: 'v and S :: exact_artifact
    and f :: "local_address \<Rightarrow> local_address" and g :: "'u definition_site \<Rightarrow> 'v definition_site"
  assumes source_formed: "environment_formed E" and source: "artifact_at E u R"
    and target_formed: "environment_formed F" and target: "artifact_at F w S"
    and injective: "inj f" and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (f ` rra_carrier (object_structure R))"
    and literals: "\<forall>k\<in>rra_carrier (object_structure R).
      external_slot_values E u k = external_slot_values F w (f k)"
    and locations: "\<And>r c I v a. citation_at R r c I \<Longrightarrow> citation_location E u c v a \<Longrightarrow>
      citation_location F w (map_citation_positions f c) (fst (g (v,a))) (snd (g (v,a)))"
begin

lemma source_exact: "exact_formed R"
  using source_formed source unfolding environment_formed_def by blast

lemma target_exact: "exact_formed S"
  using target_formed target unfolding environment_formed_def by blast

lemma target_object: "object_formed S" using target_exact by (simp add: exact_formed_def)

lemma local_injective: "inj_on f (rra_carrier (object_structure R))"
  using injective by (auto simp: inj_on_def)

lemma restricted_reads:
  assumes "I \<subseteq> rra_carrier (object_structure R)"
  shows "object_reads_agree (push_object f R) S (f ` I)"
  by (rule object_reads_agree_mono[OF reads]) (use assms in blast)

lemma restricted_literals:
  assumes "K \<subseteq> rra_carrier (object_structure R)"
  shows "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
  using literals assms by blast

lemma copy_record:
  assumes rec: "record_at R r ps xs"
  shows "record_at S (f r) (map f ps) (map f xs)"
proof -
  have copied: "record_at (push_object f R) (f r) (map f ps) (map f xs)"
    by (rule record_at_push[OF rec local_injective])
  show ?thesis by (rule record_at_read_transport[OF copied target_object reads])
    (use record_interior_in_carrier[OF rec] in auto)
qed

lemma copy_family:
  assumes family: "family_at R r M"
  shows "family_at S (f r) ((\<lambda>(p,a). (f p,f a)) ` M)"
proof -
  have copied: "family_at (push_object f R) (f r) ((\<lambda>(p,a). (f p,f a)) ` M)"
    by (rule family_at_push[OF family local_injective])
  show ?thesis by (rule family_at_read_transport[OF copied target_object reads])
    (use family_interior_in_carrier[OF family] in \<open>auto simp: pair_image_domain\<close>)
qed

lemma copy_citation:
  assumes cite: "citation_at R r c I"
  shows "citation_at S (f r) (map_citation_positions f c) (f ` I)"
  by (rule citation_at_read_transport[OF citation_at_push[OF cite addressing] target_exact
        restricted_reads[OF citation_interior_in_carrier[OF cite]]])

lemma copy_pattern:
  assumes quote: "pattern_quoted_at E u V r p I K"
  shows "pattern_quoted_at F w (f ` V) (f r) (rename_pattern f p) (f ` I) (f ` K)"
proof -
  have bound: "I \<union> K \<subseteq> rra_carrier (object_structure R)"
    using pattern_quoted_carrier[OF quote source] by blast
  have ri: "object_reads_agree (push_object f R) S (f ` I)"
    by (rule restricted_reads) (use bound in blast)
  have sk: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    by (rule restricted_literals) (use bound in blast)
  show ?thesis by (rule pattern_quotation_transport[OF quote source addressing ri sk injective target_formed target])
qed

lemma copy_scoped_pattern:
  assumes quote: "scoped_pattern_at E u r p I K"
  shows "scoped_pattern_at F w (f r) (rename_pattern f p) (f ` I) (f ` K)"
proof -
  have bound: "I \<union> K \<subseteq> rra_carrier (object_structure R)"
    by (rule scoped_pattern_carrier[OF quote source])
  have ri: "object_reads_agree (push_object f R) S (f ` I)"
    by (rule restricted_reads) (use bound in blast)
  have sk: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    by (rule restricted_literals) (use bound in blast)
  show ?thesis by (rule scoped_pattern_transport[OF quote source addressing ri sk injective target_formed target])
qed

lemma copy_material:
  assumes quote: "native_material_at E u V r M I K"
  shows "native_material_at F w (f ` V) (f r) (rename_material_pattern f M) (f ` I) (f ` K)"
proof -
  have bound: "I \<union> K \<subseteq> rra_carrier (object_structure R)"
    by (rule native_material_carrier[OF quote source])
  have ri: "object_reads_agree (push_object f R) S (f ` I)"
    by (rule restricted_reads) (use bound in blast)
  have sk: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    by (rule restricted_literals) (use bound in blast)
  show ?thesis by (rule native_material_transport[OF quote source addressing ri sk injective target_formed target])
qed

lemma copy_prospective_call:
  assumes call: "prospective_call_at E u V r d p I K"
  shows "prospective_call_at F w (f ` V) (f r) (g d) (rename_pattern f p) (f ` I) (f ` K)"
proof -
  obtain T ps c a cite C J A where parts:
    "artifact_at E u T" "record_at T r ps [c,a]" "citation_at T c cite C"
    "citation_location E u cite (fst d) (snd d)" "pattern_quoted_at E u V a p J A"
    "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
    "I=insert r (set ps \<union> C \<union> J)" "K=citation_slots cite \<union> A" "I \<inter> (K \<union> V) = {}"
    using call by (auto simp: prospective_call_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have rec: "record_at R r ps [c,a]" and citation: "citation_at R c cite C" using parts(2,3) same by simp_all
  have copied_rec: "record_at S (f r) (map f ps) [f c,f a]" using copy_record[OF rec] by simp
  have copied_cite: "citation_at S (f c) (map_citation_positions f cite) (f ` C)" by (rule copy_citation[OF citation])
  have copied_location: "citation_location F w (map_citation_positions f cite) (fst (g d)) (snd (g d))"
    using locations[OF citation parts(4)] by simp
  have body: "pattern_quoted_at F w (f ` V) (f a) (rename_pattern f p) (f ` J) (f ` A)"
    by (rule copy_pattern[OF parts(5)])
  have top_separate: "insert (f r) (set (map f ps)) \<inter> (f ` C \<union> f ` J) = {}"
    using image_Int[OF injective, of "insert r (set ps)" "C \<union> J"] parts(6) by (simp add: image_Un)
  have children: "f ` C \<inter> f ` J = {}" using image_Int[OF injective, of C J] parts(7) by simp
  have boundary: "f ` I \<inter> (f ` K \<union> f ` V) = {}"
    using image_Int[OF injective, of I "K \<union> V"] parts(10) by (simp add: image_Un)
  show ?thesis unfolding prospective_call_at_def
    apply (rule conjI[OF target_formed])
    apply (rule exI[of _ S], rule exI[of _ "map f ps"], rule exI[of _ "f c"], rule exI[of _ "f a"],
        rule exI[of _ "map_citation_positions f cite"], rule exI[of _ "f ` C"],
        rule exI[of _ "f ` J"], rule exI[of _ "f ` A"])
    using target copied_rec copied_cite copied_location body top_separate children boundary parts(8,9)
    by (simp add: image_Un citation_slots_push)
qed

lemma copy_premise:
  assumes premise: "native_premise_at E u V r p I K"
  shows "native_premise_at F w (f ` V) (f r) (map_native_premise f g p) (f ` I) (f ` K)"
  using premise by (cases rule: native_premise_at.cases)
    (auto intro: copy_prospective_call copy_material)

lemma copy_premise_family:
  assumes family: "native_premise_family_at E u V r Q C"
  shows "native_premise_family_at F w (f ` V) (f r) (map_socket_graph f g (rename_pattern f) Q)
    ((\<lambda>(s,M). (f s,rename_material_pattern f M)) ` C)"
proof -
  let ?P = "socket_sum Q C"
  let ?Q = "map_socket_graph f g (rename_pattern f) Q"
  let ?C = "(\<lambda>(s,M). (f s,rename_material_pattern f M)) ` C"
  let ?N = "socket_sum ?Q ?C"
  obtain T M where parts: "artifact_at E u T" "family_at T r M"
    "finite ?P" "single_valued ?P" "rel_dom ?P=rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>p I K. (s,p) \<in> ?P \<and> native_premise_at E u V a p I K)"
    using family by (auto simp: native_premise_family_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have raw: "family_at R r M" using parts(2) same by simp
  let ?M = "(\<lambda>(s,a). (f s,f a)) ` M"
  have copied_family: "family_at S (f r) ?M" by (rule copy_family[OF raw])
  have mapped: "?N = (\<lambda>(s,p). (f s,map_native_premise f g p)) ` ?P"
    by (rule mapped_native_socket_sum)
  have finite: "finite ?N" using parts(3) by (simp add: mapped)
  have sinj: "inj_on f (rel_dom ?P)" using injective by (auto simp: inj_on_def)
  have functional: "single_valued ?N"
    using single_valued_pair_image[OF parts(4) sinj, where g="map_native_premise f g"] by (simp add: mapped)
  have domain: "rel_dom ?N = rel_dom ?M" by (simp only: mapped pair_image_domain parts(5))
  have each: "\<forall>s a. (s,a) \<in> ?M \<longrightarrow>
    (\<exists>p I K. (s,p) \<in> ?N \<and> native_premise_at F w (f ` V) a p I K)"
  proof (intro allI impI)
    fix s a assume member: "(s,a) \<in> ?M"
    obtain b c where original: "(b,c) \<in> M" "s=f b" "a=f c" using member by auto
    obtain p I K where old: "(b,p) \<in> ?P" "native_premise_at E u V c p I K"
      using parts(6) original(1) by blast
    have present: "(s,map_native_premise f g p) \<in> ?N"
      using imageI[OF old(1), of "\<lambda>(s,p). (f s,map_native_premise f g p)"] original(2)
      by (simp add: mapped)
    have read: "native_premise_at F w (f ` V) a (map_native_premise f g p) (f ` I) (f ` K)"
      using copy_premise[OF old(2)] original(3) by simp
    show "\<exists>p I K. (s,p) \<in> ?N \<and> native_premise_at F w (f ` V) a p I K"
      using present read by blast
  qed
  show ?thesis unfolding native_premise_family_at_def
    by (rule conjI[OF target_formed], rule exI[of _ S], rule exI[of _ ?M])
       (use target copied_family finite functional domain each in blast)
qed

lemma copy_schema:
  assumes schema: "native_schema_at E u r A"
  shows "native_schema_at F w (f r) (rename_schema f f g A)"
proof -
  obtain T ps b c m V I K where parts: "artifact_at E u T" "record_at T r ps [b,c,m]"
    "binder_scope_at T b V" "pattern_quoted_at E u V c (schema_conclusion A) I K"
    "native_premise_family_at E u V m (schema_premises A) (schema_material_premises A)"
    "V=schema_variables A" "insert r (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {}"
    "insert b V \<inter> I = {}" "b \<noteq> m" "m \<notin> I"
    using schema by (auto simp: native_schema_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have rec: "record_at R r ps [b,c,m]" and scope: "binder_scope_at R b V" using parts(2,3) same by simp_all
  have copied_rec: "record_at S (f r) (map f ps) [f b,f c,f m]" using copy_record[OF rec] by simp
  have raw_scope: "family_at R b ((\<lambda>a. (a,a)) ` V)" using scope by (simp add: binder_scope_at_def)
  have copied_scope: "binder_scope_at S (f b) (f ` V)"
    using copy_family[OF raw_scope] by (simp add: binder_scope_at_def image_image)
  have conclusion: "pattern_quoted_at F w (f ` V) (f c)
    (schema_conclusion (rename_schema f f g A)) (f ` I) (f ` K)"
    using copy_pattern[OF parts(4)] by (simp add: rename_schema_def)
  have body: "native_premise_family_at F w (f ` V) (f m)
    (schema_premises (rename_schema f f g A)) (schema_material_premises (rename_schema f f g A))"
    using copy_premise_family[OF parts(5)] by (simp add: rename_schema_def)
  have variables: "f ` V = schema_variables (rename_schema f f g A)"
    by (simp add: parts(6) renamed_schema_variables)
  have top_separate: "insert (f r) (set (map f ps)) \<inter>
    (insert (f b) (f ` V) \<union> f ` I \<union> {f m}) = {}"
    using image_Int[OF injective, of "insert r (set ps)" "insert b V \<union> I \<union> {m}"] parts(7)
    by (simp add: image_Un)
  have scope_separate: "insert (f b) (f ` V) \<inter> f ` I = {}"
    using image_Int[OF injective, of "insert b V" I] parts(8) by simp
  have roots: "f b \<noteq> f m" "f m \<notin> f ` I"
    using parts(9,10) injective by (auto simp: inj_eq)
  show ?thesis unfolding native_schema_at_def
    apply (rule conjI[OF target_formed])
    apply (rule exI[of _ S], rule exI[of _ "map f ps"], rule exI[of _ "f b"], rule exI[of _ "f c"],
        rule exI[of _ "f m"], rule exI[of _ "f ` V"], rule exI[of _ "f ` I"], rule exI[of _ "f ` K"])
    using target copied_rec copied_scope conclusion body variables top_separate scope_separate roots by blast
qed


lemma copy_schema_family:
  assumes family: "native_schema_family_at E u r C"
  shows "native_schema_family_at F w (f r) ((\<lambda>(s,A). (f s,rename_schema f f g A)) ` C)"
proof -
  obtain T M where parts: "artifact_at E u T" "family_at T r M" "finite C" "single_valued C"
    "rel_dom C = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>A. (s,A) \<in> C \<and> native_schema_at E u a A)"
    using family by (auto simp: native_schema_family_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have raw: "family_at R r M" using parts(2) same by simp
  let ?M = "(\<lambda>(s,a). (f s,f a)) ` M"
  let ?C = "(\<lambda>(s,A). (f s,rename_schema f f g A)) ` C"
  have copied_family: "family_at S (f r) ?M" by (rule copy_family[OF raw])
  have finite: "finite ?C" using parts(3) by simp
  have inj: "inj_on f (rel_dom C)" using injective by (auto simp: inj_on_def)
  have functional: "single_valued ?C" by (rule single_valued_pair_image[OF parts(4) inj])
  have domain: "rel_dom ?C = rel_dom ?M" by (simp add: pair_image_domain parts(5))
  have each: "\<forall>s a. (s,a) \<in> ?M \<longrightarrow> (\<exists>A. (s,A) \<in> ?C \<and> native_schema_at F w a A)"
  proof (intro allI impI)
    fix s a assume entry: "(s,a) \<in> ?M"
    obtain t b where original: "(t,b) \<in> M" "s=f t" "a=f b" using entry by auto
    obtain A where old: "(t,A) \<in> C" "native_schema_at E u b A" using parts(6) original(1) by blast
    have present: "(s,rename_schema f f g A) \<in> ?C"
      using imageI[OF old(1), of "\<lambda>(s,A). (f s,rename_schema f f g A)"] original(2) by simp
    have copied: "native_schema_at F w a (rename_schema f f g A)" using copy_schema[OF old(2)] original(3) by simp
    show "\<exists>A. (s,A) \<in> ?C \<and> native_schema_at F w a A" using present copied by blast
  qed
  show ?thesis unfolding native_schema_family_at_def
    by (rule conjI[OF target_formed], rule exI[of _ S], rule exI[of _ ?M])
       (use target copied_family finite functional domain each in blast)
qed

lemma copy_definition:
  assumes defined: "native_definition_at E u r p C"
  shows "native_definition_at F w (f r) (rename_pattern f p)
    ((\<lambda>(s,A). (f s,rename_schema f f g A)) ` C)"
proof -
  obtain T ps i m I K where parts: "artifact_at E u T" "record_at T r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    "insert r (set ps) \<inter> (I \<union> {m}) = {}" "m \<notin> I"
    using defined by (auto simp: native_definition_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have raw: "record_at R r ps [i,m]" using parts(2) same by simp
  have rec: "record_at S (f r) (map f ps) [f i,f m]" using copy_record[OF raw] by simp
  have interface: "scoped_pattern_at F w (f i) (rename_pattern f p) (f ` I) (f ` K)"
    by (rule copy_scoped_pattern[OF parts(3)])
  have family: "native_schema_family_at F w (f m) ((\<lambda>(s,A). (f s,rename_schema f f g A)) ` C)"
    by (rule copy_schema_family[OF parts(4)])
  have separate: "insert (f r) (set (map f ps)) \<inter> (f ` I \<union> {f m}) = {}"
    using image_Int[OF injective, of "insert r (set ps)" "I \<union> {m}"] parts(5) by auto
  have outside: "f m \<notin> f ` I" using parts(6) injective by (auto simp: inj_eq)
  show ?thesis unfolding native_definition_at_def
    by (rule conjI[OF target_formed], rule exI[of _ S], rule exI[of _ "map f ps"],
        rule exI[of _ "f i"], rule exI[of _ "f m"], rule exI[of _ "f ` I"], rule exI[of _ "f ` K"])
       (use target rec interface family separate outside in blast)
qed

end

text \<open>
  These transport theorems require an actual injective structural copy, agreement
  on literal values, and preservation of the locations recovered from actual
  citations. They add no truth assumption. A constructor using the theorems must
  establish all of those concrete conditions in its destination environment.
  Binder, socket, and callee changes are precisely the schema renaming already
  proved to preserve instantiation and material satisfaction.
\<close>

end
