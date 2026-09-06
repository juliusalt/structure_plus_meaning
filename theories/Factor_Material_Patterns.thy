theory Factor_Material_Patterns
  imports Factor_Patterns Factor_Material_Observation
begin

section \<open>Patterns for every operand of a complete material equation\<close>

record 'a material_pattern =
  material_source :: "'a term_pattern"
  material_atoms :: "'a term_pattern"
  material_edges :: "'a term_pattern"
  material_counts :: "'a term_pattern"
  material_functions :: "'a term_pattern"

definition material_fields :: "'a material_pattern \<Rightarrow> 'a term_pattern list" where
  "material_fields M = [material_source M,material_atoms M,material_edges M,material_counts M,material_functions M]"

definition material_variables :: "'a material_pattern \<Rightarrow> 'a set" where
  "material_variables M = (\<Union>p\<in>set (material_fields M). pattern_variables p)"

definition material_pattern_formed :: "'a material_pattern \<Rightarrow> bool" where
  "material_pattern_formed M \<longleftrightarrow> (\<forall>p\<in>set (material_fields M). pattern_formed p)"

lemma material_variables_finite [simp]: "finite (material_variables M)"
  by (simp add: material_variables_def)

lemma material_fields_unique:
  "material_fields M = material_fields N \<longleftrightarrow> M = N"
  by (cases M; cases N) (simp add: material_fields_def)

definition material_pattern_instance ::
  "('a \<times> factor_term) set \<Rightarrow> 'a material_pattern \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "material_pattern_instance V M source atoms edges counts functions \<longleftrightarrow>
    pattern_instance V (material_source M) source \<and>
    pattern_instance V (material_atoms M) atoms \<and>
    pattern_instance V (material_edges M) edges \<and>
    pattern_instance V (material_counts M) counts \<and>
    pattern_instance V (material_functions M) functions"

lemma material_pattern_instance_unique:
  assumes sv: "single_valued V"
    and first: "material_pattern_instance V M s a e b f"
    and second: "material_pattern_instance V M s' a' e' b' f'"
  shows "(s,a,e,b,f) = (s',a',e',b',f')"
  using first second unfolding material_pattern_instance_def
  by (blast intro: pattern_instance_unique[OF sv])

lemma material_pattern_instance_formed:
  assumes bindings: "term_bindings_formed B V"
    and inst: "material_pattern_instance V M s a e b f"
  shows "term_formed s \<and> term_formed a \<and> term_formed e \<and> term_formed b \<and> term_formed f"
  using inst unfolding material_pattern_instance_def
  by (blast intro: pattern_instance_formed_term[OF bindings])

lemma material_pattern_instance_exists:
  assumes formed: "material_pattern_formed M" and scope: "material_variables M \<subseteq> rel_dom V"
  shows "\<exists>s a e b f. material_pattern_instance V M s a e b f"
proof -
  have each: "\<And>p. p \<in> set (material_fields M) \<Longrightarrow> \<exists>t. pattern_instance V p t"
  proof -
    fix p assume member: "p \<in> set (material_fields M)"
    have pf: "pattern_formed p" using formed member by (simp add: material_pattern_formed_def)
    have used: "pattern_variables p \<subseteq> rel_dom V"
      using scope member by (auto simp: material_variables_def)
    show "\<exists>t. pattern_instance V p t" by (rule pattern_instance_exists[OF pf used])
  qed
  have source: "\<exists>s. pattern_instance V (material_source M) s"
    by (rule each) (simp add: material_fields_def)
  have atoms: "\<exists>a. pattern_instance V (material_atoms M) a"
    by (rule each) (simp add: material_fields_def)
  have edges: "\<exists>e. pattern_instance V (material_edges M) e"
    by (rule each) (simp add: material_fields_def)
  have counts: "\<exists>b. pattern_instance V (material_counts M) b"
    by (rule each) (simp add: material_fields_def)
  have funcs: "\<exists>f. pattern_instance V (material_functions M) f"
    by (rule each) (simp add: material_fields_def)
  show ?thesis using source atoms edges counts funcs
    unfolding material_pattern_instance_def by blast
qed

definition material_pattern_satisfied :: "('a \<times> factor_term) set \<Rightarrow> 'a material_pattern \<Rightarrow> bool" where
  "material_pattern_satisfied V M \<longleftrightarrow>
    (\<exists>s a e b f. material_pattern_instance V M s a e b f \<and> material_observation s a e b f)"

theorem material_pattern_satisfied_at_instance:
  assumes sv: "single_valued V" and inst: "material_pattern_instance V M s a e b f"
  shows "material_pattern_satisfied V M \<longleftrightarrow> material_observation s a e b f"
  using material_pattern_instance_unique[OF sv inst] inst
  unfolding material_pattern_satisfied_def by blast

section \<open>Ordered fields are recovered from their actual pattern roots\<close>

inductive pattern_vector_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow>
    local_address list \<Rightarrow> local_address term_pattern list \<Rightarrow>
    local_address set \<Rightarrow> local_address set \<Rightarrow> bool"
  for E u V where
  empty: "environment_formed E \<Longrightarrow> pattern_vector_at E u V [] [] {} {}"
| cons: "pattern_quoted_at E u V r p A B \<Longrightarrow> pattern_vector_at E u V rs ps I K \<Longrightarrow>
    A \<inter> I = {} \<Longrightarrow> (A \<union> I) \<inter> (B \<union> K) = {} \<Longrightarrow>
    pattern_vector_at E u V (r#rs) (p#ps) (A \<union> I) (B \<union> K)"

lemma pattern_vector_nil:
  "pattern_vector_at E u V [] ps I K \<longleftrightarrow>
    environment_formed E \<and> ps=[] \<and> I={} \<and> K={}"
  by (auto elim: pattern_vector_at.cases intro: pattern_vector_at.empty)

lemma pattern_vector_cons:
  assumes "pattern_vector_at E u V (r#rs) ps I K"
  shows "\<exists>p qs A B J W. ps=p#qs \<and> pattern_quoted_at E u V r p A B \<and>
    pattern_vector_at E u V rs qs J W \<and> A \<inter> J = {} \<and> (A \<union> J) \<inter> (B \<union> W) = {} \<and>
    I=A \<union> J \<and> K=B \<union> W"
  using assms by (cases rule: pattern_vector_at.cases) auto

lemma pattern_vector_formed:
  assumes "pattern_vector_at E u V rs ps I K"
  shows "environment_formed E \<and> length rs = length ps \<and>
    (\<forall>p\<in>set ps. pattern_formed p \<and> pattern_variables p \<subseteq> V)"
  using assms by (induction rule: pattern_vector_at.induct)
    (auto dest: pattern_quoted_formed)

lemma pattern_vector_boundary:
  assumes "pattern_vector_at E u V rs ps I K"
  shows "finite I \<and> finite K \<and> set rs \<subseteq> I \<and> I \<inter> (K \<union> V) = {}"
  using assms by (induction rule: pattern_vector_at.induct)
    (auto dest: pattern_quoted_boundary)

lemma pattern_vector_carrier:
  assumes vector: "pattern_vector_at E u V rs ps I K" and art: "artifact_at E u R"
  shows "I \<union> K \<subseteq> rra_carrier (object_structure R)"
  using vector by (induction rule: pattern_vector_at.induct)
    (use pattern_quoted_carrier[OF _ art] in auto)

theorem pattern_vector_unique:
  assumes first: "pattern_vector_at E u V rs ps I K" and second: "pattern_vector_at E u V rs qs J W"
  shows "ps=qs \<and> I=J \<and> K=W"
  using first second
proof (induction arbitrary: qs J W rule: pattern_vector_at.induct)
  case empty
  then show ?case by (simp add: pattern_vector_nil)
next
  case (cons r p A B rs ps I K)
  obtain q ts C D L X where other: "qs=q#ts" "pattern_quoted_at E u V r q C D"
    "pattern_vector_at E u V rs ts L X" "J=C \<union> L" "W=D \<union> X"
    using pattern_vector_cons[OF cons.prems] by blast
  have head: "p=q \<and> A=C \<and> B=D" by (rule pattern_quoted_unique[OF cons.hyps(1) other(2)])
  have tail: "ps=ts \<and> I=L \<and> K=X" by (rule cons.IH[OF other(3)])
  show ?case using head tail other(1,4,5) by simp
qed

definition pattern_record_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    local_address term_pattern list \<Rightarrow> local_address set \<Rightarrow> local_address set \<Rightarrow> bool" where
  "pattern_record_at E u V r ps I K \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ports roots J. artifact_at E u R \<and> record_at R r ports roots \<and>
      pattern_vector_at E u V roots ps J K \<and> insert r (set ports) \<inter> J = {} \<and>
      I=insert r (set ports \<union> J) \<and> I \<inter> (K \<union> V) = {})"

theorem pattern_record_unique:
  assumes first: "pattern_record_at E u V r ps I K" and second: "pattern_record_at E u V r qs J W"
  shows "ps=qs \<and> I=J \<and> K=W"
proof -
  have ef: "environment_formed E" using first by (simp add: pattern_record_at_def)
  obtain R ports roots A where left: "artifact_at E u R" "record_at R r ports roots"
    "pattern_vector_at E u V roots ps A K" "I=insert r (set ports \<union> A)"
    using first by (auto simp: pattern_record_at_def)
  obtain S sockets fields B where right: "artifact_at E u S" "record_at S r sockets fields"
    "pattern_vector_at E u V fields qs B W" "J=insert r (set sockets \<union> B)"
    using second by (auto simp: pattern_record_at_def)
  have art: "S=R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r sockets fields" using right(2) art by simp
  have positions: "sockets=ports \<and> fields=roots" by (rule record_at_unique[OF rec left(2)])
  have vector: "pattern_vector_at E u V roots qs B W" using right(3) positions by simp
  have same: "ps=qs \<and> A=B \<and> K=W" by (rule pattern_vector_unique[OF left(3) vector])
  show ?thesis using same positions left(4) right(4) by simp
qed

lemma pattern_record_formed:
  assumes "pattern_record_at E u V r ps I K"
  shows "environment_formed E \<and> (\<forall>p\<in>set ps. pattern_formed p \<and> pattern_variables p \<subseteq> V) \<and>
    r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> (K \<union> V) = {}"
proof -
  obtain R ports roots J where parts: "environment_formed E"
    "pattern_vector_at E u V roots ps J K" "I=insert r (set ports \<union> J)"
    "I \<inter> (K \<union> V) = {}"
    using assms by (auto simp: pattern_record_at_def)
  show ?thesis using parts(1,3,4) pattern_vector_formed[OF parts(2)] pattern_vector_boundary[OF parts(2)]
    by auto
qed

definition native_material_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    local_address material_pattern \<Rightarrow> local_address set \<Rightarrow> local_address set \<Rightarrow> bool" where
  "native_material_at E u V r M I K \<longleftrightarrow> pattern_record_at E u V r (material_fields M) I K"

theorem native_material_unique:
  assumes "native_material_at E u V r M I K" "native_material_at E u V r N J W"
  shows "M=N \<and> I=J \<and> K=W"
proof -
  have first: "pattern_record_at E u V r (material_fields M) I K"
    and second: "pattern_record_at E u V r (material_fields N) J W"
    using assms by (simp_all add: native_material_at_def)
  show ?thesis using pattern_record_unique[OF first second] by (simp add: material_fields_unique)
qed

lemma native_material_formed:
  assumes "native_material_at E u V r M I K"
  shows "environment_formed E \<and> material_pattern_formed M \<and> material_variables M \<subseteq> V \<and>
    r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> (K \<union> V) = {}"
proof -
  have rec: "pattern_record_at E u V r (material_fields M) I K"
    using assms by (simp add: native_material_at_def)
  show ?thesis using pattern_record_formed[OF rec]
    by (auto simp: material_pattern_formed_def material_variables_def)
qed

lemma native_material_five_fields:
  assumes "native_material_at E u V r M I K"
  shows "\<exists>R ports roots. artifact_at E u R \<and> record_at R r ports roots \<and> length roots=5"
proof -
  obtain R ports roots J where parts: "artifact_at E u R" "record_at R r ports roots"
    "pattern_vector_at E u V roots (material_fields M) J K"
    using assms by (auto simp: native_material_at_def pattern_record_at_def)
  have count: "length roots=5"
    using pattern_vector_formed[OF parts(3)] by (simp add: material_fields_def)
  show ?thesis using parts(1,2) count by blast
qed

lemma pattern_vector_reinterpretation:
  assumes vector: "pattern_vector_at E u V rs ps I K" and source: "artifact_at E u R"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w k"
    and ff: "environment_formed F" and target: "artifact_at F w R"
  shows "pattern_vector_at F w V rs ps I K"
  using vector slots
proof (induction rule: pattern_vector_at.induct)
  case empty
  show ?case by (rule pattern_vector_at.empty[OF ff])
next
  case (cons r p A B rs ps I K)
  have reads: "object_reads_agree R R A"
    using pattern_quoted_carrier[OF cons.hyps(1) source] by (auto simp: object_reads_agree_def)
  have head_slots: "\<forall>k\<in>B. external_slot_values E u k = external_slot_values F w k"
    and tail_slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w k"
    using cons.prems by auto
  have head: "pattern_quoted_at F w V r p A B"
    by (rule pattern_quotation_embedding[OF cons.hyps(1) source reads head_slots ff target])
  have tail: "pattern_vector_at F w V rs ps I K" by (rule cons.IH[OF tail_slots])
  show ?case by (rule pattern_vector_at.cons[OF head tail cons.hyps(3,4)])
qed

lemma pattern_record_reinterpretation:
  assumes rec: "pattern_record_at E u V r ps I K" and source: "artifact_at E u R"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w k"
    and ff: "environment_formed F" and target: "artifact_at F w R"
  shows "pattern_record_at F w V r ps I K"
proof -
  have ef: "environment_formed E" using rec by (simp add: pattern_record_at_def)
  obtain S ports roots J where parts: "artifact_at E u S" "record_at S r ports roots"
    "pattern_vector_at E u V roots ps J K" "insert r (set ports) \<inter> J = {}"
    "I=insert r (set ports \<union> J)" "I \<inter> (K \<union> V) = {}"
    using rec by (auto simp: pattern_record_at_def)
  have same: "S=R" by (rule environment_artifact_unique[OF ef parts(1) source])
  have rec_read: "record_at R r ports roots" using parts(2) same by simp
  have vector: "pattern_vector_at F w V roots ps J K"
    by (rule pattern_vector_reinterpretation[OF parts(3) source slots ff target])
  show ?thesis using ff target rec_read vector parts(4-6) unfolding pattern_record_at_def by blast
qed

lemma native_material_reinterpretation:
  assumes "native_material_at E u V r M I K" "artifact_at E u R"
    "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w k"
    "environment_formed F" "artifact_at F w R"
  shows "native_material_at F w V r M I K"
  using assms unfolding native_material_at_def by (rule pattern_record_reinterpretation)

section \<open>Renaming the complete material pattern boundary\<close>

definition rename_material_pattern ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a material_pattern \<Rightarrow> 'b material_pattern" where
  "rename_material_pattern f M =
    \<lparr>material_source = rename_pattern f (material_source M),
     material_atoms = rename_pattern f (material_atoms M),
     material_edges = rename_pattern f (material_edges M),
     material_counts = rename_pattern f (material_counts M),
     material_functions = rename_pattern f (material_functions M)\<rparr>"

lemma renamed_material_fields:
  "material_fields (rename_material_pattern f M) = map (rename_pattern f) (material_fields M)"
  by (simp add: rename_material_pattern_def material_fields_def)

lemma renamed_material_variables:
  "material_variables (rename_material_pattern f M) = f ` material_variables M"
  by (auto simp: material_variables_def renamed_material_fields rename_pattern_variables)

lemma renamed_material_formed [simp]:
  "material_pattern_formed (rename_material_pattern f M) = material_pattern_formed M"
  by (simp add: material_pattern_formed_def renamed_material_fields)

lemma rename_material_identity [simp]: "rename_material_pattern id M = M"
  by (cases M) (simp add: rename_material_pattern_def)

lemma rename_material_composition:
  "rename_material_pattern g (rename_material_pattern f M) = rename_material_pattern (g \<circ> f) M"
  by (simp add: rename_material_pattern_def rename_pattern_composition)

lemma rename_material_agreement:
  assumes agree: "\<forall>a\<in>material_variables M. f a = g a"
  shows "rename_material_pattern f M = rename_material_pattern g M"
proof -
  have each: "\<And>p. p \<in> set (material_fields M) \<Longrightarrow> rename_pattern f p = rename_pattern g p"
    by (rule rename_pattern_agreement) (use agree in \<open>auto simp: material_variables_def\<close>)
  have fields: "material_fields (rename_material_pattern f M) = material_fields (rename_material_pattern g M)"
    by (simp only: renamed_material_fields) (rule map_cong[OF refl], rule each; assumption)
  show ?thesis using fields by (simp add: material_fields_unique)
qed

theorem material_pattern_instance_renaming:
  assumes injective: "inj_on f (rel_dom V)" and scope: "material_variables M \<subseteq> rel_dom V"
  shows "material_pattern_instance (rename_term_bindings f V) (rename_material_pattern f M) s a e b g
    \<longleftrightarrow> material_pattern_instance V M s a e b g"
proof -
  have each: "\<And>p t. p \<in> set (material_fields M) \<Longrightarrow>
    pattern_instance (rename_term_bindings f V) (rename_pattern f p) t \<longleftrightarrow>
    pattern_instance V p t"
  proof -
    fix p t assume member: "p \<in> set (material_fields M)"
    have included: "pattern_variables p \<subseteq> rel_dom V"
      using scope member by (auto simp: material_variables_def)
    show "pattern_instance (rename_term_bindings f V) (rename_pattern f p) t \<longleftrightarrow>
      pattern_instance V p t"
      by (rule pattern_instance_renaming[OF injective included])
  qed
  show ?thesis
    by (simp add: material_pattern_instance_def rename_material_pattern_def
        each[of "material_source M" s, simplified material_fields_def]
        each[of "material_atoms M" a, simplified material_fields_def]
        each[of "material_edges M" e, simplified material_fields_def]
        each[of "material_counts M" b, simplified material_fields_def]
        each[of "material_functions M" g, simplified material_fields_def])
qed

theorem material_pattern_satisfied_renaming:
  assumes "inj_on f (rel_dom V)" "material_variables M \<subseteq> rel_dom V"
  shows "material_pattern_satisfied (rename_term_bindings f V) (rename_material_pattern f M)
    \<longleftrightarrow> material_pattern_satisfied V M"
  by (simp only: material_pattern_satisfied_def material_pattern_instance_renaming[OF assms])

theorem pattern_vector_transport:
  assumes vector: "pattern_vector_at E u V rs ps I K" and source: "artifact_at E u R"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (f ` I)"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    and injective: "inj f" and ff: "environment_formed F" and target: "artifact_at F w S"
  shows "pattern_vector_at F w (f ` V) (map f rs) (map (rename_pattern f) ps) (f ` I) (f ` K)"
  using vector reads slots
proof (induction rule: pattern_vector_at.induct)
  case empty
  show ?case by (simp add: pattern_vector_at.empty[OF ff])
next
  case (cons r p A B rs ps I K)
  have head_reads: "object_reads_agree (push_object f R) S (f ` A)"
    by (rule object_reads_agree_mono[OF cons.prems(1)]) blast
  have tail_reads: "object_reads_agree (push_object f R) S (f ` I)"
    by (rule object_reads_agree_mono[OF cons.prems(1)]) blast
  have head_slots: "\<forall>k\<in>B. external_slot_values E u k = external_slot_values F w (f k)"
    and tail_slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    using cons.prems(2) by auto
  have head: "pattern_quoted_at F w (f ` V) (f r) (rename_pattern f p) (f ` A) (f ` B)"
    by (rule pattern_quotation_transport[OF cons.hyps(1) source addressing head_reads
          head_slots injective ff target])
  have tail: "pattern_vector_at F w (f ` V) (map f rs) (map (rename_pattern f) ps) (f ` I) (f ` K)"
    by (rule cons.IH[OF tail_reads tail_slots])
  have separate: "f ` A \<inter> f ` I = {}"
    using cons.hyps(3) image_Int[OF injective, of A I] by simp
  have boundary: "(f ` A \<union> f ` I) \<inter> (f ` B \<union> f ` K) = {}"
    using cons.hyps(4) image_Int[OF injective, of "A \<union> I" "B \<union> K"]
    by (simp add: image_Un)
  show ?case using pattern_vector_at.cons[OF head tail separate boundary]
    by (simp add: image_Un)
qed

lemma pattern_vector_embedding:
  assumes vector: "pattern_vector_at E u V rs ps I K" and source: "artifact_at E u R"
    and reads: "object_reads_agree R S I"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w k"
    and ff: "environment_formed F" and target: "artifact_at F w S"
  shows "pattern_vector_at F w V rs ps I K"
proof -
  have ef: "environment_formed E" using pattern_vector_formed[OF vector] by blast
  have rf: "exact_formed R" using ef source unfolding environment_formed_def by blast
  have oformed: "object_formed R" using rf by (simp add: exact_formed_def)
  have addressing: "finite_addressing (rra_carrier (object_structure R)) id"
    using rf by (auto simp: exact_formed_def finite_addressing_def inj_on_def)
  have copied: "object_reads_agree (push_object id R) S (id ` I)"
    using reads push_object_identity[OF oformed] by simp
  have agreement: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (id k)"
    using slots by simp
  have result: "pattern_vector_at F w (id ` V) (map id rs) (map (rename_pattern id) ps) (id ` I) (id ` K)"
    by (rule pattern_vector_transport[OF vector source addressing copied agreement _ ff target]) simp
  have identity: "rename_pattern id = id"
    by (rule ext) (simp add: rename_pattern_def)
  show ?thesis using result by (simp add: identity)
qed

theorem pattern_record_transport:
  assumes rec: "pattern_record_at E u V r ps I K" and source: "artifact_at E u R"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (f ` I)"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    and injective: "inj f" and ff: "environment_formed F" and target: "artifact_at F w S"
  shows "pattern_record_at F w (f ` V) (f r) (map (rename_pattern f) ps) (f ` I) (f ` K)"
proof -
  have ef: "environment_formed E" using rec by (simp add: pattern_record_at_def)
  obtain T ports roots J where parts: "artifact_at E u T" "record_at T r ports roots"
    "pattern_vector_at E u V roots ps J K" "insert r (set ports) \<inter> J = {}"
    "I=insert r (set ports \<union> J)" "I \<inter> (K \<union> V) = {}"
    using rec by (auto simp: pattern_record_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF ef parts(1) source])
  have source_rec: "record_at R r ports roots" using parts(2) same by simp
  have local_inj: "inj_on f (rra_carrier (object_structure R))"
    using injective by (auto simp: inj_on_def)
  have copied: "record_at (push_object f R) (f r) (map f ports) (map f roots)"
    by (rule record_at_push[OF source_rec local_inj])
  have sf: "object_formed S" using ff target
    by (auto simp: environment_formed_def exact_formed_def)
  have recovered: "record_at S (f r) (map f ports) (map f roots)"
    by (rule record_at_read_transport[OF copied sf reads]) (use parts(5) in auto)
  have child_reads: "object_reads_agree (push_object f R) S (f ` J)"
    by (rule object_reads_agree_mono[OF reads]) (use parts(5) in blast)
  have children: "pattern_vector_at F w (f ` V) (map f roots)
    (map (rename_pattern f) ps) (f ` J) (f ` K)"
    by (rule pattern_vector_transport[OF parts(3) source addressing child_reads slots injective ff target])
  have separate: "insert (f r) (set (map f ports)) \<inter> f ` J = {}"
    using image_Int[OF injective, of "insert r (set ports)" J] parts(4) by simp
  have boundary: "f ` I \<inter> (f ` K \<union> f ` V) = {}"
    using image_Int[OF injective, of I "K \<union> V"] parts(6) by (simp add: image_Un)
  show ?thesis
    unfolding pattern_record_at_def
    apply (rule conjI[OF ff])
    apply (rule exI[of _ S], rule exI[of _ "map f ports"], rule exI[of _ "map f roots"],
        rule exI[of _ "f ` J"])
    using target recovered children separate boundary parts(5)
    by (simp add: image_Un)
qed

theorem native_material_transport:
  assumes "native_material_at E u V r M I K" "artifact_at E u R"
    "finite_addressing (rra_carrier (object_structure R)) f"
    "object_reads_agree (push_object f R) S (f ` I)"
    "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    "inj f" "environment_formed F" "artifact_at F w S"
  shows "native_material_at F w (f ` V) (f r) (rename_material_pattern f M) (f ` I) (f ` K)"
  using pattern_record_transport[OF assms[unfolded native_material_at_def]]
  by (simp add: native_material_at_def renamed_material_fields)

text \<open>
  Each of the five fields supplies one ordinary pattern operand of the material
  equation. The record's actual field order recovers those roles. No unused
  discriminator is present. The mathematical record above is this unique
  projection, rather than a separate signature supplied beside the artifact.
  Satisfaction evaluates the one fixed material equation after instantiation;
  recovering the pattern invokes no truth or evidence predicate.
\<close>

end
