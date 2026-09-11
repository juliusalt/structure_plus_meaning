theory Factor_Historical_Views
  imports Factor_System_Unions Factor_Tagged_Views
begin

section \<open>Finite interface and truth views of a complete earlier program\<close>

locale historical_views =
  fixes P :: "('a,'s,'d,'c) schema_system" and Q :: "('a,'s,'e,'c) schema_system"
    and label :: "'d \<Rightarrow> factor_term" and key :: "'d \<Rightarrow> 'c"
    and a :: 'a and s :: 's
  assumes source_formed: "schema_system_formed P"
    and other_formed: "schema_system_formed Q"
    and labels_formed: "\<forall>d\<in>system_definitions P. term_formed (label d)"
    and keys: "inj_on key (system_definitions P)"
begin

abbreviation combined :: "('a,'s,('d+'e)+bool,'c) schema_system" where
  "combined \<equiv> rename_system Inl (separated_systems P Q)"

lemma combined_formed: "schema_system_formed combined"
  by (rule renamed_system_formed[OF separated_systems_formed[OF source_formed other_formed]])
    (auto simp: inj_on_def)

lemma combined_definitions [simp]:
  "system_definitions combined =
    (\<lambda>d. Inl (Inl d)) ` system_definitions P \<union>
    (\<lambda>d. Inl (Inr d)) ` system_definitions Q"
  by (simp add: renamed_system_definitions image_Un image_image)

lemma combined_source:
  assumes member: "d\<in>system_definitions P"
  shows "schema_call_formed combined (Inl (Inl d)) t \<longleftrightarrow> schema_call_formed P d t"
    and "(Inl (Inl d),t)\<in>positive_meaning combined \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have formed: "schema_system_formed (separated_systems P Q)"
    by (rule separated_systems_formed[OF source_formed other_formed])
  have injective: "inj_on Inl (system_definitions (separated_systems P Q))"
    by (auto simp: inj_on_def)
  have inside: "Inl d\<in>system_definitions (separated_systems P Q)" using member by simp
  show "schema_call_formed combined (Inl (Inl d)) t \<longleftrightarrow> schema_call_formed P d t"
    using renamed_system_call[OF formed injective inside, of t]
      separated_systems_left(1)[OF source_formed other_formed member, of t] by blast
  have renamed: "(Inl (Inl d),t)\<in>positive_meaning combined \<longleftrightarrow>
    (Inl d,t)\<in>positive_meaning (separated_systems P Q)"
    by (auto simp: renamed_system_positive_meaning[OF formed injective] map_prod_def)
  show "(Inl (Inl d),t)\<in>positive_meaning combined \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    using renamed separated_systems_left(2)[OF source_formed other_formed member, of t] by blast
qed

lemma combined_other:
  assumes member: "d\<in>system_definitions Q"
  shows "schema_call_formed combined (Inl (Inr d)) t \<longleftrightarrow> schema_call_formed Q d t"
    and "(Inl (Inr d),t)\<in>positive_meaning combined \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
proof -
  have formed: "schema_system_formed (separated_systems P Q)"
    by (rule separated_systems_formed[OF source_formed other_formed])
  have injective: "inj_on Inl (system_definitions (separated_systems P Q))"
    by (auto simp: inj_on_def)
  have inside: "Inr d\<in>system_definitions (separated_systems P Q)" using member by simp
  show "schema_call_formed combined (Inl (Inr d)) t \<longleftrightarrow> schema_call_formed Q d t"
    using renamed_system_call[OF formed injective inside, of t]
      separated_systems_right(1)[OF source_formed other_formed member, of t] by blast
  have renamed: "(Inl (Inr d),t)\<in>positive_meaning combined \<longleftrightarrow>
    (Inr d,t)\<in>positive_meaning (separated_systems P Q)"
    by (auto simp: renamed_system_positive_meaning[OF formed injective] map_prod_def)
  show "(Inl (Inr d),t)\<in>positive_meaning combined \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
    using renamed separated_systems_right(2)[OF source_formed other_formed member, of t] by blast
qed

definition admission_clauses :: "('c \<times> ('a,'s,('d+'e)+bool) factor_schema) set" where
  "admission_clauses =
    (\<lambda>d. (key d,recognizer_schema
      (Pattern_Pair (exact_term_pattern (label d)) (system_interface P d)))) ` system_definitions P"

definition truth_clauses :: "('c \<times> ('a,'s,('d+'e)+bool) factor_schema) set" where
  "truth_clauses =
    (\<lambda>d. (key d,tagged_call_schema a s (label d) (Inl (Inl d)))) ` system_definitions P"

abbreviation with_admission where
  "with_admission \<equiv> add_view_definition combined (Inr False) (Pattern_Variable a) admission_clauses"

abbreviation extended where
  "extended \<equiv> add_view_definition with_admission (Inr True) (Pattern_Variable a) truth_clauses"

sublocale admission: positive_view combined "Inr False" "Pattern_Variable a" admission_clauses
proof (rule positive_view.intro)
  show "schema_system_formed combined" by (rule combined_formed)
  show "Inr False\<notin>system_definitions combined" by auto
  show "pattern_formed (Pattern_Variable a)" by simp
  show "finite admission_clauses"
    using system_definitions_finite[OF source_formed] by (simp add: admission_clauses_def)
  show "single_valued admission_clauses"
    using keys by (auto simp: admission_clauses_def single_valued_def inj_on_def)
  show "\<forall>c S. (c,S)\<in>admission_clauses \<longrightarrow> schema_formed S"
    using labels_formed system_interface_formed[OF source_formed]
    by (auto simp: admission_clauses_def)
  show "\<forall>c S. (c,S)\<in>admission_clauses \<longrightarrow> schema_dependencies S \<subseteq> system_definitions combined"
    by (auto simp: admission_clauses_def recognizer_schema_def schema_dependencies_def rel_ran_def)
qed

sublocale truth: positive_view with_admission "Inr True" "Pattern_Variable a" truth_clauses
proof (rule positive_view.intro)
  show "schema_system_formed with_admission" by (rule admission.formed)
  show "Inr True\<notin>system_definitions with_admission" by auto
  show "pattern_formed (Pattern_Variable a)" by simp
  show "finite truth_clauses"
    using system_definitions_finite[OF source_formed] by (simp add: truth_clauses_def)
  show "single_valued truth_clauses"
    using keys by (auto simp: truth_clauses_def single_valued_def inj_on_def)
  show "\<forall>c S. (c,S)\<in>truth_clauses \<longrightarrow> schema_formed S"
    using labels_formed by (auto simp: truth_clauses_def)
  show "\<forall>c S. (c,S)\<in>truth_clauses \<longrightarrow> schema_dependencies S \<subseteq> system_definitions with_admission"
    by (auto simp: truth_clauses_def)
qed

lemma formed: "schema_system_formed extended"
  by (rule truth.formed)

lemma definitions:
  "system_definitions extended =
    insert (Inr True) (insert (Inr False)
      ((\<lambda>d. Inl (Inl d)) ` system_definitions P \<union>
       (\<lambda>d. Inl (Inr d)) ` system_definitions Q))"
  by simp

theorem source_calls:
  assumes member: "d\<in>system_definitions P"
  shows "schema_call_formed extended (Inl (Inl d)) t \<longleftrightarrow> schema_call_formed P d t"
proof -
  have base: "Inl (Inl d)\<in>system_definitions combined" using member by auto
  have after_admission: "Inl (Inl d)\<in>system_definitions with_admission" using base by simp
  show ?thesis by (simp only: truth.old_calls[OF after_admission] admission.old_calls[OF base] combined_source(1)[OF member])
qed

theorem source_meaning:
  assumes member: "d\<in>system_definitions P"
  shows "(Inl (Inl d),t)\<in>positive_meaning extended \<longleftrightarrow> (d,t)\<in>positive_meaning P"
proof -
  have base: "Inl (Inl d)\<in>system_definitions combined" using member by auto
  have after_admission: "Inl (Inl d)\<in>system_definitions with_admission" using base by simp
  show ?thesis by (simp only: truth.old_meaning[OF after_admission] admission.old_meaning[OF base] combined_source(2)[OF member])
qed

theorem other_calls:
  assumes member: "d\<in>system_definitions Q"
  shows "schema_call_formed extended (Inl (Inr d)) t \<longleftrightarrow> schema_call_formed Q d t"
proof -
  have base: "Inl (Inr d)\<in>system_definitions combined" using member by auto
  have after_admission: "Inl (Inr d)\<in>system_definitions with_admission" using base by simp
  show ?thesis by (simp only: truth.old_calls[OF after_admission] admission.old_calls[OF base] combined_other(1)[OF member])
qed

theorem other_meaning:
  assumes member: "d\<in>system_definitions Q"
  shows "(Inl (Inr d),t)\<in>positive_meaning extended \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
proof -
  have base: "Inl (Inr d)\<in>system_definitions combined" using member by auto
  have after_admission: "Inl (Inr d)\<in>system_definitions with_admission" using base by simp
  show ?thesis by (simp only: truth.old_meaning[OF after_admission] admission.old_meaning[OF base] combined_other(2)[OF member])
qed

lemma admission_call: "schema_call_formed extended (Inr False) x \<longleftrightarrow> term_formed x"
proof -
  have member: "Inr False\<in>system_definitions with_admission" by simp
  show ?thesis by (simp only: truth.old_calls[OF member] admission.view_call variable_accepts)
qed

lemma truth_call: "schema_call_formed extended (Inr True) x \<longleftrightarrow> term_formed x"
  by (simp only: truth.view_call variable_accepts)

theorem admission_meaning:
  "(Inr False,x)\<in>positive_meaning extended \<longleftrightarrow>
    (\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t)"
proof -
  have each: "schema_rule_instance (recognizer_schema
    (Pattern_Pair (exact_term_pattern (label d)) (system_interface P d))) X x \<longleftrightarrow>
    (\<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t)"
    if member: "d\<in>system_definitions P" for d X
  proof -
    have lf: "term_formed (label d)" using labels_formed member by blast
    show ?thesis
      by (simp only: recognizer_schema_rule tagged_pattern_accepts[OF lf]
        schema_call_at_interface[OF source_formed]) (use member in blast)
  qed
  have rules: "(\<exists>c S. (c,S)\<in>admission_clauses \<and>
      schema_rule_instance S (positive_meaning combined) x) \<longleftrightarrow>
    (\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t)"
  proof
    assume "\<exists>c S. (c,S)\<in>admission_clauses \<and> schema_rule_instance S (positive_meaning combined) x"
    then show "\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t"
      by (auto simp: admission_clauses_def each)
  next
    assume "\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t"
    then obtain d t where parts: "d\<in>system_definitions P" "schema_call_formed P d t"
      "x=Pair_Term (label d) t" by blast
    let ?S="recognizer_schema (Pattern_Pair (exact_term_pattern (label d)) (system_interface P d))"
    have selected: "(key d,?S)\<in>admission_clauses"
      unfolding admission_clauses_def by (rule rev_image_eqI[OF parts(1)]) simp
    have rule: "schema_rule_instance ?S (positive_meaning combined) x"
      using each[OF parts(1), of "positive_meaning combined"] parts(2,3) by blast
    show "\<exists>c S. (c,S)\<in>admission_clauses \<and> schema_rule_instance S (positive_meaning combined) x"
      using selected rule by blast
  qed
  have terms: "term_formed x" if witness:
    "\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and> x=Pair_Term (label d) t"
  proof -
    obtain d t where parts: "d\<in>system_definitions P" "schema_call_formed P d t"
      "x=Pair_Term (label d) t" using witness by blast
    show ?thesis using labels_formed parts schema_call_formed_target[OF parts(2)] by auto
  qed
  have member: "Inr False\<in>system_definitions with_admission" by simp
  show ?thesis
    by (simp only: truth.old_meaning[OF member] admission.view_meaning variable_accepts rules)
      (use terms in blast)
qed

theorem truth_meaning:
  "(Inr True,x)\<in>positive_meaning extended \<longleftrightarrow>
    (\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t)"
proof -
  have terms: "\<And>d t. (d,t)\<in>positive_meaning P \<Longrightarrow> term_formed t"
  proof -
    fix d t assume positive: "(d,t)\<in>positive_meaning P"
    have call: "schema_call_formed P d t" by (rule positive_meaning_formed[OF positive])
    show "term_formed t" using schema_call_formed_target[OF call] by blast
  qed
  have each: "schema_rule_instance (tagged_call_schema a s (label d) (Inl (Inl d)))
    (positive_meaning with_admission) x \<longleftrightarrow>
    (\<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t)"
    if member: "d\<in>system_definitions P" for d
  proof -
    have lf: "term_formed (label d)" using labels_formed member by blast
    have inside: "Inl (Inl d)\<in>system_definitions combined" using member by auto
    have prior: "\<And>t. (Inl (Inl d),t)\<in>positive_meaning with_admission \<longleftrightarrow>
      (d,t)\<in>positive_meaning P"
      by (simp only: admission.old_meaning[OF inside] combined_source(2)[OF member])
    show ?thesis by (simp only: tagged_call_schema_rule lf prior) (use terms in blast)
  qed
  have rules: "(\<exists>c S. (c,S)\<in>truth_clauses \<and>
      schema_rule_instance S (positive_meaning with_admission) x) \<longleftrightarrow>
    (\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t)"
  proof
    assume "\<exists>c S. (c,S)\<in>truth_clauses \<and> schema_rule_instance S (positive_meaning with_admission) x"
    then show "\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t"
      by (auto simp: truth_clauses_def each)
  next
    assume "\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t"
    then obtain d t where parts: "d\<in>system_definitions P" "(d,t)\<in>positive_meaning P"
      "x=Pair_Term (label d) t" by blast
    let ?S="tagged_call_schema a s (label d) (Inl (Inl d))"
    have selected: "(key d,?S)\<in>truth_clauses"
      unfolding truth_clauses_def by (rule rev_image_eqI[OF parts(1)]) simp
    have rule: "schema_rule_instance ?S (positive_meaning with_admission) x"
      using each[OF parts(1)] parts(2,3) by blast
    show "\<exists>c S. (c,S)\<in>truth_clauses \<and> schema_rule_instance S (positive_meaning with_admission) x"
      using selected rule by blast
  qed
  have result_formed: "term_formed x" if witness:
    "\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and> x=Pair_Term (label d) t"
    using witness labels_formed terms by auto
  show ?thesis by (simp only: truth.view_meaning variable_accepts rules) (use result_formed in blast)
qed

end

text \<open>
  Every old definition contributes one interface-recognition clause and one
  truth-forwarding clause. Both complete families are finite, even when their
  call relations are infinite. The source interfaces are copied exactly; the
  truth clauses invoke the correspondingly relocated old definitions. The
  separate other program may have any formed interfaces, clauses, and meaning.

  The two new roots are construction coordinates for ordinary definitions.
  Formation and truth have separate entries because a formed old call may be
  false. Both query interfaces accept every formed term, and the proved output
  equations account for every positive result, including rejection of unrelated
  shapes. No old call domain is replaced by a finite list of arguments.
\<close>

end
