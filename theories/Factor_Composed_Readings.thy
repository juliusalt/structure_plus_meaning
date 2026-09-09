theory Factor_Composed_Readings
  imports Factor_Reader_Clauses Factor_Presentation_Transport
begin

section \<open>Two readers share one actual intermediate presentation\<close>

definition composed_reading_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "composed_reading_schema first second=data_rule (Pattern_Pair data_x data_z)
    {(0,first,Pattern_Pair data_x data_y),(1,second,Pattern_Pair data_y data_z)}"

lemma composed_reading_schema_formed [simp]:
  "schema_formed (composed_reading_schema first second)"
  by (auto simp: composed_reading_schema_def schema_formed_def single_valued_def)

lemma composed_reading_schema_dependencies [simp]:
  "schema_dependencies (composed_reading_schema first second)={first,second}"
  by (simp add: composed_reading_schema_def schema_dependencies_def rel_ran_image)

lemma composed_reading_schema_ordinary [simp]:
  "schema_material_premises (composed_reading_schema first second)={}"
  by (simp add: composed_reading_schema_def)

locale composed_reading_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry first second :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>{(0,composed_reading_schema first second)}"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 2) \<and>
      (first,Pair_Term (h 0) (h 1))\<in>positive_meaning P \<and>
      (second,Pair_Term (h 1) (h 2))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family composed_reading_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q r. t=Pair_Term p r \<and> (first,Pair_Term p q)\<in>positive_meaning P \<and>
      (second,Pair_Term q r)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>p q r. t=Pair_Term p r \<and> (first,Pair_Term p q)\<in>positive_meaning P \<and>
      (second,Pair_Term q r)\<in>positive_meaning P"
    by (simp only: valuation; blast)
next
  assume "\<exists>p q r. t=Pair_Term p r \<and> (first,Pair_Term p q)\<in>positive_meaning P \<and>
      (second,Pair_Term q r)\<in>positive_meaning P"
  then obtain p q r where shape: "t=Pair_Term p r"
    and support: "(first,Pair_Term p q)\<in>positive_meaning P" "(second,Pair_Term q r)\<in>positive_meaning P"
    by blast
  have formed: "term_formed p" "term_formed q" "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF support(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF support(2)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then q else r"
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h]) (use shape support formed in auto)
qed

corollary at_pair:
  "(entry,Pair_Term p r)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>q. (first,Pair_Term p q)\<in>positive_meaning P \<and> (second,Pair_Term q r)\<in>positive_meaning P)"
  by (auto simp: exact)

theorem function_contract:
  assumes first_contract: "presented_function_contract R D A S E B f
      (\<lambda>p q. (first,Pair_Term p q)\<in>positive_meaning P)"
    and second_contract: "presented_function_contract S E B T F C g
      (\<lambda>q r. (second,Pair_Term q r)\<in>positive_meaning P)"
  shows "presented_function_contract R D A T F C (g\<circ>f)
    (\<lambda>p r. (entry,Pair_Term p r)\<in>positive_meaning P)"
proof -
  interpret first: presented_function_contract R D A S E B f
    "\<lambda>p q. (first,Pair_Term p q)\<in>positive_meaning P" by (rule first_contract)
  interpret second: presented_function_contract S E B T F C g
    "\<lambda>q r. (second,Pair_Term q r)\<in>positive_meaning P" by (rule second_contract)
  have meaning: "(entry,Pair_Term p r)\<in>positive_meaning P \<longleftrightarrow>
      presented_relation R T (\<lambda>a c. c=(g\<circ>f) a) p r" for p r
    by (simp only: at_pair first.exact second.exact
        presented_relation_compose[OF first.right.presentation_class_axioms])
      (use first.image_boundary first.left.subject_boundary in \<open>auto simp: presented_relation_def; blast\<close>)
  show ?thesis using first.left.presentation_class_axioms second.right.presentation_class_axioms
    first.image_boundary second.image_boundary meaning
    by (auto simp: presented_function_contract_def presented_function_contract_axioms_def
      presented_relation_contract_def presented_relation_contract_axioms_def)
qed

end

theorem composed_reading_view:
  assumes "schema_system_formed P" "entry\<notin>system_definitions P"
    "first\<in>system_definitions P" "second\<in>system_definitions P"
  shows "positive_view P entry data_x {(0,composed_reading_schema first second)}"
  by (rule positive_view.intro[OF assms(1,2)]) (use assms in \<open>auto simp: single_valued_def\<close>)

theorem composed_reading_view_profile:
  assumes view: "positive_view P entry data_x {(0,composed_reading_schema first second)}"
  shows "composed_reading_profile
    (add_view_definition P entry data_x {(0,composed_reading_schema first second)}) entry first second"
proof -
  interpret view: positive_view P entry data_x "{(0,composed_reading_schema first second)}" by (rule view)
  show ?thesis by (unfold_locales)
    (use view.formed view.view_call view.no_old_clause in auto)
qed

text \<open>
  Each premise has its own socket and both calls share the actual intermediate
  term. Callees may coincide. Complete function contracts at the same
  intermediate class suffice for the composed contract, including all its
  output presentations. The class's recovery and coverage discharge the
  intermediate relationship through the general relational composition law.

  Different intermediate classes still need their explicit correspondence.
  No arbitrary mathematical function becomes a native callee. The clause,
  its finite interface and dependencies, and its native compilation are
  ordinary instances of the existing view and program constructions.
\<close>

end
