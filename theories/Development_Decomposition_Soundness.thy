theory Development_Decomposition_Soundness
  imports Development_Definition_Verification Development_Refinement_Repair Development_Decomposition
begin

section \<open>The predicate a problem's contract states\<close>

text \<open>
  A problem's contract names its subject and the kind of statement its answer must establish; the
  request that issues it adds what the answer may use (its support) and what must stay unchanged.
  The two are kept apart. The predicate of the contract is read of a state judged against the table
  the problem was posed in: every constant of the subject has, in the judged state, a statement of the
  demanded kind, and every constant such a statement mentions is declared there. It is stated once
  over the demanded reading, as the verdict is, and an accepted verdict of either kind establishes it
  for the one constant of its problem.

  The verdict itself is not the predicate a decomposition reduces. It judges an answer against the
  state its problem was posed in and permits only statements of the subject to be added, so an answer
  that also defines the intermediates a decomposition names is refused there
  (\<open>development_refinement_verdict_refuses_definitions\<close>): the children's requests carry the
  intermediates in their supports, which the parent's request did not. What composes is the
  contract, and the requests of the children are the decomposition's own.
\<close>

definition development_stated_in ::
    "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> String.literal list \<Rightarrow> isabelle_context \<Rightarrow> nat fset \<Rightarrow> bool" where
  "development_stated_in demanded names C' P \<longleftrightarrow> P\<noteq>{||} \<and>
    (\<forall>c. c |\<in>| P \<longrightarrow> (\<exists>e\<in>set (snd C'). development_answer_statement demanded C'
        {|isabelle_state_embedding names (fst C') c|} e \<and>
      (\<forall>q. isabelle_specified_proposition e=Some q \<longrightarrow>
        set (isabelle_term_constants q)\<subseteq>set (List.map_filter isabelle_declared_constant (snd C')))))"

lemma isabelle_assessment_closed_declared:
  assumes closed: "isabelle_assessment_closed (isabelle_context_assessment roots C)"
    and member: "e\<in>set (snd C)" and statement: "isabelle_specified_proposition e=Some q"
  shows "set (isabelle_term_constants q)\<subseteq>set (List.map_filter isabelle_declared_constant (snd C))"
proof
  fix d assume d: "d\<in>set (isabelle_term_constants q)"
  have "fset_of_list (isabelle_undeclared_constants roots C)={||}"
    using closed by (simp add: isabelle_assessment_closed_def isabelle_context_assessment_def)
  then have "set (isabelle_undeclared_constants roots C)={}"
    by (metis fset_of_list.rep_eq bot_fset.rep_eq)
  moreover have "d\<in>set (isabelle_mentioned_constants roots C)"
    unfolding isabelle_mentioned_constants_def using member statement d by (auto intro!: bexI[of _ e])
  ultimately show "d\<in>set (List.map_filter isabelle_declared_constant (snd C))"
    using isabelle_undeclared_constants_exact[of d roots C] by (metis empty_iff)
qed

theorem development_constant_verdict_states:
  assumes accepted: "development_verdict_accepted
      (development_constant_verdict replaceable demanded S (p,s,support,E) S')"
    and subject: "problem_subject p={|c|}"
  shows "development_stated_in demanded (fst (snd S)) (snd S') {|c|}"
proof -
  obtain e where member: "e\<in>set (snd (snd S'))"
    and statement: "development_answer_statement demanded (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject p)) e"
    using development_constant_verdict_contract(3)[OF accepted] by blast
  have closed: "isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))"
    by (rule development_constant_verdict_contract(5)[OF accepted])
  show ?thesis
    unfolding development_stated_in_def
    using member statement subject isabelle_assessment_closed_declared[OF closed member] by auto
qed

corollary development_refinement_verdict_states:
  assumes "development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
    "problem_subject p={|c|}"
  shows "development_stated_in (development_demanded isabelle_code_equation_proposition)
    (fst (snd S)) (snd S') {|c|}"
  using assms unfolding development_refinement_verdict_def by (rule development_constant_verdict_states)

corollary development_definition_verdict_states:
  assumes "development_verdict_accepted (development_definition_verdict S (p,s,support,E) S')"
    "problem_subject p={|c|}"
  shows "development_stated_in (development_demanded isabelle_definition_proposition)
    (fst (snd S)) (snd S') {|c|}"
  using assms unfolding development_definition_verdict_def by (rule development_constant_verdict_states)

theorem development_refinement_verdict_refuses_definitions:
  assumes added: "Isabelle_Definition q\<in>set (isabelle_state_added (snd S) (snd S'))"
  shows "\<not>development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
proof -
  have refused: "\<not>development_answer_statement (development_demanded isabelle_code_equation_proposition) C P
      (Isabelle_Definition q)" for C P
    by (simp add: development_answer_statement_def development_demanded_def)
  show ?thesis
  proof
    assume "development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
    then have "\<forall>e\<in>set (isabelle_state_added (snd S) (snd S')).
        development_answer_statement (development_demanded isabelle_code_equation_proposition) (snd S')
          (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject p)) e"
      unfolding development_refinement_verdict_def development_constant_verdict_def
        development_verdict_accepted_def Let_def
      by (simp add: filter_empty_conv)
    then show False using added refused by blast
  qed
qed

section \<open>The kind of a contract selects its reading\<close>

fun development_contract_reading :: "development_contract \<Rightarrow> isabelle_entity \<Rightarrow> isabelle_term option" where
  "development_contract_reading (Development_Refinement t)=isabelle_code_equation_proposition"
| "development_contract_reading (Development_Definition t)=isabelle_definition_proposition"
| "development_contract_reading (Development_Proof t)=(\<lambda>_. None)"
| "development_contract_reading (Development_Presentation t)=(\<lambda>_. None)"
| "development_contract_reading (Development_Amendment t)=(\<lambda>_. None)"

fun development_contract_kind :: "development_contract \<Rightarrow> isabelle_term \<Rightarrow> development_contract" where
  "development_contract_kind (Development_Refinement t)=Development_Refinement"
| "development_contract_kind (Development_Definition t)=Development_Definition"
| "development_contract_kind (Development_Proof t)=Development_Proof"
| "development_contract_kind (Development_Presentation t)=Development_Presentation"
| "development_contract_kind (Development_Amendment t)=Development_Amendment"

lemma development_contract_reading_kind [simp]:
  "development_contract_reading (development_contract_kind k t)=development_contract_reading k"
  by (cases k) simp_all

text \<open>
  The predicate of a problem reads its contract's kind: a refinement demands code equations, a
  definition kernel definitions; a proof, presentation or amendment problem is not a problem of a
  constant here and states nothing a decomposition could reduce.
\<close>

definition development_problem_stated ::
    "String.literal list \<Rightarrow> isabelle_context \<Rightarrow> development_problem \<Rightarrow> bool" where
  "development_problem_stated names C' p \<longleftrightarrow> development_stated_in
     (development_demanded (development_contract_reading (problem_contract p))) names C' (problem_subject p)"

lemma development_constant_problem_contract:
  assumes "development_constant_problem reading kind C r a c=Some q"
  shows "\<exists>t. problem_contract q=kind t"
  using assms unfolding development_constant_problem_def development_constant_contract_def by auto

section \<open>The general schema: intermediates first, then one part per subject constant\<close>

text \<open>
  An application names intermediates and never invents them. Each intermediate becomes a definition
  problem and each constant of the parent's subject a problem of the parent's own kind, both over the
  state the application is read in, which holds the intermediates. The children are one functional
  family of sockets, the intermediates first. The material the schema reads off the state (the
  parent's support and its partition among the intermediates) decides where it applies and is
  observed separately; the soundness does not depend on it.
\<close>

definition development_intermediate_problem :: "isabelle_context \<Rightarrow> nat \<Rightarrow> development_problem option" where
  "development_intermediate_problem C h=development_constant_problem isabelle_definition_proposition
     Development_Definition C Development_Demand Development_Generated h"

definition development_part_problem ::
    "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat \<Rightarrow> development_problem option" where
  "development_part_problem C p c=development_constant_problem
     (development_contract_reading (problem_contract p)) (development_contract_kind (problem_contract p))
     C Development_Demand Development_Generated c"

definition development_decomposition_application ::
    "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat list \<Rightarrow> (nat\<times>development_problem) fset \<Rightarrow> bool" where
  "development_decomposition_application C p I H \<longleftrightarrow> problem_subject p\<noteq>{||} \<and>
    (\<exists>ds rs. list_all2 (\<lambda>h q. development_intermediate_problem C h=Some q) I ds \<and>
      list_all2 (\<lambda>c q. development_part_problem C p c=Some q) (sorted_list_of_fset (problem_subject p)) rs \<and>
      H=fset_of_list (zip [0..<length (ds@rs)] (ds@rs)))"

lemma list_all2_left_member:
  "list_all2 P xs ys \<Longrightarrow> x\<in>set xs \<Longrightarrow> \<exists>y\<in>set ys. P x y"
  by (induction rule: list_all2_induct) auto

lemma list_all2_some_map_filter:
  "list_all2 (\<lambda>x y. f x=Some y) xs ys \<Longrightarrow> List.map_filter f xs=ys"
  by (induction rule: list_all2_induct) (simp_all add: List.map_filter_simps)

lemma list_all2_some_the:
  "(\<forall>x\<in>set xs. f x\<noteq>None) \<Longrightarrow> list_all2 (\<lambda>x y. f x=Some y) xs (map (the \<circ> f) xs)"
  by (induction xs) auto

lemma zip_indices_values: "snd ` set (zip [0..<length zs] zs)=set zs"
  using zip_range[of "[0..<length zs]" zs] by (simp add: rel_ran_image)

lemma zip_indices_functional: "single_valued (set (zip [0..<length zs] zs))"
  by (rule single_valued_zip) simp

lemma development_decomposition_application_functional:
  assumes "development_decomposition_application C p I H"
  shows "single_valued (fset H)"
proof -
  obtain zs where "H=fset_of_list (zip [0..<length zs] zs)"
    using assms unfolding development_decomposition_application_def by blast
  then show ?thesis using zip_indices_functional[of zs] by (simp add: fset_of_list.rep_eq)
qed

theorem development_decomposition_application_exists:
  assumes subject: "problem_subject p\<noteq>{||}"
    and intermediates: "\<forall>h\<in>set I. development_intermediate_problem C h\<noteq>None"
    and parts: "\<forall>c. c |\<in>| problem_subject p \<longrightarrow> development_part_problem C p c\<noteq>None"
  shows "\<exists>H. development_decomposition_application C p I H"
proof -
  have "\<forall>c\<in>set (sorted_list_of_fset (problem_subject p)). development_part_problem C p c\<noteq>None"
    using parts by simp
  then show ?thesis
    unfolding development_decomposition_application_def
    using subject list_all2_some_the[OF intermediates] list_all2_some_the by blast
qed

section \<open>Every application reduces its parent to its children\<close>

theorem development_decomposition_stated:
  assumes application: "development_decomposition_application C p I H"
    and children: "\<And>s q. (s,q) |\<in>| H \<Longrightarrow> development_problem_stated names C' q"
  shows "development_problem_stated names C' p"
proof -
  obtain ds rs where nonempty: "problem_subject p\<noteq>{||}"
    and parts: "list_all2 (\<lambda>c q. development_part_problem C p c=Some q)
      (sorted_list_of_fset (problem_subject p)) rs"
    and family: "H=fset_of_list (zip [0..<length (ds@rs)] (ds@rs))"
    using application unfolding development_decomposition_application_def by blast
  have member: "development_problem_stated names C' q" if "q\<in>set rs" for q
  proof -
    have "q\<in>snd ` fset H" using that family zip_indices_values[of "ds@rs"] by (simp add: fset_of_list.rep_eq)
    then obtain s where "(s,q)\<in>fset H" by auto
    then show ?thesis by (rule children)
  qed
  have "\<exists>e\<in>set (snd C'). development_answer_statement
      (development_demanded (development_contract_reading (problem_contract p))) C'
        {|isabelle_state_embedding names (fst C') c|} e \<and>
      (\<forall>q. isabelle_specified_proposition e=Some q \<longrightarrow>
        set (isabelle_term_constants q)\<subseteq>set (List.map_filter isabelle_declared_constant (snd C')))"
    if c: "c |\<in>| problem_subject p" for c
  proof -
    obtain q where q: "q\<in>set rs" and part: "development_part_problem C p c=Some q"
      using list_all2_left_member[OF parts] c by auto
    have subject: "problem_subject q={|c|}"
      using part unfolding development_part_problem_def by (rule development_constant_problem_subject)
    obtain t where contract: "problem_contract q=development_contract_kind (problem_contract p) t"
      using part unfolding development_part_problem_def by (blast dest: development_constant_problem_contract)
    show ?thesis
      using member[OF q] subject contract
      unfolding development_problem_stated_def development_stated_in_def by auto
  qed
  then show ?thesis
    using nonempty unfolding development_problem_stated_def development_stated_in_def by blast
qed

section \<open>A library of applications is sound, and settles only stated problems\<close>

definition development_decomposition_library ::
    "(development_problem\<times>(nat\<times>development_problem) fset) fset \<Rightarrow> bool" where
  "development_decomposition_library L \<longleftrightarrow>
    (\<forall>p H. (p,H) |\<in>| L \<longrightarrow> (\<exists>C I. development_decomposition_application C p I H))"

theorem development_decomposition_sound:
  assumes library: "development_decomposition_library L"
    and answered: "\<And>p. p |\<in>| answered \<Longrightarrow> development_problem_stated names C' p"
  shows "inference_sound (development_problem_stated names C')
    (finite_inference_rules (development_answered_rules D answered |\<union>| L))"
  unfolding inference_sound_def
proof (intro allI impI)
  fix a Hs
  assume rule: "finite_inference_rules (development_answered_rules D answered |\<union>| L) a Hs"
    and supported: "rel_ran Hs\<subseteq>{b. development_problem_stated names C' b}"
  from rule obtain G where member: "(a,G) |\<in>| development_answered_rules D answered |\<union>| L"
    and Hs: "Hs=fset G"
    unfolding finite_inference_rules_def by blast
  show "development_problem_stated names C' a"
  proof (cases "(a,G) |\<in>| L")
    case True
    then obtain C I where application: "development_decomposition_application C a I G"
      using library unfolding development_decomposition_library_def by blast
    show ?thesis
    proof (rule development_decomposition_stated[OF application])
      fix s q assume "(s,q) |\<in>| G"
      then show "development_problem_stated names C' q" using supported Hs by (auto simp: rel_ran_def)
    qed
  next
    case False
    then have "(a,G) |\<in>| development_answered_rules D answered" using member by simp
    then have "a |\<in>| answered" unfolding development_answered_rules_def by auto
    then show ?thesis by (rule answered)
  qed
qed

text \<open>
  The reduction of one application and the soundness of the library are one fact: an application is
  the library holding it alone, and \<open>inference_supplies_reduction\<close> reads the reduction off
  its soundness. Nesting needs no law of its own: \<open>obligation_reduction_compose\<close> composes
  reductions with every socket kept, and \<open>obligation_reduction_residual\<close> discharges the
  answered children.
\<close>

theorem development_decomposition_reduction:
  assumes application: "development_decomposition_application C p I H"
  shows "obligation_reduction {p} (development_problem_stated names C') (development_problem_stated names C')
    (\<lambda>_. fset H)"
proof -
  have library: "development_decomposition_library {|(p,H)|}"
    unfolding development_decomposition_library_def
  proof (intro allI impI)
    fix p' H' assume "(p',H') |\<in>| {|(p,H)|}"
    then have "p'=p" "H'=H" by simp_all
    then show "\<exists>C I. development_decomposition_application C p' I H'" using application by blast
  qed
  have empty: "development_answered_rules {||} {||}={||}"
    unfolding development_answered_rules_def by (rule fset_eqI) simp
  have sound: "inference_sound (development_problem_stated names C') (finite_inference_rules {|(p,H)|})"
    using development_decomposition_sound[OF library, of "{||}" names C' "{||}"] empty by simp
  have closure: "p\<in>inference_closure (finite_inference_rules {|(p,H)|}) (rel_ran (fset H))"
  proof (rule inference_closure_step)
    show "finite (fset H)" by simp
    show "single_valued (fset H)" by (rule development_decomposition_application_functional[OF application])
    show "finite_inference_rules {|(p,H)|} p (fset H)" unfolding finite_inference_rules_def by blast
    show "rel_ran (fset H)\<subseteq>inference_closure (finite_inference_rules {|(p,H)|}) (rel_ran (fset H))"
      by (rule inference_closure_seed)
  qed
  show ?thesis by (rule inference_supplies_reduction[OF sound]) (use closure in simp)
qed

corollary development_composed_settled_stated:
  assumes library: "development_decomposition_library L"
    and answered: "\<And>p. p |\<in>| answered \<Longrightarrow> development_problem_stated names C' p"
    and settled: "q\<in>development_composed_settled D L answered"
  shows "development_problem_stated names C' q"
  using inference_closure_sound[OF development_decomposition_sound[OF library answered, where D=D], where K="{}"] settled
  unfolding development_composed_settled_exact by blast

section \<open>Instance B: one constant, one intermediate splitting its support\<close>

text \<open>
  The material of a split is a computed observation of the state: the part of the support each
  intermediate's definitions mention. A split names one intermediate outside the support whose
  definitions take a nonempty part of it; no threshold on the size of the support is asserted.
\<close>

definition development_statement_constants ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_context \<Rightarrow> nat \<Rightarrow> nat fset" where
  "development_statement_constants reading C c=
    fset_of_list (concat (map isabelle_term_constants (development_statements reading C c)))"

definition development_support_partition :: "isabelle_context \<Rightarrow> nat fset \<Rightarrow> nat list \<Rightarrow> (nat\<times>nat fset) list" where
  "development_support_partition C S I=
    map (\<lambda>h. (h,S |\<inter>| development_statement_constants isabelle_definition_proposition C h)) I"

definition development_split_application ::
    "isabelle_context \<Rightarrow> nat fset \<Rightarrow> development_problem \<Rightarrow> nat \<Rightarrow> (nat\<times>development_problem) fset \<Rightarrow> bool" where
  "development_split_application C S p h H \<longleftrightarrow> (\<exists>c. problem_subject p={|c|}) \<and> h |\<notin>| S \<and>
    snd (hd (development_support_partition C S [h]))\<noteq>{||} \<and> development_decomposition_application C p [h] H"

lemma development_split_application_general:
  "development_split_application C S p h H \<Longrightarrow> development_decomposition_application C p [h] H"
  unfolding development_split_application_def by blast

corollary development_split_reduction:
  assumes "development_split_application C S p h H"
  shows "obligation_reduction {p} (development_problem_stated names C') (development_problem_stated names C')
    (\<lambda>_. fset H)"
  by (rule development_decomposition_reduction[OF development_split_application_general[OF assms]])

section \<open>Instance C: the repair of a refused answer\<close>

text \<open>
  The repair names its intermediates from the refusal: the constants the answer introduces, placed in
  the table of the extended state. An application at the extended state over those intermediates has
  exactly the repair's definition problems as its definition children; the repair's output is
  therefore a row of the library, and it inherits the soundness of the schema.
\<close>

definition development_repair_intermediates ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> nat list" where
  "development_repair_intermediates S r S' I=map (isabelle_state_embedding (fst (snd S'))
     (fst (snd (development_repair_state S r S' I)))) I"

definition development_repair_application ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow>
      (nat\<times>development_problem) fset \<Rightarrow> bool" where
  "development_repair_application S r S' I H \<longleftrightarrow> development_decomposition_application
     (snd (development_repair_state S r S' I)) (fst r) (development_repair_intermediates S r S' I) H"

lemma development_repair_definition_problems:
  "fst (snd (development_refinement_repair S r S' I))=development_definition_problems
     (development_repair_state S r S' I) (development_repair_intermediates S r S' I)"
  by (simp add: development_refinement_repair_def development_repair_state_def
      development_repair_intermediates_def Let_def)

theorem development_repair_application_children:
  assumes application: "development_repair_application S r S' I H"
  shows "set (fst (snd (development_refinement_repair S r S' I)))\<subseteq>snd ` fset H"
proof -
  obtain ds rs where defs: "list_all2 (\<lambda>h q. development_intermediate_problem
      (snd (development_repair_state S r S' I)) h=Some q) (development_repair_intermediates S r S' I) ds"
    and family: "H=fset_of_list (zip [0..<length (ds@rs)] (ds@rs))"
    using application unfolding development_repair_application_def development_decomposition_application_def
    by blast
  have "fst (snd (development_refinement_repair S r S' I))=ds"
    unfolding development_repair_definition_problems development_definition_problems_def
      development_constant_problems_def
    using list_all2_some_map_filter[OF defs[unfolded development_intermediate_problem_def]] .
  then show ?thesis using family zip_indices_values[of "ds@rs"] by (auto simp: fset_of_list.rep_eq)
qed

corollary development_repair_reduction:
  assumes "development_repair_application S r S' I H"
  shows "obligation_reduction {fst r} (development_problem_stated names C') (development_problem_stated names C')
    (\<lambda>_. fset H)"
  using assms unfolding development_repair_application_def by (rule development_decomposition_reduction)

end
