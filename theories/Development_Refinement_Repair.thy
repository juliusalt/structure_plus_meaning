theory Development_Refinement_Repair
  imports Development_Refinement_Verification
begin

section \<open>A refused answer derives the extension of its request\<close>

text \<open>
  An answer whose equation needs constants outside the issued support is refused, and the
  refusal is the start of a derived problem rather than an end. The verdict names the excess
  constants; the checked context of the answer names the constants the answer itself
  introduced. From these the request state is extended by exactly the material the answer
  state holds about them: the declarations of every excess or introduced constant and, for an
  introduced constant, its definitions, code equations and any specification. The new names are
  appended to the table, so every position of the request state keeps its meaning. The request
  is issued again against the extended state with the excess added to its support, every
  introduced constant becomes a definition problem, and the extension itself is judged: it may
  remove nothing, may state no axiom, and may define only constants the request state did not
  know. Nothing here admits the extension; it computes what must be admitted.
\<close>

subsection \<open>Renamings that fix every used position leave an entity unchanged\<close>

lemma isabelle_type_rename_id: "isabelle_type_rename id T=T"
  by (induction T) (simp_all add: map_idI)

lemma isabelle_term_rename_id: "isabelle_term_rename id t=t"
  by (induction t) (simp_all add: isabelle_type_rename_id[unfolded id_def])

lemma isabelle_entity_rename_id: "isabelle_entity_rename id e=e"
  by (cases e) (simp_all add: isabelle_term_rename_id)

lemma isabelle_name_position_append:
  "isabelle_name_position (xs@ys) n=(case isabelle_name_position xs n of Some j \<Rightarrow> Some j
    | None \<Rightarrow> map_option ((+) (length xs)) (isabelle_name_position ys n))"
  by (induction xs) (cases "isabelle_name_position ys n"; auto split: option.splits)+

lemma isabelle_state_embedding_prefix:
  assumes distinct: "distinct names" and bound: "i<length names"
  shows "isabelle_state_embedding names (names@extra) i=i"
proof -
  have "isabelle_name_position (names@extra) (names!i)=Some i"
    by (simp add: isabelle_name_position_append isabelle_name_position_at[OF distinct bound])
  then show ?thesis using bound by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
qed

subsection \<open>The material an answer state holds about given constants\<close>

definition development_introduced_material :: "isabelle_context \<Rightarrow> nat list \<Rightarrow> isabelle_entity list" where
  "development_introduced_material C I=filter (\<lambda>e. isabelle_declared_constant e=None \<and>
    list_ex (\<lambda>d. d\<in>set I) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)) (snd C)"

definition development_answer_material :: "isabelle_context \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> isabelle_entity list" where
  "development_answer_material C X I=(let introduced=development_introduced_material C I;
     mentioned=concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) introduced) in
     filter (\<lambda>e. case isabelle_declared_constant e of
       Some d \<Rightarrow> d\<in>set X \<or> d\<in>set I \<or> d\<in>set mentioned
     | None \<Rightarrow> e\<in>set introduced) (snd C))"

theorem development_answer_material_exact:
  "e\<in>set (development_answer_material C X I) \<longleftrightarrow> e\<in>set (snd C) \<and>
    (case isabelle_declared_constant e of
       Some d \<Rightarrow> d\<in>set X \<or> d\<in>set I \<or> (\<exists>f\<in>set (development_introduced_material C I).
         \<exists>q. isabelle_specified_proposition f=Some q \<and> d\<in>set (isabelle_term_constants q))
     | None \<Rightarrow> e\<in>set (development_introduced_material C I))"
proof -
  have mentioned: "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)) \<longleftrightarrow>
      (\<exists>f\<in>set L. \<exists>q. isabelle_specified_proposition f=Some q \<and> d\<in>set (isabelle_term_constants q))" for d L
  proof
    assume "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L))"
    then obtain l where listed: "l\<in>set (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)"
      and inside: "d\<in>set l" by auto
    obtain f where member: "f\<in>set L" and read: "(map_option isabelle_term_constants \<circ> isabelle_specified_proposition) f=Some l"
      using listed by (simp only: map_filter_member) blast
    obtain q where statement: "isabelle_specified_proposition f=Some q" and constants: "l=isabelle_term_constants q"
      using read by (auto simp: map_option_eq_Some)
    show "\<exists>f\<in>set L. \<exists>q. isabelle_specified_proposition f=Some q \<and> d\<in>set (isabelle_term_constants q)"
      using member statement inside constants by blast
  next
    assume "\<exists>f\<in>set L. \<exists>q. isabelle_specified_proposition f=Some q \<and> d\<in>set (isabelle_term_constants q)"
    then obtain f q where member: "f\<in>set L" and statement: "isabelle_specified_proposition f=Some q"
      and inside: "d\<in>set (isabelle_term_constants q)" by blast
    have "(map_option isabelle_term_constants \<circ> isabelle_specified_proposition) f=Some (isabelle_term_constants q)"
      by (simp add: statement)
    then have "isabelle_term_constants q\<in>set (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L)"
      using member by (simp only: map_filter_member) blast
    then show "d\<in>set (concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) L))"
      using inside by auto
  qed
  show ?thesis
    by (simp only: development_answer_material_def Let_def set_filter mem_Collect_eq mentioned split: option.split)
qed

text \<open>
  The material closes under what the introduced constants' specifications mention: a helper
  defined through a constant the request state never read brings that constant's declaration
  with it, so the extension is closed exactly as far as the answer reaches.
\<close>

definition isabelle_appended_names :: "String.literal list \<Rightarrow> String.literal list \<Rightarrow> String.literal list" where
  "isabelle_appended_names names names'=names@filter (\<lambda>n. n\<notin>set names) names'"

definition development_request_extension ::
    "isabelle_rooted_context \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> isabelle_rooted_context" where
  "development_request_extension S S' X I=(let names=isabelle_appended_names (fst (snd S)) (fst (snd S'));
     g=isabelle_state_embedding (fst (snd S')) names;
     added=filter (\<lambda>e. e\<notin>set (snd (snd S))) (map (isabelle_entity_rename g) (development_answer_material (snd S') X I)) in
     (fst S,(names,snd (snd S)@added)))"

text \<open>
  The extension keeps the request state as it is: its roots, its entities and the position of
  every name it uses. Its difference from the request state is therefore only what it adds.
\<close>

theorem development_request_extension_persists:
  assumes distinct: "distinct (fst (snd S))" and known: "isabelle_unknown_positions (snd S)=[]"
  shows "isabelle_state_removed (snd S) (snd (development_request_extension S S' X I))=[]"
    "fst (development_request_extension S S' X I)=fst S"
proof -
  let ?E="development_request_extension S S' X I"
  obtain extra where names: "fst (snd ?E)=fst (snd S)@extra"
    by (simp add: development_request_extension_def Let_def isabelle_appended_names_def)
  have kept: "set (snd (snd S))\<subseteq>set (snd (snd ?E))"
    by (auto simp: development_request_extension_def Let_def)
  have same: "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd ?E))) e=e"
    if member: "e\<in>set (snd (snd S))" for e
  proof -
    have "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd ?E))) e=isabelle_entity_rename id e"
    proof (rule isabelle_entity_rename_cong)
      fix i assume used: "i\<in>set (isabelle_entity_positions e)"
      have bound: "i<length (fst (snd S))"
        using known member used isabelle_unknown_positions_exact[of i "snd S"] by auto
      show "isabelle_state_embedding (fst (snd S)) (fst (snd ?E)) i=id i"
        by (simp only: names isabelle_state_embedding_prefix[OF distinct bound] id_apply)
    qed
    then show ?thesis by (simp only: isabelle_entity_rename_id)
  qed
  show "isabelle_state_removed (snd S) (snd ?E)=[]"
    using kept by (auto simp: isabelle_state_removed_def Let_def same filter_empty_conv)
  show "fst ?E=fst S" by (simp add: development_request_extension_def Let_def)
qed

subsection \<open>The request issued again, the definition problems and the judgment of the extension\<close>

text \<open>
  A definition problem demands the kernel definition of its subject. That reading of the entity
  language is separate from the code-equation reading: a definition and a code equation of one
  constant share their subjects, and only the entity kind tells the two demands apart.
\<close>

fun isabelle_definition_proposition :: "isabelle_entity \<Rightarrow> isabelle_term option" where
  "isabelle_definition_proposition (Isabelle_Definition p)=Some p"
| "isabelle_definition_proposition _=None"

lemma isabelle_definition_proposition_exact:
  "isabelle_definition_proposition e=Some p \<longleftrightarrow> e=Isabelle_Definition p"
  by (cases e) simp_all

definition development_extended_request ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> nat list \<Rightarrow> development_request" where
  "development_extended_request S r X=(case r of (p,s,support,E) \<Rightarrow>
    (p,s,support |\<union>| fset_of_list X,E |\<union>| fset_of_list (filter (\<lambda>e. case isabelle_declared_constant e of
       Some d \<Rightarrow> d\<in>set X | None \<Rightarrow> False) (snd (snd S)))))"

definition development_definition_problems :: "isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> development_problem list" where
  "development_definition_problems S I=List.map_filter (\<lambda>i. map_option (\<lambda>q.
     Development_Problem {|i|} (Development_Definition q) Development_Demand Development_Generated)
     (list_singleton_option (List.map_filter isabelle_definition_proposition (development_refinement_scope (snd S) i)))) I"

definition development_extension_permitted :: "isabelle_context \<Rightarrow> nat list \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "development_extension_permitted C I e \<longleftrightarrow> isabelle_declared_constant e\<noteq>None \<or>
    ((isabelle_definition_proposition e\<noteq>None \<or> isabelle_code_equation_proposition e\<noteq>None) \<and>
     list_all (\<lambda>d. d\<in>set I) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))"

type_synonym development_extension_verdict = "isabelle_entity list\<times>isabelle_entity list\<times>nat list\<times>bool"

definition development_extension_verdict ::
    "isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> nat list \<Rightarrow> development_extension_verdict" where
  "development_extension_verdict C C' I=(let added=isabelle_state_added C C' in
    (isabelle_state_removed C C',filter (\<lambda>e. \<not>development_extension_permitted C' I e) added,
     filter (\<lambda>i. case isabelle_name_at (fst C') i of Some n \<Rightarrow> n\<in>set (fst C) | None \<Rightarrow> True) I,
     distinct (fst C')))"

definition development_extension_accepted :: "development_extension_verdict \<Rightarrow> bool" where
  "development_extension_accepted v \<longleftrightarrow> (case v of (removed,unpermitted,known,tables) \<Rightarrow>
    removed=[] \<and> unpermitted=[] \<and> known=[] \<and> tables)"

text \<open>
  An accepted extension removes nothing, adds only declarations and the definitions and code
  equations of introduced constants, and introduces only names the request state did not hold:
  it states no axiom and redefines nothing.
\<close>

theorem development_extension_contract:
  assumes accepted: "development_extension_accepted (development_extension_verdict C C' I)"
  shows "isabelle_state_removed C C'=[]"
    and "\<And>e. e\<in>set (isabelle_state_added C C') \<Longrightarrow> development_extension_permitted C' I e"
    and "\<And>i n. i\<in>set I \<Longrightarrow> isabelle_name_at (fst C') i=Some n \<Longrightarrow> n\<notin>set (fst C)"
  using accepted by (auto simp: development_extension_accepted_def development_extension_verdict_def Let_def
    filter_empty_conv split: option.splits)

type_synonym development_refinement_repair =
  "development_extension_verdict\<times>development_problem list\<times>development_request\<times>development_refinement_verdict\<times>bool"

definition development_refinement_repair ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow>
      development_refinement_repair" where
  "development_refinement_repair S r S' I=(let v=development_refinement_verdict S r S';
     X=development_refinement_verdict_excess v; E=development_request_extension S S' X I;
     g=isabelle_state_embedding (fst (snd S')) (fst (snd E)); X'=map g X; I'=map g I;
     r'=development_extended_request E r X'; v'=development_refinement_verdict E r' S' in
     (development_extension_verdict (snd S) (snd E) I',development_definition_problems E I',r',v',
      development_refinement_accepted v'))"

text \<open>
  The repair composes two judgments: the extension, admitted as its own problems, and the same
  answer judged against the request issued again. When both accept, the answer refines its
  subject within the extended support, and the extension is exactly what it had to add. Neither
  judgment is repeated for a use; admitting the definition problems and the extension is the
  process's decision, not this computation's.
\<close>

text \<open>
  The state a repaired answer is judged against again is the request state extended by exactly the
  material of the constants the verdict found outside the support and of the constants the answer
  introduces. The repaired successor moves the development to it, and an admitted answer's route
  reads it; both take it from here.
\<close>

definition development_repair_state ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> isabelle_rooted_context" where
  "development_repair_state S r S' I=development_request_extension S S'
     (development_refinement_verdict_excess (development_refinement_verdict S r S')) I"

definition development_extension_verdict_data :: "development_extension_verdict \<Rightarrow> finite_factor_term" where
  "development_extension_verdict_data=finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
      (finite_pair_presentation (finite_sequence_presentation isabelle_position_data) finite_boolean_data))"

lemma development_extension_verdict_data_injective [intro]: "inj development_extension_verdict_data"
  unfolding development_extension_verdict_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    isabelle_entity_data_injective isabelle_position_data_injective finite_boolean_data_injective)

definition development_refinement_repair_data :: "development_refinement_repair \<Rightarrow> finite_factor_term" where
  "development_refinement_repair_data=finite_pair_presentation development_extension_verdict_data
    (finite_pair_presentation development_problems_data
      (finite_pair_presentation development_request_data
        (finite_pair_presentation development_refinement_verdict_data finite_boolean_data)))"

lemma development_refinement_repair_data_injective [intro]: "inj development_refinement_repair_data"
  unfolding development_refinement_repair_data_def
  by (intro finite_pair_presentation_injective development_extension_verdict_data_injective
    development_problems_data_injective development_request_data_injective
    development_refinement_verdict_data_injective finite_boolean_data_injective)

end
