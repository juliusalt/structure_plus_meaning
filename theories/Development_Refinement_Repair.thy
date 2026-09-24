theory Development_Refinement_Repair
  imports Development_Refinement_Verification Isabelle_Local_Names
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

lemma isabelle_state_embedding_prefix:
  assumes distinct: "distinct names" and bound: "i<length names"
  shows "isabelle_state_embedding names (names@extra) i=i"
proof -
  have "isabelle_name_position (names@extra) (names!i)=Some i"
    by (simp add: isabelle_name_position_append isabelle_name_position_at[OF distinct bound])
  then show ?thesis using bound by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
qed

subsection \<open>A state read into a table extended by the names it lacks\<close>

text \<open>
  A state is read into a table by appending the names the state's own table lacks
  (\<open>isabelle_appended_names\<close>) and moving each position of the state to the position of its name
  there. Every position of the table is kept, and the reading is a correspondence of the state's table
  with the appended one, so a decision with a renaming contract decides on the read state as on the
  state itself. Where a position of the state names a name the table holds, the embedding of the table
  into the state's table and the reading lead back to each other. The extension of a request and the
  successor of the development read their answer state so: the reading is stated once, here.
\<close>

abbreviation isabelle_appended_embedding :: "String.literal list \<Rightarrow> String.literal list \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_appended_embedding names ns\<equiv>isabelle_state_embedding ns (isabelle_appended_names names ns)"

definition isabelle_rooted_read :: "String.literal list \<Rightarrow> isabelle_rooted_context \<Rightarrow> isabelle_rooted_context" where
  "isabelle_rooted_read names S=isabelle_rooted_rename (isabelle_appended_embedding names (fst (snd S)))
    (isabelle_appended_names names (fst (snd S))) S"

lemma isabelle_rooted_read_fields:
  "fst (isabelle_rooted_read names S)=map (isabelle_term_rename (isabelle_appended_embedding names (fst (snd S)))) (fst S)"
  "snd (isabelle_rooted_read names S)=(isabelle_appended_names names (fst (snd S)),
    map (isabelle_entity_rename (isabelle_appended_embedding names (fst (snd S)))) (snd (snd S)))"
  by (simp_all add: isabelle_rooted_read_def isabelle_rooted_rename_def isabelle_context_rename_def)

lemma isabelle_appended_names_distinct:
  "distinct names \<Longrightarrow> distinct ns \<Longrightarrow> distinct (isabelle_appended_names names ns)"
  by (auto simp: isabelle_appended_names_def)

lemma isabelle_appended_embedding_correspondence:
  assumes distinct: "distinct ns"
  shows "isabelle_table_correspondence (isabelle_appended_embedding names ns) ns (isabelle_appended_names names ns)"
  by (rule isabelle_state_embedding_correspondence[OF distinct]) (auto simp: isabelle_appended_names_def)

lemma isabelle_state_embedding_inside_shared:
  assumes bound: "i<length names" and inside: "isabelle_state_embedding names ns i<length ns"
  shows "names!i\<in>set ns"
proof (rule ccontr)
  assume outside: "names!i\<notin>set ns"
  have "isabelle_state_embedding names ns i=length ns+i"
    by (rule isabelle_state_embedding_unshared) (use bound outside in \<open>auto simp: isabelle_name_at_def\<close>)
  then show False using inside by simp
qed

lemma isabelle_appended_embedding_back:
  assumes distinct: "distinct names" and bound: "i<length names" and shared: "names!i\<in>set ns"
  shows "isabelle_appended_embedding names ns (isabelle_state_embedding names ns i)=i"
proof -
  let ?j="isabelle_state_embedding names ns i"
  have named: "isabelle_name_at ns ?j=Some (names!i)"
    by (rule isabelle_state_embedding_shared) (use bound shared in \<open>simp_all add: isabelle_name_at_def\<close>)
  have home: "isabelle_name_position names (names!i)=Some i" by (rule isabelle_name_position_at[OF distinct bound])
  have "isabelle_appended_embedding names ns ?j=isabelle_state_embedding ns names ?j"
    unfolding isabelle_state_embedding_def[of ns]
    by (simp add: named home isabelle_appended_names_def isabelle_name_position_append)
  then show ?thesis by (simp only: isabelle_state_embedding_back[OF distinct bound shared])
qed

lemma isabelle_appended_embedding_forth:
  assumes distinct: "distinct ns" and bound: "j<length ns"
    and kept: "isabelle_appended_embedding names ns j<length names"
  shows "isabelle_state_embedding names ns (isabelle_appended_embedding names ns j)=j"
proof -
  define k where "k=isabelle_appended_embedding names ns j"
  have corr: "isabelle_table_correspondence (isabelle_appended_embedding names ns) ns (isabelle_appended_names names ns)"
    by (rule isabelle_appended_embedding_correspondence[OF distinct])
  have moved: "isabelle_name_at (isabelle_appended_names names ns) k=isabelle_name_at ns j"
    unfolding k_def by (rule isabelle_table_correspondence_name[OF corr])
  have prefix: "isabelle_name_at (isabelle_appended_names names ns) k=isabelle_name_at names k"
    unfolding k_def by (rule isabelle_appended_names_prefix[OF kept])
  have "isabelle_name_at names k=isabelle_name_at ns j" using moved prefix by simp
  then have named: "isabelle_name_at names k=Some (ns!j)" using bound by (simp add: isabelle_name_at_def)
  have "isabelle_state_embedding names ns k=j"
    by (simp add: isabelle_state_embedding_def named isabelle_name_position_at[OF distinct bound])
  then show ?thesis by (simp only: k_def)
qed

lemma isabelle_appended_embedding_meets:
  assumes distinct: "distinct names" "distinct ns" and bound: "i<length names" and inside: "j<length ns"
  shows "isabelle_appended_embedding names ns j=i \<longleftrightarrow> isabelle_state_embedding names ns i=j"
proof
  assume "isabelle_appended_embedding names ns j=i"
  then show "isabelle_state_embedding names ns i=j"
    using isabelle_appended_embedding_forth[OF distinct(2) inside] bound by auto
next
  assume moved: "isabelle_state_embedding names ns i=j"
  have "names!i\<in>set ns" by (rule isabelle_state_embedding_inside_shared[OF bound]) (simp add: moved inside)
  then show "isabelle_appended_embedding names ns j=i"
    unfolding moved[symmetric] by (rule isabelle_appended_embedding_back[OF distinct(1) bound])
qed

lemma isabelle_appended_embedding_image:
  assumes distinct: "distinct names" "distinct ns" and positions: "fset Q\<subseteq>{..<length names}"
    and inside: "j<length ns"
  shows "isabelle_appended_embedding names ns j |\<in>| Q \<longleftrightarrow> j |\<in>| fimage (isabelle_state_embedding names ns) Q"
proof
  assume member: "isabelle_appended_embedding names ns j |\<in>| Q"
  have "isabelle_state_embedding names ns (isabelle_appended_embedding names ns j)=j"
    using isabelle_appended_embedding_meets[OF distinct _ inside] member positions by auto
  then show "j |\<in>| fimage (isabelle_state_embedding names ns) Q" using member by (force simp: fimage_iff)
next
  assume "j |\<in>| fimage (isabelle_state_embedding names ns) Q"
  then obtain q where member: "q |\<in>| Q" and image: "j=isabelle_state_embedding names ns q" by (auto simp: fimage_iff)
  have "isabelle_appended_embedding names ns j=q"
    using isabelle_appended_embedding_meets[OF distinct _ inside] member positions image by auto
  then show "isabelle_appended_embedding names ns j |\<in>| Q" using member by simp
qed

text \<open>
  The appended embedding and the state's embedding fix every position of the two tables that the
  other keeps; a renaming through both is the identity on a value whose positions are all such.
\<close>

lemma isabelle_appended_embedding_fixes:
  "\<lbrakk>distinct names; i<length names; isabelle_state_embedding names ns i<length ns\<rbrakk> \<Longrightarrow>
    (isabelle_appended_embedding names ns \<circ> isabelle_state_embedding names ns) i=id i"
  "\<lbrakk>distinct ns; j<length ns; isabelle_appended_embedding names ns j<length names\<rbrakk> \<Longrightarrow>
    (isabelle_state_embedding names ns \<circ> isabelle_appended_embedding names ns) j=id j"
  using isabelle_appended_embedding_back[of names i ns] isabelle_state_embedding_inside_shared[of i names ns]
    isabelle_appended_embedding_forth[of ns j names] by simp_all

lemma isabelle_appended_term_back:
  assumes distinct: "distinct names"
    and inside: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> i<length names"
    and shared: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> isabelle_state_embedding names ns i<length ns"
  shows "isabelle_term_rename (isabelle_appended_embedding names ns) (isabelle_term_rename (isabelle_state_embedding names ns) t)=t"
proof -
  have "isabelle_term_rename (isabelle_appended_embedding names ns \<circ> isabelle_state_embedding names ns) t=
      isabelle_term_rename id t"
    by (rule isabelle_term_rename_cong) (rule isabelle_appended_embedding_fixes(1)[OF distinct inside shared])
  then show ?thesis by (simp only: isabelle_term_rename_compose isabelle_term_rename_id)
qed

lemma isabelle_appended_entity_back:
  assumes distinct: "distinct names"
    and inside: "\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> i<length names"
    and shared: "\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> isabelle_state_embedding names ns i<length ns"
  shows "isabelle_entity_rename (isabelle_appended_embedding names ns) (isabelle_entity_rename (isabelle_state_embedding names ns) e)=e"
proof -
  have "isabelle_entity_rename (isabelle_appended_embedding names ns \<circ> isabelle_state_embedding names ns) e=
      isabelle_entity_rename id e"
    by (rule isabelle_entity_rename_cong) (rule isabelle_appended_embedding_fixes(1)[OF distinct inside shared])
  then show ?thesis by (simp only: isabelle_entity_rename_compose isabelle_entity_rename_id)
qed

lemma isabelle_appended_term_forth:
  assumes distinct: "distinct ns"
    and inside: "\<And>j. j\<in>set (isabelle_term_positions t) \<Longrightarrow> j<length ns"
    and kept: "\<And>j. j\<in>set (isabelle_term_positions t) \<Longrightarrow> isabelle_appended_embedding names ns j<length names"
  shows "isabelle_term_rename (isabelle_state_embedding names ns) (isabelle_term_rename (isabelle_appended_embedding names ns) t)=t"
proof -
  have "isabelle_term_rename (isabelle_state_embedding names ns \<circ> isabelle_appended_embedding names ns) t=
      isabelle_term_rename id t"
    by (rule isabelle_term_rename_cong) (rule isabelle_appended_embedding_fixes(2)[OF distinct inside kept])
  then show ?thesis by (simp only: isabelle_term_rename_compose isabelle_term_rename_id)
qed

lemma isabelle_appended_entity_forth:
  assumes distinct: "distinct ns"
    and inside: "\<And>j. j\<in>set (isabelle_entity_positions e) \<Longrightarrow> j<length ns"
    and kept: "\<And>j. j\<in>set (isabelle_entity_positions e) \<Longrightarrow> isabelle_appended_embedding names ns j<length names"
  shows "isabelle_entity_rename (isabelle_state_embedding names ns) (isabelle_entity_rename (isabelle_appended_embedding names ns) e)=e"
proof -
  have "isabelle_entity_rename (isabelle_state_embedding names ns \<circ> isabelle_appended_embedding names ns) e=
      isabelle_entity_rename id e"
    by (rule isabelle_entity_rename_cong) (rule isabelle_appended_embedding_fixes(2)[OF distinct inside kept])
  then show ?thesis by (simp only: isabelle_entity_rename_compose isabelle_entity_rename_id)
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

definition development_request_extension ::
    "isabelle_rooted_context \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> isabelle_rooted_context" where
  "development_request_extension S S' X I=(let names=isabelle_appended_names (fst (snd S)) (fst (snd S'));
     g=isabelle_appended_embedding (fst (snd S)) (fst (snd S'));
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
  An introduced constant becomes the problem of that constant under the definition reading:
  its subject is the constant, its contract the constant as the extended state declares it,
  marked as a definition, and its incumbent the kernel definitions the extended state states for
  it, which are the answer's own. It is the same notion as a refinement problem with the other
  reading, so a definition problem keeps its identity when a later answer replaces the
  definition, and an introduced constant the extension defines other than by a kernel definition
  yields no problem.
\<close>

definition development_extended_request ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> nat list \<Rightarrow> development_request" where
  "development_extended_request S r X=(case r of (p,s,support,E) \<Rightarrow>
    (p,s,support |\<union>| fset_of_list X,E |\<union>| fset_of_list (filter (\<lambda>e. case isabelle_declared_constant e of
       Some d \<Rightarrow> d\<in>set X | None \<Rightarrow> False) (snd (snd S)))))"

definition development_definition_problems :: "isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> development_problem list" where
  "development_definition_problems S I=development_constant_problems isabelle_definition_proposition
     Development_Definition (snd S) Development_Demand Development_Generated I"

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
  "development_extension_verdict\<times>development_problem list\<times>development_request\<times>development_constant_verdict\<times>bool"

definition development_refinement_repair ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow>
      development_refinement_repair" where
  "development_refinement_repair S r S' I=(let v=development_refinement_verdict S r S';
     X=development_verdict_excess v; E=development_request_extension S S' X I;
     g=isabelle_state_embedding (fst (snd S')) (fst (snd E)); X'=map g X; I'=map g I;
     r'=development_extended_request E r X'; v'=development_refinement_verdict E r' S' in
     (development_extension_verdict (snd S) (snd E) I',development_definition_problems E I',r',v',
      development_verdict_accepted v'))"

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
     (development_verdict_excess (development_refinement_verdict S r S')) I"

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
        (finite_pair_presentation development_verdict_data finite_boolean_data)))"

lemma development_refinement_repair_data_injective [intro]: "inj development_refinement_repair_data"
  unfolding development_refinement_repair_data_def
  by (intro finite_pair_presentation_injective development_extension_verdict_data_injective
    development_problems_data_injective development_request_data_injective
    development_verdict_data_injective finite_boolean_data_injective)

end
