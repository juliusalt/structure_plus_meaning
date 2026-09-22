theory Development_Native_Answers
  imports Development_Definition_Verification Isabelle_Local_Names Isabelle_Readers Finite_Term_Word_Readers
    Development_State_Rows
    "HOL-Library.Parallel"
begin

section \<open>An answer is a native value presented with the names it uses\<close>

text \<open>
  An answer to a problem of a constant is the change it makes to the state the request was made
  against: the entities it removes and the entities it adds, presented with the names they use,
  as a published payload carries its names, so an answer reads the same beside every table holding
  those names. An answer is therefore native content, and it is judged natively: the answer state is
  the request state with the answer applied, and the verdict of the problem's kind reads the two
  states. What that judgment establishes is that the answer is admissible for installation. Whether
  what it states holds is Isabelle's acceptance when it is installed, a request of its own.
\<close>

type_synonym development_native_answer = "String.literal list\<times>isabelle_entity list\<times>isabelle_entity list"

definition development_native_answer_data :: "development_native_answer \<Rightarrow> finite_factor_term" where
  "development_native_answer_data=finite_pair_presentation isabelle_names_data
    (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
      (finite_sequence_presentation isabelle_entity_data))"

definition development_native_answer_presented_read :: "finite_factor_term \<Rightarrow> development_native_answer option" where
  "development_native_answer_presented_read=finite_pair_read isabelle_names_read
    (finite_pair_read (finite_sequence_read isabelle_entity_read) (finite_sequence_read isabelle_entity_read))"

lemma development_native_answer_presented_reads:
  "finite_reads development_native_answer_presented_read development_native_answer_data"
  unfolding development_native_answer_presented_read_def development_native_answer_data_def
  by (intro finite_pair_reads finite_sequence_reads isabelle_names_reads isabelle_entity_reads)

lemma development_native_answer_data_injective [intro]: "inj development_native_answer_data"
  by (rule finite_reads_injective[OF development_native_answer_presented_reads])

text \<open>
  An answer is formed when its names are distinct and every position its removed and added entities use
  is a position of those names. Only then is the answer state it makes a state whose table is free of
  repeated names and holds every position the state uses (\<open>development_native_answer_state_presentable\<close>),
  which a presented state carries (\<open>state_presents_distinct_names\<close>, \<open>state_presents_unknown_positions\<close>).
  The reader of an answer is the source of an answer state, so it refuses every presented answer that is
  not formed: a refusal is no answer, never an answer repaired, deduplicated or renamed.
\<close>

definition development_native_answer_formed :: "development_native_answer \<Rightarrow> bool" where
  "development_native_answer_formed A \<longleftrightarrow> (case A of (ns,removed,added) \<Rightarrow> distinct ns \<and>
    list_all (\<lambda>e. list_all (\<lambda>i. i<length ns) (isabelle_entity_positions e)) (removed@added))"

lemma development_native_answer_formed_exact:
  "development_native_answer_formed (ns,removed,added) \<longleftrightarrow> distinct ns \<and>
    (\<forall>e\<in>set (removed@added). \<forall>i\<in>set (isabelle_entity_positions e). i<length ns)"
  by (simp add: development_native_answer_formed_def list_all_iff)

definition development_native_answer_read :: "finite_factor_term \<Rightarrow> development_native_answer option" where
  "development_native_answer_read t=Option.bind (development_native_answer_presented_read t)
    (\<lambda>A. if development_native_answer_formed A then Some A else None)"

theorem development_native_answer_reads:
  "development_native_answer_read t=Some A \<longleftrightarrow>
    t=development_native_answer_data A \<and> development_native_answer_formed A"
proof -
  have "development_native_answer_read t=Some A \<longleftrightarrow>
      development_native_answer_presented_read t=Some A \<and> development_native_answer_formed A"
    by (cases "development_native_answer_presented_read t") (auto simp: development_native_answer_read_def)
  then show ?thesis by (simp only: finite_readsD[OF development_native_answer_presented_reads])
qed

section \<open>An answer arrives as the word of its presentation\<close>

text \<open>
  An answer is transported as the padded word of its presentation, as a report is. Its presentation
  holds no target, so the word reader applies, and reading refuses every sequence of bits that is
  not exactly the padded word of an answer.
\<close>

lemma finite_data_list_targets:
  "finite_term_targets (finite_data_list ts)=(\<Union>t\<in>set ts. finite_term_targets t)"
  by (induction ts) auto

lemma isabelle_data_targets [simp]:
  "finite_term_targets (isabelle_position_data n)={}"
  "finite_term_targets (isabelle_name_data s)={}"
  "finite_term_targets (isabelle_sort_data S)={}"
  by (simp_all add: isabelle_position_data_def finite_binary_natural_value_def finite_storage_path_value_def
    isabelle_name_data_def isabelle_sort_data_def finite_sequence_presentation_def finite_data_list_targets)

lemma isabelle_type_data_targets [simp]: "finite_term_targets (isabelle_type_data T)={}"
  by (induction T) (simp_all add: finite_data_list_targets)

lemma isabelle_term_data_targets [simp]: "finite_term_targets (isabelle_term_data t)={}"
  by (induction t) simp_all

lemma isabelle_entity_data_targets [simp]: "finite_term_targets (isabelle_entity_data e)={}"
  by (cases e) simp_all

lemma development_native_answer_data_targets [simp]:
  "finite_term_targets (development_native_answer_data A)={}"
  by (simp add: development_native_answer_data_def finite_pair_presentation_def isabelle_names_data_def
    finite_sequence_presentation_def finite_data_list_targets)

definition development_native_answer_word :: "development_native_answer \<Rightarrow> bool list" where
  "development_native_answer_word A=finite_term_shared_word (development_native_answer_data A)@[True]"

definition development_native_answer_bits_read :: "bool list \<Rightarrow> development_native_answer option" where
  "development_native_answer_bits_read bits=Option.bind (finite_padded_term_read bits) development_native_answer_read"

theorem development_native_answer_bits_read_exact:
  "development_native_answer_bits_read bits=Some A \<longleftrightarrow> development_native_answer_formed A \<and>
    (\<exists>k. bits=finite_term_shared_word (development_native_answer_data A)@True#replicate k False)"
  by (auto simp: development_native_answer_bits_read_def bind_eq_Some_conv finite_padded_term_read_exact
    development_native_answer_reads)

corollary development_native_answer_word_read:
  assumes formed: "development_native_answer_formed A"
  shows "development_native_answer_bits_read (development_native_answer_word A)=Some A"
  using development_native_answer_bits_read_exact[of "development_native_answer_word A" A] formed
  by (auto simp: development_native_answer_word_def intro: exI[of _ 0])

section \<open>The answer state is the request state with the answer applied\<close>

text \<open>
  The names of an answer are appended to the request state's table where it lacks them, and every
  entity of the answer is read through the position of its names there; the removed entities are
  taken out and the added ones put in. The roots and every name position of the request state are
  kept, so the verdict's correspondence between the two tables is the identity on the request
  state's positions.
\<close>

definition development_native_answer_state ::
    "isabelle_rooted_context \<Rightarrow> development_native_answer \<Rightarrow> isabelle_rooted_context" where
  "development_native_answer_state S A=(case A of (ns,removed,added) \<Rightarrow>
    let names=isabelle_appended_names (fst (snd S)) ns; g=isabelle_state_embedding ns names;
      gone=map (isabelle_entity_rename g) removed in
    (fst S,(names,filter (\<lambda>e. e\<notin>set gone) (snd (snd S))@map (isabelle_entity_rename g) added)))"

lemma development_native_answer_state_fields:
  "fst (development_native_answer_state S (ns,removed,added))=fst S"
  "fst (snd (development_native_answer_state S (ns,removed,added)))=isabelle_appended_names (fst (snd S)) ns"
  by (simp_all add: development_native_answer_state_def Let_def)

section \<open>A formed answer keeps a state presentable\<close>

text \<open>
  A presented state carries three conditions: its names are distinct, every position it uses is a
  position of its table, and its roots are distinct as local presentations. The answer state of a formed
  answer keeps all three: the names it appends are distinct and new, every position of an added entity
  is moved to the position of its name in the appended table, and the roots are the request state's,
  whose local presentations the appended table does not change, so their distinctness is preserved,
  not established again.
\<close>

theorem development_native_answer_state_presentable:
  assumes formed: "development_native_answer_formed A"
    and distinct: "distinct (fst (snd S))"
    and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}"
    and roots: "distinct (map (isabelle_local_root (fst (snd S))) (fst S))"
  shows "distinct (fst (snd (development_native_answer_state S A)))"
    and "state_positions (development_native_answer_state S A)\<subseteq>{..<length (fst (snd (development_native_answer_state S A)))}"
    and "distinct (map (isabelle_local_root (fst (snd (development_native_answer_state S A))))
      (fst (development_native_answer_state S A)))"
proof -
  obtain ns removed added where A: "A=(ns,removed,added)" by (cases A) auto
  let ?names="fst (snd S)"
  let ?N="isabelle_appended_names ?names ns"
  let ?g="isabelle_state_embedding ns ?N"
  have ns: "distinct ns" and used: "\<And>e i. e\<in>set (removed@added) \<Longrightarrow> i\<in>set (isabelle_entity_positions e) \<Longrightarrow> i<length ns"
    using formed by (auto simp: A development_native_answer_formed_exact)
  have state: "development_native_answer_state S A=(fst S,(?N,filter (\<lambda>e. e\<notin>set (map (isabelle_entity_rename ?g) removed))
      (snd (snd S))@map (isabelle_entity_rename ?g) added))"
    by (simp add: A development_native_answer_state_def Let_def)
  have longer: "length ?names\<le>length ?N" by (simp add: isabelle_appended_names_def)
  have prefix: "isabelle_name_at ?N i=isabelle_name_at ?names i" if bound: "i<length ?names" for i
    using bound by (simp add: isabelle_appended_names_def isabelle_name_at_def nth_append)
  show "distinct (fst (snd (development_native_answer_state S A)))"
    using distinct ns by (auto simp: state isabelle_appended_names_def)
  have moved: "?g i<length ?N" if bound: "i<length ns" for i
  proof -
    have named: "isabelle_name_at ns i=Some (ns!i)" using bound by (simp add: isabelle_name_at_def)
    have shared: "ns!i\<in>set ?N" using nth_mem[OF bound] by (auto simp: isabelle_appended_names_def)
    have "isabelle_name_at ?N (?g i)=Some (ns!i)" by (rule isabelle_state_embedding_shared[OF named shared])
    then show ?thesis by (simp add: isabelle_name_at_def split: if_splits)
  qed
  have old: "i<length ?N" if member: "e\<in>set (snd (snd S))" and position: "i\<in>set (isabelle_entity_positions e)" for e i
  proof -
    have "i\<in>state_positions S" using member position by (auto simp: state_positions_def)
    then show ?thesis using inside longer by auto
  qed
  have new: "i<length ?N" if member: "a\<in>set added" and position: "i\<in>set (isabelle_entity_positions (isabelle_entity_rename ?g a))" for a i
  proof -
    obtain j where j: "j\<in>set (isabelle_entity_positions a)" "i=?g j"
      using position by (auto simp: isabelle_entity_rename_positions)
    have "j<length ns" by (rule used) (use member j in auto)
    then show ?thesis using moved j by simp
  qed
  have root: "i<length ?N" if member: "t\<in>set (fst S)" and position: "i\<in>set (isabelle_term_positions t)" for t i
  proof -
    have "i\<in>state_positions S" using member position by (auto simp: state_positions_def)
    then show ?thesis using inside longer by auto
  qed
  show "state_positions (development_native_answer_state S A)\<subseteq>{..<length (fst (snd (development_native_answer_state S A)))}"
    unfolding state state_positions_def by (auto intro: old new root)
  have same_roots: "map (isabelle_local_root ?N) (fst S)=map (isabelle_local_root ?names) (fst S)"
  proof (rule map_cong[OF refl])
    fix t assume member: "t\<in>set (fst S)"
    show "isabelle_local_root ?N t=isabelle_local_root ?names t"
    proof (rule isabelle_local_root_agree)
      fix i assume position: "i\<in>set (isabelle_term_positions t)"
      have "i\<in>state_positions S" using member position by (auto simp: state_positions_def)
      then show "isabelle_name_at ?N i=isabelle_name_at ?names i" using inside by (intro prefix) auto
    qed
  qed
  show "distinct (map (isabelle_local_root (fst (snd (development_native_answer_state S A))))
      (fst (development_native_answer_state S A)))"
    using roots by (simp only: state fst_conv snd_conv same_roots)
qed

text \<open>
  An edit of a state whose positions its table holds is presented as an answer with the names it
  uses (\<open>development_native_answer_of\<close>), the local presentation a published payload has, and
  applying that answer performs exactly the edit. An edit whose positions the table holds is presented as
  a formed answer (\<open>development_native_answer_of_formed\<close>), so the reader reads it.
\<close>

definition development_native_answer_of ::
    "String.literal list \<Rightarrow> isabelle_entity list \<Rightarrow> isabelle_entity list \<Rightarrow> development_native_answer" where
  "development_native_answer_of names removed added=(let ps=concat (map isabelle_entity_positions (removed@added));
    g=isabelle_local_embedding names ps in
    (isabelle_local_names names ps,map (isabelle_entity_rename g) removed,map (isabelle_entity_rename g) added))"

theorem development_native_answer_of_formed:
  assumes known: "\<And>e i. e\<in>set (removed@added) \<Longrightarrow> i\<in>set (isabelle_entity_positions e) \<Longrightarrow> i<length names"
  shows "development_native_answer_formed (development_native_answer_of names removed added)"
proof -
  let ?ps="concat (map isabelle_entity_positions (removed@added))"
  let ?L="isabelle_local_names names ?ps"
  let ?h="isabelle_local_embedding names ?ps"
  have moved: "?h i<length ?L" if member: "i\<in>set ?ps" and bound: "i<length names" for i
  proof -
    have named: "isabelle_name_at names i=Some (names!i)" using bound by (simp add: isabelle_name_at_def)
    have shared: "names!i\<in>set ?L"
      using member named by (auto simp: isabelle_local_names_def map_filter_member)
    have "isabelle_name_at ?L (?h i)=Some (names!i)"
      unfolding isabelle_local_embedding_def by (rule isabelle_state_embedding_shared[OF named shared])
    then show ?thesis by (simp add: isabelle_name_at_def split: if_splits)
  qed
  have positions: "j<length ?L" if member: "e\<in>set (removed@added)"
    and position: "j\<in>set (isabelle_entity_positions (isabelle_entity_rename ?h e))" for e j
  proof -
    obtain i where i: "i\<in>set (isabelle_entity_positions e)" "j=?h i"
      using position by (auto simp: isabelle_entity_rename_positions)
    have "i\<in>set ?ps" using member i by auto
    then show ?thesis using moved known[OF member i(1)] i by simp
  qed
  show ?thesis
    unfolding development_native_answer_of_def Let_def development_native_answer_formed_exact
  proof (intro conjI ballI)
    show "distinct ?L" by (simp add: isabelle_local_names_def)
    fix e' j
    assume e': "e'\<in>set (map (isabelle_entity_rename ?h) removed@map (isabelle_entity_rename ?h) added)"
      and j: "j\<in>set (isabelle_entity_positions e')"
    obtain e where e: "e\<in>set (removed@added)" "e'=isabelle_entity_rename ?h e" using e' by auto
    show "j<length ?L" using positions[OF e(1)] j e(2) by simp
  qed
qed

theorem development_native_answer_of_state:
  assumes distinct: "distinct (fst (snd S))"
    and known: "\<And>e i. e\<in>set (removed@added) \<Longrightarrow> i\<in>set (isabelle_entity_positions e) \<Longrightarrow> i<length (fst (snd S))"
  shows "development_native_answer_state S (development_native_answer_of (fst (snd S)) removed added)=
    (fst S,(fst (snd S),filter (\<lambda>e. e\<notin>set removed) (snd (snd S))@added))"
proof -
  let ?names="fst (snd S)"
  let ?ps="concat (map isabelle_entity_positions (removed@added))"
  let ?L="isabelle_local_names ?names ?ps"
  let ?h="isabelle_local_embedding ?names ?ps"
  let ?g="isabelle_state_embedding ?L ?names"
  have local_names: "set ?L\<subseteq>set ?names"
    by (auto simp: isabelle_local_names_def map_filter_member isabelle_name_at_def split: if_splits)
  have appended: "isabelle_appended_names ?names ?L=?names"
    using local_names by (auto simp: isabelle_appended_names_def filter_empty_conv)
  have restored: "isabelle_entity_rename ?g (isabelle_entity_rename ?h e)=e"
    if member: "e\<in>set (removed@added)" for e
  proof -
    have "isabelle_entity_rename ?g (isabelle_entity_rename ?h e)=isabelle_entity_rename (?g \<circ> ?h) e"
      by (rule isabelle_entity_rename_compose)
    also have "\<dots>=isabelle_entity_rename id e"
    proof (rule isabelle_entity_rename_cong)
      fix i assume used: "i\<in>set (isabelle_entity_positions e)"
      have bound: "i<length ?names" by (rule known[OF member used])
      have "i\<in>set ?ps" using member used by auto
      then have "?names!i\<in>set ?L"
        using bound by (auto simp: isabelle_local_names_def map_filter_member isabelle_name_at_def)
      then show "(?g \<circ> ?h) i=id i"
        using isabelle_state_embedding_back[OF distinct bound] by (simp add: isabelle_local_embedding_def)
    qed
    also have "\<dots>=e" by (rule isabelle_entity_rename_id)
    finally show ?thesis .
  qed
  have removed_back: "map (isabelle_entity_rename ?g) (map (isabelle_entity_rename ?h) removed)=removed"
    unfolding map_map by (rule map_idI) (use restored in auto)
  have added_back: "map (isabelle_entity_rename ?g) (map (isabelle_entity_rename ?h) added)=added"
    unfolding map_map by (rule map_idI) (use restored in auto)
  show ?thesis
    by (simp only: development_native_answer_state_def development_native_answer_of_def Let_def case_prod_conv
      appended removed_back added_back)
qed

section \<open>An answer is judged natively\<close>

text \<open>
  The native judgment of an answer to a request reads the answer from its bits and applies the
  verdict of the problem's kind to the request state and the answer state. It is refused exactly
  when the bits present no answer, and otherwise it is the verdict of the answer the bits present;
  an accepted verdict's contract (\<open>development_constant_verdict_contract\<close>) is then the answer's
  local contract, consumed by every use without being established again.
\<close>

type_synonym development_native_judgment = "(development_native_answer\<times>development_constant_verdict) option"

definition development_native_judgment ::
    "(isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_constant_verdict) \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> bool list \<Rightarrow> development_native_judgment" where
  "development_native_judgment verdict S r bits=map_option (\<lambda>A. (A,verdict S r (development_native_answer_state S A)))
    (development_native_answer_bits_read bits)"

theorem development_native_judgment_exact:
  "development_native_judgment verdict S r bits=Some (A,v) \<longleftrightarrow> development_native_answer_formed A \<and>
    (\<exists>k. bits=finite_term_shared_word (development_native_answer_data A)@True#replicate k False) \<and>
    v=verdict S r (development_native_answer_state S A)"
  unfolding development_native_judgment_def map_option_eq_Some development_native_answer_bits_read_exact
  by (simp only: prod.inject) blast

corollary development_native_judgment_word:
  assumes formed: "development_native_answer_formed A"
  shows "development_native_judgment verdict S r (development_native_answer_word A)=
    Some (A,verdict S r (development_native_answer_state S A))"
  by (simp add: development_native_judgment_def development_native_answer_word_read[OF formed])

section \<open>The restating answer\<close>

text \<open>
  The deterministic executor's answer, stated natively: it removes the subject's statements of the
  demanded kind that the request's context holds and adds them again. It is computed from the request
  state and the request alone, and it changes nothing the request reads.
\<close>

definition development_restating_answer ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow>
      development_native_answer" where
  "development_restating_answer reading S r=(let stated=filter (\<lambda>e. e |\<in>| snd (snd (snd r)) \<and>
       development_answer_statement (development_demanded reading) (snd S) (problem_subject (fst r)) e) (snd (snd S)) in
     development_native_answer_of (fst (snd S)) stated stated)"

section \<open>Derived answers exercise a verdict\<close>

text \<open>
  Before an answer of a kind exists, its verdict is exercised on answers derived from the request
  state and the request itself, each standing for one kind of answer and applied to the request state
  as an executor's answer is. The unchanged answer must be accepted. The others state the subject's
  demanded statements as axioms, drop them, state them through a constant the state does not know,
  drop the demanded statements of the other subjects, and drop the subject's other statements. Each
  is derived from the request, the reading of its kind and the state; none names a position of
  either list or selects a subject. Beside them the renaming of the whole state, which is no answer,
  shows that the verdict reads no position.
\<close>

fun isabelle_right_wrap :: "isabelle_term \<Rightarrow> isabelle_term \<Rightarrow> isabelle_term" where
  "isabelle_right_wrap g (Isabelle_Application (Isabelle_Application (Isabelle_Constant e T) l) r)=
    Isabelle_Application (Isabelle_Application (Isabelle_Constant e T) l) (Isabelle_Application g r)"
| "isabelle_right_wrap g (Isabelle_Application (Isabelle_Constant j T) p)=
    Isabelle_Application (Isabelle_Constant j T) (isabelle_right_wrap g p)"
| "isabelle_right_wrap g t=t"

definition development_absent_name :: "String.literal list \<Rightarrow> String.literal" where
  "development_absent_name names=foldr (+) names STR ''.absent''"

definition development_control_answers ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> isabelle_entity) \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> nat fset \<Rightarrow> development_request \<Rightarrow> development_native_answer list" where
  "development_control_answers reading restate S subjects r=(case r of (p,s,support,E) \<Rightarrow>
    let names=fst (snd S); es=snd (snd S); P=problem_subject p; others=subjects |-| P;
      stated=development_answer_statement (development_demanded reading) (snd S);
      mine=filter (stated P) es;
      fresh=Isabelle_Constant (length names) (Isabelle_Type_Application (length names) []) in
    [development_native_answer_of names [] [],
     development_native_answer_of names [] (map (\<lambda>e. Isabelle_Specification (the (reading e))) mine),
     development_native_answer_of names mine [],
     development_native_answer_of (names@[development_absent_name names]) mine
       (map (\<lambda>e. restate (isabelle_right_wrap fresh (the (reading e)))) mine@[Isabelle_Development_Constant fresh]),
     development_native_answer_of names (filter (stated others) es) [],
     development_native_answer_of names (filter (\<lambda>e. isabelle_specified_proposition e\<noteq>None \<and> reading e=None \<and>
       list_ex (\<lambda>c. c |\<in>| P) (isabelle_entity_subjects names (isabelle_development_constants es) e)) es) []])"

definition development_answer_controls ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> (isabelle_term \<Rightarrow> isabelle_entity) \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat fset \<Rightarrow> development_request \<Rightarrow>
      isabelle_rooted_context list" where
  "development_answer_controls reading restate S renamed subjects r=
    (case map (development_native_answer_state S) (development_control_answers reading restate S subjects r) of
      [] \<Rightarrow> [renamed] | A#As \<Rightarrow> A#renamed#As)"

section \<open>The native answers of the issued requests\<close>

text \<open>
  For each issued request the restating answer is transported as its word and judged from it, and the
  same word without its terminating bit is judged too: the first reads back as the answer and is
  judged by the verdict of the request's kind, the second presents no answer and is refused.
\<close>

definition development_native_answers ::
    "(isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_constant_verdict) \<Rightarrow>
      (isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request list \<Rightarrow>
      (development_native_judgment\<times>bool) list" where
  "development_native_answers verdict reading S rs=Parallel.map (\<lambda>r.
    let bits=development_native_answer_word (development_restating_answer reading S r) in
    (development_native_judgment verdict S r bits,development_native_judgment verdict S r (butlast bits)=None)) rs"

definition development_native_judgment_data :: "development_native_judgment \<Rightarrow> finite_factor_term" where
  "development_native_judgment_data=finite_option_presentation
    (finite_pair_presentation development_native_answer_data development_verdict_data)"

lemma development_native_judgment_data_injective [intro]: "inj development_native_judgment_data"
  unfolding development_native_judgment_data_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective
    development_native_answer_data_injective development_verdict_data_injective)

definition development_native_answers_data :: "(development_native_judgment\<times>bool) list \<Rightarrow> finite_factor_term" where
  "development_native_answers_data=finite_sequence_presentation
    (finite_pair_presentation development_native_judgment_data finite_boolean_data)"

lemma development_native_answers_data_injective [intro]: "inj development_native_answers_data"
  unfolding development_native_answers_data_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
    development_native_judgment_data_injective finite_boolean_data_injective)

section \<open>An executor's answer names its request\<close>

text \<open>
  An executor's answer arrives as bits beside the name of the subject of the request it answers; the
  request is read by that name in the request state's table, and the answer is judged against it.
  The summary retains whether the answer was read, whether its verdict is accepted, the verdict's
  counts, the names of the constants outside the support and the size of the answer.
\<close>

definition development_named_native_judgment ::
    "(isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_constant_verdict) \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> development_request list \<Rightarrow> String.literal \<Rightarrow> bool list \<Rightarrow>
      (development_request\<times>development_native_judgment) option" where
  "development_named_native_judgment verdict S rs n bits=map_option (\<lambda>r. (r,development_native_judgment verdict S r bits))
    (development_named_request (snd S) rs n)"

definition development_named_native_judgment_data ::
    "(development_request\<times>development_native_judgment) option \<Rightarrow> finite_factor_term" where
  "development_named_native_judgment_data=finite_option_presentation
    (finite_pair_presentation development_request_data development_native_judgment_data)"

lemma development_named_native_judgment_data_injective [intro]: "inj development_named_native_judgment_data"
  unfolding development_named_native_judgment_data_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective
    development_request_data_injective development_native_judgment_data_injective)

definition development_native_summary ::
    "(isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_constant_verdict) \<Rightarrow>
      isabelle_rooted_context \<Rightarrow> development_request list \<Rightarrow> String.literal \<Rightarrow> bool list \<Rightarrow>
      (bool\<times>bool\<times>nat list\<times>String.literal list\<times>nat list) option" where
  "development_native_summary verdict S rs n bits=map_option (\<lambda>(r,j). case j of
      None \<Rightarrow> (False,False,[],[],[])
    | Some (A,v) \<Rightarrow> (True,development_verdict_accepted v,development_verdict_counts v,
        List.map_filter (isabelle_name_at (fst (snd (development_native_answer_state S A)))) (development_verdict_excess v),
        case A of (ns,removed,added) \<Rightarrow> [length ns,length removed,length added]))
    (development_named_native_judgment verdict S rs n bits)"

section \<open>A request is presented to an executor natively\<close>

text \<open>
  An executor receives the request natively: the constant, the issued support, the least context and
  the incumbent statements the request replaces, presented with the names they use, as an answer is.
  The packet is transported as the word of that presentation, as a report is, and the executor's
  answer returns as the word of a native answer, read by its exact reader. An executor that removes
  the incumbent statements of its packet and adds them again answers with the restating answer's edit
  over the packet's names: the same answer state, another presentation of it.
\<close>

type_synonym development_native_packet =
  "String.literal list\<times>isabelle_term\<times>nat list\<times>isabelle_entity list\<times>isabelle_entity list"

definition development_native_packet ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow>
      development_native_packet" where
  "development_native_packet reading S r=(case r of (p,s,support,E) \<Rightarrow>
    let names=fst (snd S); context=filter (\<lambda>e. e |\<in>| E) (snd (snd S));
      incumbent=filter (development_answer_statement (development_demanded reading) (snd S) (problem_subject p)) context;
      ps=isabelle_term_positions s@sorted_list_of_fset support@concat (map isabelle_entity_positions context);
      g=isabelle_local_embedding names ps in
    (isabelle_local_names names ps,isabelle_term_rename g s,map g (sorted_list_of_fset support),
     map (isabelle_entity_rename g) context,map (isabelle_entity_rename g) incumbent))"

definition development_native_packet_data :: "development_native_packet \<Rightarrow> finite_factor_term" where
  "development_native_packet_data=finite_pair_presentation isabelle_names_data
    (finite_pair_presentation isabelle_term_data
      (finite_pair_presentation (finite_sequence_presentation isabelle_position_data)
        (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data)
          (finite_sequence_presentation isabelle_entity_data))))"

lemma development_native_packet_data_injective [intro]: "inj development_native_packet_data"
  unfolding development_native_packet_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective isabelle_names_data_injective
    isabelle_term_data_injective isabelle_position_data_injective isabelle_entity_data_injective)

definition development_named_native_packet_data ::
    "(isabelle_entity \<Rightarrow> isabelle_term option) \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_request list \<Rightarrow>
      String.literal \<Rightarrow> finite_factor_term" where
  "development_named_native_packet_data reading S rs n=finite_option_presentation development_native_packet_data
    (map_option (development_native_packet reading S) (development_named_request (snd S) rs n))"

end
