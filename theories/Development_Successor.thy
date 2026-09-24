theory Development_Successor
  imports Development_Refinement_Repair Development_Policy Development_Decomposition Development_State_Rows
begin

section \<open>Problems move with the positions of the state\<close>

text \<open>
  A problem's subject and contract are positions and terms of the state it was posed in. A renaming
  of the state moves every problem with the correspondence of the two tables. Dependencies are
  finite inference rules, so they move as the existing embedding of a rule table, and the existing
  renaming theorem of the least closure carries settlement and readiness across. These are the
  contracts of a genuine renaming, a state moved to another table on purpose. The successor of the
  development renames nothing: it reads its answer state into the request state's table, so every
  problem it carries stands where it stood (\<open>development_successor_keeps\<close>).
\<close>

fun development_contract_rename :: "(nat \<Rightarrow> nat) \<Rightarrow> development_contract \<Rightarrow> development_contract" where
  "development_contract_rename f (Development_Refinement t)=Development_Refinement (isabelle_term_rename f t)"
| "development_contract_rename f (Development_Proof t)=Development_Proof (isabelle_term_rename f t)"
| "development_contract_rename f (Development_Presentation t)=Development_Presentation (isabelle_term_rename f t)"
| "development_contract_rename f (Development_Definition t)=Development_Definition (isabelle_term_rename f t)"
| "development_contract_rename f (Development_Amendment t)=Development_Amendment (isabelle_term_rename f t)"

definition development_problem_rename :: "(nat \<Rightarrow> nat) \<Rightarrow> development_problem \<Rightarrow> development_problem" where
  "development_problem_rename f p=Development_Problem (fimage f (problem_subject p))
    (development_contract_rename f (problem_contract p)) (problem_origin p) (problem_authority p)"

text \<open>
  A problem uses the positions of its subject and of its contract's term; a renaming that fixes them
  fixes the problem.
\<close>

definition development_problem_positions :: "development_problem \<Rightarrow> nat set" where
  "development_problem_positions p=fset (problem_subject p)\<union>
    set (isabelle_term_positions (development_contract_term (problem_contract p)))"

lemma development_problem_rename_fixed:
  assumes fixed: "\<And>i. i\<in>development_problem_positions p \<Longrightarrow> f i=i"
  shows "development_problem_rename f p=p"
proof -
  have subject: "fimage f (problem_subject p)=problem_subject p"
  proof -
    have "fimage f (problem_subject p)=fimage id (problem_subject p)"
      by (rule fset.map_cong0) (simp add: fixed development_problem_positions_def)
    then show ?thesis by simp
  qed
  have renamed: "isabelle_term_rename f t=t" if used: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> f i=i" for t
  proof -
    have "isabelle_term_rename f t=isabelle_term_rename id t" by (rule isabelle_term_rename_cong) (simp add: used)
    then show ?thesis by (simp only: isabelle_term_rename_id)
  qed
  have contract: "development_contract_rename f (problem_contract p)=problem_contract p"
    using fixed by (cases "problem_contract p") (auto simp: development_problem_positions_def intro!: renamed)
  show ?thesis unfolding development_problem_rename_def subject contract by (cases p) simp
qed

theorem development_answered_rules_renaming:
  assumes injective: "inj g"
  shows "development_answered_rules (finite_embedded_inferences g D) (fimage g answered)=
    finite_embedded_inferences g (development_answered_rules D answered)"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| development_answered_rules (finite_embedded_inferences g D) (fimage g answered) \<longleftrightarrow>
      x |\<in>| finite_embedded_inferences g (development_answered_rules D answered)"
    using injective by (auto simp: development_answered_rules_def finite_embedded_inferences_def fimage_iff
      inj_eq split: prod.splits)
qed

theorem development_settled_renaming:
  assumes injective: "inj g" and formed: "finite_inference_formed (development_answered_rules D answered)"
  shows "development_settled (finite_embedded_inferences g D) (fimage g answered)=g ` development_settled D answered"
proof -
  have "development_settled (finite_embedded_inferences g D) (fimage g answered)=
      finite_inference_result (finite_embedded_inferences g (development_answered_rules D answered)) (fimage g {||})"
    by (simp only: development_settled_def development_answered_rules_renaming[OF injective] fimage_fempty)
  then show ?thesis
    by (simp only: finite_inference_result_renaming[OF injective formed] development_settled_def)
qed

theorem development_decompositions_renaming:
  assumes injective: "inj g"
  shows "development_decompositions (finite_embedded_inferences g D) (g p)=
    fimage (fimage (\<lambda>(i,b). (i,g b))) (development_decompositions D p)"
proof -
  let ?h="\<lambda>(a,H). (g a,fimage (\<lambda>(i,b). (i,g b)) H)"
  have filtered: "ffilter (\<lambda>(q,H). q=g p) (fimage ?h D)=fimage ?h (ffilter (\<lambda>(q,H). q=p) D)"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| ffilter (\<lambda>(q,H). q=g p) (fimage ?h D) \<longleftrightarrow> x |\<in>| fimage ?h (ffilter (\<lambda>(q,H). q=p) D)"
      using injective by (auto simp: fimage_iff inj_eq)
  qed
  have composed: "snd \<circ> ?h=fimage (\<lambda>(i,b). (i,g b)) \<circ> snd" by (rule ext) (simp add: split_def)
  show ?thesis
    by (simp only: development_decompositions_def finite_embedded_inferences_def filtered fset.map_comp composed)
qed

theorem development_premises_renaming:
  assumes injective: "inj g"
  shows "development_premises (finite_embedded_inferences g D) (g p)=fimage g (development_premises D p)"
proof -
  have composed: "fimage snd \<circ> fimage (\<lambda>(i,b). (i,g b))=fimage g \<circ> fimage snd"
    by (rule ext) (simp add: fset.map_comp comp_def split_def)
  have flatten: "fimage g (ffUnion X)=ffUnion (fimage (fimage g) X)" for X
    by (rule fset_eqI) (auto simp: ffUnion.rep_eq fimage.rep_eq)
  show ?thesis
    by (simp only: development_premises_def development_decompositions_renaming[OF injective]
      fset.map_comp composed flatten)
qed

theorem development_ready_renaming:
  assumes injective: "inj g" and formed: "finite_inference_formed (development_answered_rules D answered)"
  shows "development_ready (finite_embedded_inferences g D) (fimage g answered) (g p) \<longleftrightarrow>
    development_ready D answered p"
  using injective by (auto simp: development_ready_def development_premises_renaming[OF injective]
    development_settled_renaming[OF injective formed] fimage_iff inj_eq inj_image_mem_iff)

section \<open>An answer is admitted as a generation of the development\<close>

text \<open>
  An admitted answer is recorded as a generation: its locus is the problem it answers, its
  predecessors are the context of the request, its payload is the subject's equations in the
  answer state, and its cause is the accepted verdict. The first loop's policy admits exactly
  the entities the checked context accepted, and every payload entity is an entity of the
  answer state, so the policy admits the payload; the policy's own contract, proved once, is
  what decides it.
\<close>

type_synonym development_generation = "development_problem\<times>isabelle_entity fset\<times>isabelle_entity list\<times>development_constant_verdict"

definition development_answer_generation ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_generation option" where
  "development_answer_generation S r S'=(case r of (p,s,support,E) \<Rightarrow>
    let v=development_refinement_verdict S r S' in
    if development_verdict_accepted v then
      Some (p,E,development_answer_equations (snd S')
        (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject p)),v)
    else None)"

theorem development_answer_generation_payload:
  assumes generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
  shows "development_verdict_accepted v" "set payload\<subseteq>set (snd (snd S'))" "payload\<noteq>[]"
proof -
  obtain q s support E' where request: "r=(q,s,support,E')" by (cases r) auto
  have accepted: "development_verdict_accepted (development_refinement_verdict S r S')"
    and fields: "p=q" "E=E'" "payload=development_answer_equations (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject q))"
      "v=development_refinement_verdict S r S'"
    using generation by (auto simp: development_answer_generation_def request Let_def split: if_splits)
  show "development_verdict_accepted v" using accepted by (simp only: fields(4))
  show "set payload\<subseteq>set (snd (snd S'))"
    by (simp add: fields(3) development_answer_equations_exact)
  obtain e' where member: "e'\<in>set (snd (snd S'))"
    and answer: "development_answer_equation (snd S')
      (fimage (isabelle_state_embedding (fst (snd S)) (fst (snd S'))) (problem_subject q)) e'"
    using development_refinement_verdict_contract(3)[OF accepted[unfolded request]] by blast
  have "e'\<in>set payload" using member answer by (simp add: fields(3) development_answer_equations_exact)
  then show "payload\<noteq>[]" by auto
qed

theorem development_answer_generation_policy:
  assumes generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
    and policy: "development_policy_source (snd (snd S'))=Some (a,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and payload: "e\<in>set payload"
  shows "(a,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning T"
  by (rule development_policy_admits_member[OF policy package])
    (use development_answer_generation_payload(2)[OF generation] payload in blast)

section \<open>The answer state read into the request state's table is judged as exported\<close>

text \<open>
  The successor judges its answer state read into the request state's table
  (\<open>isabelle_rooted_read\<close>). The reading is a correspondence of the answer state's table with the
  extended one, and the verdict of every kind whose statements are invariant under renaming accepts on
  the read state exactly when it accepts on the state as exported. The premises are the two states'
  own: distinct tables, every position within its table, and a request whose subject and support are
  positions of the request state. The read state removes and adds exactly the entities the exported
  one does, read in the extended table; its statements, their excess, its assessment and its roots
  correspond through the reading, and a name the answer dropped keeps its position in the extended
  table, used by no entity. Nothing about a verdict is proved again: the reading's laws and the
  renaming contracts of the assessment and of the subject reading carry it.
\<close>

theorem development_constant_verdict_read:
  assumes kinds: "\<And>g e. replaceable (isabelle_entity_rename g e)=replaceable e"
      "\<And>g e. demanded (isabelle_entity_rename g e)=demanded e"
    and distinct: "distinct (fst (snd S))" "distinct (fst (snd S'))"
    and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}" "state_positions S'\<subseteq>{..<length (fst (snd S'))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
    and support: "fset support\<subseteq>{..<length (fst (snd S))}"
  shows "development_verdict_accepted (development_constant_verdict replaceable demanded S (p,s,support,E)
      (isabelle_rooted_read (fst (snd S)) S')) \<longleftrightarrow>
    development_verdict_accepted (development_constant_verdict replaceable demanded S (p,s,support,E) S')"
proof -
  let ?n="fst (snd S)" and ?n'="fst (snd S')" and ?C="snd (snd S)" and ?C'="snd (snd S')"
  let ?N="isabelle_appended_names ?n ?n'" and ?h="isabelle_appended_embedding ?n ?n'"
  let ?f="isabelle_state_embedding ?n ?n'" and ?g="isabelle_state_embedding ?n ?N"
  let ?R="isabelle_rooted_read ?n S'" and ?P="problem_subject p"
  have read: "fst ?R=map (isabelle_term_rename ?h) (fst S')" "snd ?R=(?N,map (isabelle_entity_rename ?h) ?C')"
    by (simp_all only: isabelle_rooted_read_fields)
  have corr: "isabelle_table_correspondence ?h ?n' ?N"
    by (rule isabelle_appended_embedding_correspondence[OF distinct(2)])
  have tables: "distinct ?N" by (rule isabelle_appended_names_distinct[OF distinct])
  have entity_S: "i<length ?n" if "e\<in>set ?C" "i\<in>set (isabelle_entity_positions e)" for e i
    using inside(1) that by (auto simp: state_positions_def)
  have entity_S': "j<length ?n'" if "e'\<in>set ?C'" "j\<in>set (isabelle_entity_positions e')" for e' j
    using inside(2) that by (auto simp: state_positions_def)
  have root_S: "i<length ?n" if "t\<in>set (fst S)" "i\<in>set (isabelle_term_positions t)" for t i
    using inside(1) that by (auto simp: state_positions_def)
  have root_S': "j<length ?n'" if "t\<in>set (fst S')" "j\<in>set (isabelle_term_positions t)" for t j
    using inside(2) that by (auto simp: state_positions_def)
  have kept: "?g i=i" if "i<length ?n" for i
    using isabelle_state_embedding_prefix[OF distinct(1) that] by (simp add: isabelle_appended_names_def)
  have kept_entity: "isabelle_entity_rename ?g e=e" if member: "e\<in>set ?C" for e
  proof -
    have "isabelle_entity_rename ?g e=isabelle_entity_rename id e"
      by (rule isabelle_entity_rename_cong) (simp add: kept entity_S[OF member])
    then show ?thesis by (simp only: isabelle_entity_rename_id)
  qed
  have kept_root: "isabelle_term_rename ?g t=t" if member: "t\<in>set (fst S)" for t
  proof -
    have "isabelle_term_rename ?g t=isabelle_term_rename id t"
      by (rule isabelle_term_rename_cong) (simp add: kept root_S[OF member])
    then show ?thesis by (simp only: isabelle_term_rename_id)
  qed
  have kept_subject: "fimage ?g ?P=?P"
  proof -
    have "fimage ?g ?P=fimage id ?P" by (rule fset.map_cong0) (use subject in \<open>auto intro!: kept\<close>)
    then show ?thesis by simp
  qed
  have kept_support: "fimage ?g support=support"
  proof -
    have "fimage ?g support=fimage id support" by (rule fset.map_cong0) (use support in \<open>auto intro!: kept\<close>)
    then show ?thesis by simp
  qed
  have returned: "isabelle_entity_rename ?h (isabelle_entity_rename ?f e)=e"
    if member: "e\<in>set ?C" and moved: "isabelle_entity_rename ?f e\<in>set ?C'" for e
  proof (rule isabelle_appended_entity_back[OF distinct(1)])
    fix i assume used: "i\<in>set (isabelle_entity_positions e)"
    show "i<length ?n" by (rule entity_S[OF member used])
  next
    fix i assume used: "i\<in>set (isabelle_entity_positions e)"
    have "?f i\<in>set (isabelle_entity_positions (isabelle_entity_rename ?f e))"
      using used by (simp add: isabelle_entity_rename_positions)
    then show "?f i<length ?n'" by (rule entity_S'[OF moved])
  qed
  have carried: "isabelle_entity_rename ?f (isabelle_entity_rename ?h e')=e'"
    if member: "e'\<in>set ?C'" and moved: "isabelle_entity_rename ?h e'\<in>set ?C" for e'
  proof (rule isabelle_appended_entity_forth[OF distinct(2)])
    fix j assume used: "j\<in>set (isabelle_entity_positions e')"
    show "j<length ?n'" by (rule entity_S'[OF member used])
  next
    fix j assume used: "j\<in>set (isabelle_entity_positions e')"
    have "?h j\<in>set (isabelle_entity_positions (isabelle_entity_rename ?h e'))"
      using used by (simp add: isabelle_entity_rename_positions)
    then show "?h j<length ?n" by (rule entity_S[OF moved])
  qed
  have back_root: "isabelle_term_rename ?h (isabelle_term_rename ?f t)=t"
    if member: "t\<in>set (fst S)" and moved: "isabelle_term_rename ?f t\<in>set (fst S')" for t
  proof (rule isabelle_appended_term_back[OF distinct(1)])
    fix i assume used: "i\<in>set (isabelle_term_positions t)"
    show "i<length ?n" by (rule root_S[OF member used])
  next
    fix i assume used: "i\<in>set (isabelle_term_positions t)"
    have "?f i\<in>set (isabelle_term_positions (isabelle_term_rename ?f t))"
      using used by (simp add: isabelle_term_rename_positions)
    then show "?f i<length ?n'" by (rule root_S'[OF moved])
  qed
  have forth_root: "isabelle_term_rename ?f (isabelle_term_rename ?h t')=t'"
    if member: "t'\<in>set (fst S')" and moved: "isabelle_term_rename ?h t'\<in>set (fst S)" for t'
  proof (rule isabelle_appended_term_forth[OF distinct(2)])
    fix j assume used: "j\<in>set (isabelle_term_positions t')"
    show "j<length ?n'" by (rule root_S'[OF member used])
  next
    fix j assume used: "j\<in>set (isabelle_term_positions t')"
    have "?h j\<in>set (isabelle_term_positions (isabelle_term_rename ?h t'))"
      using used by (simp add: isabelle_term_rename_positions)
    then show "?h j<length ?n" by (rule root_S[OF moved])
  qed
  have persists: "isabelle_entity_rename ?f e\<in>set ?C' \<longleftrightarrow> e\<in>set (map (isabelle_entity_rename ?h) ?C')"
    if member: "e\<in>set ?C" for e
  proof
    assume moved: "isabelle_entity_rename ?f e\<in>set ?C'"
    have "isabelle_entity_rename ?h (isabelle_entity_rename ?f e)\<in>set (map (isabelle_entity_rename ?h) ?C')"
      using moved by simp
    then show "e\<in>set (map (isabelle_entity_rename ?h) ?C')" by (simp only: returned[OF member moved])
  next
    assume "e\<in>set (map (isabelle_entity_rename ?h) ?C')"
    then obtain e' where e': "e'\<in>set ?C'" and image: "e=isabelle_entity_rename ?h e'" by auto
    have "isabelle_entity_rename ?f e=e'" using carried[OF e'] member image by simp
    then show "isabelle_entity_rename ?f e\<in>set ?C'" using e' by simp
  qed
  have imaged: "isabelle_entity_rename ?h e'\<in>set ?C \<longleftrightarrow> e'\<in>set (map (isabelle_entity_rename ?f) ?C)"
    if member: "e'\<in>set ?C'" for e'
  proof
    assume moved: "isabelle_entity_rename ?h e'\<in>set ?C"
    have "isabelle_entity_rename ?f (isabelle_entity_rename ?h e')\<in>set (map (isabelle_entity_rename ?f) ?C)"
      using moved by simp
    then show "e'\<in>set (map (isabelle_entity_rename ?f) ?C)" by (simp only: carried[OF member moved])
  next
    assume "e'\<in>set (map (isabelle_entity_rename ?f) ?C)"
    then obtain e where e: "e\<in>set ?C" and image: "e'=isabelle_entity_rename ?f e" by auto
    have "isabelle_entity_rename ?h e'=e" using returned[OF e] member image by simp
    then show "isabelle_entity_rename ?h e'\<in>set ?C" using e by simp
  qed
  have removed: "isabelle_state_removed (snd S) (snd ?R)=isabelle_state_removed (snd S) (snd S')"
    unfolding isabelle_state_removed_def Let_def read(2) fst_conv snd_conv
    by (rule filter_cong[OF refl]) (simp only: kept_entity persists)
  have added: "isabelle_state_added (snd S) (?N,map (isabelle_entity_rename ?h) ?C')=
      map (isabelle_entity_rename ?h) (isabelle_state_added (snd S) (snd S'))"
  proof -
    have gone: "map (isabelle_entity_rename ?g) ?C=?C" by (rule map_idI) (rule kept_entity)
    show ?thesis
      unfolding isabelle_state_added_def Let_def isabelle_state_image_def fst_conv snd_conv gone filter_map
      by (rule arg_cong[where f="map (isabelle_entity_rename ?h)"], rule filter_cong[OF refl]) (simp add: imaged)
  qed
  have statement: "development_answer_statement K (?N,map (isabelle_entity_rename ?h) ?C') ?P
        (isabelle_entity_rename ?h e') \<longleftrightarrow> development_answer_statement K (snd S') (fimage ?f ?P) e'"
    if kind: "\<And>g e. K (isabelle_entity_rename g e)=K e" and member: "e'\<in>set ?C'" for K e'
  proof -
    have subjects: "isabelle_entity_subjects ?N (isabelle_development_constants (map (isabelle_entity_rename ?h) ?C'))
        (isabelle_entity_rename ?h e')=map ?h (isabelle_entity_subjects ?n' (isabelle_development_constants ?C') e')"
      by (simp only: isabelle_rename_development_constants isabelle_rename_entity_subjects[OF corr])
    have met: "?h d |\<in>| ?P \<longleftrightarrow> d |\<in>| fimage ?f ?P"
      if listed: "d\<in>set (isabelle_entity_subjects ?n' (isabelle_development_constants ?C') e')" for d
    proof -
      have "d<length ?n'" using listed isabelle_entity_subjects_positions entity_S'[OF member] by blast
      then show ?thesis by (rule isabelle_appended_embedding_image[OF distinct subject])
    qed
    show ?thesis
      unfolding development_answer_statement_def fst_conv snd_conv subjects kind list_ex_iff
      by (auto simp: met)
  qed
  have statements: "development_answer_statements K (?N,map (isabelle_entity_rename ?h) ?C') ?P=
      map (isabelle_entity_rename ?h) (development_answer_statements K (snd S') (fimage ?f ?P))"
    if kind: "\<And>g e. K (isabelle_entity_rename g e)=K e" for K
    unfolding development_answer_statements_def snd_conv filter_map
    by (rule arg_cong[where f="map (isabelle_entity_rename ?h)"], rule filter_cong[OF refl])
      (simp add: statement[OF kind])
  let ?L="concat (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition)
    (development_answer_statements replaceable (snd S') (fimage ?f ?P)))"
  have bounded: "d<length ?n'" if listed: "d\<in>set ?L" for d
  proof -
    obtain l e' where e': "e'\<in>set (development_answer_statements replaceable (snd S') (fimage ?f ?P))"
      and found: "(map_option isabelle_term_constants \<circ> isabelle_specified_proposition) e'=Some l"
      and within: "d\<in>set l"
      using listed by (auto simp: map_filter_member)
    obtain q where q: "isabelle_specified_proposition e'=Some q" "l=isabelle_term_constants q"
      using found by (auto simp: map_option_eq_Some)
    have member: "e'\<in>set ?C'" using e' by (simp add: development_answer_statements_def)
    have "d\<in>set (isabelle_entity_positions e')"
      using q within isabelle_term_constants_positions[of q]
      by (cases e') (auto simp: isabelle_entity_positions_def)
    then show ?thesis by (rule entity_S'[OF member])
  qed
  have listed: "List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition)
      (map (isabelle_entity_rename ?h) X)=
    map (map ?h) (List.map_filter (map_option isabelle_term_constants \<circ> isabelle_specified_proposition) X)" for X
    by (rule map_filter_rename)
      (simp add: isabelle_entity_rename_specified isabelle_term_rename_constants option.map_comp comp_def)
  have excess: "development_answer_statements_excess replaceable (?N,map (isabelle_entity_rename ?h) ?C') ?P support=[] \<longleftrightarrow>
      development_answer_statements_excess replaceable (snd S') (fimage ?f ?P) (fimage ?f support)=[]"
  proof -
    have left: "development_answer_statements_excess replaceable (?N,map (isabelle_entity_rename ?h) ?C') ?P support=[] \<longleftrightarrow>
        (\<forall>d\<in>set ?L. ?h d |\<in>| support)"
      unfolding development_answer_statements_excess_def statements[OF kinds(1)] listed map_concat[symmetric]
      by (simp add: filter_map filter_empty_conv)
    have right: "development_answer_statements_excess replaceable (snd S') (fimage ?f ?P) (fimage ?f support)=[] \<longleftrightarrow>
        (\<forall>d\<in>set ?L. d |\<in>| fimage ?f support)"
      unfolding development_answer_statements_excess_def by (simp add: filter_empty_conv)
    show ?thesis unfolding left right
      by (rule ball_cong[OF refl]) (rule isabelle_appended_embedding_image[OF distinct support bounded])
  qed
  have unpermitted: "filter (\<lambda>e. \<not>development_answer_statement replaceable (snd ?R)
        (fimage (isabelle_state_embedding ?n (fst (snd ?R))) ?P) e) (isabelle_state_added (snd S) (snd ?R))=[] \<longleftrightarrow>
      filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S') (fimage ?f ?P) e)
        (isabelle_state_added (snd S) (snd S'))=[]"
  proof -
    have "filter ((\<lambda>e. \<not>development_answer_statement replaceable (?N,map (isabelle_entity_rename ?h) ?C') ?P e) \<circ>
          isabelle_entity_rename ?h) (isabelle_state_added (snd S) (snd S'))=
        filter (\<lambda>e. \<not>development_answer_statement replaceable (snd S') (fimage ?f ?P) e)
          (isabelle_state_added (snd S) (snd S'))"
      by (rule filter_cong[OF refl]) (simp add: statement[OF kinds(1)] isabelle_state_added_exact)
    then show ?thesis by (simp only: read(2) fst_conv kept_subject added filter_map map_is_Nil_conv)
  qed
  have demanded: "development_answer_statements demanded (snd ?R) (fimage (isabelle_state_embedding ?n (fst (snd ?R))) ?P)=[] \<longleftrightarrow>
      development_answer_statements demanded (snd S') (fimage ?f ?P)=[]"
    by (simp only: read(2) fst_conv kept_subject statements[OF kinds(2)] map_is_Nil_conv)
  have exceeded: "development_answer_statements_excess replaceable (snd ?R)
        (fimage (isabelle_state_embedding ?n (fst (snd ?R))) ?P) (fimage (isabelle_state_embedding ?n (fst (snd ?R))) support)=[] \<longleftrightarrow>
      development_answer_statements_excess replaceable (snd S') (fimage ?f ?P) (fimage ?f support)=[]"
    by (simp only: read(2) fst_conv kept_subject kept_support excess)
  have assessment: "isabelle_context_assessment (fst ?R) (snd ?R)=
      isabelle_assessment_rename ?h (isabelle_context_assessment (fst S') (snd S'))"
    unfolding isabelle_rooted_read_def by (rule isabelle_renamed_rooted_assessment[OF corr])
  have closed: "isabelle_assessment_closed (isabelle_context_assessment (fst ?R) (snd ?R)) \<longleftrightarrow>
      isabelle_assessment_closed (isabelle_context_assessment (fst S') (snd S'))"
    unfolding assessment
    by (cases "isabelle_context_assessment (fst S') (snd S')" rule: prod_cases5) (simp add: isabelle_assessment_closed_def)
  have roots: "map (isabelle_term_rename (isabelle_state_embedding ?n (fst (snd ?R)))) (fst S)=fst ?R \<longleftrightarrow>
      map (isabelle_term_rename ?f) (fst S)=fst S'"
  proof -
    have kept_roots: "map (isabelle_term_rename ?g) (fst S)=fst S" by (rule map_idI) (rule kept_root)
    have "fst S=map (isabelle_term_rename ?h) (fst S') \<longleftrightarrow> map (isabelle_term_rename ?f) (fst S)=fst S'"
    proof
      assume same: "fst S=map (isabelle_term_rename ?h) (fst S')"
      have "map (isabelle_term_rename ?f) (map (isabelle_term_rename ?h) (fst S'))=fst S'"
      proof (rule trans[OF map_map], rule map_idI)
        fix t' assume member: "t'\<in>set (fst S')"
        have "isabelle_term_rename ?h t'\<in>set (fst S)" using member by (simp add: same)
        then show "(isabelle_term_rename ?f \<circ> isabelle_term_rename ?h) t'=t'" by (simp add: forth_root[OF member])
      qed
      then show "map (isabelle_term_rename ?f) (fst S)=fst S'" by (simp only: same)
    next
      assume same: "map (isabelle_term_rename ?f) (fst S)=fst S'"
      have "map (isabelle_term_rename ?h) (map (isabelle_term_rename ?f) (fst S))=fst S"
      proof (rule trans[OF map_map], rule map_idI)
        fix t assume member: "t\<in>set (fst S)"
        have "isabelle_term_rename ?f t\<in>set (fst S')" using member by (simp add: same[symmetric])
        then show "(isabelle_term_rename ?h \<circ> isabelle_term_rename ?f) t=t" by (simp add: back_root[OF member])
      qed
      then show "fst S=map (isabelle_term_rename ?h) (fst S')" by (simp only: same)
    qed
    then show ?thesis by (simp only: read fst_conv kept_roots)
  qed
  have named: "distinct (fst (snd ?R))" by (simp only: read(2) fst_conv tables)
  show ?thesis
    unfolding development_verdict_accepted_def development_constant_verdict_def Let_def prod.case
    by (simp only: removed unpermitted demanded exceeded closed roots named distinct simp_thms)
qed

lemma development_demanded_code_renamed:
  "development_demanded isabelle_code_equation_proposition (isabelle_entity_rename g e)=
    development_demanded isabelle_code_equation_proposition e"
  by (cases e) (simp_all add: development_demanded_def)

corollary development_refinement_verdict_read:
  assumes distinct: "distinct (fst (snd S))" "distinct (fst (snd S'))"
    and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}" "state_positions S'\<subseteq>{..<length (fst (snd S'))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
    and support: "fset support\<subseteq>{..<length (fst (snd S))}"
  shows "development_verdict_accepted (development_refinement_verdict S (p,s,support,E)
      (isabelle_rooted_read (fst (snd S)) S')) \<longleftrightarrow>
    development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
  unfolding development_refinement_verdict_def
  by (rule development_constant_verdict_read[OF development_demanded_code_renamed development_demanded_code_renamed
    distinct inside subject support])

section \<open>The successor of the development state\<close>

text \<open>
  The development state is the rooted state of the checked context, its problems, their
  dependencies, the answered problems and the history of its admitted decisions. Three kinds of
  decision are recorded: a selection of the next problems, as the executed native packet and the
  problems it admitted; an admitted answer, as its generation; and a repair derived from a
  refused answer, as the refused request and its repair. An admitted answer moves the development
  to its answer state read into the request state's table extended by the names it lacks, so every
  position of the old state keeps its meaning: every problem, dependency, answered problem and
  record stands unchanged, the answered problem joins the answered ones and the generation, computed
  on the read state, joins the history. Problems are carried, not computed again from the new state:
  the seeding was one choice, and a later state poses no problem the process did not derive.
\<close>

type_synonym development_packet =
  "native_development_question\<times>native_development_report\<times>finite_factor_term list option"

datatype development_record =
    Development_Selection_Record development_packet "development_problem list"
  | Development_Issue_Record development_request "(nat\<times>development_problem) fset fset"
  | Development_Answer_Record development_generation
  | Development_Repair_Record development_request development_refinement_repair

type_synonym development_loop =
  "isabelle_rooted_context\<times>development_problem list\<times>development_dependencies\<times>development_problem fset\<times>
    development_record list"

definition development_successor ::
    "development_loop \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> development_loop option" where
  "development_successor L r S'=(case L of (S,ps,D,answered,history) \<Rightarrow>
    let S2=isabelle_rooted_read (fst (snd S)) S' in
    case development_answer_generation S r S2 of None \<Rightarrow> None
    | Some G \<Rightarrow> Some (S2,ps,D,finsert (fst r) answered,history@[Development_Answer_Record G]))"

theorem development_successor_answered:
  assumes successor: "development_successor (S,ps,D,answered,history) r S'=Some (S2,ps',D',answered',history')"
  shows "fst r |\<in>| answered'" "S2=isabelle_rooted_read (fst (snd S)) S'"
    "\<exists>G. development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')=Some G \<and>
      history'=history@[Development_Answer_Record G]"
    "ps'=ps" "D'=D" "answered'=finsert (fst r) answered"
proof -
  obtain G where gen: "development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')=Some G"
    and fields: "S2=isabelle_rooted_read (fst (snd S)) S'" "ps'=ps" "D'=D" "answered'=finsert (fst r) answered"
      "history'=history@[Development_Answer_Record G]"
  proof (cases "development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')")
    case None
    then show ?thesis using successor by (simp add: development_successor_def Let_def)
  next
    case (Some G)
    have "(S2,ps',D',answered',history')=(isabelle_rooted_read (fst (snd S)) S',ps,D,finsert (fst r) answered,
        history@[Development_Answer_Record G])"
      using successor Some by (simp add: development_successor_def Let_def)
    then show ?thesis using Some by (intro that) auto
  qed
  show "fst r |\<in>| answered'" using fields(4) by simp
  show "S2=isabelle_rooted_read (fst (snd S)) S'" by (rule fields(1))
  show "\<exists>G. development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')=Some G \<and>
      history'=history@[Development_Answer_Record G]" using gen fields(5) by blast
  show "ps'=ps" by (rule fields(2))
  show "D'=D" by (rule fields(3))
  show "answered'=finsert (fst r) answered" by (rule fields(4))
qed

text \<open>
  The successor's correspondence is the identity on every position the old state uses, so every
  problem, locus, row and record of the old state stands unchanged in the successor: renaming a
  problem of the old state by it gives the problem itself. What a locus means stays local to this
  contract; no reader of the history applies a transport.
\<close>

theorem development_successor_keeps:
  assumes successor: "development_successor (S,ps,D,answered,history) r S'=Some (S2,ps',D',answered',history')"
    and distinct: "distinct (fst (snd S))"
  shows "\<And>i. i<length (fst (snd S)) \<Longrightarrow> isabelle_state_embedding (fst (snd S)) (fst (snd S2)) i=i"
    and "\<And>p. development_problem_positions p\<subseteq>{..<length (fst (snd S))} \<Longrightarrow>
      development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S2))) p=p"
proof -
  have table: "fst (snd S2)=fst (snd S)@filter (\<lambda>n. n\<notin>set (fst (snd S))) (fst (snd S'))"
    using development_successor_answered(2)[OF successor] by (simp add: isabelle_rooted_read_fields isabelle_appended_names_def)
  show kept: "isabelle_state_embedding (fst (snd S)) (fst (snd S2)) i=i" if "i<length (fst (snd S))" for i
    unfolding table by (rule isabelle_state_embedding_prefix[OF distinct that])
  show "development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S2))) p=p"
    if "development_problem_positions p\<subseteq>{..<length (fst (snd S))}" for p
    by (rule development_problem_rename_fixed) (use that kept in auto)
qed

theorem development_successor_ready:
  assumes successor: "development_successor (S,ps,D,answered,history) r S'=Some (S2,ps',D',answered',history')"
  shows "development_ready D' answered' q \<longleftrightarrow> development_ready D (finsert (fst r) answered) q"
  by (simp only: development_successor_answered(5,6)[OF successor])

text \<open>
  The successor admits exactly the answers the verdict of the request's kind admits on the answer
  state as exported, whenever both states are presented within their tables and the request's subject
  and support are positions of the request state. The two conditions on each state are those
  @{text state_presentable} spells, and the exporter proves them of every state it defines: its names
  are distinct (@{text NAME_names_distinct}) and its entities and roots use positions of its table
  (@{text NAME_positions_closed}, @{text NAME_roots_closed}, which @{text state_positions_exported}
  joins). So on every pair of states the exporter defines, for a request whose subject and support are
  positions of the request state, the successor admits exactly what the exported verdict admits. The
  lemma says nothing on a state the exporter did not define, where, for an answer the native reader
  reads, @{text development_native_answer_formed} refuses exactly the answers whose state repeats a
  name or uses a position outside its table, nor for a request outside those premises.
\<close>

lemma state_positions_exported:
  assumes entities: "\<forall>e\<in>set (snd C). set (isabelle_entity_positions e)\<subseteq>{..<length (fst C)}"
    and roots: "\<forall>t\<in>set rs. set (isabelle_term_positions t)\<subseteq>{..<length (fst C)}"
  shows "state_positions (rs,C)\<subseteq>{..<length (fst C)}"
  using assms by (auto simp: state_positions_def)

theorem development_successor_admits:
  assumes request: "r=(p,s,support,E)"
    and distinct: "distinct (fst (snd S))" "distinct (fst (snd S'))"
    and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}" "state_positions S'\<subseteq>{..<length (fst (snd S'))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
    and support: "fset support\<subseteq>{..<length (fst (snd S))}"
  shows "development_successor (S,ps,D,answered,history) r S'\<noteq>None \<longleftrightarrow>
    development_verdict_accepted (development_refinement_verdict S r S')"
proof -
  have exists: "development_successor (S,ps,D,answered,history) r S'\<noteq>None \<longleftrightarrow>
      development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')\<noteq>None"
    by (cases "development_answer_generation S r (isabelle_rooted_read (fst (snd S)) S')")
      (simp_all add: development_successor_def Let_def)
  have generation: "development_answer_generation S r R\<noteq>None \<longleftrightarrow>
      development_verdict_accepted (development_refinement_verdict S r R)" for R
  proof (cases "development_verdict_accepted (development_refinement_verdict S r R)")
    case True
    then show ?thesis by (simp add: development_answer_generation_def request Let_def)
  next
    case False
    then show ?thesis by (simp add: development_answer_generation_def request Let_def)
  qed
  show ?thesis
    by (subst exists, subst generation, unfold request,
      rule development_refinement_verdict_read[OF distinct inside subject support])
qed

text \<open>
  Selecting the next problems is the native question on their readiness; the executed packet
  and the admitted problems are recorded, so the decision is part of the history it governs.
\<close>

definition development_loop_selection :: "development_loop \<Rightarrow> (development_loop\<times>development_problem list) option" where
  "development_loop_selection L=(case L of (S,ps,D,answered,history) \<Rightarrow>
    case development_selection_question D answered ps of None \<Rightarrow> None
    | Some Q \<Rightarrow> (let packet=native_development_packet Q in
        map_option (\<lambda>xs. ((S,ps,D,answered,history@[Development_Selection_Record packet xs]),xs))
          (development_packet_problems D answered ps packet)))"

theorem development_loop_selection_ready:
  assumes selection: "development_loop_selection (S,ps,D,answered,history)=Some (L',xs)" and member: "p\<in>set xs"
  shows "p\<in>set ps \<and> development_ready D answered p"
    "\<exists>packet. L'=(S,ps,D,answered,history@[Development_Selection_Record packet xs])"
proof -
  obtain Q where question: "development_selection_question D answered ps=Some Q"
    and admitted: "development_packet_problems D answered ps (native_development_packet Q)=Some xs"
    and state: "L'=(S,ps,D,answered,history@[Development_Selection_Record (native_development_packet Q) xs])"
    using selection by (auto simp: development_loop_selection_def Let_def split: option.splits)
  show "p\<in>set ps \<and> development_ready D answered p" by (rule development_packet_problems_ready[OF question admitted member])
  show "\<exists>packet. L'=(S,ps,D,answered,history@[Development_Selection_Record packet xs])" using state by blast
qed

text \<open>
  Issuing sends a request to an executor only for a leaf of the development library whose
  prerequisites are settled; every other problem is returned unissued. Each issue records the
  request with the library reading it rested on, the absence of any rule for its problem.
\<close>

definition development_loop_issue ::
    "development_dependencies \<Rightarrow> (development_problem \<Rightarrow> development_request option) \<Rightarrow> development_loop \<Rightarrow>
      development_problem list \<Rightarrow> development_loop\<times>development_request list\<times>development_problem list" where
  "development_loop_issue L request_of loop xs=(case loop of (S,ps,D,answered,history) \<Rightarrow>
    let issued=List.map_filter (\<lambda>p. if development_issuable D L answered p then
          Option.bind (request_of p) (\<lambda>r. if fst r=p then Some r else None) else None) xs in
    ((S,ps,D,answered,history@map (\<lambda>r. Development_Issue_Record r (development_library_reading L (fst r))) issued),
     issued,filter (\<lambda>p. p\<notin>fst ` set issued) xs))"

theorem development_loop_issue_leaf:
  assumes issue: "development_loop_issue L request_of (S,ps,D,answered,history) xs=(loop',issued,unissued)"
    and member: "r\<in>set issued"
  shows "fst r\<in>set xs" "development_issuable D L answered (fst r)" "development_library_reading L (fst r)={||}"
    "request_of (fst r)=Some r"
proof -
  obtain p where p: "p\<in>set xs" and built: "(if development_issuable D L answered p then
      Option.bind (request_of p) (\<lambda>r. if fst r=p then Some r else None) else None)=Some r"
    using issue member by (auto simp: development_loop_issue_def Let_def map_filter_member)
  have issuable: "development_issuable D L answered p" using built by (simp split: if_splits)
  obtain r' where requested: "request_of p=Some r'" and same: "fst r'=p" and equal: "r'=r"
    using built issuable by (auto simp: bind_eq_Some_conv split: if_splits)
  show "fst r\<in>set xs" using p same equal by simp
  show "development_issuable D L answered (fst r)" using issuable same equal by simp
  show "development_library_reading L (fst r)={||}"
    using issuable same equal by (simp add: development_issuable_def development_leaf_reading)
  show "request_of (fst r)=Some r" using requested same equal by simp
qed

text \<open>
  A refused answer whose repair is accepted moves the development through the extended request:
  the extension becomes the state, the definition problems of the introduced constants join the
  problems as answered leaves, since the answer's own definitions answer them and the extension
  verdict judged those definitions, the repair joins the history, and the same answer is then
  admitted against the request issued again.
\<close>

definition development_repaired_successor ::
    "development_loop \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> nat list \<Rightarrow> development_loop option" where
  "development_repaired_successor L r S' I=(case L of (S,ps,D,answered,history) \<Rightarrow>
    let R=development_refinement_repair S r S' I in
    case R of (extension,definitions,r',v',accepted') \<Rightarrow>
      if development_extension_accepted extension \<and> accepted' then
        development_successor (development_repair_state S r S' I,
          ps@definitions,D |\<union>| fset_of_list (map (\<lambda>q. (q,{||})) definitions),
          answered |\<union>| fset_of_list definitions,history@[Development_Repair_Record r R]) r' S'
      else None)"

theorem development_repaired_successor_records:
  assumes successor: "development_repaired_successor (S,ps,D,answered,history) r S' I=Some L'"
  obtains extension definitions r' v' where
    "development_refinement_repair S r S' I=(extension,definitions,r',v',True)"
    "development_extension_accepted extension"
    "\<exists>G S2 ps' D' answered'. L'=(S2,ps',D',answered',history@[Development_Repair_Record r
      (extension,definitions,r',v',True),Development_Answer_Record G])"
proof -
  obtain extension definitions r' v' a where repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
    by (cases "development_refinement_repair S r S' I") auto
  have fields: "development_extension_accepted extension" "a"
    using successor by (auto simp: development_repaired_successor_def repair Let_def split: if_splits)
  let ?E="development_repair_state S r S' I"
  have moved: "development_successor (?E,ps@definitions,D |\<union>| fset_of_list (map (\<lambda>q. (q,{||})) definitions),
      answered |\<union>| fset_of_list definitions,history@[Development_Repair_Record r (extension,definitions,r',v',a)]) r' S'=Some L'"
    using successor fields by (simp add: development_repaired_successor_def repair Let_def)
  obtain S2 ps' D' answered' history' where L': "L'=(S2,ps',D',answered',history')" by (cases L') auto
  obtain G where "history'=(history@[Development_Repair_Record r (extension,definitions,r',v',a)])@[Development_Answer_Record G]"
    using development_successor_answered(3)[OF moved[unfolded L']] by blast
  then have final: "\<exists>G S2 ps' D' answered'. L'=(S2,ps',D',answered',history@[Development_Repair_Record r
      (extension,definitions,r',v',True),Development_Answer_Record G])"
    using L' fields(2) by (intro exI[of _ G] exI[of _ S2] exI[of _ ps'] exI[of _ D'] exI[of _ answered']) simp
  have repaired: "development_refinement_repair S r S' I=(extension,definitions,r',v',True)"
    using repair fields(2) by simp
  show thesis by (rule that[OF repaired fields(1) final])
qed

text \<open>
  A request issued against the old state stays current exactly when every entity of its
  context persists in the new one; otherwise its answer would be judged against a context the
  development no longer has, and the request is a re-evaluation problem instead of current work.
\<close>

definition development_request_current :: "isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> development_request \<Rightarrow> bool" where
  "development_request_current C C' r=(case r of (p,s,support,E) \<Rightarrow>
    fBall E (\<lambda>e. isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) e\<in>set (snd C')))"

theorem development_request_current_exact:
  assumes inside: "fset E\<subseteq>set (snd C)"
  shows "development_request_current C C' (p,s,support,E) \<longleftrightarrow> fset E\<inter>set (isabelle_state_removed C C')={}"
proof
  assume "development_request_current C C' (p,s,support,E)"
  then show "fset E\<inter>set (isabelle_state_removed C C')={}"
    by (auto simp: development_request_current_def isabelle_state_removed_exact)
next
  assume disjoint: "fset E\<inter>set (isabelle_state_removed C C')={}"
  show "development_request_current C C' (p,s,support,E)"
  proof (unfold development_request_current_def prod.case, rule fBallI)
    fix e assume member: "e |\<in>| E"
    have "e\<in>set (snd C)" using inside member by auto
    moreover have "e\<notin>set (isabelle_state_removed C C')" using disjoint member by auto
    ultimately show "isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) e\<in>set (snd C')"
      by (simp add: isabelle_state_removed_exact)
  qed
qed

section \<open>A library extension reaches exactly the issues that relied on its absence\<close>

text \<open>
  An issued request rests on the absence of any library rule for its problem, and its record
  retains that reading. Against a changed library the records whose reading no longer holds are
  computed from the history, and their requests are re-evaluations for the process; an issue whose
  reading still holds is reused unchanged. Nothing is re-issued by this computation, and no other
  record is touched.
\<close>

definition development_reevaluations :: "development_dependencies \<Rightarrow> development_record list \<Rightarrow> development_request list" where
  "development_reevaluations L history=List.map_filter (\<lambda>entry. case entry of
     Development_Issue_Record q reading \<Rightarrow> if development_library_reading L (fst q)=reading then None else Some q
   | _ \<Rightarrow> None) history"

theorem development_reevaluations_exact:
  "q\<in>set (development_reevaluations L history) \<longleftrightarrow>
    (\<exists>reading. Development_Issue_Record q reading\<in>set history \<and> development_library_reading L (fst q)\<noteq>reading)"
proof
  assume "q\<in>set (development_reevaluations L history)"
  then obtain entry where member: "entry\<in>set history" and read: "(case entry of
      Development_Issue_Record q' reading \<Rightarrow> if development_library_reading L (fst q')=reading then None else Some q'
    | _ \<Rightarrow> None)=Some q"
    by (auto simp: development_reevaluations_def map_filter_member)
  show "\<exists>reading. Development_Issue_Record q reading\<in>set history \<and> development_library_reading L (fst q)\<noteq>reading"
  proof (cases entry)
    case (Development_Issue_Record q' reading)
    then have same: "q'=q" and changed: "development_library_reading L (fst q')\<noteq>reading"
      using read by (simp_all split: if_splits)
    show ?thesis using member Development_Issue_Record same changed by blast
  qed (use read in simp_all)
next
  assume "\<exists>reading. Development_Issue_Record q reading\<in>set history \<and> development_library_reading L (fst q)\<noteq>reading"
  then obtain reading where member: "Development_Issue_Record q reading\<in>set history"
    and changed: "development_library_reading L (fst q)\<noteq>reading" by blast
  show "q\<in>set (development_reevaluations L history)"
    unfolding development_reevaluations_def map_filter_member
    by (rule bexI[OF _ member]) (simp add: changed)
qed

theorem development_reevaluations_local:
  assumes issued: "\<And>q reading. Development_Issue_Record q reading\<in>set history \<Longrightarrow>
      development_library_reading L (fst q)=reading"
    and extension: "\<And>p H. (p,H) |\<in>| L' \<Longrightarrow> (p,H) |\<notin>| L \<Longrightarrow>
      (\<nexists>q reading. Development_Issue_Record q reading\<in>set history \<and> fst q=p)"
    and kept: "L |\<subseteq>| L'"
  shows "development_reevaluations L' history=[]"
proof -
  have same: "development_library_reading L' (fst q)=reading" if member: "Development_Issue_Record q reading\<in>set history" for q reading
  proof -
    have "development_decompositions L' (fst q)=development_decompositions L (fst q)"
    proof (rule fset_eqI)
      fix H
      show "H |\<in>| development_decompositions L' (fst q) \<longleftrightarrow> H |\<in>| development_decompositions L (fst q)"
      proof
        assume "H |\<in>| development_decompositions L' (fst q)"
        then have row: "(fst q,H) |\<in>| L'" by (auto simp: development_decompositions_def)
        have "(fst q,H) |\<in>| L" using extension[OF row] member by blast
        then show "H |\<in>| development_decompositions L (fst q)" by (force simp: development_decompositions_def)
      next
        assume "H |\<in>| development_decompositions L (fst q)"
        then have "(fst q,H) |\<in>| L" by (auto simp: development_decompositions_def)
        then have "(fst q,H) |\<in>| L'" using kept by blast
        then show "H |\<in>| development_decompositions L' (fst q)" by (force simp: development_decompositions_def)
      qed
    qed
    then show ?thesis using issued[OF member] by (simp add: development_library_reading_def)
  qed
  show ?thesis
  proof (rule ccontr)
    assume "development_reevaluations L' history\<noteq>[]"
    then obtain q where "q\<in>set (development_reevaluations L' history)" by (cases "development_reevaluations L' history") auto
    then obtain reading where member: "Development_Issue_Record q reading\<in>set history"
      and changed: "development_library_reading L' (fst q)\<noteq>reading"
      by (simp only: development_reevaluations_exact) blast
    then show False using same[OF member] by simp
  qed
qed

section \<open>Answers to independent requests leave each other current\<close>

text \<open>
  The admitted problems of a selection form one group of independent work, and their requests
  are answered concurrently. An admitted answer to one of them leaves every request for another
  subject current: the entities of that subject persist by the verdict's contract, because an
  answer may replace only its own subject's code equations, and the declarations of its support
  persist because the answer state is closed and every constant the persisting entities mention
  keeps its one declaration. The answers can therefore be admitted in any order, each against a
  request that is still current; the premise is that the request state declares every constant
  once (@{const isabelle_declared_once}, the exporter's obligation), which the state's own entities
  decide.
\<close>

theorem development_admitted_keeps_independent_current:
  assumes accepted: "development_verdict_accepted (development_refinement_verdict S (p,s,support,E) S')"
    and subject: "problem_subject p={|c|}" and other: "d\<noteq>c"
    and once: "isabelle_declared_once (snd S)"
  shows "development_request_current (snd S) (snd S') (q,t,development_request_support (snd S) d,
    development_request_context (snd S) d)"
proof -
  let ?C="snd S" and ?C'="snd S'"
  let ?f="isabelle_state_embedding (fst ?C) (fst ?C')"
  note contract=development_refinement_verdict_contract[OF accepted]
  have scoped: "isabelle_entity_rename ?f x\<in>set (snd ?C')"
    if member: "x\<in>set (development_constant_scope ?C d)" for x
  proof -
    have state: "x\<in>set (snd ?C)" and subjects: "d\<in>set (isabelle_entity_subjects (fst ?C) (isabelle_development_constants (snd ?C)) x)"
      using member by (simp_all add: development_constant_scope_member)
    have undeclared: "isabelle_declared_constant x=None" using subjects by (cases x) auto
    have "\<not>development_answer_equation ?C (problem_subject p) x"
    proof
      assume "development_answer_equation ?C (problem_subject p) x"
      then obtain e where equation: "isabelle_code_equation_proposition x=Some e"
        and hit: "list_ex (\<lambda>c'. c' |\<in>| problem_subject p) (isabelle_entity_subjects (fst ?C) (isabelle_development_constants (snd ?C)) x)"
        by (auto simp: development_answer_equation_exact)
      have code: "x=Isabelle_Code_Equation e" using equation by (simp only: isabelle_code_equation_proposition_exact)
      have "set (isabelle_entity_subjects (fst ?C) (isabelle_development_constants (snd ?C)) x)\<subseteq>{d}"
      proof (cases "Option.bind (isabelle_equation_left (fst ?C) e) isabelle_head_constant")
        case None
        then show ?thesis using subjects by (simp add: code)
      next
        case (Some h)
        then show ?thesis using subjects by (simp add: code)
      qed
      then show False using hit other by (auto simp: subject list_ex_iff)
    qed
    then show ?thesis using contract(1)[OF state _ undeclared] by blast
  qed
  show ?thesis
  proof (unfold development_request_current_def prod.case, rule fBallI)
    fix e assume member: "e |\<in>| development_request_context ?C d"
    have state: "e\<in>set (snd ?C)" and origin: "e\<in>set (development_constant_scope ?C d) \<or>
        (\<exists>d'. isabelle_declared_constant e=Some d' \<and> d' |\<in>| development_request_support ?C d)"
      using member by (simp_all only: development_request_context_exact)
    show "isabelle_entity_rename ?f e\<in>set (snd ?C')"
    proof (cases "e\<in>set (development_constant_scope ?C d)")
      case True
      then show ?thesis by (rule scoped)
    next
      case False
      then obtain d' where declares: "isabelle_declared_constant e=Some d'"
        and supported: "d' |\<in>| development_request_support ?C d" using origin by blast
      obtain x q where x: "x\<in>set (development_constant_scope ?C d)" and statement: "isabelle_specified_proposition x=Some q"
        and mentions: "d'\<in>set (isabelle_term_constants q)"
        using supported by (auto simp: development_request_support_member)
      have persisting: "isabelle_entity_rename ?f x\<in>set (snd ?C')" by (rule scoped[OF x])
      have "?f d'\<in>set (isabelle_mentioned_constants (fst S') ?C')"
        using persisting statement mentions
        by (auto simp: isabelle_mentioned_constants_def isabelle_entity_rename_specified isabelle_term_rename_constants
          intro!: bexI[of _ "isabelle_entity_rename ?f x"])
      moreover have "?f d'\<notin>set (isabelle_undeclared_constants (fst S') ?C')"
      proof
        assume inside: "?f d'\<in>set (isabelle_undeclared_constants (fst S') ?C')"
        have "fset_of_list (isabelle_undeclared_constants (fst S') ?C')={||}"
          using contract(5) by (simp add: isabelle_assessment_closed_def isabelle_context_assessment_def)
        then have "set (isabelle_undeclared_constants (fst S') ?C')={}"
          using arg_cong[where f=fset] by (fastforce simp: fset_of_list.rep_eq)
        then show False using inside by simp
      qed
      ultimately have "?f d'\<in>set (List.map_filter isabelle_declared_constant (snd ?C'))"
        by (simp add: isabelle_undeclared_constants_exact)
      then obtain y where y: "y\<in>set (snd ?C')" and names: "isabelle_declared_constant y=Some (?f d')"
        by (auto simp: map_filter_member)
      have "(\<exists>e0\<in>set (snd ?C). y=isabelle_entity_rename ?f e0) \<or>
          development_answer_equation ?C' (fimage ?f (problem_subject p)) y"
        using contract(2)[OF y] by simp
      moreover have "\<not>development_answer_equation ?C' (fimage ?f (problem_subject p)) y"
        using names by (cases y) (auto simp: development_answer_equation_exact)
      ultimately obtain e0 where e0: "e0\<in>set (snd ?C)" and image: "y=isabelle_entity_rename ?f e0" by blast
      have "map_option ?f (isabelle_declared_constant e0)=Some (?f d')"
        using names by (simp add: image isabelle_entity_rename_declared)
      then obtain d'' where declares0: "isabelle_declared_constant e0=Some d''" and moved: "?f d''=?f d'"
        by (auto simp: map_option_eq_Some)
      have "d''=d'" using moved contract(7) by (simp add: inj_eq)
      then have "e0=e" using once[unfolded isabelle_declared_once_def] e0 state declares0 declares by blast
      then show ?thesis using y image by simp
    qed
  qed
qed

section \<open>The development state is presented injectively\<close>

definition development_dependencies_data :: "development_dependencies \<Rightarrow> finite_factor_term" where
  "development_dependencies_data=finite_collection_presentation (finite_pair_presentation development_problem_data
    (finite_collection_presentation (finite_pair_presentation isabelle_position_data development_problem_data)))"

lemma development_dependencies_data_injective [intro]: "inj development_dependencies_data"
  unfolding development_dependencies_data_def
  by (intro finite_collection_presentation_injective finite_pair_presentation_injective
    development_problem_data_injective isabelle_position_data_injective)

definition development_generation_data :: "development_generation \<Rightarrow> finite_factor_term" where
  "development_generation_data=finite_pair_presentation development_problem_data
    (finite_pair_presentation isabelle_entities_data
      (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data) development_verdict_data))"

lemma development_generation_data_injective [intro]: "inj development_generation_data"
  unfolding development_generation_data_def
  by (intro finite_pair_presentation_injective development_problem_data_injective
    isabelle_collections_injective finite_sequence_presentation_injective isabelle_entity_data_injective
    development_verdict_data_injective)

text \<open>
  A record is presented through a presentation of the executed packet it may carry, supplied by
  the use: it is read as the one of its three parts it has, and presented by the existing option
  and pair presentations, so it is injective whenever the packet's presentation is.
\<close>

definition development_record_parts :: "development_record \<Rightarrow>
    (development_packet\<times>development_problem list) option\<times>
      (development_request\<times>(nat\<times>development_problem) fset fset) option\<times>development_generation option\<times>
      (development_request\<times>development_refinement_repair) option" where
  "development_record_parts r=(case r of
     Development_Selection_Record q ps \<Rightarrow> (Some (q,ps),None,None,None)
   | Development_Issue_Record r' reading \<Rightarrow> (None,Some (r',reading),None,None)
   | Development_Answer_Record G \<Rightarrow> (None,None,Some G,None)
   | Development_Repair_Record r' R \<Rightarrow> (None,None,None,Some (r',R)))"

lemma development_record_parts_injective: "inj development_record_parts"
proof (rule injI)
  fix x y assume "development_record_parts x=development_record_parts y"
  then show "x=y" by (cases x; cases y) (simp_all add: development_record_parts_def)
qed

definition development_record_data :: "(development_packet \<Rightarrow> finite_factor_term) \<Rightarrow> development_record \<Rightarrow> finite_factor_term" where
  "development_record_data packet=finite_pair_presentation
    (finite_option_presentation (finite_pair_presentation packet development_problems_data))
    (finite_pair_presentation (finite_option_presentation (finite_pair_presentation development_request_data
        (finite_collection_presentation (finite_collection_presentation
          (finite_pair_presentation isabelle_position_data development_problem_data)))))
      (finite_pair_presentation (finite_option_presentation development_generation_data)
        (finite_option_presentation (finite_pair_presentation development_request_data development_refinement_repair_data))))
    \<circ> development_record_parts"

lemma development_record_data_injective:
  assumes packet: "inj packet"
  shows "inj (development_record_data packet)"
  unfolding development_record_data_def
  by (intro inj_compose[OF _ development_record_parts_injective] finite_pair_presentation_injective
    finite_option_presentation_injective packet development_problems_data_injective finite_collection_presentation_injective
    isabelle_position_data_injective development_problem_data_injective
    development_generation_data_injective development_request_data_injective development_refinement_repair_data_injective)

definition development_loop_data :: "(development_packet \<Rightarrow> finite_factor_term) \<Rightarrow> development_loop \<Rightarrow> finite_factor_term" where
  "development_loop_data packet=finite_pair_presentation isabelle_rooted_context_data
    (finite_pair_presentation development_problems_data
      (finite_pair_presentation development_dependencies_data
        (finite_pair_presentation (finite_collection_presentation development_problem_data)
          (finite_sequence_presentation (development_record_data packet)))))"

lemma development_loop_data_injective:
  assumes packet: "inj packet"
  shows "inj (development_loop_data packet)"
  unfolding development_loop_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective isabelle_rooted_context_data_injective
    development_problems_data_injective development_dependencies_data_injective
    finite_collection_presentation_injective development_problem_data_injective
    development_record_data_injective[OF packet])

end
