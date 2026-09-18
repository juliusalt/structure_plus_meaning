theory Development_Publication
  imports Development_Successor RRA_Finite_Transactions Factor_Finite_Data_Syntax Finite_Presented_Structures
begin

section \<open>A presented value carries the names it uses\<close>

text \<open>
  A generation is read beside states whose name tables differ, so its locus and payload carry
  the names they use: every position a value mentions is replaced by the position of its name
  in the list of the names the value mentions, in the order they first occur, through the
  existing embedding of one table into another. The presentation then depends on the value's
  structure and its names and on no other position of the table; a correspondence of tables
  leaves it unchanged.
\<close>

definition isabelle_local_names :: "String.literal list \<Rightarrow> nat list \<Rightarrow> String.literal list" where
  "isabelle_local_names names ps=remdups (List.map_filter (isabelle_name_at names) ps)"

definition isabelle_local_embedding :: "String.literal list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_local_embedding names ps=isabelle_state_embedding names (isabelle_local_names names ps)"

lemma isabelle_type_rename_compose:
  "isabelle_type_rename g (isabelle_type_rename f T)=isabelle_type_rename (g \<circ> f) T"
  by (induction T) auto

lemma isabelle_term_rename_compose:
  "isabelle_term_rename g (isabelle_term_rename f t)=isabelle_term_rename (g \<circ> f) t"
  by (induction t) (simp_all add: isabelle_type_rename_compose comp_def)

lemma isabelle_type_rename_cong:
  "\<forall>i\<in>set (isabelle_type_positions T). f i=g i \<Longrightarrow> isabelle_type_rename f T=isabelle_type_rename g T"
  by (induction T) auto

lemma isabelle_term_rename_cong:
  "\<forall>i\<in>set (isabelle_term_positions t). f i=g i \<Longrightarrow> isabelle_term_rename f t=isabelle_term_rename g t"
  by (induction t) (auto intro: isabelle_type_rename_cong)

lemma isabelle_entity_rename_compose:
  "isabelle_entity_rename g (isabelle_entity_rename f e)=isabelle_entity_rename (g \<circ> f) e"
  by (cases e) (simp_all add: isabelle_term_rename_compose)

lemma isabelle_entity_rename_cong:
  "\<forall>i\<in>set (isabelle_entity_positions e). f i=g i \<Longrightarrow> isabelle_entity_rename f e=isabelle_entity_rename g e"
  by (cases e) (auto simp: isabelle_entity_positions_def intro: isabelle_term_rename_cong)

lemma isabelle_local_names_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
  shows "List.map_filter (isabelle_name_at names') (map f ps)=List.map_filter (isabelle_name_at names) ps"
  by (induction ps) (simp_all add: isabelle_table_correspondence_name[OF corr] split: option.split)

lemma isabelle_local_embedding_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and member: "i\<in>set ps" and inside: "i<length names"
  shows "isabelle_local_embedding names' (map f ps) (f i)=isabelle_local_embedding names ps i"
proof -
  let ?L="isabelle_local_names names ps"
  have local: "isabelle_local_names names' (map f ps)=?L"
    by (simp add: isabelle_local_names_def isabelle_local_names_renamed[OF corr])
  have named: "isabelle_name_at names i=Some (names!i)"
    using inside by (simp add: isabelle_name_at_def)
  have "names!i\<in>set (List.map_filter (isabelle_name_at names) ps)"
    using member named by (auto simp: map_filter_member)
  then have used: "names!i\<in>set ?L" by (simp add: isabelle_local_names_def)
  obtain j where found: "isabelle_name_position ?L (names!i)=Some j"
    using used isabelle_name_position_none[of ?L "names!i"] by (cases "isabelle_name_position ?L (names!i)") auto
  have moved: "isabelle_name_at names' (f i)=Some (names!i)"
    using named by (simp add: isabelle_table_correspondence_name[OF corr])
  show ?thesis
    by (simp add: isabelle_local_embedding_def local isabelle_state_embedding_def named moved found)
qed

section \<open>A contract presented with its names locates its problem\<close>

fun development_contract_term :: "development_contract \<Rightarrow> isabelle_term" where
  "development_contract_term (Development_Refinement t)=t"
| "development_contract_term (Development_Proof t)=t"
| "development_contract_term (Development_Presentation t)=t"
| "development_contract_term (Development_Definition t)=t"
| "development_contract_term (Development_Amendment t)=t"

lemma development_contract_term_rename:
  "development_contract_term (development_contract_rename f k)=isabelle_term_rename f (development_contract_term k)"
  by (cases k) simp_all

lemma development_contract_rename_compose:
  "development_contract_rename g (development_contract_rename f k)=development_contract_rename (g \<circ> f) k"
  by (cases k) (simp_all add: isabelle_term_rename_compose)

lemma development_contract_rename_cong:
  "\<forall>i\<in>set (isabelle_term_positions (development_contract_term k)). f i=g i \<Longrightarrow>
    development_contract_rename f k=development_contract_rename g k"
  by (cases k) (auto intro: isabelle_term_rename_cong)

definition development_local_contract ::
    "String.literal list \<Rightarrow> development_contract \<Rightarrow> String.literal list\<times>development_contract" where
  "development_local_contract names k=(let ps=isabelle_term_positions (development_contract_term k) in
    (isabelle_local_names names ps,development_contract_rename (isabelle_local_embedding names ps) k))"

theorem development_local_contract_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and inside: "\<forall>i\<in>set (isabelle_term_positions (development_contract_term k)). i<length names"
  shows "development_local_contract names' (development_contract_rename f k)=development_local_contract names k"
proof -
  let ?ps="isabelle_term_positions (development_contract_term k)"
  have positions: "isabelle_term_positions (development_contract_term (development_contract_rename f k))=map f ?ps"
    by (simp add: development_contract_term_rename isabelle_term_rename_positions)
  have names: "isabelle_local_names names' (map f ?ps)=isabelle_local_names names ?ps"
    by (simp add: isabelle_local_names_def isabelle_local_names_renamed[OF corr])
  have agree: "\<forall>i\<in>set ?ps. (isabelle_local_embedding names' (map f ?ps) \<circ> f) i=isabelle_local_embedding names ?ps i"
    using inside by (simp add: isabelle_local_embedding_renamed[OF corr])
  have renamed: "development_contract_rename (isabelle_local_embedding names' (map f ?ps)) (development_contract_rename f k)=
      development_contract_rename (isabelle_local_embedding names ?ps) k"
    by (simp only: development_contract_rename_compose development_contract_rename_cong[OF agree])
  show ?thesis
    by (simp only: development_local_contract_def Let_def positions names renamed)
qed

definition isabelle_local_entities :: "String.literal list \<Rightarrow> isabelle_entity list \<Rightarrow> isabelle_context" where
  "isabelle_local_entities names es=(let ps=concat (map isabelle_entity_positions es) in
    (isabelle_local_names names ps,map (isabelle_entity_rename (isabelle_local_embedding names ps)) es))"

theorem isabelle_local_entities_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and inside: "\<forall>e\<in>set es. \<forall>i\<in>set (isabelle_entity_positions e). i<length names"
  shows "isabelle_local_entities names' (map (isabelle_entity_rename f) es)=isabelle_local_entities names es"
proof -
  let ?ps="concat (map isabelle_entity_positions es)"
  have positions: "concat (map isabelle_entity_positions (map (isabelle_entity_rename f) es))=map f ?ps"
    by (induction es) (simp_all add: isabelle_entity_rename_positions)
  have names: "isabelle_local_names names' (map f ?ps)=isabelle_local_names names ?ps"
    by (simp add: isabelle_local_names_def isabelle_local_names_renamed[OF corr])
  have entity: "isabelle_entity_rename (isabelle_local_embedding names' (map f ?ps)) (isabelle_entity_rename f e)=
      isabelle_entity_rename (isabelle_local_embedding names ?ps) e" if member: "e\<in>set es" for e
  proof -
    have agree: "\<forall>i\<in>set (isabelle_entity_positions e).
        (isabelle_local_embedding names' (map f ?ps) \<circ> f) i=isabelle_local_embedding names ?ps i"
    proof
      fix i assume position: "i\<in>set (isabelle_entity_positions e)"
      have "i\<in>set ?ps" using member position by auto
      moreover have "i<length names" using member position inside by auto
      ultimately show "(isabelle_local_embedding names' (map f ?ps) \<circ> f) i=isabelle_local_embedding names ?ps i"
        by (simp add: isabelle_local_embedding_renamed[OF corr])
    qed
    show ?thesis
      by (simp only: isabelle_entity_rename_compose isabelle_entity_rename_cong[OF agree])
  qed
  show ?thesis
    unfolding isabelle_local_entities_def Let_def positions names
    by (simp add: entity)
qed

text \<open>
  The locus of a problem is its contract presented with its names: a refinement's contract is
  its constant as the state declares it, so every problem posed about that constant, whatever
  its origin or authority, stands at one locus, and at most one answer to it is selected.
  Subject positions, origin and authority are not part of the locus. A correspondence of tables
  leaves the locus unchanged, so it is read identically from every state that holds the names.
\<close>

definition development_problem_locus :: "String.literal list \<Rightarrow> development_problem \<Rightarrow> finite_factor_term" where
  "development_problem_locus names p=finite_pair_presentation isabelle_names_data development_contract_data
    (development_local_contract names (problem_contract p))"

section \<open>Generations of the development are generations of the library\<close>

text \<open>
  A presented value becomes an exact target as the whole artifact of its complete data
  quotation. A generation of the development is then an ordinary finite generation: its locus,
  payload and cause are such targets and its predecessors are generations. Formation of these
  values establishes nothing about the validity of a cause.
\<close>

definition development_data_target :: "finite_factor_term \<Rightarrow> finite_exact_target option" where
  "development_data_target t=map_option Finite_Whole (finite_data_syntax (decode_finite_term t))"

definition development_generation_value ::
    "finite_factor_term \<Rightarrow> finite_generation fset \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow>
      finite_generation option" where
  "development_generation_value l P p c=(case development_data_target l of None \<Rightarrow> None
     | Some l' \<Rightarrow> (case development_data_target p of None \<Rightarrow> None
       | Some p' \<Rightarrow> map_option (\<lambda>c'. Generation l' P p' c') (development_data_target c)))"

lemma development_generation_value_fields:
  assumes "development_generation_value l P p c=Some G"
  shows "development_data_target l=Some (generation_locus G)" "generation_predecessors G=P"
    "development_data_target p=Some (generation_payload G)" "development_data_target c=Some (generation_cause G)"
  using assms by (auto simp: development_generation_value_def split: option.splits)

text \<open>
  The incumbent of a problem is the family of code equations the checked context states for its
  subject. It is a base generation: its locus is the problem's, its payload is that family
  presented with its names, its cause is the acceptance of the family by the checked context,
  and it has no predecessor, because the checked build established it before the process.
\<close>

definition development_incumbent_generation :: "isabelle_rooted_context \<Rightarrow> development_problem \<Rightarrow> finite_generation option" where
  "development_incumbent_generation S p=(let C=snd S; es=development_answer_equations C (problem_subject p) in
    development_generation_value (development_problem_locus (fst C) p) {||}
      (isabelle_context_data (isabelle_local_entities (fst C) es))
      (isabelle_acceptance_assessment_data (isabelle_demand_acceptance (snd C) es)))"

definition development_incumbent_snapshot :: "isabelle_rooted_context \<Rightarrow> development_problem list \<Rightarrow> finite_snapshot option" where
  "development_incumbent_snapshot S ps=map_option fset_of_list (those (map (development_incumbent_generation S) ps))"

text \<open>
  An admitted answer is published as a generation at its problem's locus: its payload is the
  subject's equations in the answer state presented with their names, its cause is the verdict
  that accepted it, and its predecessor is the incumbent it was judged against, whose equations
  the request's context holds. The admitted answer itself is recorded in the history whether or
  not it is ever published.
\<close>

definition development_answer_publication ::
    "isabelle_rooted_context \<Rightarrow> development_request \<Rightarrow> isabelle_rooted_context \<Rightarrow> finite_generation option \<Rightarrow>
      finite_generation option" where
  "development_answer_publication S r S' incumbent=(case development_answer_generation S r S' of
     None \<Rightarrow> None
   | Some (p,E,payload,v) \<Rightarrow> development_generation_value (development_problem_locus (fst (snd S)) p)
       (case incumbent of None \<Rightarrow> {||} | Some G \<Rightarrow> {|G|})
       (isabelle_context_data (isabelle_local_entities (fst (snd S')) payload))
       (development_refinement_verdict_data v))"

lemma development_answer_publication_locus:
  assumes published: "development_answer_publication S r S' incumbent=Some G"
  shows "development_data_target (development_problem_locus (fst (snd S)) (fst r))=Some (generation_locus G)"
proof -
  obtain p E payload v where generation: "development_answer_generation S r S'=Some (p,E,payload,v)"
    using published by (auto simp: development_answer_publication_def split: option.splits)
  have problem: "p=fst r"
    using generation by (auto simp: development_answer_generation_def Let_def split: prod.splits if_splits)
  have presented: "development_generation_value (development_problem_locus (fst (snd S)) p)
      (case incumbent of None \<Rightarrow> {||} | Some G \<Rightarrow> {|G|})
      (isabelle_context_data (isabelle_local_entities (fst (snd S')) payload))
      (development_refinement_verdict_data v)=Some G"
    using published generation by (simp add: development_answer_publication_def)
  show ?thesis using development_generation_value_fields(1)[OF presented] problem by simp
qed

section \<open>Publication is a transaction against the published state\<close>

text \<open>
  Publishing a generation executes the transaction that expects, at its locus, exactly what the
  publisher read there. When the published state still holds that incumbent, the generation
  replaces it and every other locus keeps its selection; when the locus has moved, the result is
  the complete observed comparison and no successor. Both follow from the structural replacement
  through the exactness of the executed transaction; nothing is proved again here.
\<close>

theorem development_publication_applied:
  assumes published: "finite_snapshot_formed S"
    and incumbent: "finite_snapshot_lookup S (generation_locus G)=Some I"
    and formed: "finite_generation_formed G"
  obtains U where "finite_transact S (finite_locus_transaction (Some I) G)=Some (Finite_Applied U)"
    "finite_snapshot_formed U" "finite_snapshot_lookup U (generation_locus G)=Some G"
    "\<And>l. l\<noteq>generation_locus G \<Longrightarrow> finite_snapshot_lookup U l=finite_snapshot_lookup S l"
proof -
  have member: "I\<in>fset S" "generation_locus I=generation_locus G"
    using incumbent by (simp_all add: finite_snapshot_lookup_formed[OF published])
  have decoded: "snapshot_formed (decode_finite_snapshot S)"
    using published by (simp only: finite_snapshot_formed_correct)
  have selected: "snapshot_lookup (decode_finite_snapshot S) (generation_locus (decode_finite_generation I))=
      Some (decode_finite_generation I)"
    by (simp add: decode_finite_generation_selectors finite_snapshot_lookup_exact[OF published] member(2) incumbent)
  have new: "generation_formed (decode_finite_generation G)"
    using formed by (simp only: finite_generation_formed_correct)
  have locus: "generation_locus (decode_finite_generation G)=generation_locus (decode_finite_generation I)"
    by (simp add: decode_finite_generation_selectors member(2))
  let ?T="finite_locus_transaction (Some I) G"
  have "transact (decode_finite_snapshot S) (decode_finite_transaction ?T)
      (Applied (replace_snapshot (decode_finite_snapshot S) {|decode_finite_generation G|} {||}))"
    using selected_generation_replacement[OF decoded selected new locus]
    by (simp add: decode_finite_locus_transaction)
  then obtain r where executed: "finite_transact S ?T=Some r"
    and result: "Applied (replace_snapshot (decode_finite_snapshot S) {|decode_finite_generation G|} {||})=
      decode_finite_transaction_result r"
    by (auto simp: finite_transact_exact)
  obtain U where applied: "r=Finite_Applied U"
    using result by (cases r) auto
  have transition: "transact (decode_finite_snapshot S) (decode_finite_transaction ?T) (Applied (decode_finite_snapshot U))"
    by (simp add: finite_transact_exact executed applied)
  have successor: "finite_snapshot_formed U"
    using successful_transaction_formed[OF transition] by (simp only: finite_snapshot_formed_correct)
  have replaced: "transact (decode_finite_snapshot S)
      (replacement_transaction (decode_finite_generation I) (decode_finite_generation G)) (Applied (decode_finite_snapshot U))"
    using transition by (simp add: decode_finite_locus_transaction)
  have at: "finite_snapshot_lookup U (generation_locus G)=Some G"
  proof -
    have "snapshot_lookup (decode_finite_snapshot U) (decode_finite_target (generation_locus G))=
        Some (decode_finite_generation G)"
      using replacement_result(1)[OF replaced] by (simp add: decode_finite_generation_selectors)
    then show ?thesis
      by (simp add: finite_snapshot_lookup_exact[OF successor] map_option_eq_Some)
  qed
  have others: "finite_snapshot_lookup U l=finite_snapshot_lookup S l" if other: "l\<noteq>generation_locus G" for l
  proof -
    have "decode_finite_target l\<noteq>generation_locus (decode_finite_generation G)"
      using other by (simp add: decode_finite_generation_selectors)
    then have "snapshot_lookup (decode_finite_snapshot U) (decode_finite_target l)=
        snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)"
      by (rule replacement_result(2)[OF replaced])
    then show ?thesis
      by (simp add: finite_snapshot_lookup_exact[OF successor] finite_snapshot_lookup_exact[OF published]
        map_option_decode_finite_generation_eq)
  qed
  have "finite_transact S ?T=Some (Finite_Applied U)" using executed applied by simp
  then show ?thesis by (rule that[OF _ successor at others])
qed

theorem development_publication_conflict:
  assumes published: "finite_snapshot_formed S"
    and moved: "finite_snapshot_lookup S (generation_locus G)\<noteq>Some I"
    and formed: "finite_generation_formed I" "finite_generation_formed G"
    and locus: "generation_locus G=generation_locus I"
  shows "finite_transact S (finite_locus_transaction (Some I) G)=
    Some (Finite_Conflict (finite_observed_comparison S (finite_locus_transaction (Some I) G)))"
proof -
  let ?T="finite_locus_transaction (Some I) G"
  have decoded: "snapshot_formed (decode_finite_snapshot S)"
    using published by (simp only: finite_snapshot_formed_correct)
  have old: "generation_formed (decode_finite_generation I)" and new: "generation_formed (decode_finite_generation G)"
    using formed by (simp_all only: finite_generation_formed_correct)
  have same: "generation_locus (decode_finite_generation G)=generation_locus (decode_finite_generation I)"
    by (simp add: decode_finite_generation_selectors locus)
  have different: "snapshot_lookup (decode_finite_snapshot S) (generation_locus (decode_finite_generation I))\<noteq>
      Some (decode_finite_generation I)"
    using moved by (simp add: decode_finite_generation_selectors finite_snapshot_lookup_exact[OF published]
      locus map_option_eq_Some)
  have "transact (decode_finite_snapshot S) (decode_finite_transaction ?T)
      (Conflict (observed_comparison (decode_finite_snapshot S) (decode_finite_transaction ?T)))"
    using replacement_expectation_conflict[OF decoded old new same different]
    by (simp add: decode_finite_locus_transaction)
  then obtain r where executed: "finite_transact S ?T=Some r"
    and result: "Conflict (observed_comparison (decode_finite_snapshot S) (decode_finite_transaction ?T))=
      decode_finite_transaction_result r"
    by (auto simp: finite_transact_exact)
  obtain C where conflict: "r=Finite_Conflict C"
    using result by (cases r) auto
  have "C=finite_observed_comparison S ?T"
    using executed conflict by (auto simp: finite_transact_def split: if_splits)
  then show ?thesis using executed conflict by simp
qed

section \<open>Presentations of generations, snapshots and transaction results\<close>

definition finite_target_generation_value :: "finite_generation \<Rightarrow> finite_factor_term" where
  "finite_target_generation_value=finite_generation_value Finite_Target"

definition finite_snapshot_value :: "finite_snapshot \<Rightarrow> finite_factor_term" where
  "finite_snapshot_value=finite_collection_presentation finite_target_generation_value"

fun finite_transaction_result_value :: "finite_transaction_result \<Rightarrow> finite_factor_term" where
  "finite_transaction_result_value (Finite_Applied U)=Finite_Pair (Finite_Payload [0]) (finite_snapshot_value U)"
| "finite_transaction_result_value (Finite_Conflict C)=Finite_Pair (Finite_Payload [1])
    (finite_collection_presentation (finite_pair_presentation Finite_Target
      (finite_option_presentation finite_target_generation_value)) C)"

lemma finite_target_generation_value_injective [intro]: "inj finite_target_generation_value"
  unfolding finite_target_generation_value_def by (rule finite_generation_value_injective) (simp add: inj_def)

lemma finite_snapshot_value_injective [intro]: "inj finite_snapshot_value"
  unfolding finite_snapshot_value_def by (intro finite_collection_presentation_injective) blast

lemma finite_transaction_result_value_injective [intro]: "inj finite_transaction_result_value"
proof (rule injI)
  have observations: "inj (finite_collection_presentation (finite_pair_presentation Finite_Target
      (finite_option_presentation finite_target_generation_value)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_option_presentation_injective finite_target_generation_value_injective) (simp add: inj_def)
  fix x y show "finite_transaction_result_value x=finite_transaction_result_value y \<Longrightarrow> x=y"
    using finite_snapshot_value_injective observations
    by (cases x; cases y) (auto dest: injD)
qed

end
