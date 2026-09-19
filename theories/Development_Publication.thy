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
  payload and cause are such targets and its predecessors are generations. Development_Certified_Generations
  records its cause as a certified call of the policy that lists the family it records; formation of
  these values establishes nothing about the validity of a cause.
\<close>

definition development_data_target :: "finite_factor_term \<Rightarrow> finite_exact_target option" where
  "development_data_target t=map_option Finite_Whole (finite_data_syntax (decode_finite_term t))"

section \<open>A decision stands at the locus of its kind\<close>

text \<open>
  The development records its decisions as generations too, and each decision stands at a locus of its
  own kind beside the loci of the problems. The issue of a problem, the request an executor answers for
  it, stands at the problem's issue locus: at most one request for a problem is current, and issuing it
  again replaces the earlier one. The selection of the next problems stands at the development's
  selection locus: at most one selection is current. The kind of a locus is the constructor of its
  presentation, so no issue or selection locus is the locus of any problem.
\<close>

definition development_issue_locus :: "String.literal list \<Rightarrow> development_problem \<Rightarrow> finite_factor_term" where
  "development_issue_locus names p=Finite_Pair (Finite_Payload [1]) (development_problem_locus names p)"

definition development_selection_locus :: finite_factor_term where
  "development_selection_locus=Finite_Pair (Finite_Payload [2]) (Finite_Payload [])"

lemma isabelle_names_data_not_payload:
  "isabelle_names_data ns\<noteq>Finite_Payload [n]" "Finite_Payload [n]\<noteq>isabelle_names_data ns"
  by (cases ns; simp add: isabelle_names_data_def finite_sequence_presentation_def)+

lemma development_decision_loci_distinct:
  "development_issue_locus names p\<noteq>development_problem_locus names' q"
  "development_selection_locus\<noteq>development_problem_locus names' q"
  "development_selection_locus\<noteq>development_issue_locus names p"
  by (simp_all add: development_issue_locus_def development_selection_locus_def development_problem_locus_def
    finite_pair_presentation_def isabelle_names_data_not_payload)

lemma development_issue_locus_eq:
  "development_issue_locus names p=development_issue_locus names' q \<longleftrightarrow>
    development_problem_locus names p=development_problem_locus names' q"
  by (simp add: development_issue_locus_def)

lemma development_loci_formed [simp]:
  "finite_term_formed (development_problem_locus names p)"
  "finite_term_formed (development_issue_locus names p)"
  "finite_term_formed development_selection_locus"
  by (simp_all add: development_problem_locus_def development_issue_locus_def development_selection_locus_def
    finite_pair_presentation_def octets_formed_def)

text \<open>
  A formed value's complete data quotation determines the value, so distinct loci are distinct
  targets: the quotation of a locus is read back to exactly one presented value.
\<close>

lemma development_data_target_injective:
  assumes first: "development_data_target t=Some x" and second: "development_data_target t'=Some x"
    and formed: "finite_term_formed t" "finite_term_formed t'"
  shows "t=t'"
proof -
  obtain R where built: "finite_data_syntax (decode_finite_term t)=Some R" and whole: "x=Finite_Whole R"
    using first by (auto simp: development_data_target_def)
  obtain R' where built': "finite_data_syntax (decode_finite_term t')=Some R'" and whole': "x=Finite_Whole R'"
    using second by (auto simp: development_data_target_def)
  have same: "R'=R" using whole whole' by simp
  have "term_formed (decode_finite_term t)" "term_formed (decode_finite_term t')"
    using formed by (simp_all only: finite_term_formed_correct)
  then have quoted: "complete_data_quoted_at (decode_finite_object R) [] (decode_finite_term t)"
      "complete_data_quoted_at (decode_finite_object R) [] (decode_finite_term t')"
    using finite_data_syntax_complete_quotation built built'[unfolded same] by blast+
  have "[]=([]::local_address) \<and> decode_finite_term t=decode_finite_term t'"
    by (rule complete_data_quotation_whole_unique[OF quoted])
  then show ?thesis by simp
qed

corollary development_data_targets_distinct:
  assumes "development_data_target t=Some x" "development_data_target t'=Some y"
    "finite_term_formed t" "finite_term_formed t'" "t\<noteq>t'"
  shows "x\<noteq>y"
  using development_data_target_injective assms by blast

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

text \<open>
  A generation whose locus the published state does not hold is admitted by the transaction that
  expects that absence: it applies, the locus then holds the generation, and every other locus keeps
  its selection. This is the admission transaction of the published state, executed through the
  exactness theorem as the replacement is.
\<close>

theorem development_publication_admitted:
  assumes published: "finite_snapshot_formed S"
    and absent: "finite_snapshot_lookup S (generation_locus G)=None"
    and formed: "finite_generation_formed G"
  obtains U where "finite_transact S (finite_locus_transaction None G)=Some (Finite_Applied U)"
    "finite_snapshot_formed U" "finite_snapshot_lookup U (generation_locus G)=Some G"
    "\<And>l. l\<noteq>generation_locus G \<Longrightarrow> finite_snapshot_lookup U l=finite_snapshot_lookup S l"
proof -
  let ?T="finite_locus_transaction None G"
  let ?g="decode_finite_generation G"
  let ?W="{|?g|}"
  have decoded: "snapshot_formed (decode_finite_snapshot S)"
    using published by (simp only: finite_snapshot_formed_correct)
  have new: "generation_formed ?g"
    using formed by (simp only: finite_generation_formed_correct)
  have single: "snapshot_formed ?W"
    using new by (simp add: snapshot_formed_def selection_formed_def)
  have transaction: "transaction_formed (admission_transaction ?W)"
    by (rule admission_transaction_formed[OF single])
  have missing: "snapshot_lookup (decode_finite_snapshot S) (generation_locus ?g)=None"
    using absent by (simp add: decode_finite_generation_selectors finite_snapshot_lookup_exact[OF published])
  have passes: "comparison_passes (decode_finite_snapshot S) (admission_transaction ?W)"
    using missing by (simp add: comparison_passes_def comparison_loci_def admission_transaction_def snapshot_loci_def)
  have decoded_transaction: "decode_finite_transaction ?T=admission_transaction ?W"
    by (simp add: decode_finite_locus_transaction)
  have "transact (decode_finite_snapshot S) (decode_finite_transaction ?T)
      (Applied (transaction_update (decode_finite_snapshot S) (admission_transaction ?W)))"
    using decoded transaction passes by (simp add: transact_applied_iff decoded_transaction)
  then obtain r where executed: "finite_transact S ?T=Some r"
    and result: "Applied (transaction_update (decode_finite_snapshot S) (admission_transaction ?W))=
      decode_finite_transaction_result r"
    by (auto simp: finite_transact_exact)
  obtain U where applied: "r=Finite_Applied U"
    using result by (cases r) auto
  have transition: "transact (decode_finite_snapshot S) (decode_finite_transaction ?T) (Applied (decode_finite_snapshot U))"
    by (simp add: finite_transact_exact executed applied)
  have successor: "finite_snapshot_formed U"
    using successful_transaction_formed[OF transition] by (simp only: finite_snapshot_formed_correct)
  have admitted: "transact (decode_finite_snapshot S) (admission_transaction ?W) (Applied (decode_finite_snapshot U))"
    using transition by (simp only: decoded_transaction)
  note lookups=successful_transaction_lookup[OF admitted]
  have at: "finite_snapshot_lookup U (generation_locus G)=Some G"
  proof -
    have "snapshot_lookup ?W (generation_locus ?g)=Some ?g"
      by (rule snapshot_lookup_member[OF single]) simp
    then have "snapshot_lookup (decode_finite_snapshot U) (decode_finite_target (generation_locus G))=Some ?g"
      using lookups[of "generation_locus ?g"]
      by (simp add: admission_transaction_def snapshot_loci_def decode_finite_generation_selectors)
    then show ?thesis
      by (simp add: finite_snapshot_lookup_exact[OF successor] map_option_eq_Some)
  qed
  have others: "finite_snapshot_lookup U l=finite_snapshot_lookup S l" if other: "l\<noteq>generation_locus G" for l
  proof -
    have outside: "decode_finite_target l\<notin>snapshot_loci ?W"
      using other by (simp add: snapshot_loci_def decode_finite_generation_selectors)
    have "snapshot_lookup (decode_finite_snapshot U) (decode_finite_target l)=
        snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)"
      using lookups[of "decode_finite_target l"] outside by (simp add: admission_transaction_def)
    then show ?thesis
      by (simp add: finite_snapshot_lookup_exact[OF successor] finite_snapshot_lookup_exact[OF published]
        map_option_decode_finite_generation_eq)
  qed
  have "finite_transact S ?T=Some (Finite_Applied U)" using executed applied by simp
  then show ?thesis by (rule that[OF _ successor at others])
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
