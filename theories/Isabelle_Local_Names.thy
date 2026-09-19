theory Isabelle_Local_Names
  imports Isabelle_State_Difference
begin

section \<open>A presented value carries the names it uses\<close>

text \<open>
  A value read beside states whose name tables differ carries the names it uses: every position the
  value mentions is replaced by the position of its name in the list of the names the value mentions,
  in the order they first occur, through the existing embedding of one table into another. The
  presentation then depends on the value's structure and its names and on no other position of the
  table, and a correspondence of tables leaves it unchanged. A published locus and payload, an answer
  and a packet are values of this kind; each instantiates this notion instead of restating it.
\<close>

subsection \<open>Renamings compose, and a renaming that fixes every used position fixes the value\<close>

lemma isabelle_type_rename_id: "isabelle_type_rename id T=T"
  by (induction T) (simp_all add: map_idI)

lemma isabelle_term_rename_id: "isabelle_term_rename id t=t"
  by (induction t) (simp_all add: isabelle_type_rename_id[unfolded id_def])

lemma isabelle_entity_rename_id: "isabelle_entity_rename id e=e"
  by (cases e) (simp_all add: isabelle_term_rename_id)

lemma isabelle_type_rename_compose:
  "isabelle_type_rename g (isabelle_type_rename f T)=isabelle_type_rename (g \<circ> f) T"
  by (induction T) auto

lemma isabelle_term_rename_compose:
  "isabelle_term_rename g (isabelle_term_rename f t)=isabelle_term_rename (g \<circ> f) t"
  by (induction t) (simp_all add: isabelle_type_rename_compose comp_def)

lemma isabelle_entity_rename_compose:
  "isabelle_entity_rename g (isabelle_entity_rename f e)=isabelle_entity_rename (g \<circ> f) e"
  by (cases e) (simp_all add: isabelle_term_rename_compose)

text \<open>
  Agreement of two renamings on the positions a value uses is \<open>isabelle_entity_rename_cong\<close>
  and its type and term instances in \<open>Isabelle_State_Difference\<close>; they are not stated again.
\<close>

subsection \<open>The local names of a value and its local presentation\<close>

definition isabelle_local_names :: "String.literal list \<Rightarrow> nat list \<Rightarrow> String.literal list" where
  "isabelle_local_names names ps=remdups (List.map_filter (isabelle_name_at names) ps)"

definition isabelle_local_embedding :: "String.literal list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_local_embedding names ps=isabelle_state_embedding names (isabelle_local_names names ps)"

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
    using member named by (induction ps) (auto split: option.splits)
  then have used: "names!i\<in>set ?L" by (simp add: isabelle_local_names_def)
  obtain j where found: "isabelle_name_position ?L (names!i)=Some j"
    using used isabelle_name_position_none[of ?L "names!i"] by (cases "isabelle_name_position ?L (names!i)") auto
  have moved: "isabelle_name_at names' (f i)=Some (names!i)"
    using named by (simp add: isabelle_table_correspondence_name[OF corr])
  show ?thesis
    by (simp add: isabelle_local_embedding_def local isabelle_state_embedding_def named moved found)
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
    have "isabelle_entity_rename (isabelle_local_embedding names' (map f ?ps) \<circ> f) e=
        isabelle_entity_rename (isabelle_local_embedding names ?ps) e"
    proof (rule isabelle_entity_rename_cong)
      fix i assume position: "i\<in>set (isabelle_entity_positions e)"
      have "i\<in>set ?ps" using member position by auto
      moreover have "i<length names" using member position inside by auto
      ultimately show "(isabelle_local_embedding names' (map f ?ps) \<circ> f) i=isabelle_local_embedding names ?ps i"
        by (simp add: isabelle_local_embedding_renamed[OF corr])
    qed
    then show ?thesis by (simp only: isabelle_entity_rename_compose)
  qed
  show ?thesis
    unfolding isabelle_local_entities_def Let_def positions names
    by (simp add: entity)
qed

subsection \<open>A table extended by the names it lacks\<close>

text \<open>
  A value presented with its names is read into a state by appending to the state's table the names
  it lacks: every position of the state is kept, and each name of the value is found at one position,
  from which the embedding leads back to the value's own position.
\<close>

definition isabelle_appended_names :: "String.literal list \<Rightarrow> String.literal list \<Rightarrow> String.literal list" where
  "isabelle_appended_names names names'=names@filter (\<lambda>n. n\<notin>set names) names'"

lemma isabelle_name_position_append:
  "isabelle_name_position (xs@ys) n=(case isabelle_name_position xs n of Some j \<Rightarrow> Some j
    | None \<Rightarrow> map_option ((+) (length xs)) (isabelle_name_position ys n))"
  by (induction xs) (cases "isabelle_name_position ys n"; auto split: option.splits)+

lemma isabelle_state_embedding_back:
  assumes distinct: "distinct names" and bound: "i<length names" and shared: "names!i\<in>set L"
  shows "isabelle_state_embedding L names (isabelle_state_embedding names L i)=i"
proof -
  obtain j where found: "isabelle_name_position L (names!i)=Some j"
    using shared isabelle_name_position_none[of L "names!i"] by (cases "isabelle_name_position L (names!i)") auto
  have at: "j<length L \<and> L!j=names!i" by (rule isabelle_name_position_some[OF found])
  have there: "isabelle_state_embedding names L i=j"
    using bound found by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
  have home: "isabelle_name_position names (names!i)=Some i" by (rule isabelle_name_position_at[OF distinct bound])
  have "isabelle_state_embedding L names j=i"
    using at home by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
  then show ?thesis by (simp only: there)
qed

end
