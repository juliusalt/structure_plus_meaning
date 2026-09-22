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

text \<open>An appended table keeps the original's names at its positions.\<close>

lemma isabelle_appended_names_longer: "length names\<le>length (isabelle_appended_names names ns)"
  by (simp add: isabelle_appended_names_def)

lemma isabelle_appended_names_nth:
  "i<length names \<Longrightarrow> isabelle_appended_names names ns!i=names!i"
  by (simp add: isabelle_appended_names_def nth_append)

lemma isabelle_appended_names_prefix:
  "i<length names \<Longrightarrow> isabelle_name_at (isabelle_appended_names names ns) i=isabelle_name_at names i"
  by (simp add: isabelle_appended_names_def isabelle_name_at_def nth_append)

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

subsection \<open>A root carries the names it uses, as an entity does\<close>

text \<open>
  A root is a term of a state, not an entity, and it is presented by the same notion: the value
  with the names it uses, its positions replaced by their positions in that list. The law of the
  notion is not proved again for it; it is consumed from \<open>isabelle_local_entities_renamed\<close> at a
  one-entity list, whose entity is a proof device and appears in no relation.
\<close>

definition isabelle_local_root :: "String.literal list \<Rightarrow> isabelle_term \<Rightarrow> String.literal list\<times>isabelle_term" where
  "isabelle_local_root names t=(isabelle_local_names names (isabelle_term_positions t),
    isabelle_term_rename (isabelle_local_embedding names (isabelle_term_positions t)) t)"

lemma isabelle_local_root_entities:
  "isabelle_local_entities names [Isabelle_Definition t]=
    (fst (isabelle_local_root names t),[Isabelle_Definition (snd (isabelle_local_root names t))])"
  by (simp add: isabelle_local_entities_def isabelle_local_root_def isabelle_entity_positions_def Let_def)

theorem isabelle_local_root_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and inside: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> i<length names"
  shows "isabelle_local_root names' (isabelle_term_rename f t)=isabelle_local_root names t"
proof -
  have positions: "\<forall>e\<in>set [Isabelle_Definition t]. \<forall>i\<in>set (isabelle_entity_positions e). i<length names"
    using inside by (simp add: isabelle_entity_positions_def)
  have "isabelle_local_entities names' (map (isabelle_entity_rename f) [Isabelle_Definition t])=
      isabelle_local_entities names [Isabelle_Definition t]"
    by (rule isabelle_local_entities_renamed[OF corr positions])
  then have "(fst (isabelle_local_root names' (isabelle_term_rename f t)),
      [Isabelle_Definition (snd (isabelle_local_root names' (isabelle_term_rename f t)))])=
    (fst (isabelle_local_root names t),[Isabelle_Definition (snd (isabelle_local_root names t))])"
    by (simp only: list.map isabelle_entity_rename.simps isabelle_local_root_entities)
  then show ?thesis
    by (cases "isabelle_local_root names' (isabelle_term_rename f t)";
        cases "isabelle_local_root names t") simp
qed

subsection \<open>Local presentations compared across two states\<close>

text \<open>
  Two states whose tables differ are not related by a correspondence when one drops or adds names,
  so the invariance above does not compare their values. The comparison they need is stated here,
  once: the local presentation of a value of one state equals that of a value of the other exactly
  when the second is the first moved by the embedding of the one table into the other. It holds for
  any positions in range of their tables; only the second table must be free of repeated names, as
  the way back from a local list into it requires. Its root analogue follows through the one-entity
  wrapper.
\<close>

lemma isabelle_local_names_in_range:
  assumes inside: "\<forall>i\<in>set ps. i<length names"
  shows "isabelle_local_names names ps=remdups (map ((!) names) ps)"
proof -
  have "List.map_filter (isabelle_name_at names) ps=map ((!) names) ps"
    using inside by (induction ps) (simp_all add: List.map_filter_simps isabelle_name_at_def)
  then show ?thesis by (simp add: isabelle_local_names_def)
qed

lemma isabelle_state_embedding_named:
  assumes named: "isabelle_name_at names i=Some n" and found: "isabelle_name_position L n=Some k"
  shows "isabelle_state_embedding names L i=k"
  using named found by (simp add: isabelle_state_embedding_def)

lemma isabelle_name_position_member:
  assumes "n\<in>set L"
  obtains k where "isabelle_name_position L n=Some k" "k<length L" "L!k=n"
  using assms isabelle_name_position_none[of L n] isabelle_name_position_some[of L n]
  by (cases "isabelle_name_position L n") auto

theorem isabelle_local_entities_compared:
  assumes distinct: "distinct names'"
    and inside: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
    and inside': "\<forall>j\<in>set (isabelle_entity_positions g). j<length names'"
  shows "isabelle_local_entities names [e]=isabelle_local_entities names' [g] \<longleftrightarrow>
    isabelle_entity_rename (isabelle_state_embedding names names') e=g"
proof -
  let ?ps="isabelle_entity_positions e" and ?qs="isabelle_entity_positions g"
  let ?L="isabelle_local_names names ?ps" and ?M="isabelle_local_names names' ?qs"
  let ?f="isabelle_state_embedding names names'"
  have L: "set ?L=(!) names ` set ?ps" using inside by (simp add: isabelle_local_names_in_range)
  have M: "set ?M=(!) names' ` set ?qs" using inside' by (simp add: isabelle_local_names_in_range)
  have unfolded: "isabelle_local_entities names [e]=isabelle_local_entities names' [g] \<longleftrightarrow>
      ?L=?M \<and> isabelle_entity_rename (isabelle_state_embedding names ?L) e=
        isabelle_entity_rename (isabelle_state_embedding names' ?M) g"
    by (simp add: isabelle_local_entities_def isabelle_local_embedding_def Let_def)
  have named: "isabelle_name_at names i=Some (names!i)" if "i\<in>set ?ps" for i
    using that inside by (simp add: isabelle_name_at_def)
  show ?thesis
  proof
    assume equal: "isabelle_local_entities names [e]=isabelle_local_entities names' [g]"
    have both: "?L=?M \<and> isabelle_entity_rename (isabelle_state_embedding names ?L) e=
        isabelle_entity_rename (isabelle_state_embedding names' ?M) g"
      by (rule iffD1[OF unfolded equal])
    then have same: "?L=?M" by (rule conjunct1)
    from both have moved: "isabelle_entity_rename (isabelle_state_embedding names ?L) e=
        isabelle_entity_rename (isabelle_state_embedding names' ?M) g" by (rule conjunct2)
    have returned: "isabelle_entity_rename (isabelle_state_embedding ?M names')
        (isabelle_entity_rename (isabelle_state_embedding names' ?M) g)=g"
    proof -
      have "isabelle_entity_rename (isabelle_state_embedding ?M names' \<circ> isabelle_state_embedding names' ?M) g=
          isabelle_entity_rename id g"
      proof (rule isabelle_entity_rename_cong)
        fix j assume position: "j\<in>set ?qs"
        then have "j<length names'" "names'!j\<in>set ?M" using inside' M by auto
        then show "(isabelle_state_embedding ?M names' \<circ> isabelle_state_embedding names' ?M) j=id j"
          by (simp add: isabelle_state_embedding_back[OF distinct])
      qed
      then show ?thesis by (simp only: isabelle_entity_rename_compose isabelle_entity_rename_id)
    qed
    have forth: "isabelle_entity_rename (isabelle_state_embedding ?M names')
        (isabelle_entity_rename (isabelle_state_embedding names ?L) e)=isabelle_entity_rename ?f e"
    proof -
      have "isabelle_entity_rename (isabelle_state_embedding ?M names' \<circ> isabelle_state_embedding names ?L) e=
          isabelle_entity_rename ?f e"
      proof (rule isabelle_entity_rename_cong)
        fix i assume position: "i\<in>set ?ps"
        have inL: "names!i\<in>set ?L" using position L by auto
        then have "names!i\<in>set names'" using same M inside' by auto
        then obtain p where p: "isabelle_name_position names' (names!i)=Some p"
          by (rule isabelle_name_position_member)
        obtain k where k: "isabelle_name_position ?L (names!i)=Some k" "k<length ?L" "?L!k=names!i"
          using inL by (rule isabelle_name_position_member)
        have "isabelle_name_at ?M k=Some (names!i)" using k same by (simp add: isabelle_name_at_def)
        then have "isabelle_state_embedding ?M names' k=p" using p by (rule isabelle_state_embedding_named)
        moreover have "isabelle_state_embedding names ?L i=k"
          using named[OF position] k(1) by (rule isabelle_state_embedding_named)
        moreover have "?f i=p" using named[OF position] p by (rule isabelle_state_embedding_named)
        ultimately show "(isabelle_state_embedding ?M names' \<circ> isabelle_state_embedding names ?L) i=?f i"
          by simp
      qed
      then show ?thesis by (simp only: isabelle_entity_rename_compose)
    qed
    show "isabelle_entity_rename ?f e=g" using forth moved returned by simp
  next
    assume renamed: "isabelle_entity_rename ?f e=g"
    have positions: "?qs=map ?f ?ps"
      unfolding renamed[symmetric] by (rule isabelle_entity_rename_positions)
    have present: "names'!(?f i)=names!i" if position: "i\<in>set ?ps" for i
    proof -
      have below: "?f i<length names'" using position positions inside' by auto
      have "names!i\<in>set names'"
      proof (rule ccontr)
        assume "names!i\<notin>set names'"
        then have "?f i=length names'+i"
          using named[OF position] by (intro isabelle_state_embedding_unshared) simp
        then show False using below by simp
      qed
      then have "isabelle_name_at names' (?f i)=Some (names!i)"
        by (rule isabelle_state_embedding_shared[OF named[OF position]])
      then show ?thesis using below by (simp add: isabelle_name_at_def)
    qed
    have "map ((!) names') ?qs=map ((!) names) ?ps"
      unfolding positions by (simp add: present)
    then have same: "?M=?L" using inside inside' by (simp add: isabelle_local_names_in_range)
    have "isabelle_entity_rename (isabelle_state_embedding names' ?L \<circ> ?f) e=
        isabelle_entity_rename (isabelle_state_embedding names ?L) e"
    proof (rule isabelle_entity_rename_cong)
      fix i assume position: "i\<in>set ?ps"
      have "names!i\<in>set ?L" using position L by auto
      then obtain k where k: "isabelle_name_position ?L (names!i)=Some k"
        by (rule isabelle_name_position_member)
      have below: "?f i<length names'" using position positions inside' by auto
      have "isabelle_name_at names' (?f i)=Some (names!i)"
        using below present[OF position] by (simp add: isabelle_name_at_def)
      then have "isabelle_state_embedding names' ?L (?f i)=k" using k by (rule isabelle_state_embedding_named)
      moreover have "isabelle_state_embedding names ?L i=k" using named[OF position] k by (rule isabelle_state_embedding_named)
      ultimately show "(isabelle_state_embedding names' ?L \<circ> ?f) i=isabelle_state_embedding names ?L i" by simp
    qed
    moreover have "isabelle_entity_rename (isabelle_state_embedding names' ?M) g=
        isabelle_entity_rename (isabelle_state_embedding names' ?L \<circ> ?f) e"
    proof -
      have "isabelle_entity_rename (isabelle_state_embedding names' ?M) g=
          isabelle_entity_rename (isabelle_state_embedding names' ?L) g" by (simp only: same)
      also have "\<dots>=isabelle_entity_rename (isabelle_state_embedding names' ?L \<circ> ?f) e"
        unfolding renamed[symmetric] by (rule isabelle_entity_rename_compose)
      finally show ?thesis .
    qed
    ultimately have "isabelle_entity_rename (isabelle_state_embedding names' ?M) g=
        isabelle_entity_rename (isabelle_state_embedding names ?L) e" by (simp only:)
    then show "isabelle_local_entities names [e]=isabelle_local_entities names' [g]"
      using unfolded same by simp
  qed
qed

theorem isabelle_local_root_compared:
  assumes distinct: "distinct names'"
    and inside: "\<forall>i\<in>set (isabelle_term_positions t). i<length names"
    and inside': "\<forall>j\<in>set (isabelle_term_positions u). j<length names'"
  shows "isabelle_local_root names t=isabelle_local_root names' u \<longleftrightarrow>
    isabelle_term_rename (isabelle_state_embedding names names') t=u"
proof -
  have "isabelle_local_root names t=isabelle_local_root names' u \<longleftrightarrow>
      isabelle_local_entities names [Isabelle_Definition t]=isabelle_local_entities names' [Isabelle_Definition u]"
    by (simp add: isabelle_local_root_entities prod_eq_iff)
  also have "\<dots> \<longleftrightarrow> isabelle_entity_rename (isabelle_state_embedding names names') (Isabelle_Definition t)=
      Isabelle_Definition u"
    by (rule isabelle_local_entities_compared[OF distinct])
      (use inside inside' in \<open>simp_all add: isabelle_entity_positions_def\<close>)
  also have "\<dots> \<longleftrightarrow> isabelle_term_rename (isabelle_state_embedding names names') t=u" by simp
  finally show ?thesis .
qed

subsection \<open>Two tables that agree on the names a value uses give it one local presentation\<close>

text \<open>
  A value's local names and local embedding read only the names at the positions it uses, so two tables
  that agree there give it the same local names and the same embedding at those positions. The local
  presentations of entities and of roots are its instances; neither establishes the agreement again.
  The equation reading of a statement likewise reads only the names at the positions it uses; it is
  proved by its own recursion and stated beside them. The notion these share, a reading of a name table
  that depends only on the names at the positions it uses, is stated after them with its laws.
\<close>


lemma isabelle_local_names_agree:
  assumes agree: "\<And>i. i\<in>set ps \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
  shows "isabelle_local_names names' ps=isabelle_local_names names ps"
    and "\<And>i. i\<in>set ps \<Longrightarrow> isabelle_local_embedding names' ps i=isabelle_local_embedding names ps i"
proof -
  show local_names: "isabelle_local_names names' ps=isabelle_local_names names ps"
    unfolding isabelle_local_names_def by (simp only: map_filter_agree[of ps, OF agree])
  show "isabelle_local_embedding names' ps i=isabelle_local_embedding names ps i" if used: "i\<in>set ps" for i
    unfolding isabelle_local_embedding_def isabelle_state_embedding_def local_names agree[OF used] ..
qed

lemma isabelle_local_entities_agree:
  assumes agree: "\<And>i. i\<in>set (concat (map isabelle_entity_positions es)) \<Longrightarrow>
      isabelle_name_at names' i=isabelle_name_at names i"
  shows "isabelle_local_entities names' es=isabelle_local_entities names es"
proof -
  note same=isabelle_local_names_agree[OF agree]
  have "map (isabelle_entity_rename (isabelle_local_embedding names' (concat (map isabelle_entity_positions es)))) es=
      map (isabelle_entity_rename (isabelle_local_embedding names (concat (map isabelle_entity_positions es)))) es"
  proof (rule map_cong[OF refl])
    fix e assume e: "e\<in>set es"
    show "isabelle_entity_rename (isabelle_local_embedding names' (concat (map isabelle_entity_positions es))) e=
        isabelle_entity_rename (isabelle_local_embedding names (concat (map isabelle_entity_positions es))) e"
      by (rule isabelle_entity_rename_cong) (rule same(2), use e in auto)
  qed
  then show ?thesis by (simp only: isabelle_local_entities_def Let_def same(1))
qed

lemma isabelle_local_root_agree:
  assumes agree: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
  shows "isabelle_local_root names' t=isabelle_local_root names t"
proof -
  note same=isabelle_local_names_agree[OF agree]
  have "isabelle_term_rename (isabelle_local_embedding names' (isabelle_term_positions t)) t=
      isabelle_term_rename (isabelle_local_embedding names (isabelle_term_positions t)) t"
    by (rule isabelle_term_rename_cong) (rule same(2))
  then show ?thesis by (simp only: isabelle_local_root_def same(1))
qed

lemma isabelle_equation_left_agree:
  assumes "\<And>i. i\<in>set (isabelle_term_positions p) \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
  shows "isabelle_equation_left names' p=isabelle_equation_left names p"
  using assms
proof (induction names p rule: isabelle_equation_left.induct)
  case (1 names c T p)
  have head: "isabelle_name_at names' c=isabelle_name_at names c" by (rule "1.prems") simp
  show ?case
  proof (cases "isabelle_name_at names c=Some isabelle_judgment_name")
    case True
    have "isabelle_equation_left names' p=isabelle_equation_left names p"
      using True "1.prems" by (intro "1.IH") auto
    then show ?thesis using True head by simp
  next
    case False
    then show ?thesis using head by simp
  qed
next
  case (2 names c T l r)
  have head: "isabelle_name_at names' c=isabelle_name_at names c" by (rule "2.prems") simp
  then show ?case by simp
qed simp_all

subsection \<open>A reading of a name table at the positions it uses\<close>

text \<open>
  A reading of a name table is a function of the table and a value that depends only on the names at the
  positions the value uses: two tables that agree at those positions give equal readings. That is the
  notion's one condition, and its first law. Its second law follows once: a table appended with the names
  it lacks (\<open>isabelle_appended_names\<close>) keeps every reading of a value whose positions are the original's.
  The local names, the local embedding, the local presentations of entities and roots, the equation
  reading and the subjects of an entity are its instances; each receiving proof cites the notion's laws at
  its instance and establishes no agreement again.
\<close>

locale isabelle_name_reading =
  fixes read :: "String.literal list \<Rightarrow> 'v \<Rightarrow> 'r" and positions :: "'v \<Rightarrow> nat list"
  assumes agree: "(\<And>i. i\<in>set (positions v) \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i) \<Longrightarrow>
      read names' v=read names v"
begin

theorem appended:
  assumes inside: "\<And>i. i\<in>set (positions v) \<Longrightarrow> i<length names"
  shows "read (isabelle_appended_names names ns) v=read names v"
proof (rule agree)
  fix i assume "i\<in>set (positions v)"
  then show "isabelle_name_at (isabelle_appended_names names ns) i=isabelle_name_at names i"
    by (rule isabelle_appended_names_prefix[OF inside])
qed

end

lemma isabelle_local_names_reading: "isabelle_name_reading isabelle_local_names (\<lambda>ps. ps)"
  by (rule isabelle_name_reading.intro) (rule isabelle_local_names_agree(1), blast)

lemma isabelle_local_embedding_reading:
  "isabelle_name_reading (\<lambda>names v. isabelle_local_embedding names (fst v) (snd v)) (\<lambda>v. snd v#fst v)"
proof (rule isabelle_name_reading.intro)
  fix v :: "nat list\<times>nat" and names' names :: "String.literal list"
  assume agree: "\<And>i. i\<in>set (snd v#fst v) \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
  have local_names: "isabelle_local_names names' (fst v)=isabelle_local_names names (fst v)"
    by (rule isabelle_local_names_agree(1)) (rule agree, simp)
  have at: "isabelle_name_at names' (snd v)=isabelle_name_at names (snd v)" by (rule agree) simp
  show "isabelle_local_embedding names' (fst v) (snd v)=isabelle_local_embedding names (fst v) (snd v)"
    unfolding isabelle_local_embedding_def isabelle_state_embedding_def local_names at ..
qed

lemma isabelle_local_entities_reading:
  "isabelle_name_reading isabelle_local_entities (\<lambda>es. concat (map isabelle_entity_positions es))"
  by (rule isabelle_name_reading.intro) (rule isabelle_local_entities_agree, blast)

lemma isabelle_local_root_reading: "isabelle_name_reading isabelle_local_root isabelle_term_positions"
  by (rule isabelle_name_reading.intro) (rule isabelle_local_root_agree, blast)

lemma isabelle_equation_left_reading: "isabelle_name_reading isabelle_equation_left isabelle_term_positions"
  by (rule isabelle_name_reading.intro) (rule isabelle_equation_left_agree, blast)

lemma isabelle_entity_subjects_reading:
  "isabelle_name_reading (\<lambda>names. isabelle_entity_subjects names D) isabelle_entity_positions"
proof (rule isabelle_name_reading.intro)
  fix e and names' names :: "String.literal list"
  assume agree: "\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
  show "isabelle_entity_subjects names' D e=isabelle_entity_subjects names D e"
  proof (cases e)
    case (Isabelle_Definition p)
    have "isabelle_equation_left names' p=isabelle_equation_left names p"
      by (rule isabelle_equation_left_agree) (rule agree, simp add: Isabelle_Definition isabelle_entity_positions_def)
    then show ?thesis by (simp add: Isabelle_Definition)
  next
    case (Isabelle_Code_Equation p)
    have "isabelle_equation_left names' p=isabelle_equation_left names p"
      by (rule isabelle_equation_left_agree) (rule agree, simp add: Isabelle_Code_Equation isabelle_entity_positions_def)
    then show ?thesis by (simp add: Isabelle_Code_Equation)
  qed simp_all
qed

text \<open>The roots' corollary: an appended table keeps the local presentation of every root of the original.\<close>

corollary isabelle_local_root_appended:
  "(\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> i<length names) \<Longrightarrow>
    isabelle_local_root (isabelle_appended_names names ns) t=isabelle_local_root names t"
  by (rule isabelle_name_reading.appended[OF isabelle_local_root_reading])

corollary isabelle_local_roots_appended:
  assumes inside: "\<And>t i. t\<in>set ts \<Longrightarrow> i\<in>set (isabelle_term_positions t) \<Longrightarrow> i<length names"
  shows "map (isabelle_local_root (isabelle_appended_names names ns)) ts=map (isabelle_local_root names) ts"
proof (rule map_cong[OF refl])
  fix t assume member: "t\<in>set ts"
  show "isabelle_local_root (isabelle_appended_names names ns) t=isabelle_local_root names t"
    by (rule isabelle_local_root_appended) (rule inside[OF member])
qed

end
