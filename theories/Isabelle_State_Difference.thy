theory Isabelle_State_Difference
  imports Isabelle_Renaming
begin

section \<open>Two checked states correspond through the names they share\<close>

text \<open>
  Two states read from different checked contexts have different name tables: a change adds
  and removes names, and every later name moves. The names are the only link between the two
  tables, because the kernel identifies a constant, a type or a variable by its name. The
  embedding below sends each position of the first table to the position of the same name in
  the second, and every position the second table does not hold to a position outside it, so
  it is injective whenever both tables are. On the names both tables hold it is a
  correspondence in the sense of the renaming account; no name is compared with another, and
  no position of either table orders anything.
\<close>

fun isabelle_name_position :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> nat option" where
  "isabelle_name_position [] n=None"
| "isabelle_name_position (m#ms) n=(if m=n then Some 0 else map_option Suc (isabelle_name_position ms n))"

lemma isabelle_name_position_some:
  "isabelle_name_position ms n=Some j \<Longrightarrow> j<length ms \<and> ms!j=n"
proof (induction ms arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  show ?case
  proof (cases "m=n")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case False
    then obtain k where found: "isabelle_name_position ms n=Some k" and shifted: "j=Suc k"
      using Cons.prems by (auto simp: map_option_eq_Some)
    show ?thesis using Cons.IH[OF found] by (simp add: shifted)
  qed
qed

lemma isabelle_name_position_none:
  "isabelle_name_position ms n=None \<longleftrightarrow> n\<notin>set ms"
  by (induction ms) auto

lemma isabelle_name_position_at:
  assumes distinct: "distinct ms" and bound: "j<length ms"
  shows "isabelle_name_position ms (ms!j)=Some j"
  using assms
proof (induction ms arbitrary: j)
  case Nil
  then show ?case by simp
next
  case (Cons m ms)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc k)
    have inside: "ms!k\<in>set ms" using Cons.prems(2) by (simp add: Suc)
    have other: "m\<noteq>ms!k" using Cons.prems(1) inside by auto
    have "isabelle_name_position ms (ms!k)=Some k"
      using Cons.IH[of k] Cons.prems by (simp add: Suc)
    then show ?thesis using other by (simp add: Suc)
  qed
qed

definition isabelle_state_embedding :: "String.literal list \<Rightarrow> String.literal list \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_state_embedding names names' i=
    (case Option.bind (isabelle_name_at names i) (isabelle_name_position names') of
       Some j \<Rightarrow> j
     | None \<Rightarrow> length names'+i)"

lemma isabelle_state_embedding_shared:
  assumes named: "isabelle_name_at names i=Some n" and shared: "n\<in>set names'"
  shows "isabelle_name_at names' (isabelle_state_embedding names names' i)=Some n"
proof -
  obtain j where found: "isabelle_name_position names' n=Some j"
    using shared isabelle_name_position_none[of names' n] by (cases "isabelle_name_position names' n") auto
  have at: "j<length names' \<and> names'!j=n" by (rule isabelle_name_position_some[OF found])
  have "isabelle_state_embedding names names' i=j" by (simp add: isabelle_state_embedding_def named found)
  then show ?thesis using at by (simp add: isabelle_name_at_def)
qed

lemma isabelle_state_embedding_unshared:
  assumes "\<nexists>n. isabelle_name_at names i=Some n \<and> n\<in>set names'"
  shows "isabelle_state_embedding names names' i=length names'+i"
proof (cases "isabelle_name_at names i")
  case None
  then show ?thesis by (simp add: isabelle_state_embedding_def)
next
  case (Some n)
  then have "isabelle_name_position names' n=None"
    using assms by (simp add: isabelle_name_position_none)
  then show ?thesis by (simp add: isabelle_state_embedding_def Some)
qed

theorem isabelle_state_embedding_injective:
  assumes distinct: "distinct names"
  shows "inj (isabelle_state_embedding names names')"
proof (rule injI)
  fix i k assume equal: "isabelle_state_embedding names names' i=isabelle_state_embedding names names' k"
  let ?found="\<lambda>i. Option.bind (isabelle_name_at names i) (isabelle_name_position names')"
  show "i=k"
  proof (cases "?found i")
    case None
    note first=None
    show ?thesis
    proof (cases "?found k")
      case None
      then show ?thesis using equal first by (simp add: isabelle_state_embedding_def)
    next
      case (Some j)
      obtain n where "isabelle_name_at names k=Some n" "isabelle_name_position names' n=Some j"
        using Some by (auto simp: bind_eq_Some_conv)
      then have "j<length names'" using isabelle_name_position_some by blast
      then show ?thesis using equal first Some by (simp add: isabelle_state_embedding_def)
    qed
  next
    case (Some j)
    note first=Some
    obtain n where named: "isabelle_name_at names i=Some n" and at: "isabelle_name_position names' n=Some j"
      using first by (auto simp: bind_eq_Some_conv)
    have bound: "j<length names'" using isabelle_name_position_some[OF at] by simp
    show ?thesis
    proof (cases "?found k")
      case None
      then show ?thesis using equal first bound by (simp add: isabelle_state_embedding_def)
    next
      case (Some j')
      obtain n' where named': "isabelle_name_at names k=Some n'" and at': "isabelle_name_position names' n'=Some j'"
        using Some by (auto simp: bind_eq_Some_conv)
      have "j=j'" using equal first Some by (simp add: isabelle_state_embedding_def)
      then have "n=n'" using isabelle_name_position_some[OF at] isabelle_name_position_some[OF at'] by simp
      moreover have bounds: "i<length names" "k<length names" and "names!i=n" "names!k=n'"
        using named named' by (auto simp: isabelle_name_at_def split: if_splits)
      ultimately have "names!i=names!k" by simp
      then show ?thesis using nth_eq_iff_index_eq[OF distinct bounds] by simp
    qed
  qed
qed

text \<open>
  When the second table holds every name of the first, the embedding is a correspondence of
  the two tables, so every theorem of the renaming account applies to it unchanged.
\<close>

theorem isabelle_state_embedding_correspondence:
  assumes distinct: "distinct names" and shared: "set names\<subseteq>set names'"
  shows "isabelle_table_correspondence (isabelle_state_embedding names names') names names'"
proof (unfold isabelle_table_correspondence_def, intro conjI allI)
  show "inj (isabelle_state_embedding names names')" by (rule isabelle_state_embedding_injective[OF distinct])
  fix i
  show "isabelle_name_at names' (isabelle_state_embedding names names' i)=isabelle_name_at names i"
  proof (cases "isabelle_name_at names i")
    case None
    then show ?thesis by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
  next
    case (Some n)
    have "n\<in>set names" using Some by (auto simp: isabelle_name_at_def split: if_splits)
    then have "n\<in>set names'" using shared by blast
    then show ?thesis using isabelle_state_embedding_shared[OF Some] Some by simp
  qed
qed

section \<open>The difference of two states is read through that embedding\<close>

text \<open>
  An entity of the first state persists when its image under the embedding is an entity of the
  second; an entity of the second state is added when it is not the image of any entity of the
  first. A persisting entity keeps every name it uses, because its image is an entity of the
  second state, whose positions its table holds. Both readings are computed on the actual
  entity lists; neither depends on a position or on the order of either list.
\<close>

definition isabelle_state_image :: "isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity list" where
  "isabelle_state_image C C'=map (isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C'))) (snd C)"

definition isabelle_state_removed :: "isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity list" where
  "isabelle_state_removed C C'=(let f=isabelle_state_embedding (fst C) (fst C') in
    filter (\<lambda>e. isabelle_entity_rename f e\<notin>set (snd C')) (snd C))"

definition isabelle_state_added :: "isabelle_context \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity list" where
  "isabelle_state_added C C'=(let image=isabelle_state_image C C' in
    filter (\<lambda>e. e\<notin>set image) (snd C'))"

theorem isabelle_state_removed_exact:
  "e\<in>set (isabelle_state_removed C C') \<longleftrightarrow>
    e\<in>set (snd C) \<and> isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) e\<notin>set (snd C')"
  by (simp add: isabelle_state_removed_def)

theorem isabelle_state_added_exact:
  "e\<in>set (isabelle_state_added C C') \<longleftrightarrow>
    e\<in>set (snd C') \<and> (\<nexists>d. d\<in>set (snd C) \<and> e=isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) d)"
  by (auto simp: isabelle_state_added_def isabelle_state_image_def)

text \<open>
  The two readings account for both states completely: every entity of the second state is
  the image of a persisting entity of the first or is added, and every entity of the first
  either persists or is removed. Nothing is compared outside these two lists.
\<close>

theorem isabelle_state_difference_complete:
  "set (snd C')=isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) `
      (set (snd C)-set (isabelle_state_removed C C'))\<union>set (isabelle_state_added C C')"
  by (auto simp: isabelle_state_removed_exact isabelle_state_added_exact)

theorem isabelle_state_persisting:
  assumes "e\<in>set (snd C)" "e\<notin>set (isabelle_state_removed C C')"
  shows "isabelle_entity_rename (isabelle_state_embedding (fst C) (fst C')) e\<in>set (snd C')"
  using assms by (simp add: isabelle_state_removed_exact)

text \<open>
  A renaming depends only on the positions an entity uses, so two renamings that agree there
  move the entity alike.
\<close>

lemma isabelle_type_rename_cong:
  "(\<And>i. i\<in>set (isabelle_type_positions T) \<Longrightarrow> f i=g i) \<Longrightarrow> isabelle_type_rename f T=isabelle_type_rename g T"
  by (induction T) (auto intro!: map_cong)

lemma isabelle_term_rename_cong:
  "(\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> f i=g i) \<Longrightarrow> isabelle_term_rename f t=isabelle_term_rename g t"
  by (induction t) (auto intro!: isabelle_type_rename_cong)

lemma isabelle_entity_rename_cong:
  "(\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> f i=g i) \<Longrightarrow> isabelle_entity_rename f e=isabelle_entity_rename g e"
  by (cases e) (auto simp: isabelle_entity_positions_def intro!: isabelle_term_rename_cong)

text \<open>
  A state unchanged up to the positions of its names has no difference at all: read against
  its renaming by any correspondence of distinct tables, a state whose positions its table
  holds removes and adds nothing. The embedding agrees with the correspondence on every
  position the first table holds, so the difference cannot depend on how names are placed.
\<close>

lemma isabelle_state_embedding_agrees:
  assumes distinct: "distinct names'" and corr: "isabelle_table_correspondence f names names'"
    and named: "i<length names"
  shows "isabelle_state_embedding names names' i=f i"
proof -
  have "isabelle_name_at names' (f i)=Some (names!i)"
    using isabelle_table_correspondence_name[OF corr, of i] named by (simp add: isabelle_name_at_def)
  then have image: "f i<length names'" "names'!(f i)=names!i"
    by (auto simp: isabelle_name_at_def split: if_splits)
  have "isabelle_name_position names' (names!i)=Some (f i)"
    using isabelle_name_position_at[OF distinct image(1)] by (simp only: image(2))
  then show ?thesis using named by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
qed

theorem isabelle_state_renamed_unchanged:
  assumes distinct: "distinct names'" and corr: "isabelle_table_correspondence f (fst C) names'"
    and known: "isabelle_unknown_positions C=[]"
  shows "isabelle_state_removed C (isabelle_context_rename f names' C)=[]"
    "isabelle_state_added C (isabelle_context_rename f names' C)=[]"
proof -
  let ?h="isabelle_state_embedding (fst C) names'"
  have same: "isabelle_entity_rename ?h e=isabelle_entity_rename f e" if member: "e\<in>set (snd C)" for e
  proof (rule isabelle_entity_rename_cong)
    fix i assume used: "i\<in>set (isabelle_entity_positions e)"
    have "i<length (fst C)"
      using known member used isabelle_unknown_positions_exact[of i C] by auto
    then show "?h i=f i" using isabelle_state_embedding_agrees[OF distinct corr] by simp
  qed
  have image: "map (isabelle_entity_rename ?h) (snd C)=map (isabelle_entity_rename f) (snd C)"
    by (rule map_cong) (simp_all add: same)
  show "isabelle_state_removed C (isabelle_context_rename f names' C)=[]"
    by (auto simp: isabelle_state_removed_def isabelle_context_rename_def Let_def same filter_empty_conv)
  show "isabelle_state_added C (isabelle_context_rename f names' C)=[]"
    by (simp add: isabelle_state_added_def isabelle_state_image_def isabelle_context_rename_def Let_def
      image filter_empty_conv)
qed

end
