theory Development_Exported_Edit
  imports Development_State_Edit Development_Refinement_Repair Finite_Ordered_Set_Difference
begin

section \<open>An exported answer state is read into its edit by the difference of two listings\<close>

text \<open>
  An exported answer state (a framed answer, or a renamed control) states its entities in a table of its
  own. It is read into the request state's table extended by the names it lacks (\<open>isabelle_rooted_read\<close>,
  task 161), and its edit is the difference of the two entity lists there: the removed entities are the
  request state's that the read state lacks, the added ones the read state's that the request state lacks.
  Both are computed by one merge of the two lists ordered by the entities' keys (\<open>entity_order_key\<close>),
  and the edit is then the constructor's at those entities: the exported answer is the constructor's second
  instance, and its contract is consumed, not stated again.
\<close>

subsection \<open>A difference of two listings ordered by a key is one merge pass\<close>

text \<open>
  The merge is the difference of canonical listings (@{const ascending_difference}) read through a key:
  it compares the keys of the two heads and keeps a member of the first listing whose key the second
  lacks. Its keys are exactly the ascending difference of the keys, so its meaning is that difference's,
  carried back through a key injective on the two listings.
\<close>

fun keyed_difference :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "keyed_difference f [] ys=[]"
| "keyed_difference f xs []=xs"
| "keyed_difference f (x#xs) (y#ys)=(if f x<f y then x#keyed_difference f xs (y#ys)
    else if f y<f x then keyed_difference f (x#xs) ys else keyed_difference f xs (y#ys))"

lemma keyed_difference_map:
  "map f (keyed_difference f xs ys)=ascending_difference (map f xs) (map f ys)"
  by (induction f xs ys rule: keyed_difference.induct) simp_all

lemma keyed_difference_subset: "set (keyed_difference f xs ys)\<subseteq>set xs"
  by (induction f xs ys rule: keyed_difference.induct) auto

theorem keyed_difference_filter:
  assumes sorted: "sorted (map f xs)" "sorted (map f ys)" and inj: "inj_on f (set xs\<union>set ys)"
  shows "keyed_difference f xs ys=filter (\<lambda>z. z\<notin>set ys) xs"
proof -
  have same: "filter (\<lambda>z. f z\<notin>f ` set ys) xs=filter (\<lambda>z. z\<notin>set ys) xs"
    by (rule filter_cong[OF refl]) (simp add: inj_on_image_mem_iff[OF inj])
  have "map f (keyed_difference f xs ys)=ascending_difference (map f xs) (map f ys)"
    by (rule keyed_difference_map)
  also have "\<dots>=filter (\<lambda>z. z\<notin>set (map f ys)) (map f xs)"
    by (rule ascending_difference_filter[OF sorted])
  also have "\<dots>=map f (filter (\<lambda>z. f z\<notin>f ` set ys) xs)"
    by (simp add: filter_map comp_def)
  also have "\<dots>=map f (filter (\<lambda>z. z\<notin>set ys) xs)"
    by (simp only: same)
  finally have mapped: "map f (keyed_difference f xs ys)=map f (filter (\<lambda>z. z\<notin>set ys) xs)" .
  have inj': "inj_on f (set (keyed_difference f xs ys)\<union>set (filter (\<lambda>z. z\<notin>set ys) xs))"
    by (rule inj_on_subset[OF inj]) (use keyed_difference_subset[of f xs ys] in auto)
  show ?thesis by (rule iffD1[OF inj_on_map_eq_map[OF inj'] mapped])
qed

text \<open>
  Entities are listed by their keys once, with the library's merge sort
  (@{thm [source] sort_key_by_mergesort}), and subtracted by one merge: the difference costs the two sorts
  and a pass linear in the two lists.
\<close>

definition entity_difference :: "isabelle_entity list \<Rightarrow> isabelle_entity list \<Rightarrow> isabelle_entity list" where
  "entity_difference E E'=keyed_difference entity_order_key
    (sort_key entity_order_key E) (sort_key entity_order_key E')"

theorem entity_difference_set: "set (entity_difference E E')=set E-set E'"
proof -
  have inj: "inj_on entity_order_key A" for A
    by (rule inj_on_subset[OF entity_order_key_injective subset_UNIV])
  show ?thesis
    by (auto simp: entity_difference_def keyed_difference_filter[OF sorted_sort_key sorted_sort_key inj])
qed

subsection \<open>The exported answer's edit\<close>

definition exported_answer_edit :: "isabelle_rooted_context \<Rightarrow> isabelle_rooted_context \<Rightarrow> state_edit option" where
  "exported_answer_edit S S'=(let F=snd (snd (isabelle_rooted_read (fst (snd S)) S')) in
    state_edit_of S (fst (snd S')) (entity_difference (snd (snd S)) F) (entity_difference F (snd (snd S))))"

text \<open>
  A stage judging several exported answers against one request state lists the request state's entities
  once and applies the constructor's partial application to that state once, as the native answer's edit
  does (@{thm [source] development_native_answer_edit_shared}).
\<close>

lemma exported_answer_edit_shared [code]:
  "exported_answer_edit S=(let edit=state_edit_of S; names=fst (snd S);
     L=sort_key entity_order_key (snd (snd S)) in
     (\<lambda>S'. let L'=sort_key entity_order_key (snd (snd (isabelle_rooted_read names S'))) in
       edit (fst (snd S')) (keyed_difference entity_order_key L L') (keyed_difference entity_order_key L' L)))"
  by (simp add: fun_eq_iff exported_answer_edit_def entity_difference_def Let_def)

section \<open>The read answer state is the edit applied\<close>

text \<open>
  The read state and the edit applied to the request state have the same table, and the same roots when
  the answer keeps the request state's roots; their entities are the same set, listed in their own orders.
  A presentation reads a state's entities as a set: a row depends on the entity list only through the
  development constants it holds, and every condition of @{const state_presents} and
  @{const state_presentable} reads the list through its members. So the constructor's contract, stated for
  the edit applied, holds of the read state itself.
\<close>

lemma entity_row_entity_set:
  assumes names: "fst C'=fst C" and entities: "set (snd C')=set (snd C)"
  shows "entity_row key C'=entity_row key C"
proof
  fix e
  have constants: "set (isabelle_development_constants (snd C'))=set (isabelle_development_constants (snd C))"
    by (simp add: isabelle_development_constants_def List.map_filter_def entities)
  have "isabelle_entity_subjects (fst C') (isabelle_development_constants (snd C')) e=
      isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e"
    by (cases e) (simp_all add: names constants)
  then show "entity_row key C' e=entity_row key C e" by (simp add: entity_row_def names)
qed

lemma state_presentable_entity_set:
  assumes "fst S'=fst S" "fst (snd S')=fst (snd S)" "set (snd (snd S'))=set (snd (snd S))"
  shows "state_presentable S'\<longleftrightarrow>state_presentable S"
  using assms by (simp add: state_presentable_def state_positions_def)

lemma state_presents_entity_set:
  assumes roots: "fst S'=fst S" and names: "fst (snd S')=fst (snd S)"
    and entities: "set (snd (snd S'))=set (snd (snd S))"
  shows "state_presents key S' R\<longleftrightarrow>state_presents key S R"
proof -
  have row: "entity_row key (snd S')=entity_row key (snd S)"
    by (rule entity_row_entity_set) (simp_all add: names entities)
  have root: "root_row key (snd S')=root_row key (snd S)"
    by (rule ext) (simp add: root_row_def names)
  show ?thesis
    by (simp only: state_presents_def rows_present_def roots_present_def state_positions_def
        row root roots names entities)
qed

theorem exported_answer_edit_contract:
  assumes presented: "state_presenter S=Some R" and read: "isabelle_rooted_read (fst (snd S)) S'=T"
    and answer: "state_presentable T" and roots: "fst T=fst S"
    and edit: "exported_answer_edit S S'=Some e"
  shows "state_presents state_constant_key T (edited_state R e)"
    and "keys_shared R (edited_state R e)"
    and "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and "state_roots (edited_state R e)=state_roots R"
    and "\<And>z. z\<in>presented_rows R \<Longrightarrow> z\<notin>edit_rows (edit_removed e) \<Longrightarrow> z\<in>presented_rows (edited_state R e)"
    and "\<And>a n. (a,n)\<in>set (edit_atoms e) \<Longrightarrow> a\<notin>fst ` set (state_atoms R)"
    and "\<And>g. g\<in>set (snd (snd S)) \<Longrightarrow> g\<in>set (snd (snd T)) \<Longrightarrow>
      (development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
        \<in>set (state_entities (edited_state R e) (entity_kind_of g))"
    and "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and "\<And>b q. (b,q)\<in>edit_rows (edit_added e) \<Longrightarrow> b\<notin>fst ` presented_rows R"
proof -
  let ?E="snd (snd S)" and ?F="snd (snd T)" and ?ns="fst (snd S')"
  let ?A="edit_applied S ?ns (entity_difference ?E ?F) (entity_difference ?F ?E)"
  have edit': "state_edit_of S ?ns (entity_difference ?E ?F) (entity_difference ?F ?E)=Some e"
    using edit by (simp add: exported_answer_edit_def Let_def read)
  have tables: "fst (snd ?A)=fst (snd T)"
    by (simp add: edit_applied_def read[symmetric] isabelle_rooted_read_fields)
  have roots': "fst ?A=fst T" using roots by (simp add: edit_applied_def)
  have entities: "set (snd (snd ?A))=set ?F" by (auto simp: edit_applied_def entity_difference_set)
  have answer': "state_presentable ?A"
    using answer by (simp only: state_presentable_entity_set[OF roots' tables entities])
  note contract=state_edit_contract[OF presented answer' edit']
  show "state_presents state_constant_key T (edited_state R e)"
    using contract(1) by (simp only: state_presents_entity_set[OF roots' tables entities])
  show "keys_shared R (edited_state R e)" by (rule contract(2))
  show "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    by (rule contract(3))
  show "state_roots (edited_state R e)=state_roots R" by (rule contract(4))
  show "z\<in>presented_rows (edited_state R e)" if "z\<in>presented_rows R" "z\<notin>edit_rows (edit_removed e)" for z
    by (rule contract(5)[OF that])
  show "a\<notin>fst ` set (state_atoms R)" if "(a,n)\<in>set (edit_atoms e)" for a n
    by (rule contract(6)[OF that])
  show "(development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
      \<in>set (state_entities (edited_state R e) (entity_kind_of g))" if "g\<in>set ?E" "g\<in>set ?F" for g
    using contract(7)[OF that(1)] that(2) entities by simp
  show "a\<notin>fst ` presented_rows (edited_state R e)" if "(a,z)\<in>edit_rows (edit_removed e)" for a z
    by (rule contract(8)[OF that])
  show "b\<notin>fst ` presented_rows R" if "(b,q)\<in>edit_rows (edit_added e)" for b q
    by (rule contract(9)[OF that])
qed

section \<open>The merge computes the difference of the two presentations\<close>

text \<open>
  Read into the request state's table, a request entity keeps every position, so the embedding of the
  request table into the read table fixes it; the difference of the two states
  (@{const isabelle_state_removed}, @{const isabelle_state_added}) is then the merge's. Task 38's
  @{thm [source] state_difference_removed} and @{thm [source] state_difference_added} read that difference
  as the search of the other state's rows by key: a row of the request state is found among the answer
  state's exactly when the merge does not remove its entity, and a row of the answer state is found among the
  request state's exactly when the merge does not add it. The edit is reduced by the constructor, never
  checked by a decision.
\<close>

lemma appended_entity_fixed:
  assumes distinct: "distinct names" and inside: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
  shows "isabelle_entity_rename (isabelle_state_embedding names (isabelle_appended_names names ns)) e=e"
proof -
  have fixed: "isabelle_state_embedding names (isabelle_appended_names names ns) i=i" if bound: "i<length names" for i
    unfolding isabelle_appended_names_def by (rule isabelle_state_embedding_prefix[OF distinct bound])
  have "isabelle_entity_rename (isabelle_state_embedding names (isabelle_appended_names names ns)) e=
      isabelle_entity_rename id e"
    by (rule isabelle_entity_rename_cong) (use inside fixed in simp)
  then show ?thesis by (simp add: isabelle_entity_rename_id)
qed

theorem exported_answer_difference_lists:
  assumes presentable: "state_presentable S" and read: "isabelle_rooted_read (fst (snd S)) S'=T"
  shows "set (isabelle_state_removed (snd S) (snd T))=set (entity_difference (snd (snd S)) (snd (snd T)))"
    and "set (isabelle_state_added (snd S) (snd T))=set (entity_difference (snd (snd T)) (snd (snd S)))"
proof -
  have table: "fst (snd T)=isabelle_appended_names (fst (snd S)) (fst (snd S'))"
    by (simp add: read[symmetric] isabelle_rooted_read_fields)
  have fixed: "isabelle_entity_rename (isabelle_state_embedding (fst (snd S)) (fst (snd T))) g=g"
    if "g\<in>set (snd (snd S))" for g
    unfolding table
    by (rule appended_entity_fixed) (use presentable that in \<open>auto simp: state_presentable_def state_positions_def\<close>)
  show "set (isabelle_state_removed (snd S) (snd T))=set (entity_difference (snd (snd S)) (snd (snd T)))"
    by (auto simp: isabelle_state_removed_def Let_def entity_difference_set fixed)
  have image: "isabelle_state_image (snd S) (snd T)=snd (snd S)"
    unfolding isabelle_state_image_def by (rule map_idI) (simp add: fixed)
  show "set (isabelle_state_added (snd S) (snd T))=set (entity_difference (snd (snd T)) (snd (snd S)))"
    by (auto simp: isabelle_state_added_def Let_def entity_difference_set image)
qed

theorem exported_answer_edit_found:
  assumes presented: "state_presenter S=Some R" and read: "isabelle_rooted_read (fst (snd S)) S'=T"
    and answer: "state_presentable T" and roots: "fst T=fst S"
    and edit: "exported_answer_edit S S'=Some e"
  shows "\<And>g a. g\<in>set (snd (snd S)) \<Longrightarrow> (a,entity_row state_constant_key (snd S) g)\<in>presented_rows R \<Longrightarrow>
      store_lookup (family_row_store (state_all_families (edited_state R e))) a\<noteq>None \<longleftrightarrow>
        g\<notin>set (entity_difference (snd (snd S)) (snd (snd T)))"
    and "\<And>g b. g\<in>set (snd (snd T)) \<Longrightarrow> (b,entity_row state_constant_key (snd T) g)\<in>presented_rows (edited_state R e) \<Longrightarrow>
      store_lookup (family_row_store (state_all_families R)) b\<noteq>None \<longleftrightarrow>
        g\<notin>set (entity_difference (snd (snd T)) (snd (snd S)))"
proof -
  have presentable: "state_presentable S" using presented by (simp add: state_presenter_def split: if_splits)
  have present: "state_presents state_constant_key S R" by (rule state_presenter_presents[OF presented])
  note contract=exported_answer_edit_contract[OF presented read answer roots edit]
  note lists=exported_answer_difference_lists[OF presentable read]
  show "store_lookup (family_row_store (state_all_families (edited_state R e))) a\<noteq>None \<longleftrightarrow>
      g\<notin>set (entity_difference (snd (snd S)) (snd (snd T)))"
    if "g\<in>set (snd (snd S))" "(a,entity_row state_constant_key (snd S) g)\<in>presented_rows R" for g a
    using state_difference_removed[OF present contract(1) contract(2) that] lists(1) by simp
  show "store_lookup (family_row_store (state_all_families R)) b\<noteq>None \<longleftrightarrow>
      g\<notin>set (entity_difference (snd (snd T)) (snd (snd S)))"
    if "g\<in>set (snd (snd T))" "(b,entity_row state_constant_key (snd T) g)\<in>presented_rows (edited_state R e)" for g b
    using state_difference_added[OF present contract(1) contract(2) that] lists(2) by simp
qed

section \<open>A renamed control has the empty edit\<close>

text \<open>
  The control that renames a state by reversing its table (@{const development_answer_controls}' second
  member) reads back into the request state's table as the request state itself: every name it holds is the
  table's, and the reading undoes the reversal on every position the state uses. Its edit is therefore
  empty, and the empty edit leaves a presentation unchanged: the control is judged from the request state's
  assessment alone.
\<close>

lemma development_answer_controls_renamed:
  "renamed\<in>set (development_answer_controls reading restate S renamed subjects r)"
  by (simp add: development_answer_controls_def split: list.split)

theorem exported_answer_edit_renamed:
  assumes presentable: "state_presentable S"
  shows "exported_answer_edit S (isabelle_rooted_rename (isabelle_reversal (length (fst (snd S))))
      (rev (fst (snd S))) S)=Some \<lparr>edit_atoms=[],edit_removed=(\<lambda>k. []),edit_added=(\<lambda>k. [])\<rparr>"
proof -
  let ?names="fst (snd S)" and ?E="snd (snd S)" and ?n="length (fst (snd S))"
  let ?R="isabelle_rooted_rename (isabelle_reversal ?n) (rev ?names) S"
  have distinct: "distinct ?names" using presentable by (simp add: state_presentable_def)
  have inside: "i<?n" if "e\<in>set ?E" "i\<in>set (isabelle_entity_positions e)" for e i
    using presentable that by (auto simp: state_presentable_def state_positions_def)
  have agree: "isabelle_state_embedding ?names (rev ?names) i=isabelle_reversal ?n i" if "i<?n" for i
    by (rule isabelle_state_embedding_agrees[OF _ isabelle_reversal_correspondence that]) (simp add: distinct)
  have undone: "isabelle_entity_rename (isabelle_appended_embedding ?names (rev ?names))
      (isabelle_entity_rename (isabelle_reversal ?n) e)=e" if e: "e\<in>set ?E" for e
  proof -
    have same: "isabelle_entity_rename (isabelle_reversal ?n) e=
        isabelle_entity_rename (isabelle_state_embedding ?names (rev ?names)) e"
      by (rule isabelle_entity_rename_cong) (simp add: agree inside[OF e])
    have "isabelle_entity_rename (isabelle_appended_embedding ?names (rev ?names))
        (isabelle_entity_rename (isabelle_state_embedding ?names (rev ?names)) e)=e"
      by (rule isabelle_appended_entity_back[OF distinct]) (auto simp: agree isabelle_reversal_def dest: inside[OF e])
    then show ?thesis by (simp only: same)
  qed
  have entities: "snd (snd (isabelle_rooted_read ?names ?R))=?E"
  proof -
    have "map (isabelle_entity_rename (isabelle_appended_embedding ?names (rev ?names)) \<circ>
        isabelle_entity_rename (isabelle_reversal ?n)) ?E=?E"
      by (rule map_idI) (simp add: undone)
    then show ?thesis by (simp add: isabelle_rooted_read_fields isabelle_rooted_rename_def)
  qed
  have ns: "fst (snd ?R)=rev ?names" by (simp add: isabelle_rooted_rename_def)
  have table: "isabelle_appended_names ?names (rev ?names)=?names"
    by (simp add: isabelle_appended_names_def filter_empty_conv)
  have empty: "entity_difference ?E ?E=[]" using entity_difference_set[of ?E ?E] by simp
  have condition: "edit_specification_condition ?E ?E"
    by (auto simp: edit_specification_condition_def list_all_iff split: isabelle_entity_with.split)
  show ?thesis
    by (simp add: exported_answer_edit_def Let_def entities ns empty state_edit_of_def edit_applied_def
        table condition)
qed

lemma edited_state_empty:
  "edited_state R \<lparr>edit_atoms=[],edit_removed=(\<lambda>k. []),edit_added=(\<lambda>k. [])\<rparr>=R"
  by (cases R) (simp add: edited_state_def)

end
