theory Development_Incremental_Verdict
  imports Development_Native_Verdict Development_Edited_Reach Development_Edited_Undeclared
    Established_Premises
begin

section \<open>An answer state is judged from its request state's assessment and the edit\<close>

text \<open>
  Design 171's build 6. The judgment of an answer state is not a second verdict: it is the verdict's
  entry (\<open>Development_Native_Verdict\<close>) at another argument. Each field of the entry is passed the part
  its call reads, and only how a part is built differs: from the two whole states for the whole
  judgment, from the request state's assessment and the answer's edit here. The assessment is built
  once per request state and holds presentations only; the parts of one answer are built from it and
  from the edit, so a verification stage costs one whole judgment per request state and a local one
  per answer.

  This theory states the assessment, the parts an answer's edit gives, and \<open>native_edited_fields\<close>:
  each field's call at its incremental part holds exactly when its call at its whole part on the
  answer state holds. Every field's lemma is consumed by name from builds 3, 4 and 5
  (\<open>Development_Edited_Local\<close>, \<open>Development_Edited_Undeclared\<close>, \<open>Development_Edited_Reach\<close>), and no
  field is proved again here.
\<close>

subsection \<open>A family of a state, read by its kind\<close>

text \<open>
  A presented state's families are computed once as a list (\<open>state_all_families\<close>, the one list form
  of \<open>Development_State_Rows\<close>), and a kind reads the list at its own position. Nothing compares a
  kind: the position is a reading of the kind's constructor, as the family holding a row is.
\<close>

fun kind_position :: "entity_kind \<Rightarrow> nat" where
  "kind_position Base_Kind=0"
| "kind_position Development_Kind=1"
| "kind_position Frontier_Kind=2"
| "kind_position Definition_Kind=3"
| "kind_position Specification_Kind=4"
| "kind_position Equation_Kind=5"

definition kind_item :: "'a list \<Rightarrow> entity_kind \<Rightarrow> 'a" where
  "kind_item xs j=xs!kind_position j"

lemma kind_item_map [simp]: "kind_item (map f entity_kinds) j=f j"
  by (cases j) (simp_all add: kind_item_def entity_kinds_def)

lemma kind_item_families [simp]: "kind_item (state_all_families R) j=state_entities R j"
  by (simp add: state_all_families_def)

lemma kind_item_families_map [simp]: "kind_item (map f (state_all_families R)) j=f (state_entities R j)"
  by (simp add: state_all_families_def comp_def)

lemma edit_rows_kinds: "(\<Union>F\<in>set (map G entity_kinds). set F)=edit_rows G"
  by (auto simp: edit_rows_def)

subsection \<open>The assessment of a request state\<close>

text \<open>
  The assessment holds, for a presented request state, the presentations its fields read: the subject
  index and the mention index of each family (build 1's index by a key reading), the mention index of
  the root family, the declaration store, the row store, the reach roots, and the root family. Each is
  read by the parts of an answer: an atom is a key the subject index holds, the answer state's restricted
  declaration store is the declaration store updated by the edit, and a key's declaring row is the row
  store's at the key the declaration store gives. Two lists of the state are still read whole for each
  answer: the reach roots' keys, searched at every visited key, and the request state's entities, which
  the edit's constructor indexes again at each answer. It holds no decision's answer: the premises that the request state is
  closed and declares each constant once are decided where the stage's equation checks them, not here.
\<close>

record state_assessment_parts =

  assessment_subject :: "isabelle_context state_family binary_path_store list"
  assessment_mention :: "isabelle_context state_family binary_path_store list"
  assessment_root_mention :: "(String.literal list\<times>isabelle_term) state_family binary_path_store"
  assessment_declarations :: "state_key binary_path_store"
  assessment_rows :: "(state_key\<times>isabelle_context state_row) binary_path_store"
  assessment_reach :: reach_table
  assessment_roots :: "(String.literal list\<times>isabelle_term) state_family"

definition state_assessment :: "state_rows \<Rightarrow> state_assessment_parts" where
  "state_assessment R=(let A=map fst (state_atoms R); Fs=state_all_families R in
    \<lparr>assessment_subject=map (subject_index A) Fs,
     assessment_mention=map (mention_index A) Fs,
     assessment_root_mention=mention_index A (state_roots R),
     assessment_declarations=declaration_store Fs,
     assessment_rows=family_row_store Fs,
     assessment_reach=state_reach_roots R,
     assessment_roots=state_roots R\<rparr>)"

lemma state_assessment_parts [simp]:

  "assessment_subject (state_assessment R)=map (subject_index (map fst (state_atoms R))) (state_all_families R)"
  "assessment_mention (state_assessment R)=map (mention_index (map fst (state_atoms R))) (state_all_families R)"
  "assessment_root_mention (state_assessment R)=mention_index (map fst (state_atoms R)) (state_roots R)"
  "assessment_declarations (state_assessment R)=declaration_store (state_all_families R)"
  "assessment_rows (state_assessment R)=family_row_store (state_all_families R)"
  "assessment_reach (state_assessment R)=state_reach_roots R"
  "assessment_roots (state_assessment R)=state_roots R"
  by (simp_all add: state_assessment_def Let_def)

lemma assessment_subject_at:
  "kind_item (assessment_subject (state_assessment R)) j=subject_index (map fst (state_atoms R)) (state_entities R j)"
  by (simp add: state_all_families_def comp_def)

lemma assessment_mention_at:
  "kind_item (assessment_mention (state_assessment R)) j=mention_index (map fst (state_atoms R)) (state_entities R j)"
  by (simp add: state_all_families_def comp_def)

subsection \<open>The rows about the subject, from the assessment and the edit\<close>

text \<open>
  The rows of the answer state about the subject are the fibre the request state's subject index
  holds at the subject's key, without the edit's removed rows, followed by the edit's added rows
  about the key: the index's lookup (build 1) and a filter of the edit. Nothing filters the request
  state's whole family.
\<close>

definition assessment_fibres :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key \<Rightarrow> entity_kind list \<Rightarrow>
    isabelle_context state_family list" where
  "assessment_fibres A e k ks=map (\<lambda>j. filter (\<lambda>z. z\<notin>set (edit_removed e j))
    (case store_lookup (kind_item (assessment_subject A) j) k of None \<Rightarrow> [] | Some F \<Rightarrow> F)
    @ subject_fibre k (edit_added e j)) ks"

lemma assessment_fibres_edited:
  assumes atom: "k\<in>set (map fst (state_atoms R))"
  shows "assessment_fibres (state_assessment R) e k ks=edited_fibres R e k ks"
proof -
  have "store_lookup (subject_index (map fst (state_atoms R)) (state_entities R j)) k
      =Some (subject_fibre k (state_entities R j))" for j
    using atom by (simp add: subject_index_lookup)
  then show ?thesis
    by (simp add: assessment_fibres_def edited_fibres_def assessment_subject_at)
qed

text \<open>The keys the edit's removed rows declare: the keys \<open>undeclared\<close>'s incremental part reads about.\<close>

definition edit_removed_declarations :: "state_edit \<Rightarrow> state_key list" where
  "edit_removed_declarations e=concat (map (\<lambda>z. row_declared (snd z))
    (concat (map (edit_removed e) entity_kinds)))"

lemma edit_removed_declared:
  assumes member: "z\<in>edit_rows (edit_removed e)" and declared: "d\<in>set (row_declared (snd z))"
  shows "d\<in>set (edit_removed_declarations e)"
proof -
  obtain j where "z\<in>set (edit_removed e j)" using member by (auto simp: edit_rows_def)
  then have "z\<in>set (concat (map (edit_removed e) entity_kinds))" by auto
  then show ?thesis using declared by (force simp: edit_removed_declarations_def)
qed

subsection \<open>The seeded restricted table and the walk's admission\<close>

text \<open>
  The seeded table \<open>T''\<close> restricted to the keys \<open>V\<close> the walk visits: the reach roots at the seeds outside
  \<open>O\<close> and the answer state's row at every other visited atom. Only the visited keys are read.
\<close>

definition incremental_reach_table :: "state_key list \<Rightarrow> state_key list \<Rightarrow> state_key list \<Rightarrow> (state_key \<Rightarrow> bool) \<Rightarrow>
    'j state_family \<Rightarrow> (state_key \<Rightarrow> state_key list) \<Rightarrow> reach_table" where
  "incremental_reach_table K L V atom Rs P=map (\<lambda>a. if a\<in>set K \<and> a\<notin>set L then (a,True,[])
      else (a,a\<in>set (state_root_keys Rs),P a)) (filter atom (remdups V))"

lemma incremental_reach_table_set:
  "set (incremental_reach_table K L V (\<lambda>a. a\<in>set (map fst As)) Rs (state_reach_predecessors Fs))=
    set (reach_restricted (set V) (edited_reach_table K L (state_reach_table As Rs Fs)))"
proof (rule set_eqI)
  fix w
  show "w\<in>set (incremental_reach_table K L V (\<lambda>a. a\<in>set (map fst As)) Rs (state_reach_predecessors Fs)) \<longleftrightarrow>
      w\<in>set (reach_restricted (set V) (edited_reach_table K L (state_reach_table As Rs Fs)))"
    by (cases w) (auto simp: incremental_reach_table_def reach_restricted_def edited_reach_table_member
      state_reach_table_row split: if_splits)
qed

lemma incremental_reach_table_formed: "reach_table_formed (incremental_reach_table K L V atom Rs P)"
  unfolding reach_table_formed_def single_valued_def by (auto simp: incremental_reach_table_def split: if_splits)

text \<open>
  The walk's product admitted: \<open>O\<close>'s closure and targets by build 5's two native readings, each at the
  indexes it is passed, and its visit set covering the predecessors of every visited atom not seeded and
  the keys of every checked row. The atoms are a predicate, so that the caller reads them from an index
  rather than searching a list. A walk that is refused is judged whole.
\<close>

definition walk_admitted :: "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> factor_term \<Rightarrow> state_edit \<Rightarrow>
    factor_term \<Rightarrow> (state_key \<Rightarrow> state_key list) \<Rightarrow> state_key list \<Rightarrow> (state_key \<Rightarrow> bool) \<Rightarrow>
    state_key list \<Rightarrow> state_key list \<Rightarrow> state_key list \<Rightarrow> isabelle_context state_family list \<Rightarrow> bool" where
  "walk_admitted ident C e I P K atom L V Tg X \<longleftrightarrow>
    (removal_closure,Pair_Term (Pair_Term (keys_term L) C) (keys_term L))
      \<in>positive_meaning edited_reach_system \<and>
    (removal_targets,Pair_Term (Pair_Term (keys_term L) I)
      (state_families_term ident (map (edit_removed e) entity_kinds)))\<in>positive_meaning edited_reach_system \<and>
    (\<forall>k\<in>set V. atom k \<longrightarrow> \<not>(k\<in>set K \<and> k\<notin>set L) \<longrightarrow> set (P k)\<subseteq>set V) \<and>
    (\<forall>G\<in>set X. \<forall>z\<in>set G. set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V)"

subsection \<open>The parts read from the assessment's indexes\<close>

text \<open>
  A fibre of the answer state at a key of the request state is the request state's index looked up at
  the key, the edit's removed rows filtered out and the edit's added rows about the key appended (build
  1's update), for every family: the subject fibres at the keys of \<open>O\<close>, the mention fibres at the keys a
  removed row declares, the root fibres there and the reach predecessors at a visited key.
\<close>

definition index_fibres :: "(isabelle_context state_row \<Rightarrow> state_key list) \<Rightarrow>
    isabelle_context state_family binary_path_store list \<Rightarrow> state_edit \<Rightarrow> state_key \<Rightarrow> isabelle_context state_family list" where
  "index_fibres rd idx e a=map (\<lambda>j. filter (\<lambda>z. z\<notin>set (edit_removed e j))
    (case store_lookup (kind_item idx j) a of None \<Rightarrow> [] | Some F \<Rightarrow> F) @ key_fibre rd a (edit_added e j)) entity_kinds"

lemma key_index_found: "a\<in>set A \<Longrightarrow> store_lookup (key_index rd A F) a=Some (key_fibre rd a F)"
  by (simp add: key_index_lookup)

text \<open>
  A subject index holds a fibre at every atom and at no other key (build 1's index at the atom list), so
  an atom of the request state is a key the index of its first family holds: membership is one lookup of
  an index the assessment already holds, never a search of the atom list. An atom of the answer state is
  an atom of the request state or one the edit appends.
\<close>

definition assessment_atom :: "state_assessment_parts \<Rightarrow> state_key \<Rightarrow> bool" where
  "assessment_atom A a \<longleftrightarrow> store_lookup (kind_item (assessment_subject A) Base_Kind) a\<noteq>None"

definition assessment_edited_atom :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key \<Rightarrow> bool" where
  "assessment_edited_atom A e a \<longleftrightarrow> assessment_atom A a \<or> a\<in>set (map fst (edit_atoms e))"

lemma assessment_atom_exact:
  "assessment_atom (state_assessment R) a \<longleftrightarrow> a\<in>set (map fst (state_atoms R))"
proof (cases "a\<in>set (map fst (state_atoms R))")
  case True
  then show ?thesis by (simp add: assessment_atom_def key_index_found)
next
  case False
  then show ?thesis by (simp add: assessment_atom_def key_index_outside)
qed

text \<open>
  The fibres \<open>O\<close>'s closure reads are the request state's, since the closure reads \<open>R\<close>: the subject index
  looked up at each key of \<open>O\<close>, with no edit, as the targets' are built from the index and the edit.
\<close>

definition assessment_closure_term :: "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> state_assessment_parts \<Rightarrow>
    state_key list \<Rightarrow> factor_term" where
  "assessment_closure_term ident A L=data_list_term (map (\<lambda>j. store_term (state_family_term ident)
    (path_store (map (\<lambda>a. (a,case store_lookup (kind_item (assessment_subject A) j) a of None \<Rightarrow> [] | Some F \<Rightarrow> F)) L)))
    entity_kinds)"

lemma assessment_closure_term_request:
  assumes L: "set L\<subseteq>set (map fst (state_atoms R))"
  shows "assessment_closure_term ident (state_assessment R) L=subject_indexes_term ident L (state_all_families R)"
proof -
  have f: "store_lookup (subject_index (map fst (state_atoms R)) F) a=Some (subject_fibre a F)"
    if "a\<in>set L" for a and F :: "isabelle_context state_family"
    using subsetD[OF L that] by (rule key_index_found)
  show ?thesis
    unfolding assessment_closure_term_def key_indexes_term_def key_index_term_def key_index_def key_rows_def
      state_all_families_def
    by (simp add: f cong: map_cong)
qed

lemma index_fibres_edited:
  assumes atom: "a\<in>set (map fst (state_atoms R))"
  shows "index_fibres rd (map (key_index rd (map fst (state_atoms R))) (state_all_families R)) e a=
    map (key_fibre rd a) (state_all_families (edited_state R e))"
  using atom by (simp add: index_fibres_def state_all_families_def key_index_found edited_state_entities
    key_fibre_edited comp_def)

text \<open>
  The verdict's entry passes one families argument to both \<open>undeclared\<close> and \<open>unreached\<close>, so the
  incremental argument passes one list to both: the edit's added families, the subject fibres at each key of
  \<open>O\<close> and the fibres of the rows mentioning a key a removed row declares, each from the assessment's index
  and the edit, and one family of the rows declaring a key of \<open>O\<close>: the declaration store's row key at each
  such key, read through the row store, less the removed rows, with the edit's added declarers. That family
  is an argument of those two checks only, never a family of a presented state: no program reads its
  position in the list as a kind, and the two checks read rows, never kinds. Each field's lemma takes any
  list between the rows it must check and the state's rows, so the shared list costs work and never truth.
\<close>

definition declared_row :: "state_key binary_path_store \<Rightarrow> (state_key\<times>'i state_row) binary_path_store \<Rightarrow>
    state_key \<Rightarrow> (state_key\<times>'i state_row) list" where
  "declared_row D T a=(case store_lookup D a of None \<Rightarrow> []
    | Some y \<Rightarrow> (case store_lookup T y of None \<Rightarrow> [] | Some z \<Rightarrow> [z]))"

lemma declared_row_member:
  assumes present: "state_presents key S R" and sv: "declarations_single_valued (state_all_families R)"
  shows "z\<in>set (declared_row (declaration_store (state_all_families R)) (family_row_store (state_all_families R)) a) \<longleftrightarrow>
    z\<in>presented_rows R \<and> a\<in>set (row_declared (snd z))"
proof -
  have rows: "single_valued (presented_rows R)" by (rule state_presents_rows_single_valued[OF present])
  have lookup: "store_lookup (declaration_store (state_all_families R)) a=Some y \<longleftrightarrow>
      (\<exists>p. (y,p)\<in>presented_rows R \<and> a\<in>set (row_declared p))" for y
    unfolding declaration_store_at[OF sv] by (auto simp: state_all_families_rows[symmetric])
  let ?D="declaration_store (state_all_families R)" and ?T="family_row_store (state_all_families R)"
  show ?thesis
  proof
    assume zin: "z\<in>set (declared_row (declaration_store (state_all_families R)) (family_row_store (state_all_families R)) a)"
    have "\<exists>y. store_lookup ?D a=Some y \<and> store_lookup ?T y=Some z"
    proof (cases "store_lookup ?D a")
      case None
      then show ?thesis using zin by (simp add: declared_row_def)
    next
      case (Some y)
      show ?thesis
      proof (cases "store_lookup ?T y")
        case None
        then show ?thesis using zin \<open>store_lookup ?D a=Some y\<close> by (simp add: declared_row_def)
      next
        case (Some w)
        then show ?thesis using zin \<open>store_lookup ?D a=Some y\<close> by (simp add: declared_row_def)
      qed
    qed
    then obtain y where y: "store_lookup (declaration_store (state_all_families R)) a=Some y"
      and t: "store_lookup (family_row_store (state_all_families R)) y=Some z"
      by blast
    have zy: "fst z=y" and zR: "z\<in>presented_rows R" using t by (simp_all add: state_row_search[OF present])
    obtain p where p: "(y,p)\<in>presented_rows R" "a\<in>set (row_declared p)" using y lookup by blast
    have "(y,snd z)\<in>presented_rows R" using zR zy by (cases z) simp
    then have "snd z=p" using single_valued_outputs[OF rows] p(1) by blast
    then show "z\<in>presented_rows R \<and> a\<in>set (row_declared (snd z))" using zR p(2) by simp
  next
    assume z: "z\<in>presented_rows R \<and> a\<in>set (row_declared (snd z))"
    have y: "store_lookup (declaration_store (state_all_families R)) a=Some (fst z)"
      using z lookup[of "fst z"] by (cases z) auto
    have t: "store_lookup (family_row_store (state_all_families R)) (fst z)=Some z"
      using z by (simp add: state_row_search[OF present])
    show "z\<in>set (declared_row (declaration_store (state_all_families R)) (family_row_store (state_all_families R)) a)"
      by (simp add: declared_row_def y t)
  qed
qed

definition declaring_family :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key list \<Rightarrow>
    isabelle_context state_family" where
  "declaring_family A e L=filter (\<lambda>z. z\<notin>set (concat (map (edit_removed e) entity_kinds)))
      (concat (map (declared_row (assessment_declarations A) (assessment_rows A)) L)) @
    concat (map (\<lambda>a. key_fibre row_declared a (concat (map (edit_added e) entity_kinds))) L)"

definition assessment_families_checked :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow>
    state_key list \<Rightarrow> state_key list \<Rightarrow> isabelle_context state_family list" where
  "assessment_families_checked A e L ms=map (edit_added e) entity_kinds @
    concat (map (index_fibres row_subjects (assessment_subject A) e) L) @ [declaring_family A e L] @
    concat (map (index_fibres row_mentions (assessment_mention A) e) ms)"

lemma fibres_found:
  assumes fibres: "\<And>a. a\<in>set L \<Longrightarrow> f a=map (key_fibre rd a) Fs"
  shows "(\<exists>G\<in>set (concat (map f L)). z\<in>set G) \<longleftrightarrow>
    (\<exists>F\<in>set Fs. z\<in>set F) \<and> (\<exists>a\<in>set L. a\<in>set (rd (snd z)))"
proof
  assume "\<exists>G\<in>set (concat (map f L)). z\<in>set G"
  then obtain a G where a: "a\<in>set L" and G: "G\<in>set (f a)" and z: "z\<in>set G" by auto
  obtain F where "F\<in>set Fs" "G=key_fibre rd a F" using G fibres[OF a] by auto
  then show "(\<exists>F\<in>set Fs. z\<in>set F) \<and> (\<exists>a\<in>set L. a\<in>set (rd (snd z)))"
    using a z by (auto simp: key_fibre_member)
next
  assume "(\<exists>F\<in>set Fs. z\<in>set F) \<and> (\<exists>a\<in>set L. a\<in>set (rd (snd z)))"
  then obtain F a where F: "F\<in>set Fs" "z\<in>set F" and a: "a\<in>set L" "a\<in>set (rd (snd z))" by blast
  have "key_fibre rd a F\<in>set (f a)" using F(1) fibres[OF a(1)] by simp
  moreover have "z\<in>set (key_fibre rd a F)" using F(2) a(2) by (simp add: key_fibre_member)
  ultimately show "\<exists>G\<in>set (concat (map f L)). z\<in>set G" using a(1) by auto
qed

text \<open>
  The rows the checked families hold are exactly the edit's added rows and the answer state's rows about
  a key of \<open>O\<close> (as a subject or a declaration) or mentioning a key a removed row declares: a sound and
  complete list for both checks, read from the assessment and the edit alone.
\<close>

lemma assessment_families_checked_rows:
  assumes present: "state_presents key S R" and sv: "declarations_single_valued (state_all_families R)"
    and reduced: "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and L: "set L\<subseteq>set (map fst (state_atoms R))" and ms: "set ms\<subseteq>set (map fst (state_atoms R))"
  shows "(\<exists>G\<in>set (assessment_families_checked (state_assessment R) e L ms). z\<in>set G) \<longleftrightarrow>
    (\<exists>j. z\<in>set (edit_added e j)) \<or>
    z\<in>presented_rows (edited_state R e) \<and> (\<exists>a\<in>set L. a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z))) \<or>
    z\<in>presented_rows (edited_state R e) \<and> (\<exists>a\<in>set ms. a\<in>set (row_mentions (snd z)))"
proof -
  let ?A="state_assessment R" and ?Fs'="state_all_families (edited_state R e)" and ?R'="edited_state R e"
  have answer: "(\<exists>F\<in>set ?Fs'. z\<in>set F) \<longleftrightarrow> z\<in>presented_rows ?R'"
    by (auto simp: state_all_families_rows[symmetric])
  have rows': "presented_rows ?R'=presented_rows R-edit_rows (edit_removed e)\<union>edit_rows (edit_added e)"
    using reduced by (simp add: edit_reduced_def)
  have subjects: "index_fibres row_subjects (assessment_subject ?A) e a=map (key_fibre row_subjects a) ?Fs'"
    if "a\<in>set L" for a
    using that L by (simp only: state_assessment_parts) (rule index_fibres_edited, blast)
  have mentions: "index_fibres row_mentions (assessment_mention ?A) e a=map (key_fibre row_mentions a) ?Fs'"
    if "a\<in>set ms" for a
    using that ms by (simp only: state_assessment_parts) (rule index_fibres_edited, blast)
  have kept: "z\<in>set (concat (map (declared_row (assessment_declarations ?A) (assessment_rows ?A)) L)) \<longleftrightarrow>
      z\<in>presented_rows R \<and> (\<exists>a\<in>set L. a\<in>set (row_declared (snd z)))"
    unfolding state_assessment_parts using declared_row_member[OF present sv] by auto
  have removed: "z\<in>set (concat (map (edit_removed e) entity_kinds)) \<longleftrightarrow> z\<in>edit_rows (edit_removed e)"
    by (auto simp: edit_rows_def)
  have added: "(\<exists>a\<in>set L. z\<in>set (key_fibre row_declared a (concat (map (edit_added e) entity_kinds)))) \<longleftrightarrow>
      z\<in>edit_rows (edit_added e) \<and> (\<exists>a\<in>set L. a\<in>set (row_declared (snd z)))"
    by (auto simp: key_fibre_member edit_rows_def)
  have declaring: "z\<in>set (declaring_family ?A e L) \<longleftrightarrow>
      z\<in>presented_rows ?R' \<and> (\<exists>a\<in>set L. a\<in>set (row_declared (snd z)))"
  proof -
    have "z\<in>set (declaring_family ?A e L) \<longleftrightarrow>
        (z\<in>set (concat (map (declared_row (assessment_declarations ?A) (assessment_rows ?A)) L)) \<and>
          z\<notin>set (concat (map (edit_removed e) entity_kinds))) \<or>
        (\<exists>a\<in>set L. z\<in>set (key_fibre row_declared a (concat (map (edit_added e) entity_kinds))))"
      by (simp add: declaring_family_def)
    then show ?thesis unfolding kept removed added rows' by auto
  qed
  have parts: "(\<exists>G\<in>set (assessment_families_checked ?A e L ms). z\<in>set G) \<longleftrightarrow>
      (\<exists>j. z\<in>set (edit_added e j)) \<or>
      (\<exists>G\<in>set (concat (map (index_fibres row_subjects (assessment_subject ?A) e) L)). z\<in>set G) \<or>
      z\<in>set (declaring_family ?A e L) \<or>
      (\<exists>G\<in>set (concat (map (index_fibres row_mentions (assessment_mention ?A) e) ms)). z\<in>set G)"
    by (auto simp: assessment_families_checked_def)
  have sub: "(\<exists>G\<in>set (concat (map (index_fibres row_subjects (assessment_subject ?A) e) L)). z\<in>set G) \<longleftrightarrow>
      z\<in>presented_rows ?R' \<and> (\<exists>a\<in>set L. a\<in>set (row_subjects (snd z)))"
    using fibres_found[of L "index_fibres row_subjects (assessment_subject ?A) e" row_subjects ?Fs' z, OF subjects]
    unfolding answer .
  have men: "(\<exists>G\<in>set (concat (map (index_fibres row_mentions (assessment_mention ?A) e) ms)). z\<in>set G) \<longleftrightarrow>
      z\<in>presented_rows ?R' \<and> (\<exists>a\<in>set ms. a\<in>set (row_mentions (snd z)))"
    using fibres_found[of ms "index_fibres row_mentions (assessment_mention ?A) e" row_mentions ?Fs' z, OF mentions]
    unfolding answer .
  show ?thesis
    unfolding parts sub men declaring by blast
qed

definition root_fibres :: "state_assessment_parts \<Rightarrow> state_key list \<Rightarrow> (String.literal list\<times>isabelle_term) state_family" where
  "root_fibres A ms=concat (map (\<lambda>a. case store_lookup (assessment_root_mention A) a of None \<Rightarrow> [] | Some F \<Rightarrow> F) ms)"

lemma root_fibres_edited:
  assumes ms: "set ms\<subseteq>set (map fst (state_atoms R))"
  shows "root_fibres (state_assessment R) ms=edited_undeclared_roots (state_roots R) ms"
  using ms by (induction ms) (simp_all add: root_fibres_def edited_undeclared_roots_def key_index_found)

text \<open>
  The answer state's store of declarations at the keys \<open>undeclared\<close> reads is the request state's declaration
  store looked up at each key, less the keys a removed row declares, with the edit's added declarations. Under
  the single-declaration fact of the request state (@{const declarations_single_valued}, which the exporter's
  @{const isabelle_declared_once} gives every state it defines), the looked-up row is the key's one declaring
  row, so a removed declaration is exactly a removed row's. An edit that would declare a key a kept row
  declares, or declare one key twice, has no incremental form: its answer is judged whole.
\<close>

definition kept_declaration :: "state_key binary_path_store \<Rightarrow> state_key list \<Rightarrow> state_key \<Rightarrow>
    (state_key\<times>state_key) list" where
  "kept_declaration D RD q=(if q\<in>set RD then [] else case store_lookup D q of None \<Rightarrow> [] | Some y \<Rightarrow> [(q,y)])"

lemma kept_declaration_member:
  "(a,y)\<in>set (kept_declaration D RD q) \<longleftrightarrow> a=q \<and> q\<notin>set RD \<and> store_lookup D q=Some y"
  by (cases "store_lookup D q") (auto simp: kept_declaration_def)

definition edit_added_declarations :: "state_edit \<Rightarrow> (state_key\<times>state_key) list" where
  "edit_added_declarations e=declaration_rows (map (edit_added e) entity_kinds)"

definition assessment_declaration_rows :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key list \<Rightarrow>
    (state_key\<times>state_key) list" where
  "assessment_declaration_rows A e ms=
    concat (map (kept_declaration (assessment_declarations A) (edit_removed_declarations e)) ms) @
    filter (\<lambda>r. fst r\<in>set ms) (edit_added_declarations e)"

definition edit_declarations_fresh :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> bool" where
  "edit_declarations_fresh A e \<longleftrightarrow> distinct (map fst (edit_added_declarations e)) \<and>
    list_all (\<lambda>r. fst r\<in>set (edit_removed_declarations e) \<or> store_lookup (assessment_declarations A) (fst r)=None)
      (edit_added_declarations e)"

definition assessment_declaration_term :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key list \<Rightarrow> factor_term" where
  "assessment_declaration_term A e ms=store_term path_term (path_store (assessment_declaration_rows A e ms))"

lemma assessment_declaration_rows_edited:
  fixes R :: state_rows and e :: state_edit and ms :: "state_key list"
  defines "Fs'\<equiv>state_all_families (edited_state R e)"
  assumes sv: "declarations_single_valued (state_all_families R)"
    and reduced: "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and gone: "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and fresh: "edit_declarations_fresh (state_assessment R) e"
  shows "path_store (assessment_declaration_rows (state_assessment R) e ms)=
    path_store (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs'))"
proof -
  let ?A="state_assessment R" and ?D="declaration_store (state_all_families R)"
  let ?RD="set (edit_removed_declarations e)" and ?Ad="edit_added_declarations e" and ?R'="edited_state R e"
  have lookup: "store_lookup ?D q=Some y \<longleftrightarrow> (\<exists>p. (y,p)\<in>presented_rows R \<and> q\<in>set (row_declared p))" for q y
    unfolding declaration_store_at[OF sv] by (auto simp: state_all_families_rows[symmetric])
  have answer_rows: "(\<Union>F\<in>set Fs'. set F)=presented_rows R-edit_rows (edit_removed e)\<union>edit_rows (edit_added e)"
    using reduced unfolding Fs'_def by (simp add: state_all_families_rows edit_reduced_def)
  have within: "edit_rows (edit_removed e)\<subseteq>presented_rows R" using reduced by (simp add: edit_reduced_def)
  have answer: "(q,y)\<in>set (declaration_rows Fs') \<longleftrightarrow>
      (\<exists>p. ((y,p)\<in>presented_rows R \<and> (y,p)\<notin>edit_rows (edit_removed e) \<or> (y,p)\<in>edit_rows (edit_added e)) \<and>
        q\<in>set (row_declared p))" for q y
  proof -
    have "(q,y)\<in>set (declaration_rows Fs') \<longleftrightarrow> (\<exists>p. (y,p)\<in>(\<Union>F\<in>set Fs'. set F) \<and> q\<in>set (row_declared p))"
      by (auto simp: declaration_rows_member)
    then show ?thesis unfolding answer_rows by auto
  qed
  have added: "(q,b)\<in>set ?Ad \<longleftrightarrow> (\<exists>p. (b,p)\<in>edit_rows (edit_added e) \<and> q\<in>set (row_declared p))" for q b
    by (auto simp: edit_added_declarations_def declaration_rows_member edit_rows_def)
  have removed_declared: "\<exists>z\<in>edit_rows (edit_removed e). q\<in>set (row_declared (snd z))" if "q\<in>?RD" for q
    using that by (force simp: edit_removed_declarations_def edit_rows_def)
  have kept: "(q\<notin>?RD \<and> store_lookup ?D q=Some y) \<longleftrightarrow>
      (\<exists>p. (y,p)\<in>presented_rows R \<and> (y,p)\<notin>edit_rows (edit_removed e) \<and> q\<in>set (row_declared p))" for q y
  proof
    assume l: "q\<notin>?RD \<and> store_lookup ?D q=Some y"
    then obtain p where p: "(y,p)\<in>presented_rows R" "q\<in>set (row_declared p)" using lookup[of q y] by blast
    have "(y,p)\<notin>edit_rows (edit_removed e)"
      using l p(2) edit_removed_declared[of "(y,p)" e q] by auto
    then show "\<exists>p. (y,p)\<in>presented_rows R \<and> (y,p)\<notin>edit_rows (edit_removed e) \<and> q\<in>set (row_declared p)"
      using p by blast
  next
    assume "\<exists>p. (y,p)\<in>presented_rows R \<and> (y,p)\<notin>edit_rows (edit_removed e) \<and> q\<in>set (row_declared p)"
    then obtain p where p: "(y,p)\<in>presented_rows R" "(y,p)\<notin>edit_rows (edit_removed e)" "q\<in>set (row_declared p)"
      by blast
    have found: "store_lookup ?D q=Some y" using lookup[of q y] p(1) p(3) by blast
    have "q\<notin>?RD"
    proof
      assume "q\<in>?RD"
      then obtain z where z: "z\<in>edit_rows (edit_removed e)" "q\<in>set (row_declared (snd z))"
        using removed_declared by blast
      obtain y' p' where zy: "z=(y',p')" by (cases z)
      have zR: "(y',p')\<in>presented_rows R" using z(1) within zy by blast
      then have "store_lookup ?D q=Some y'" using lookup[of q y'] z(2) zy by auto
      then have yy: "y'=y" using found by simp
      have "(y,p)\<in>presented_rows ?R'" using reduced p(1) p(2) by (auto simp: edit_reduced_def)
      then have "y\<in>fst ` presented_rows ?R'" by force
      then show False using gone[of y' p'] z(1) zy yy by simp
    qed
    then show "q\<notin>?RD \<and> store_lookup ?D q=Some y" using found by blast
  qed
  have fresh_distinct: "distinct (map fst ?Ad)"
    and fresh_keys: "\<And>q b. (q,b)\<in>set ?Ad \<Longrightarrow> q\<in>?RD \<or> store_lookup ?D q=None"
    using fresh by (auto simp: edit_declarations_fresh_def list_all_iff)
  have member: "(q,y)\<in>set (assessment_declaration_rows ?A e ms) \<longleftrightarrow>
      q\<in>set ms \<and> ((q\<notin>?RD \<and> store_lookup ?D q=Some y) \<or> (q,y)\<in>set ?Ad)" for q y
    by (auto simp: assessment_declaration_rows_def kept_declaration_member)
  have target: "(q,y)\<in>set (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs')) \<longleftrightarrow>
      q\<in>set ms \<and> ((q\<notin>?RD \<and> store_lookup ?D q=Some y) \<or> (q,y)\<in>set ?Ad)" for q y
  proof -
    have "(q,y)\<in>set (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs')) \<longleftrightarrow> q\<in>set ms \<and>
        ((\<exists>p. (y,p)\<in>presented_rows R \<and> (y,p)\<notin>edit_rows (edit_removed e) \<and> q\<in>set (row_declared p)) \<or>
         (\<exists>p. (y,p)\<in>edit_rows (edit_added e) \<and> q\<in>set (row_declared p)))"
      by (auto simp: answer)
    then show ?thesis by (simp only: kept[symmetric] added[symmetric] simp_thms)
  qed
  have same: "set (assessment_declaration_rows ?A e ms)=set (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs'))"
    by (simp only: set_eq_iff split_paired_All member target simp_thms)
  have sv_added: "single_valued (set ?Ad)" using fresh_distinct by (simp add: distinct_keys_iff)
  have sv_rows: "single_valued (set (assessment_declaration_rows ?A e ms))"
    unfolding single_valued_def
  proof (intro allI impI)
    fix q y y' assume a: "(q,y)\<in>set (assessment_declaration_rows ?A e ms)"
      and b: "(q,y')\<in>set (assessment_declaration_rows ?A e ms)"
    have a': "q\<notin>?RD \<and> store_lookup ?D q=Some y \<or> (q,y)\<in>set ?Ad" using a unfolding member by blast
    have b': "q\<notin>?RD \<and> store_lookup ?D q=Some y' \<or> (q,y')\<in>set ?Ad" using b unfolding member by blast
    show "y=y'"
      using a' b' fresh_keys[of q y] fresh_keys[of q y'] single_valued_outputs[OF sv_added, of q y y'] by auto
  qed
  have sv_target: "single_valued (set (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs')))"
    using sv_rows by (simp only: same)
  show ?thesis by (rule path_store_rows[OF sv_rows sv_target same])
qed

lemma assessment_declaration_term_edited:
  assumes sv: "declarations_single_valued (state_all_families R)"
    and reduced: "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and gone: "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and fresh: "edit_declarations_fresh (state_assessment R) e"
  shows "assessment_declaration_term (state_assessment R) e ms=
    restricted_declaration_term ms (state_all_families (edited_state R e))"
  unfolding assessment_declaration_term_def restricted_declaration_term_def
  by (simp only: assessment_declaration_rows_edited[OF sv reduced gone fresh])

text \<open>
  A presented state's rows mention only its atoms, so at a key new to the answer state the request state's
  index holds no fibre and the edit's added rows are all of it: the reach predecessors at every visited key
  are read from the mention index and the edit.
\<close>

lemma presented_mentions_atoms:
  assumes present: "state_presents key S R" and row: "(b,p)\<in>set (state_entities R j)"
    and m: "a\<in>set (row_mentions p)"
  shows "a\<in>set (map fst (state_atoms R))"
proof -
  obtain g where g: "g\<in>set (snd (snd S))" "p=entity_row key (snd S) g"
    by (rule state_presents_row_origin[OF present row]) blast
  obtain d where d: "d\<in>set (entity_mentions g)" "a=key d" using m g(2) by (auto simp: entity_row_def)
  have "d<length (fst (snd S))" by (rule state_presents_mentions_inside[OF present g(1) d(1)])
  moreover have "set (state_atoms R)=(\<lambda>i. (key i,fst (snd S)!i)) ` {..<length (fst (snd S))}"
    using state_presents_atoms[OF present] by (simp add: atoms_present_def)
  ultimately show ?thesis using d(2) by force
qed

definition assessment_predecessors :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key \<Rightarrow> state_key list" where
  "assessment_predecessors A e a=
    concat (map (\<lambda>F. concat (map (\<lambda>z. row_subjects (snd z)) F)) (index_fibres row_mentions (assessment_mention A) e a))"

lemma assessment_predecessors_edited:
  assumes present: "state_presents key S R"
  shows "assessment_predecessors (state_assessment R) e=state_reach_predecessors (state_all_families (edited_state R e))"
proof (rule ext)
  fix a
  have "index_fibres row_mentions (map (mention_index (map fst (state_atoms R))) (state_all_families R)) e a=
      map (key_fibre row_mentions a) (state_all_families (edited_state R e))"
  proof (cases "a\<in>set (map fst (state_atoms R))")
    case True
    then show ?thesis by (rule index_fibres_edited)
  next
    case False
    have none: "key_fibre row_mentions a (state_entities R j)=[]" for j
      using False presented_mentions_atoms[OF present] by (force simp: key_fibre_def filter_empty_conv)
    show ?thesis
      by (simp add: index_fibres_def state_all_families_def key_index_outside[OF False] edited_state_entities
        key_fibre_edited none comp_def)
  qed
  then show "assessment_predecessors (state_assessment R) e a=state_reach_predecessors (state_all_families (edited_state R e)) a"
    by (simp add: assessment_predecessors_def state_reach_predecessors_def comp_def)
qed

text \<open>The targets' subject indexes at the keys \<open>Tg\<close>: each kind's store at \<open>Tg\<close>, its fibres from the subject index
  and the edit.\<close>

definition kind_index_fibre :: "(isabelle_context state_row \<Rightarrow> state_key list) \<Rightarrow>
    isabelle_context state_family binary_path_store list \<Rightarrow> state_edit \<Rightarrow> entity_kind \<Rightarrow> state_key \<Rightarrow>
    isabelle_context state_family" where
  "kind_index_fibre rd idx e j a=filter (\<lambda>z. z\<notin>set (edit_removed e j))
    (case store_lookup (kind_item idx j) a of None \<Rightarrow> [] | Some F \<Rightarrow> F) @ key_fibre rd a (edit_added e j)"

definition assessment_indexes_term :: "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> state_assessment_parts \<Rightarrow>
    state_edit \<Rightarrow> state_key list \<Rightarrow> factor_term" where
  "assessment_indexes_term ident A e Tg=data_list_term (map (\<lambda>j. store_term (state_family_term ident)
    (path_store (map (\<lambda>a. (a,kind_index_fibre row_subjects (assessment_subject A) e j a)) Tg))) entity_kinds)"

lemma assessment_indexes_term_edited:
  assumes Tg: "set Tg\<subseteq>set (map fst (state_atoms R))"
  shows "assessment_indexes_term ident (state_assessment R) e Tg=
    subject_indexes_term ident Tg (state_all_families (edited_state R e))"
proof -
  have f: "store_lookup (subject_index (map fst (state_atoms R)) F) a=Some (subject_fibre a F)"
    if "a\<in>set Tg" for a and F :: "isabelle_context state_family"
    using subsetD[OF Tg that] by (rule key_index_found)
  show ?thesis
    unfolding assessment_indexes_term_def key_indexes_term_def key_index_term_def key_index_def key_rows_def
      state_all_families_def
    by (simp add: kind_index_fibre_def f edited_state_entities key_fibre_edited cong: map_cong)
qed

subsection \<open>The incremental argument\<close>

text \<open>
  The verdict's argument at the edit's parts: every part built from the assessment, the edit, and the
  walk's \<open>O\<close> and visit set. The subject's fibres come from the assessment's subject index, the restricted
  declaration store from its declaration store and the edit, the atoms from its subject index; the removed
  and added rows are the edit's own. No family of the answer state is computed.
\<close>

definition incremental_verdict_argument ::
    "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow> ((String.literal list\<times>isabelle_term) \<Rightarrow> factor_term) \<Rightarrow>
      state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key list \<Rightarrow>
      state_key list \<Rightarrow> state_key \<Rightarrow> state_key list \<Rightarrow> entity_kind list \<Rightarrow> entity_kind list \<Rightarrow> factor_term" where
  "incremental_verdict_argument ident identr A e L V k ks kr kd=
    (let X=assessment_families_checked A e L (edit_removed_declarations e);
      Rc=root_fibres A (edit_removed_declarations e) in
    term_tuple [path_term k,
      state_families_term ident (assessment_fibres A e k kd),
      keys_term ks,
      subject_indexes_term ident [k] (assessment_fibres A e k kr),
      state_families_term ident (map (edit_added e) (kinds_outside [Specification_Kind])),
      assessment_declaration_term A e (edited_undeclared_keys X Rc),
      state_families_term ident X,
      state_family_term identr Rc,
      reach_table_term (incremental_reach_table (map fst (assessment_reach A)) L V
        (assessment_edited_atom A e) (assessment_roots A) (assessment_predecessors A e)),
      store_term (state_row_term ident) empty_row_store,
      state_families_term ident (map (edit_removed e) kr),
      state_families_term ident (map (edit_removed e) (kinds_outside kr)),
      store_term (state_row_term ident) empty_row_store,
      state_families_term ident (map (edit_added e) kr),
      state_families_term ident (map (edit_added e) (kinds_outside kr)),
      keys_term (map fst (assessment_roots A)),
      keys_term (map fst (assessment_roots A))])"

lemma reach_roots_keys: "map fst (state_reach_roots R)=state_reach_seeds R"
  by (simp add: state_reach_roots_def comp_def)

lemma edited_atoms_keys: "map fst (state_atoms (edited_state R e))=map fst (state_atoms R) @ map fst (edit_atoms e)"
  by (simp add: edited_state_def)

lemma assessment_edited_atom_exact:
  "assessment_edited_atom (state_assessment R) e=(\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e))))"
  by (simp add: fun_eq_iff assessment_edited_atom_def assessment_atom_exact edited_atoms_keys)

subsection \<open>The field programs keep their meanings in the verdict's program\<close>

lemma verdict_sites:
  "verdict_statements\<in>fst ` set verdict_rows_definitions"
  "verdict_formed\<in>fst ` set verdict_rows_definitions"
  "verdict_excess\<in>fst ` set verdict_mentions_definitions"
  "verdict_undeclared\<in>fst ` set verdict_mentions_definitions"
  "verdict_unreached\<in>fst ` set verdict_unreached_definitions"
  "verdict_removed\<in>fst ` set verdict_difference_definitions"
  "verdict_added\<in>fst ` set verdict_difference_definitions"
  "verdict_roots\<in>fst ` set verdict_difference_definitions"
  by (simp_all add: verdict_rows_definitions_def verdict_mentions_definitions_def
    verdict_unreached_definitions_def verdict_difference_definitions_def)

lemmas statements_here = native_verdict_rows_field[OF verdict_sites(1)]
lemmas formed_here = native_verdict_rows_field[OF verdict_sites(2)]
lemmas excess_here = native_verdict_mentions_field[OF verdict_sites(3)]
lemmas undeclared_here = native_verdict_mentions_field[OF verdict_sites(4)]
lemmas unreached_here = native_verdict_unreached_field[OF verdict_sites(5)]
lemmas removed_here = native_verdict_difference_field[OF verdict_sites(6)]
lemmas added_here = native_verdict_difference_field[OF verdict_sites(7)]
lemmas roots_here = native_verdict_difference_field[OF verdict_sites(8)]

subsection \<open>The premises the incremental judgment consumes\<close>

text \<open>
  The request state \<open>R\<close> presented, the edit with its constructor's facts (the answer state presented,
  the keys shared, the edit reduced), the subject an atom of \<open>R\<close>, the two kind selections by
  \<open>kinds_present\<close>, and the premise that \<open>R\<close> is closed. The three closedness facts are the premise
  \<open>P\<close>(i); the stage's equation below decides them natively, once per request state. The request's
  support, by \<open>request_presents\<close>, enters only \<open>incremental_accepted\<close>, which reads the verdict it states.
\<close>

locale incremental_verdict = edited_local +
  fixes identr :: "(String.literal list\<times>isabelle_term) \<Rightarrow> factor_term"
    and k :: state_key and ks :: "state_key list"
    and replaceable :: "isabelle_entity \<Rightarrow> bool" and demanded :: "isabelle_entity \<Rightarrow> bool"
    and kr :: "entity_kind list" and kd :: "entity_kind list"
  assumes roots_identity: "\<And>y. term_formed (identr y)"
    and subject_atom: "k\<in>set (map fst (state_atoms R))"
    and replaceable_kinds: "kinds_present replaceable (set kr)"
    and demanded_kinds: "kinds_present demanded (set kd)"
    and reduced: "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and closed_malformed: "isabelle_malformed_entities (snd S)=[]"
    and closed_undeclared: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and closed_unreached: "isabelle_unreached_entities (fst S) (snd S)=[]"
begin

lemma atoms_grow: "length (fst (snd S))\<le>length (fst (snd S'))"
proof -
  have atoms: "state_atoms (edited_state R e)=state_atoms R@edit_atoms e" by (simp add: edited_state_def)
  have a1: "length (state_atoms R)=length (fst (snd S))"
    using state_presents_atoms[OF request] by (simp add: atoms_present_def)
  have a2: "length (state_atoms (edited_state R e))=length (fst (snd S'))"
    using state_presents_atoms[OF answer] by (simp add: atoms_present_def)
  show ?thesis using a1 a2 by (simp add: atoms)
qed

lemma request_subject:
  "\<exists>c. k=key c \<and> c<length (fst (snd S)) \<and> c<length (fst (snd S')) \<and> k\<in>set (map fst (state_atoms R))"
proof -
  obtain nm where kn: "(k,nm)\<in>set (state_atoms R)" using subject_atom by auto
  have "set (state_atoms R)=(\<lambda>i. (key i,fst (snd S)!i)) ` {..<length (fst (snd S))}"
    using state_presents_atoms[OF request] by (simp add: atoms_present_def)
  then obtain c where c: "c<length (fst (snd S))" and kc: "(k,nm)=(key c,fst (snd S)!c)" using kn by auto
  have "c<length (fst (snd S'))" using c atoms_grow by simp
  then show ?thesis using c kc subject_atom by auto
qed

subsection \<open>The eight fields at the edit's parts\<close>

lemma incremental_statements:
  "(verdict_statements,Pair_Term (path_term k)
      (state_families_term ident (assessment_fibres (state_assessment R) e k kd)))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_statements,Pair_Term (path_term k)
      (state_families_term ident (map (state_entities (edited_state R e)) kd)))
      \<in>positive_meaning native_verdict_system"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S'))"
      and atom: "k\<in>set (map fst (state_atoms R))"
    using request_subject by blast
  have fibres: "assessment_fibres (state_assessment R) e k kd=edited_fibres R e k kd"
    by (rule assessment_fibres_edited[OF atom])
  show ?thesis
    unfolding fibres using edited_statements(1)[OF demanded_kinds bound] by (simp add: statements_here kc)
qed

lemma incremental_excess:
  "(verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks))
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks))
      (subject_indexes_term ident (map fst (state_atoms (edited_state R e)))
        (map (state_entities (edited_state R e)) kr)))
      \<in>positive_meaning native_verdict_system"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S'))"
      and atom: "k\<in>set (map fst (state_atoms R))"
    using request_subject by blast
  have support: "key d\<in>set ks \<longleftrightarrow>
      d |\<in>| fset_of_list (filter (\<lambda>d. key d\<in>set ks) [0..<length (fst (snd S'))])"
    if "d<length (fst (snd S'))" for d
    using that by (simp add: fset_of_list_elem)
  have fibres: "assessment_fibres (state_assessment R) e k kr=edited_fibres R e k kr"
    by (rule assessment_fibres_edited[OF atom])
  show ?thesis
    unfolding fibres using edited_excess(1)[OF replaceable_kinds bound support] by (simp add: excess_here kc)
qed

lemma incremental_formed:
  "(verdict_formed,Pair_Term (path_term k)
      (state_families_term ident (map (edit_added e) (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_formed,Pair_Term (path_term k)
      (state_families_term ident (map (state_entities (edited_state R e)) (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning native_verdict_system"
proof -
  have kinds: "set (kinds_outside [Specification_Kind])=- {Specification_Kind}" by simp
  have sel: "set (map (state_entities R) (kinds_outside [Specification_Kind]))
      =state_entities R ` (- {Specification_Kind})" by simp
  have closed: "(verdict_formed,Pair_Term (path_term k)
      (state_families_term ident (map (state_entities R) (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning verdict_rows_system"
    using native_formed_exact_specifications[OF request sel identity path_term_formed] closed_malformed
    by simp
  show ?thesis using edited_formed(1)[OF kinds path_term_formed closed] by (simp add: formed_here)
qed

lemma incremental_removed:
  "(verdict_removed,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term k))
      (Pair_Term (state_families_term ident (map (edit_removed e) kr))
        (state_families_term ident (map (edit_removed e) (kinds_outside kr)))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_removed,Pair_Term (Pair_Term (family_row_term ident (state_all_families (edited_state R e)))
      (path_term k)) (Pair_Term (state_families_term ident (map (state_entities R) kr))
        (state_families_term ident (map (state_entities R) (kinds_outside kr)))))
      \<in>positive_meaning native_verdict_system"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S))" using request_subject by blast
  have other: "set (kinds_outside kr)=- set kr" by simp
  show ?thesis
    using edited_removed(1)[OF replaceable_kinds other bound] by (simp add: removed_here kc)
qed

lemma incremental_added:
  "(verdict_added,Pair_Term (Pair_Term (store_term (state_row_term ident) empty_row_store) (path_term k))
      (Pair_Term (state_families_term ident (map (edit_added e) kr))
        (state_families_term ident (map (edit_added e) (kinds_outside kr)))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_added,Pair_Term (Pair_Term (family_row_term ident (state_all_families R)) (path_term k))
      (Pair_Term (state_families_term ident (map (state_entities (edited_state R e)) kr))
        (state_families_term ident (map (state_entities (edited_state R e)) (kinds_outside kr)))))
      \<in>positive_meaning native_verdict_system"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S'))" using request_subject by blast
  have other: "set (kinds_outside kr)=- set kr" by simp
  show ?thesis
    using edited_added(1)[OF replaceable_kinds other bound] by (simp add: added_here kc)
qed

lemma incremental_roots:
  "(verdict_roots,Pair_Term (keys_term (map fst (state_roots R))) (keys_term (map fst (state_roots R))))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_roots,Pair_Term (keys_term (map fst (state_roots R)))
      (keys_term (map fst (state_roots (edited_state R e)))))\<in>positive_meaning native_verdict_system"
  using edited_roots(1) by (simp add: roots_here)

lemma in_answer:
  assumes "z\<in>set (edit_added e j)"
  shows "z\<in>(\<Union>F\<in>set (state_all_families (edited_state R e)). set F)"
proof -
  have "z\<in>set (state_entities (edited_state R e) j)" using assms edited_state_member by blast
  then show ?thesis by (auto simp: state_all_families_range)
qed

lemma incremental_undeclared:
  fixes L :: "state_key list"
  defines "X\<equiv>assessment_families_checked (state_assessment R) e L (edit_removed_declarations e)"
    and "Rc\<equiv>edited_undeclared_roots (state_roots R) (edit_removed_declarations e)"
  assumes L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
    and ms_atoms: "set (edit_removed_declarations e)\<subseteq>set (map fst (state_atoms R))"
    and single: "declarations_single_valued (state_all_families R)"
  shows "(verdict_undeclared,Pair_Term (restricted_declaration_term (edited_undeclared_keys X Rc)
        (state_all_families (edited_state R e)))
      (Pair_Term (state_families_term ident X) (state_family_term identr Rc)))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_undeclared,Pair_Term (declaration_term (state_all_families (edited_state R e)))
      (Pair_Term (state_families_term ident (state_all_families (edited_state R e)))
        (state_family_term identr (state_roots (edited_state R e)))))\<in>positive_meaning native_verdict_system"
proof -
  let ?Fs'="state_all_families (edited_state R e)"
  let ?ms="edit_removed_declarations e"
  have closed: "(verdict_undeclared,Pair_Term (declaration_term (state_all_families R))
      (Pair_Term (state_families_term ident (state_all_families R)) (state_family_term identr (state_roots R))))
      \<in>positive_meaning verdict_mentions_system"
    using native_undeclared_exact[OF request state_all_families_range identity roots_identity]
      closed_undeclared by simp
  have rows: "(\<Union>F\<in>set (state_all_families (edited_state R e)). set F)=
      (\<Union>F\<in>set (state_all_families R). set F)-edit_rows (edit_removed e) \<union>
      (\<Union>F\<in>set (map (edit_added e) entity_kinds). set F)"
    unfolding edit_rows_kinds using reduced by (simp add: state_all_families_rows edit_reduced_def)
  have keys: "d\<in>set (edit_removed_declarations e)"
    if "z\<in>edit_rows (edit_removed e)" "d\<in>set (row_declared (snd z))" for z d
    using that by (rule edit_removed_declared)
  have rows': "(\<Union>F\<in>set ?Fs'. set F)=(\<Union>F\<in>set (state_all_families R). set F)-edit_rows (edit_removed e) \<union>
      (\<Union>F\<in>set (map (edit_added e) entity_kinds). set F)"
    by (rule rows)
  note found = assessment_families_checked_rows[OF request single reduced L_atoms ms_atoms]
  have sound: "z\<in>(\<Union>F\<in>set ?Fs'. set F)" if "z\<in>(\<Union>G\<in>set X. set G)" for z
  proof -
    have "(\<exists>j. z\<in>set (edit_added e j)) \<or> z\<in>presented_rows (edited_state R e)"
      using that found[of z] unfolding X_def by blast
    then show ?thesis
    proof
      assume "\<exists>j. z\<in>set (edit_added e j)"
      then obtain j where "z\<in>set (edit_added e j)" by blast
      then show ?thesis by (rule in_answer)
    next
      assume "z\<in>presented_rows (edited_state R e)"
      then show ?thesis by (simp add: state_all_families_rows)
    qed
  qed
  have added: "z\<in>(\<Union>G\<in>set X. set G)" if "z\<in>(\<Union>F\<in>set (map (edit_added e) entity_kinds). set F)" for z
  proof -
    have "\<exists>j. z\<in>set (edit_added e j)" using that by auto
    then show ?thesis using found[of z] unfolding X_def by blast
  qed
  have mentioning: "z\<in>(\<Union>G\<in>set X. set G)"
    if zin: "z\<in>(\<Union>F\<in>set ?Fs'. set F)" and am: "a\<in>set ?ms" "a\<in>set (row_mentions (snd z))" for z a
  proof -
    have "z\<in>presented_rows (edited_state R e)" using zin by (simp add: state_all_families_rows)
    then show ?thesis using am found[of z] unfolding X_def by blast
  qed
  have sroots: "z\<in>set (state_roots R)" if "z\<in>set Rc" for z
    using that unfolding Rc_def edited_undeclared_roots_member by blast
  have croots: "z\<in>set Rc" if "z\<in>set (state_roots R)" "a\<in>set ?ms" "a\<in>set (row_mentions (snd z))" for z a
    using that unfolding Rc_def edited_undeclared_roots_member by blast
  have store: "store_lookup (path_store (filter (\<lambda>r. fst r\<in>set (edited_undeclared_keys X Rc))
        (declaration_rows ?Fs'))) q\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') q\<noteq>None"
    if "z\<in>(\<Union>G\<in>set X. set G)" "q\<in>set (row_mentions (snd z))" for z q
    using that by (rule edited_undeclared_keys_store)
  have store_roots: "store_lookup (path_store (filter (\<lambda>r. fst r\<in>set (edited_undeclared_keys X Rc))
        (declaration_rows ?Fs'))) q\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') q\<noteq>None"
    if "z\<in>set Rc" "q\<in>set (row_mentions (snd z))" for z q
    using that by (rule edited_undeclared_keys_store_roots)
  have "(verdict_undeclared,Pair_Term (restricted_declaration_term (edited_undeclared_keys X Rc) ?Fs')
      (Pair_Term (state_families_term ident X) (state_family_term identr Rc)))\<in>positive_meaning verdict_mentions_system
    \<longleftrightarrow> (verdict_undeclared,Pair_Term (declaration_term ?Fs') (Pair_Term (state_families_term ident ?Fs')
      (state_family_term identr (state_roots R))))\<in>positive_meaning verdict_mentions_system"
    unfolding restricted_declaration_term_def
    by (rule edited_undeclared[OF identity roots_identity closed rows' keys sound added mentioning sroots croots store
      store_roots])
  then show ?thesis by (simp add: undeclared_here edited_state_roots)
qed

lemma incremental_unreached:
  fixes L V Tg :: "state_key list"
  defines "X\<equiv>assessment_families_checked (state_assessment R) e L (edit_removed_declarations e)"
    and "U\<equiv>incremental_reach_table (state_reach_seeds R) L V (\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e))))
      (state_roots (edited_state R e)) (state_reach_predecessors (state_all_families (edited_state R e)))"
  assumes L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
    and ms_atoms: "set (edit_removed_declarations e)\<subseteq>set (map fst (state_atoms R))"
    and single: "declarations_single_valued (state_all_families R)"
    and admitted: "walk_admitted ident (subject_indexes_term ident L (state_all_families R)) e
      (subject_indexes_term ident Tg (state_all_families (edited_state R e)))
      (state_reach_predecessors (state_all_families (edited_state R e))) (state_reach_seeds R)
      (\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e)))) L V Tg X"
  shows "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident X))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_unreached,Pair_Term (reach_table_term answer_table)
      (state_families_term ident (state_all_families (edited_state R e))))
      \<in>positive_meaning native_verdict_system"
proof -
  let ?Fs'="state_all_families (edited_state R e)"
  have closure: "(removal_closure,Pair_Term (Pair_Term (keys_term L)
      (subject_indexes_term ident L (state_all_families R))) (keys_term L))\<in>positive_meaning edited_reach_system"
    and targets: "(removal_targets,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident Tg ?Fs'))
      (state_families_term ident (map (edit_removed e) entity_kinds)))\<in>positive_meaning edited_reach_system"
    and visit: "\<forall>k\<in>set V. k\<in>set (map fst (state_atoms (edited_state R e))) \<longrightarrow>
      \<not>(k\<in>set (state_reach_seeds R) \<and> k\<notin>set L) \<longrightarrow> set (state_reach_predecessors ?Fs' k)\<subseteq>set V"
    and visit_rows: "\<forall>G\<in>set X. \<forall>z\<in>set G. set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V"
    using admitted unfolding walk_admitted_def by blast+
  have formed: "reach_table_formed U" unfolding U_def by (rule incremental_reach_table_formed)
  have table: "set U=set (reach_restricted (set V) (edited_reach_table (state_reach_seeds R) L answer_table))"
    unfolding U_def by (rule incremental_reach_table_set)
  have seeds: "set (state_reach_seeds R)\<subseteq>set (state_reach_seeds R)" by (rule subset_refl)
  have closed_visit: "p\<in>set V"
    if "(p,q)\<in>reach_edges answer_table" "q\<in>set V" "q\<notin>set (state_reach_seeds R)-set L" for p q
    using that visit by (auto simp: reach_edges_member state_reach_table_row)
  note found = assessment_families_checked_rows[OF request single reduced L_atoms ms_atoms]
  have sound: "\<exists>F\<in>set ?Fs'. z\<in>set F" if "G\<in>set X" "z\<in>set G" for G z
  proof -
    have "(\<exists>j. z\<in>set (edit_added e j)) \<or> z\<in>presented_rows (edited_state R e)"
      using that found[of z] unfolding X_def by blast
    then show ?thesis
    proof
      assume "\<exists>j. z\<in>set (edit_added e j)"
      then obtain j where "z\<in>set (edit_added e j)" by blast
      then have "z\<in>(\<Union>F\<in>set ?Fs'. set F)" by (rule in_answer)
      then show ?thesis by blast
    next
      assume "z\<in>presented_rows (edited_state R e)"
      then show ?thesis by (auto simp: state_all_families_rows[symmetric])
    qed
  qed
  have added: "\<exists>G\<in>set X. z\<in>set G" if "z\<in>set (edit_added e j)" for j z
    using that found[of z] unfolding X_def by blast
  have fibred: "\<exists>G\<in>set X. z\<in>set G"
    if "F\<in>set ?Fs'" "z\<in>set F" "a\<in>set L" "a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z))" for F z a
  proof -
    have "z\<in>presented_rows (edited_state R e)"
      using that(1,2) by (auto simp: state_all_families_rows[symmetric])
    then show ?thesis using that(3,4) found[of z] unfolding X_def by blast
  qed
  have incremental: "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident X))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
    by (rule edited_unreached_rows_admitted[OF closed_unreached closure targets seeds formed table
      closed_visit sound added fibred visit_rows])
  have whole: "(verdict_unreached,Pair_Term (reach_table_term answer_table) (state_families_term ident ?Fs'))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
    by (rule native_unreached_exact[OF answer state_all_families_range identity])
  show ?thesis using incremental whole by (simp add: unreached_here)
qed

subsection \<open>The contract: every field, and the entry\<close>

text \<open>
  \<open>native_edited_fields\<close>: under the locale's premises (the request state presented and closed, the edit
  with its constructor's facts, the subject an atom of the request state, the kind selections by
  \<open>kinds_present\<close>) and, for the two fields that read the checked families, the keys they read atoms of the
  request state, its single declarations and the walk admitted, each field's call at its incremental part
  holds exactly when its call at its whole part on the answer state holds.
\<close>

lemmas native_edited_fields = incremental_statements incremental_excess incremental_formed
  incremental_undeclared incremental_unreached incremental_removed incremental_added incremental_roots

theorem incremental_entry:
  fixes L V Tg :: "state_key list"
  assumes L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
    and ms_atoms: "set (edit_removed_declarations e)\<subseteq>set (map fst (state_atoms R))"
    and admitted: "walk_admitted ident (subject_indexes_term ident L (state_all_families R)) e
      (subject_indexes_term ident Tg (state_all_families (edited_state R e)))
      (state_reach_predecessors (state_all_families (edited_state R e))) (state_reach_seeds R)
      (\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e)))) L V Tg
      (assessment_families_checked (state_assessment R) e L (edit_removed_declarations e))"
    and single: "declarations_single_valued (state_all_families R)"
    and fresh: "edit_declarations_fresh (state_assessment R) e"
    and gone: "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
  shows "(verdict_entry,incremental_verdict_argument ident identr (state_assessment R) e L V k ks kr kd)
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (verdict_entry,native_verdict_argument ident identr R (edited_state R e) k ks kr kd)
      \<in>positive_meaning native_verdict_system"
proof -
  have rts: "root_fibres (state_assessment R) (edit_removed_declarations e)=
      edited_undeclared_roots (state_roots R) (edit_removed_declarations e)"
    by (rule root_fibres_edited[OF ms_atoms])
  have decl: "assessment_declaration_term (state_assessment R) e ms=
      restricted_declaration_term ms (state_all_families (edited_state R e))" for ms
    by (rule assessment_declaration_term_edited[OF single reduced gone fresh])
  note st = incremental_statements and ex = incremental_excess and fo = incremental_formed
    and un = incremental_undeclared[OF L_atoms ms_atoms single]
    and ur = incremental_unreached[OF L_atoms ms_atoms single admitted]
    and rm = incremental_removed and ad = incremental_added and ro = incremental_roots
  show ?thesis
    unfolding incremental_verdict_argument_def Let_def rts decl assessment_predecessors_edited[OF request]
      assessment_edited_atom_exact native_verdict_argument_def native_verdict_entry
    using st ex fo un ur rm ad ro by (simp add: reach_roots_keys edited_atoms_keys edited_state_roots)
qed

corollary incremental_accepted:
  fixes L V Tg :: "state_key list"
  assumes request_row: "request_presents key S R rows r k ks"
    and L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
    and ms_atoms: "set (edit_removed_declarations e)\<subseteq>set (map fst (state_atoms R))"
    and admitted: "walk_admitted ident (subject_indexes_term ident L (state_all_families R)) e
      (subject_indexes_term ident Tg (state_all_families (edited_state R e)))
      (state_reach_predecessors (state_all_families (edited_state R e))) (state_reach_seeds R)
      (\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e)))) L V Tg
      (assessment_families_checked (state_assessment R) e L (edit_removed_declarations e))"
    and single: "declarations_single_valued (state_all_families R)"
    and fresh: "edit_declarations_fresh (state_assessment R) e"
    and gone: "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
  shows "(verdict_entry,incremental_verdict_argument ident identr (state_assessment R) e L V k ks kr kd)
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    development_verdict_accepted (development_constant_verdict replaceable demanded S r S')"
  using incremental_entry[OF L_atoms ms_atoms admitted single fresh gone]
    native_verdict_exact[where ident=ident and identr=identr, OF request_row answer shared replaceable_kinds
      demanded_kinds identity roots_identity]
  by simp

end

subsection \<open>The stage's premise: the request state is closed\<close>

text \<open>
  The premise \<open>P\<close>(i) is not held in the assessment: it is the native evaluation of the three
  whole-state fields on the request state, made once where the stage's equation checks it. Each field
  is the verdict's own program at the request state's whole parts, and its contract is consumed by
  name, so the premise is decided by the same three programs that judge an answer.
\<close>

definition state_closed_natively :: "(isabelle_context \<Rightarrow> factor_term) \<Rightarrow>
    ((String.literal list\<times>isabelle_term) \<Rightarrow> factor_term) \<Rightarrow> state_rows \<Rightarrow> bool" where
  "state_closed_natively ident identr R \<longleftrightarrow>
    (verdict_formed,Pair_Term (path_term [])
      (state_families_term ident (map (state_entities R) (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning native_verdict_system \<and>
    (verdict_undeclared,Pair_Term (declaration_term (state_all_families R))
      (Pair_Term (state_families_term ident (state_all_families R))
        (state_family_term identr (state_roots R))))\<in>positive_meaning native_verdict_system \<and>
    (verdict_unreached,Pair_Term
      (reach_table_term (state_reach_table (state_atoms R) (state_roots R) (state_all_families R)))
      (state_families_term ident (state_all_families R)))\<in>positive_meaning native_verdict_system"

theorem state_closed_natively_exact:
  assumes present: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
  shows "state_closed_natively ident identr R \<longleftrightarrow>
    isabelle_malformed_entities (snd S)=[] \<and> isabelle_undeclared_constants (fst S) (snd S)=[] \<and>
    isabelle_unreached_entities (fst S) (snd S)=[]"
proof -
  have sel: "set (map (state_entities R) (kinds_outside [Specification_Kind]))
      =state_entities R ` (- {Specification_Kind})" by simp
  have fam: "set (state_all_families R)=range (state_entities R)" by (rule state_all_families_range)
  have f: "(verdict_formed,Pair_Term (path_term [])
      (state_families_term ident (map (state_entities R) (kinds_outside [Specification_Kind]))))
      \<in>positive_meaning verdict_rows_system \<longleftrightarrow> isabelle_malformed_entities (snd S)=[]"
    by (rule native_formed_exact_specifications[where ident=ident, OF present sel identity path_term_formed])
  show ?thesis
    unfolding state_closed_natively_def formed_here undeclared_here unreached_here f
    by (simp add:
      native_undeclared_exact[where ident=ident and identr=identr, OF present fam identity roots_identity]
      native_unreached_exact[where ident=ident, OF present fam identity])
qed

subsection \<open>The answer state's presentability, from the request state's and the edit\<close>

text \<open>
  An answer state is presentable when its request state is and the edit appends distinct new names and adds
  entities whose positions lie in the extended table: the kept entities and the roots use only positions of
  the request state's table, whose names the extended table keeps. The request state's presentability is
  decided once, where the stage presents it; the edit's two facts are read from the edit alone, its appended
  names being the atoms the constructor appends, so no answer walks the extended table or every position.
\<close>

lemma edit_applied_presentable:
  assumes presentable: "state_presentable S"
    and names: "distinct (filter (\<lambda>n. n\<notin>set (fst (snd S))) ns)"
    and inside: "\<And>a i. a\<in>set added \<Longrightarrow> i\<in>set (isabelle_entity_positions a) \<Longrightarrow>
      i<length (isabelle_appended_names (fst (snd S)) ns)"
  shows "state_presentable (edit_applied S ns removed added)"
proof -
  let ?names="fst (snd S)" and ?N="isabelle_appended_names (fst (snd S)) ns"
  have d: "distinct ?names" and i: "state_positions S\<subseteq>{..<length ?names}"
    and r: "distinct (map (isabelle_local_root ?names) (fst S))"
    using presentable by (simp_all add: state_presentable_def)
  have longer: "length ?names\<le>length ?N" by (rule isabelle_appended_names_longer)
  have applied: "edit_applied S ns removed added=(fst S,(?N,filter (\<lambda>e. e\<notin>set removed) (snd (snd S))@added))"
    by (simp add: edit_applied_def)
  have dN: "distinct ?N" using d names by (auto simp: isabelle_appended_names_def)
  have iN: "state_positions (edit_applied S ns removed added)\<subseteq>{..<length ?N}"
  proof
    fix p assume p: "p\<in>state_positions (edit_applied S ns removed added)"
    show "p\<in>{..<length ?N}"
    proof (cases "p\<in>state_positions S")
      case True
      then show ?thesis using i longer by auto
    next
      case False
      then obtain a where "a\<in>set added" "p\<in>set (isabelle_entity_positions a)"
        using p by (auto simp: applied state_positions_def)
      then show ?thesis using inside by auto
    qed
  qed
  have roots: "map (isabelle_local_root ?N) (fst S)=map (isabelle_local_root ?names) (fst S)"
  proof (rule map_cong[OF refl])
    fix t assume t: "t\<in>set (fst S)"
    show "isabelle_local_root ?N t=isabelle_local_root ?names t"
    proof (rule isabelle_local_root_agree)
      fix j assume j: "j\<in>set (isabelle_term_positions t)"
      have "j\<in>state_positions S" using t j by (auto simp: state_positions_def)
      then have "j<length ?names" using i by auto
      then show "isabelle_name_at ?N j=isabelle_name_at ?names j" by (rule isabelle_appended_names_prefix)
    qed
  qed
  have rN: "distinct (map (isabelle_local_root ?N) (fst S))" using r unfolding roots .
  show ?thesis unfolding state_presentable_def using dN iN rN by (simp add: applied)
qed

lemma state_edit_of_atoms:
  assumes edit: "state_edit_of S ns removed added=Some e"
  shows "map snd (edit_atoms e)=filter (\<lambda>n. n\<notin>set (fst (snd S))) ns"
proof -
  let ?N="isabelle_appended_names (fst (snd S)) ns"
  have e: "edit_atoms e=map (\<lambda>i. (state_constant_key i,?N!i)) [length (fst (snd S))..<length ?N]"
    using edit by (auto simp: state_edit_of_def edit_applied_def Let_def split: if_splits)
  have "map (\<lambda>i. ?N!i) [length (fst (snd S))..<length ?N]=drop (length (fst (snd S))) ?N"
    by (rule nth_equalityI) (simp_all add: isabelle_appended_names_def nth_append)
  then show ?thesis by (simp add: e comp_def appended_new_names(1))
qed

definition edit_presentable :: "nat \<Rightarrow> state_edit \<Rightarrow> isabelle_entity list \<Rightarrow> bool" where
  "edit_presentable m e added \<longleftrightarrow> distinct (map snd (edit_atoms e)) \<and>
    list_all (\<lambda>i. i<m+length (edit_atoms e)) (concat (map isabelle_entity_positions added))"

lemma edit_presentable_applied:
  assumes presentable: "state_presentable S" and edit: "state_edit_of S ns removed added=Some e"
    and guard: "edit_presentable (length (fst (snd S))) e added"
  shows "state_presentable (edit_applied S ns removed added)"
proof -
  have atoms: "map snd (edit_atoms e)=filter (\<lambda>n. n\<notin>set (fst (snd S))) ns" by (rule state_edit_of_atoms[OF edit])
  have len: "length (fst (snd S))+length (edit_atoms e)=length (isabelle_appended_names (fst (snd S)) ns)"
    using arg_cong[OF atoms, of length] appended_new_names(2)[of "fst (snd S)" ns] by simp
  show ?thesis
  proof (rule edit_applied_presentable[OF presentable])
    show "distinct (filter (\<lambda>n. n\<notin>set (fst (snd S))) ns)" using atoms guard by (simp add: edit_presentable_def)
    show "i<length (isabelle_appended_names (fst (snd S)) ns)"
      if "a\<in>set added" "i\<in>set (isabelle_entity_positions a)" for a i
      using len guard that by (auto simp: edit_presentable_def list_all_iff)
  qed
qed

subsection \<open>The judgment of one answer, and the stage's equation\<close>

text \<open>
  The whole judgment of an answer is the verdict's entry at the whole argument of its answer state: the
  state its edit presents when the edit has a reduced form, the answer state's own presentation otherwise.
  The incremental judgment builds the assessment's parts from the edit and the walk's product, and is the
  whole judgment wherever the edit has no reduced form, its appended names or added positions leave the
  extended table unpresentable, it would declare a key a kept row declares or one key twice, the request's
  subject or a key the parts read is no atom of the request state, or the walk is refused: an unavailable
  incremental form is never a verdict. Each guard reads the edit and the assessment's indexes only.
\<close>

definition whole_answer_judgment where
  "whole_answer_judgment ident identr kr kd S R k ks ns removed added=
    (case state_edit_of S ns removed added of
      Some e \<Rightarrow> (verdict_entry,native_verdict_argument ident identr R (edited_state R e) k ks kr kd)
        \<in>positive_meaning native_verdict_system
    | None \<Rightarrow> (case state_presenter (edit_applied S ns removed added) of None \<Rightarrow> False
      | Some R' \<Rightarrow> (verdict_entry,native_verdict_argument ident identr R R' k ks kr kd)
        \<in>positive_meaning native_verdict_system))"

definition incremental_answer_judgment where
  "incremental_answer_judgment ident identr walk kr kd m S R A k ks ns removed added=
    (case state_edit_of S ns removed added of
      None \<Rightarrow> whole_answer_judgment ident identr kr kd S R k ks ns removed added
    | Some e \<Rightarrow> (let W=walk A e; L=fst W; V=fst (snd W); Tg=snd (snd W); ms=edit_removed_declarations e in
        if edit_presentable m e added \<and> edit_declarations_fresh A e \<and> assessment_atom A k \<and>
          list_all (assessment_atom A) L \<and> list_all (assessment_atom A) ms \<and> list_all (assessment_atom A) Tg \<and>
          walk_admitted ident (assessment_closure_term ident A L) e (assessment_indexes_term ident A e Tg)
            (assessment_predecessors A e) (map fst (assessment_reach A)) (assessment_edited_atom A e) L V Tg
            (assessment_families_checked A e L ms)
        then (verdict_entry,incremental_verdict_argument ident identr A e L V k ks kr kd)
          \<in>positive_meaning native_verdict_system
        else whole_answer_judgment ident identr kr kd S R k ks ns removed added))"

text \<open>
  A state declares each constant once exactly when every declaration row finds its own value in the
  declaration store: one lookup per row, so the test is linear in the declarations.
\<close>

lemma declarations_single_valued_store [code]:
  "declarations_single_valued Fs \<longleftrightarrow>
    (let D=declaration_store Fs in list_all (\<lambda>r. store_lookup D (fst r)=Some (snd r)) (declaration_rows Fs))"
  unfolding Let_def
proof
  assume sv: "declarations_single_valued Fs"
  show "list_all (\<lambda>r. store_lookup (declaration_store Fs) (fst r)=Some (snd r)) (declaration_rows Fs)"
    by (simp add: list_all_iff declaration_store_def path_store_lookup[OF sv[unfolded declarations_single_valued_def]])
next
  assume all: "list_all (\<lambda>r. store_lookup (declaration_store Fs) (fst r)=Some (snd r)) (declaration_rows Fs)"
  show "declarations_single_valued Fs"
    unfolding declarations_single_valued_def single_valued_def
  proof (intro allI impI)
    fix d a b assume "(d,a)\<in>set (declaration_rows Fs)" "(d,b)\<in>set (declaration_rows Fs)"
    then have "store_lookup (declaration_store Fs) d=Some a" "store_lookup (declaration_store Fs) d=Some b"
      using all by (auto simp: list_all_iff)
    then show "a=b" by simp
  qed
qed

text \<open>
  The stage is a function of the request state: its premises, the request state closed and declaring each
  constant once, are decided once, by the native evaluation of the three whole-state fields and by the
  declaration store's own test (\<open>declarations_single_valued_store\<close>), and the assessment is built once;
  each answer is then judged by the incremental judgment. The refusal is the whole judgment of every
  answer, computed by its own constant.
\<close>

definition stage_closed where
  "stage_closed ident identr S=(case state_presenter S of None \<Rightarrow> False | Some R \<Rightarrow>
    state_closed_natively ident identr R \<and> declarations_single_valued (state_all_families R))"

text \<open>
  At a state the exporter defines, every constant is declared by one entity (@{const isabelle_declared_once}),
  so the single-declaration test passes there and the stage's premise is the request state's closedness.
\<close>

corollary stage_closed_declared_once:
  assumes presented: "state_presenter S=Some R" and once: "isabelle_declared_once (snd S)"
  shows "stage_closed ident identr S \<longleftrightarrow> state_closed_natively ident identr R"
proof -
  have "declarations_single_valued (state_all_families R)"
    by (rule declarations_single_valued_presented[OF state_presenter_presents[OF presented] once])
      (simp add: state_all_families_range)
  then show ?thesis by (simp add: stage_closed_def presented)
qed

definition stage_whole where
  "stage_whole ident identr kr kd S=(\<lambda>(k,ks,ns,removed,added). case state_presenter S of None \<Rightarrow> False
    | Some R \<Rightarrow> whole_answer_judgment ident identr kr kd S R k ks ns removed added)"

definition stage_refusal where
  "stage_refusal ident identr kr kd S=(\<lambda>(k,ks,ns,removed,added). case state_presenter S of None \<Rightarrow> False
    | Some R \<Rightarrow> whole_answer_judgment ident identr kr kd S R k ks ns removed added)"

definition stage_answers where
  "stage_answers ident identr walk kr kd S R A=(let m=length (fst (snd S)) in (\<lambda>(k,ks,ns,removed,added).
    incremental_answer_judgment ident identr walk kr kd m S R A k ks ns removed added))"

definition stage_incremental where
  "stage_incremental ident identr walk kr kd S=(case state_presenter S of None \<Rightarrow> (\<lambda>_. False)
    | Some R \<Rightarrow> stage_answers ident identr walk kr kd S R (state_assessment R))"

locale incremental_stage =
  fixes ident :: "isabelle_context \<Rightarrow> factor_term" and identr :: "(String.literal list\<times>isabelle_term) \<Rightarrow> factor_term"
    and replaceable demanded :: "isabelle_entity \<Rightarrow> bool" and kr kd :: "entity_kind list"
    and walk :: "state_assessment_parts \<Rightarrow> state_edit \<Rightarrow> state_key list\<times>state_key list\<times>state_key list"
  assumes identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
    and replaceable_kinds: "kinds_present replaceable (set kr)" and demanded_kinds: "kinds_present demanded (set kd)"
begin

theorem answer_exact:
  assumes presented: "state_presenter S=Some R" and closed: "state_closed_natively ident identr R"
    and single: "declarations_single_valued (state_all_families R)"
  shows "incremental_answer_judgment ident identr walk kr kd (length (fst (snd S))) S R (state_assessment R)
      k ks ns removed added=whole_answer_judgment ident identr kr kd S R k ks ns removed added"
proof (cases "state_edit_of S ns removed added")
  case None
  then show ?thesis by (simp add: incremental_answer_judgment_def)
next
  case (Some e)
  obtain L V Tg where W: "walk (state_assessment R) e=(L,V,Tg)"
    by (cases "walk (state_assessment R) e" rule: prod_cases3) blast
  let ?A="state_assessment R" and ?ms="edit_removed_declarations e"
  let ?G="edit_presentable (length (fst (snd S))) e added \<and> edit_declarations_fresh ?A e \<and> assessment_atom ?A k \<and>
    list_all (assessment_atom ?A) L \<and> list_all (assessment_atom ?A) ?ms \<and> list_all (assessment_atom ?A) Tg \<and>
    walk_admitted ident (assessment_closure_term ident ?A L) e (assessment_indexes_term ident ?A e Tg)
      (assessment_predecessors ?A e) (map fst (assessment_reach ?A)) (assessment_edited_atom ?A e) L V Tg
      (assessment_families_checked ?A e L ?ms)"
  show ?thesis
  proof (cases ?G)
    case True
    then have guard: "edit_presentable (length (fst (snd S))) e added" and fresh: "edit_declarations_fresh ?A e"
      and katomA: "assessment_atom ?A k" and LA: "list_all (assessment_atom ?A) L"
      and msA: "list_all (assessment_atom ?A) ?ms" and TgA: "list_all (assessment_atom ?A) Tg"
      and admittedA: "walk_admitted ident (assessment_closure_term ident ?A L) e (assessment_indexes_term ident ?A e Tg)
        (assessment_predecessors ?A e) (map fst (assessment_reach ?A)) (assessment_edited_atom ?A e) L V Tg
        (assessment_families_checked ?A e L ?ms)"
      by blast+
    have present: "state_presents state_constant_key S R" by (rule state_presenter_presents[OF presented])
    have presS: "state_presentable S" using presented by (simp add: state_presenter_def split: if_splits)
    have presentable: "state_presentable (edit_applied S ns removed added)"
      by (rule edit_presentable_applied[OF presS Some guard])
    have katom: "k\<in>set (map fst (state_atoms R))" using katomA by (simp only: assessment_atom_exact)
    have L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
      using LA by (auto simp: list_all_iff assessment_atom_exact)
    have ms_atoms: "set ?ms\<subseteq>set (map fst (state_atoms R))"
      using msA by (auto simp: list_all_iff assessment_atom_exact)
    have Tg_atoms: "set Tg\<subseteq>set (map fst (state_atoms R))"
      using TgA by (auto simp: list_all_iff assessment_atom_exact)
    have admitted: "walk_admitted ident (subject_indexes_term ident L (state_all_families R)) e
        (subject_indexes_term ident Tg (state_all_families (edited_state R e)))
        (state_reach_predecessors (state_all_families (edited_state R e))) (state_reach_seeds R)
        (\<lambda>a. a\<in>set (map fst (state_atoms (edited_state R e)))) L V Tg (assessment_families_checked ?A e L ?ms)"
      using admittedA unfolding assessment_predecessors_edited[OF present] assessment_indexes_term_edited[OF Tg_atoms]
        assessment_closure_term_request[OF L_atoms] assessment_edited_atom_exact
      by (simp add: reach_roots_keys)
    have m: "isabelle_malformed_entities (snd S)=[]" and u: "isabelle_undeclared_constants (fst S) (snd S)=[]"
      and n: "isabelle_unreached_entities (fst S) (snd S)=[]"
      using state_closed_natively_exact[where ident=ident and identr=identr, OF present identity roots_identity]
        closed by blast+
    note contract = state_edit_contract[OF presented presentable Some]
    have el: "edited_local state_constant_key S R e (edit_applied S ns removed added) ident"
      by (rule edited_local_constructed[where ident=ident, OF presented presentable Some identity])
    have iv: "incremental_verdict state_constant_key S R e (edit_applied S ns removed added) ident identr k
        replaceable demanded kr kd"
      unfolding incremental_verdict_def incremental_verdict_axioms_def
      using el roots_identity katom replaceable_kinds demanded_kinds contract(3) m u n by blast
    have entry: "(verdict_entry,incremental_verdict_argument ident identr (state_assessment R) e L V k ks kr kd)
        \<in>positive_meaning native_verdict_system \<longleftrightarrow>
      (verdict_entry,native_verdict_argument ident identr R (edited_state R e) k ks kr kd)
        \<in>positive_meaning native_verdict_system"
      by (rule incremental_verdict.incremental_entry[OF iv L_atoms ms_atoms admitted single fresh contract(8)])
    show ?thesis
      using entry True Some W
      by (simp add: incremental_answer_judgment_def whole_answer_judgment_def Let_def reach_roots_keys edited_atoms_keys)
  next
    case False
    then show ?thesis
      using Some W
      by (auto simp: incremental_answer_judgment_def Let_def reach_roots_keys edited_atoms_keys)
  qed
qed

corollary answer_accepted:
  assumes presented: "state_presenter S=Some R" and edit: "state_edit_of S ns removed added=Some e"
    and presentable: "state_presentable (edit_applied S ns removed added)"
    and request: "request_presents state_constant_key S R rows r k ks"
  shows "whole_answer_judgment ident identr kr kd S R k ks ns removed added \<longleftrightarrow>
    development_verdict_accepted (development_constant_verdict replaceable demanded S r (edit_applied S ns removed added))"
proof -
  note contract = state_edit_contract[OF presented presentable edit]
  show ?thesis
    using native_verdict_exact[where ident=ident and identr=identr, OF request contract(1) contract(2)
      replaceable_kinds demanded_kinds identity roots_identity]
      edit by (simp add: whole_answer_judgment_def)
qed

theorem stage_exact:
  assumes closed: "stage_closed ident identr S"
  shows "stage_whole ident identr kr kd S=stage_incremental ident identr walk kr kd S"
proof -
  obtain R where presented: "state_presenter S=Some R" and cl: "state_closed_natively ident identr R"
      and single: "declarations_single_valued (state_all_families R)"
    using closed by (auto simp: stage_closed_def split: option.splits)
  show ?thesis
  proof (rule ext)
    fix x
    show "stage_whole ident identr kr kd S x=stage_incremental ident identr walk kr kd S x"
      by (cases x rule: prod_cases5)
        (simp add: stage_whole_def stage_incremental_def stage_answers_def Let_def presented
          answer_exact[OF presented cl single])
  qed
qed

sublocale stage: checked_premise "stage_whole ident identr kr kd" "stage_closed ident identr"
    "stage_incremental ident identr walk kr kd" "stage_refusal ident identr kr kd"
proof unfold_locales
  show "stage_whole ident identr kr kd x=stage_incremental ident identr walk kr kd x"
    if "stage_closed ident identr x" for x
    using that by (rule stage_exact)
  show "stage_whole ident identr kr kd x=stage_refusal ident identr kr kd x" if "\<not>stage_closed ident identr x" for x
    by (simp add: stage_whole_def stage_refusal_def)
qed

text \<open>
  The stage's equation: the premise is checked once per request state, at the arity where its argument
  ends, so every answer to every request on the state shares the one check and the one assessment.
\<close>

lemmas stage_equation = stage.checked_at_entry

end

corollary state_closed_natively_assessment:
  assumes present: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)" and roots_identity: "\<And>y. term_formed (identr y)"
  shows "state_closed_natively ident identr R \<longleftrightarrow>
    isabelle_assessment_closed (isabelle_context_assessment (fst S) (snd S))"
  using state_closed_natively_exact[where ident=ident and identr=identr, OF present identity roots_identity]
    state_presents_unknown_positions[OF present]
  by (simp add: isabelle_assessment_closed_def isabelle_context_assessment_def fset_of_list_empty_iff conj_ac)

end
