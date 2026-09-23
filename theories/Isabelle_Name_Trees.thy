theory Isabelle_Name_Trees
  imports Isabelle_Local_Names Tree_Map_Indexes
begin

section \<open>The name table is read through its index\<close>

text \<open>
  A name table is read by position (\<^const>\<open>isabelle_name_at\<close>), which walks the list to the position. Its index
  is the tree map's index (@{thm [source] tree_map_carrier_index}) of its positions paired with its names, the
  carrier read through the identity key (@{text isabelle_name_carrier_index}): built once, it reads the name at
  a position by one lookup (@{text isabelle_name_tree_lookup}). A table extended by names is read through its
  index extended by the insertions of the new positions, the tree's update (@{text tree_map_updates}), whose
  cost is the extension's (@{text isabelle_name_tree_appended}). The readings that take a table are stated here
  over a lookup (\<open>isabelle_local_entities_by\<close>, \<open>isabelle_entity_subjects_by\<close>), each equal to its reading of a
  table at the table's lookup, so a use reads names through the index and states the table's readings.
\<close>

definition isabelle_name_tree :: "String.literal list \<Rightarrow> (nat,String.literal) rbt" where
  "isabelle_name_tree names=RBT.bulkload (enumerate 0 names)"

lemma isabelle_name_rows:
  "(k,n)\<in>set (enumerate 0 names) \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> isabelle_name_at names q=Some n)"
  by (auto simp: in_set_enumerate_eq isabelle_name_at_def)

lemma isabelle_name_carrier_index:
  "carrier_index (\<lambda>names i n. isabelle_name_at names i=Some n) (\<lambda>_. True) UNIV id isabelle_name_tree tree_search"
  unfolding isabelle_name_tree_def[abs_def]
  by (rule carrier_index_through_key[OF tree_map_carrier_index, where img="enumerate 0" and formed="\<lambda>_. True"])
    (simp_all add: isabelle_name_rows)

interpretation isabelle_name_index:
  carrier_index "\<lambda>names i n. isabelle_name_at names i=Some n" "\<lambda>_. True" UNIV id isabelle_name_tree tree_search
  by (rule isabelle_name_carrier_index)

lemma isabelle_name_tree_lookup: "RBT.lookup (isabelle_name_tree names) i=isabelle_name_at names i"
proof -
  have "RBT.lookup (isabelle_name_tree names) i=Some v \<longleftrightarrow> isabelle_name_at names i=Some v" for v
    using isabelle_name_index.query_search[where c=names and q=i and v=v] by simp
  then show ?thesis by (cases "isabelle_name_at names i"; cases "RBT.lookup (isabelle_name_tree names) i") auto
qed

lemma isabelle_name_tree_lookup_fun: "RBT.lookup (isabelle_name_tree names)=isabelle_name_at names"
  by (rule ext) (rule isabelle_name_tree_lookup)

text \<open>An insertion's lookup, read from the tree's update (@{text tree_map_updates}).\<close>

lemma isabelle_name_tree_insert: "RBT.lookup (RBT.insert k u T) k'=(if k'=k then Some u else RBT.lookup T k')"
proof -
  have "RBT.lookup (RBT.insert k u T) k'=Some v \<longleftrightarrow> (if k'=k then Some u else RBT.lookup T k')=Some v" for v
    using tree_map_updates.updated[where i=T and k=k and u=u and k'=k' and v=v] by auto
  then show ?thesis
    by (cases "RBT.lookup (RBT.insert k u T) k'"; cases "if k'=k then Some u else RBT.lookup T k'") auto
qed

definition isabelle_name_tree_extend ::
    "nat \<Rightarrow> String.literal list \<Rightarrow> (nat,String.literal) rbt \<Rightarrow> (nat,String.literal) rbt" where
  "isabelle_name_tree_extend m ns T=fold (\<lambda>(i,n) T. RBT.insert i n T) (enumerate m ns) T"

lemma isabelle_name_tree_extend_lookup:
  "RBT.lookup (isabelle_name_tree_extend m ns T) k=
    (if m\<le>k \<and> k<m+length ns then Some (ns!(k-m)) else RBT.lookup T k)"
proof (induction ns arbitrary: m T)
  case Nil
  show ?case by (auto simp: isabelle_name_tree_extend_def)
next
  case (Cons x ns)
  have step: "isabelle_name_tree_extend m (x#ns) T=isabelle_name_tree_extend (Suc m) ns (RBT.insert m x T)"
    by (simp add: isabelle_name_tree_extend_def)
  show ?case unfolding step Cons.IH by (auto simp: isabelle_name_tree_insert nth_Cons')
qed

lemma isabelle_name_tree_appended:
  "RBT.lookup (isabelle_name_tree_extend (length names) ns (isabelle_name_tree names))=isabelle_name_at (names@ns)"
  by (rule ext) (auto simp: isabelle_name_tree_extend_lookup isabelle_name_tree_lookup isabelle_name_at_def nth_append)

subsection \<open>The readings of a table, over a lookup\<close>

definition isabelle_local_names_by :: "(nat \<Rightarrow> String.literal option) \<Rightarrow> nat list \<Rightarrow> String.literal list" where
  "isabelle_local_names_by look ps=remdups (List.map_filter look ps)"

definition isabelle_state_embedding_by :: "(nat \<Rightarrow> String.literal option) \<Rightarrow> String.literal list \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_state_embedding_by look names' i=(case Option.bind (look i) (isabelle_name_position names') of
     Some j \<Rightarrow> j
   | None \<Rightarrow> length names'+i)"

definition isabelle_local_entities_by :: "(nat \<Rightarrow> String.literal option) \<Rightarrow> isabelle_entity list \<Rightarrow> isabelle_context" where
  "isabelle_local_entities_by look es=(let ps=concat (map isabelle_entity_positions es); L=isabelle_local_names_by look ps in
    (L,map (isabelle_entity_rename (isabelle_state_embedding_by look L)) es))"

lemma isabelle_local_entities_by_names:
  "isabelle_local_entities names es=isabelle_local_entities_by (isabelle_name_at names) es"
  by (simp add: isabelle_local_entities_def isabelle_local_entities_by_def isabelle_local_embedding_def
      isabelle_local_names_def isabelle_local_names_by_def isabelle_state_embedding_def[abs_def]
      isabelle_state_embedding_by_def[abs_def] Let_def)

fun isabelle_equation_left_by :: "(nat \<Rightarrow> String.literal option) \<Rightarrow> isabelle_term \<Rightarrow> isabelle_term option" where
  "isabelle_equation_left_by look (Isabelle_Application (Isabelle_Constant c T) p)=
    (if look c=Some isabelle_judgment_name then isabelle_equation_left_by look p else None)"
| "isabelle_equation_left_by look (Isabelle_Application (Isabelle_Application (Isabelle_Constant c T) l) r)=
    (if (\<exists>n\<in>set isabelle_equality_names. look c=Some n) then Some l else None)"
| "isabelle_equation_left_by look t=None"

lemma isabelle_equation_left_by_names: "isabelle_equation_left names p=isabelle_equation_left_by (isabelle_name_at names) p"
  by (induction names p rule: isabelle_equation_left.induct) simp_all

definition isabelle_entity_subjects_by :: "(nat \<Rightarrow> String.literal option) \<Rightarrow> nat list \<Rightarrow> isabelle_entity \<Rightarrow> nat list" where
  "isabelle_entity_subjects_by look D e=(case e of
     Isabelle_Definition p \<Rightarrow> (case Option.bind (isabelle_equation_left_by look p) isabelle_head_constant of Some c \<Rightarrow> [c] | None \<Rightarrow> [])
   | Isabelle_Specification p \<Rightarrow> filter (\<lambda>c. c\<in>set D) (isabelle_term_constants p)
   | Isabelle_Code_Equation p \<Rightarrow> (case Option.bind (isabelle_equation_left_by look p) isabelle_head_constant of Some c \<Rightarrow> [c] | None \<Rightarrow> [])
   | _ \<Rightarrow> [])"

lemma isabelle_entity_subjects_by_names:
  "isabelle_entity_subjects names D e=isabelle_entity_subjects_by (isabelle_name_at names) D e"
  by (cases e) (simp_all add: isabelle_entity_subjects_by_def isabelle_equation_left_by_names)

end
