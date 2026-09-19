theory Isabelle_Type_Tables
  imports Isabelle_Entities "HOL-Library.RBT"
begin

section \<open>A definition holds each type of its terms once\<close>

text \<open>
  The kernel's terms carry a type at every constant, variable and abstraction, and the terms of
  a checked context mention a few types many times: the entities of the loop's fourteen notions
  have 23,311 constructors, of which 21,441 present types, while all their types together have 610
  distinct nodes. A definition that presents a state therefore holds each distinct type once, as a node of
  a table whose arguments are positions of earlier nodes, and presents its terms over positions
  of that table. Reading it back is the term's and the entity's own map through the table, so the
  state read back is the state the definition presents: holding the types once changes how the
  definition presents a state, not the state, and every observation of the state is unchanged.
\<close>

datatype isabelle_type_node =
    Isabelle_Node_Application nat "nat list"
  | Isabelle_Node_Free nat "nat list"
  | Isabelle_Node_Variable nat nat "nat list"

fun isabelle_node_type :: "(nat \<Rightarrow> isabelle_type) \<Rightarrow> isabelle_type_node \<Rightarrow> isabelle_type" where
  "isabelle_node_type ty (Isabelle_Node_Application c ks)=Isabelle_Type_Application c (map ty ks)"
| "isabelle_node_type ty (Isabelle_Node_Free a S)=Isabelle_Type_Free a S"
| "isabelle_node_type ty (Isabelle_Node_Variable a i S)=Isabelle_Type_Variable a i S"

fun isabelle_node_arguments :: "isabelle_type_node \<Rightarrow> nat list" where
  "isabelle_node_arguments (Isabelle_Node_Application c ks)=ks"
| "isabelle_node_arguments (Isabelle_Node_Free a S)=[]"
| "isabelle_node_arguments (Isabelle_Node_Variable a i S)=[]"

lemma isabelle_node_type_cong:
  assumes "\<And>j. j\<in>set (isabelle_node_arguments n) \<Longrightarrow> f j=g j"
  shows "isabelle_node_type f n=isabelle_node_type g n"
  using assms by (cases n) simp_all

text \<open>
  The table is read in order, each node reading its arguments from the nodes before it; the
  reading is kept in an ordered index, so reading a position costs a lookup.
\<close>

definition isabelle_table_type :: "(nat,isabelle_type) rbt \<Rightarrow> nat \<Rightarrow> isabelle_type" where
  "isabelle_table_type t k=the (RBT.lookup t k)"

definition isabelle_type_table_step ::
    "isabelle_type_node \<Rightarrow> (nat,isabelle_type) rbt\<times>nat \<Rightarrow> (nat,isabelle_type) rbt\<times>nat" where
  "isabelle_type_table_step n s=(case s of (t,k) \<Rightarrow>
    (RBT.insert k (isabelle_node_type (isabelle_table_type t) n) t,Suc k))"

lemma isabelle_type_table_step_pair [simp]:
  "isabelle_type_table_step n (t,k)=(RBT.insert k (isabelle_node_type (isabelle_table_type t) n) t,Suc k)"
  by (simp add: isabelle_type_table_step_def)

definition isabelle_type_table :: "isabelle_type_node list \<Rightarrow> (nat,isabelle_type) rbt" where
  "isabelle_type_table ns=fst (fold isabelle_type_table_step ns (RBT.empty,0))"

definition isabelle_nodes_ordered :: "isabelle_type_node list \<Rightarrow> bool" where
  "isabelle_nodes_ordered ns \<longleftrightarrow> (\<forall>k<length ns. \<forall>j\<in>set (isabelle_node_arguments (ns!k)). j<k)"

lemma isabelle_type_table_count:
  "snd (fold isabelle_type_table_step ns (RBT.empty,0))=length ns"
proof (induction ns rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc n ns)
  obtain t k where "fold isabelle_type_table_step ns (RBT.empty,0)=(t,k)"
    by (cases "fold isabelle_type_table_step ns (RBT.empty,0)")
  with snoc show ?case by simp
qed

theorem isabelle_type_table_exact:
  assumes ordered: "isabelle_nodes_ordered ns" and inside: "k<length ns"
  shows "isabelle_table_type (isabelle_type_table ns) k=
    isabelle_node_type (isabelle_table_type (isabelle_type_table ns)) (ns!k)"
  using assms
proof (induction ns arbitrary: k rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc n ns)
  define T where "T=isabelle_type_table ns"
  define v where "v=isabelle_node_type (isabelle_table_type T) n"
  obtain T' c where fold_ns: "fold isabelle_type_table_step ns (RBT.empty,0)=(T',c)"
    by (cases "fold isabelle_type_table_step ns (RBT.empty,0)")
  have T': "T'=T"
    using fold_ns by (simp add: T_def isabelle_type_table_def)
  have c: "c=length ns"
    using fold_ns isabelle_type_table_count[of ns] by simp
  have table: "isabelle_type_table (ns@[n])=RBT.insert (length ns) v T"
    using fold_ns T' c by (simp add: isabelle_type_table_def v_def)
  have all: "\<forall>j\<in>set (isabelle_node_arguments ((ns@[n])!k)). j<k" if "k<length (ns@[n])" for k
    using snoc.prems(1) that unfolding isabelle_nodes_ordered_def by blast
  have prefix: "isabelle_nodes_ordered ns"
    unfolding isabelle_nodes_ordered_def
  proof (intro allI impI)
    fix k assume "k<length ns"
    then show "\<forall>j\<in>set (isabelle_node_arguments (ns!k)). j<k"
      using all[of k] by (simp add: nth_append)
  qed
  have earlier: "isabelle_table_type (RBT.insert (length ns) v T) j=isabelle_table_type T j"
    if "j<length ns" for j
    using that by (simp add: isabelle_table_type_def)
  have last_args: "j<length ns" if "j\<in>set (isabelle_node_arguments n)" for j
    using all[of "length ns"] that by simp
  show ?case
  proof (cases "k<length ns")
    case True
    have args: "j<length ns" if "j\<in>set (isabelle_node_arguments (ns!k))" for j
    proof -
      have "j<k" using prefix True that unfolding isabelle_nodes_ordered_def by blast
      then show ?thesis using True by simp
    qed
    have "isabelle_table_type T k=isabelle_node_type (isabelle_table_type T) (ns!k)"
      using snoc.IH[OF prefix True] by (simp add: T_def)
    also have "\<dots>=isabelle_node_type (isabelle_table_type (RBT.insert (length ns) v T)) (ns!k)"
      by (rule isabelle_node_type_cong) (simp add: earlier args)
    finally show ?thesis
      using True by (simp add: table earlier nth_append)
  next
    case False
    then have k: "k=length ns" using snoc.prems(2) by simp
    have "isabelle_table_type (RBT.insert (length ns) v T) (length ns)=v"
      by (simp add: isabelle_table_type_def)
    also have "v=isabelle_node_type (isabelle_table_type (RBT.insert (length ns) v T)) n"
    proof -
      have "isabelle_node_type (isabelle_table_type T) n=
          isabelle_node_type (isabelle_table_type (RBT.insert (length ns) v T)) n"
        by (rule isabelle_node_type_cong) (simp add: earlier last_args)
      then show ?thesis by (simp only: v_def)
    qed
    finally show ?thesis by (simp add: table k)
  qed
qed

section \<open>A state is read from its shared presentation\<close>

text \<open>
  A shared presentation of a state is its name table, a table of type nodes and its entities
  over positions of that table. Its reading reads the table once and maps every entity and term
  through it, so every occurrence of one type reads one value. Which table and which positions
  present a state is the transport of the exporter, as the name table is; the reading is exact at
  every position of an ordered table (\<open>isabelle_type_table_exact\<close>).
\<close>

type_synonym isabelle_shared_term = "nat isabelle_term_with"

type_synonym isabelle_shared_entity = "isabelle_shared_term isabelle_entity_with"

definition isabelle_shared_terms ::
    "isabelle_type_node list \<Rightarrow> isabelle_shared_term list \<Rightarrow> isabelle_term list" where
  "isabelle_shared_terms ns ts=(let ty=isabelle_table_type (isabelle_type_table ns) in
    map (map_isabelle_term_with ty) ts)"

definition isabelle_shared_context ::
    "String.literal list \<Rightarrow> isabelle_type_node list \<Rightarrow> isabelle_shared_entity list \<Rightarrow> isabelle_context" where
  "isabelle_shared_context names ns es=(let ty=isabelle_table_type (isabelle_type_table ns) in
    (names,map (map_isabelle_entity_with (map_isabelle_term_with ty)) es))"

lemma isabelle_shared_context_fields:
  "fst (isabelle_shared_context names ns es)=names"
  "snd (isabelle_shared_context names ns es)=
    map (map_isabelle_entity_with (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ns)))) es"
  by (simp_all add: isabelle_shared_context_def Let_def)

end
