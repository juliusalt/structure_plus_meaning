theory Isabelle_Entity_Export
  imports Isabelle_Type_Tables Isabelle_Constant_Closure
begin

section \<open>A checked theory context defines the entities reachable from its roots\<close>

text \<open>
  The exporter runs inside the checked context. It follows the shared constant closure:
  a development constant contributes its kernel definitions, the non-definitional axioms
  that mention it and the code equations in effect, as declared (read by the shared closure
  under an empty simpset); a constant of the fixed Isabelle/HOL base contributes nothing. Types
  and terms are translated constructor by constructor, and every name is a position in one
  table of the defined context. The definition holds every distinct type once, as a node of a
  table of types, and presents terms over positions of that table (\<open>Isabelle_Type_Tables\<close>):
  the kernel repeats a type at every occurrence, and presented once per occurrence the types made
  up nine in ten of a state's constructors. The result is an ordinary definition of the checked
  context, so a failed build defines nothing and every later use reads exactly the defined value.
\<close>

section \<open>A defined state declares each constant once\<close>

text \<open>
  The exporter owes that no two entities of a state it defines declare one constant
  (\<open>isabelle_declared_once\<close>). It discharges the obligation where it defines the state, and reads
  what the obligation reads: the declarations. A declaration of a shared entity is read through the
  table of types without reading the type, and a statement declares nothing whatever its term, so the
  declared constants of the defined state are computed from the spine of its entity list alone, each
  entity by its constructor and the head of its term. The exporter declares every reached constant
  once and lists the declarations in the order of their positions in the name table, so the declared
  positions are strictly increasing (\<open>sorted_wrt (<)\<close>, HOL's \<open>strict_sorted\<close>), and distinctness
  follows from one comparison of each adjacent pair (\<open>strict_sorted_iff\<close>, \<open>sorted_wrt2_simps\<close>): the
  proof is linear in the declarations. It is proved of the definition's right-hand side, whose
  arguments it instantiates, and transported to the defined constant through the definition's
  equation, so the context term is never rewritten into the goal. Of the term itself only the spine
  of the entity list is read: each entity's constructor names the equation that applies to it, which
  is instantiated at the entity's arguments and at the rest of the list, so neither the rest of the
  list nor any statement's term is traversed, and each entity costs one instantiation. No name, no
  type and no statement is evaluated.
\<close>

lemma isabelle_shared_declarations:
  fixes f :: "nat \<Rightarrow> isabelle_type"
  defines "g \<equiv> map_isabelle_entity_with (map_isabelle_term_with f)"
  shows "List.map_filter isabelle_declared_constant (map g [])=[]"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Base_Constant (Isabelle_Constant c k)#es))=
      c#List.map_filter isabelle_declared_constant (map g es)"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Development_Constant (Isabelle_Constant c k)#es))=
      c#List.map_filter isabelle_declared_constant (map g es)"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Frontier_Constant (Isabelle_Constant c k)#es))=
      c#List.map_filter isabelle_declared_constant (map g es)"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Definition t#es))=
      List.map_filter isabelle_declared_constant (map g es)"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Specification t#es))=
      List.map_filter isabelle_declared_constant (map g es)"
    "List.map_filter isabelle_declared_constant (map g (Isabelle_Code_Equation t#es))=
      List.map_filter isabelle_declared_constant (map g es)"
  unfolding g_def by (simp_all add: List.map_filter_simps)

lemma isabelle_shared_declared_once:
  assumes "distinct (List.map_filter isabelle_declared_constant
    (map (map_isabelle_entity_with (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ns)))) es))"
  shows "isabelle_declared_once (isabelle_shared_context names ns es)"
  using assms by (simp only: isabelle_shared_context_fields(2) isabelle_declared_once_distinct)

section \<open>A defined state names only positions of its own table\<close>

text \<open>
  The exporter also owes the two conditions every reader of a state takes of its table
  (\<open>state_presents\<close> carries them): the names of the table are distinct, and every position an
  entity or a root of the state uses is a position of the table. It discharges both where it defines
  the state, as it does the declarations. The table is listed in the order of its names, so its
  names are strictly increasing, and distinctness follows from one comparison of each adjacent pair of
  names, each comparing the two names from their first differing character. The positions are read
  from the presentation the definition holds: every name position of an entity or root is below the
  length of the table, and every type position below the length of the table of types, whose nodes
  read only earlier nodes, so every type the table reads uses only positions of the name table. Each
  condition is stated by constructor, and a condition is instantiated at the parts of the term its
  constructor takes, so each constructor of the state costs one instantiation, and each distinct
  comparison of a position with its bound is proved once.
\<close>

fun isabelle_node_below :: "nat \<Rightarrow> nat \<Rightarrow> isabelle_type_node \<Rightarrow> bool" where
  "isabelle_node_below N k (Isabelle_Node_Application c ks)=(c<N \<and> list_all (\<lambda>j. j<k) ks)"
| "isabelle_node_below N k (Isabelle_Node_Free a S)=(a<N \<and> list_all (\<lambda>j. j<N) S)"
| "isabelle_node_below N k (Isabelle_Node_Variable a i S)=(a<N \<and> list_all (\<lambda>j. j<N) S)"

fun isabelle_nodes_below :: "nat \<Rightarrow> nat \<Rightarrow> isabelle_type_node list \<Rightarrow> bool" where
  "isabelle_nodes_below N k []=True"
| "isabelle_nodes_below N k (n#ns)=(isabelle_node_below N k n \<and> isabelle_nodes_below N (Suc k) ns)"

lemma isabelle_nodes_below_nth:
  "isabelle_nodes_below N k ns \<longleftrightarrow> (\<forall>i<length ns. isabelle_node_below N (k+i) (ns!i))"
  by (induction ns arbitrary: k) (simp_all add: All_less_Suc2)

lemma isabelle_table_type_below:
  assumes nodes: "isabelle_nodes_below N 0 ns" and inside: "k<length ns"
  shows "set (isabelle_type_positions (isabelle_table_type (isabelle_type_table ns) k))\<subseteq>{..<N}"
proof -
  have node: "isabelle_node_below N j (ns!j)" if "j<length ns" for j
    using nodes that by (simp add: isabelle_nodes_below_nth)
  have ordered: "isabelle_nodes_ordered ns"
    unfolding isabelle_nodes_ordered_def
  proof (intro allI impI ballI)
    fix j i assume j: "j<length ns" and i: "i\<in>set (isabelle_node_arguments (ns!j))"
    show "i<j" using node[OF j] i by (cases "ns!j") (auto simp: list_all_iff)
  qed
  show ?thesis using inside
  proof (induction k rule: less_induct)
    case (less k)
    have exact: "isabelle_table_type (isabelle_type_table ns) k=
        isabelle_node_type (isabelle_table_type (isabelle_type_table ns)) (ns!k)"
      by (rule isabelle_type_table_exact[OF ordered less.prems])
    show ?case
    proof (cases "ns!k")
      case (Isabelle_Node_Application c ks)
      have c: "c<N" and args: "\<forall>j\<in>set ks. j<k"
        using node[OF less.prems] Isabelle_Node_Application by (simp_all add: list_all_iff)
      have earlier: "set (isabelle_type_positions (isabelle_table_type (isabelle_type_table ns) j))\<subseteq>{..<N}"
        if "j\<in>set ks" for j
        using args that less.prems by (intro less.IH) auto
      show ?thesis using exact Isabelle_Node_Application c earlier by auto
    next
      case (Isabelle_Node_Free a S)
      then show ?thesis using exact node[OF less.prems] by (auto simp: list_all_iff)
    next
      case (Isabelle_Node_Variable a i S)
      then show ?thesis using exact node[OF less.prems] by (auto simp: list_all_iff)
    qed
  qed
qed

fun isabelle_shared_term_below :: "nat \<Rightarrow> nat \<Rightarrow> isabelle_shared_term \<Rightarrow> bool" where
  "isabelle_shared_term_below N M (Isabelle_Constant c T)=(c<N \<and> T<M)"
| "isabelle_shared_term_below N M (Isabelle_Free x T)=(x<N \<and> T<M)"
| "isabelle_shared_term_below N M (Isabelle_Variable x i T)=(x<N \<and> T<M)"
| "isabelle_shared_term_below N M (Isabelle_Bound i)=True"
| "isabelle_shared_term_below N M (Isabelle_Abstraction T t)=(T<M \<and> isabelle_shared_term_below N M t)"
| "isabelle_shared_term_below N M (Isabelle_Application t u)=
    (isabelle_shared_term_below N M t \<and> isabelle_shared_term_below N M u)"

fun isabelle_shared_entity_below :: "nat \<Rightarrow> nat \<Rightarrow> isabelle_shared_entity \<Rightarrow> bool" where
  "isabelle_shared_entity_below N M (Isabelle_Base_Constant t)=isabelle_shared_term_below N M t"
| "isabelle_shared_entity_below N M (Isabelle_Development_Constant t)=isabelle_shared_term_below N M t"
| "isabelle_shared_entity_below N M (Isabelle_Frontier_Constant t)=isabelle_shared_term_below N M t"
| "isabelle_shared_entity_below N M (Isabelle_Definition t)=isabelle_shared_term_below N M t"
| "isabelle_shared_entity_below N M (Isabelle_Specification t)=isabelle_shared_term_below N M t"
| "isabelle_shared_entity_below N M (Isabelle_Code_Equation t)=isabelle_shared_term_below N M t"


lemma isabelle_shared_term_positions:
  assumes nodes: "isabelle_nodes_below N 0 ns" and M: "M\<le>length ns" and below: "isabelle_shared_term_below N M t"
  shows "set (isabelle_term_positions (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ns)) t))\<subseteq>{..<N}"
proof -
  have types: "set (isabelle_type_positions (isabelle_table_type (isabelle_type_table ns) T))\<subseteq>{..<N}" if "T<M" for T
    by (rule isabelle_table_type_below[OF nodes]) (use that M in simp)
  show ?thesis using below by (induction t) (auto dest: types)
qed

lemma isabelle_shared_entity_positions:
  assumes nodes: "isabelle_nodes_below N 0 ns" and M: "M\<le>length ns" and below: "isabelle_shared_entity_below N M e"
  shows "set (isabelle_entity_positions (map_isabelle_entity_with
    (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ns))) e))\<subseteq>{..<N}"
  using below by (cases e) (use isabelle_shared_term_positions[OF nodes M] in \<open>simp_all add: isabelle_entity_positions_def\<close>)

text \<open>
  The facts the exporter proves of a state it defines are stated of any context and roots
  equal to a shared presentation, so each is instantiated at the defined constant and discharged by
  its definition's equation, and no step rewrites the presentation.
\<close>

lemma isabelle_shared_positions_closed:
  assumes presented: "C=isabelle_shared_context names ns es" and names: "length names=N"
    and nodes: "isabelle_nodes_below N 0 ns" and M: "length ns=M" and entities: "list_all (isabelle_shared_entity_below N M) es"
  shows "\<forall>e\<in>set (snd C). set (isabelle_entity_positions e)\<subseteq>{..<length (fst C)}"
proof -
  have "set (isabelle_entity_positions (map_isabelle_entity_with
      (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ns))) e))\<subseteq>{..<N}" if "e\<in>set es" for e
    by (rule isabelle_shared_entity_positions[OF nodes, where M=M])
      (use entities that M in \<open>simp_all add: list_all_iff\<close>)
  then show ?thesis using names by (auto simp: presented isabelle_shared_context_fields)
qed

lemma isabelle_shared_roots_closed:
  assumes roots: "R=isabelle_shared_terms ms ts" and presented: "C=isabelle_shared_context names ns es"
    and names: "length names=N" and nodes: "isabelle_nodes_below N 0 ms" and M: "length ms=M"
    and terms: "list_all (isabelle_shared_term_below N M) ts"
  shows "\<forall>t\<in>set R. set (isabelle_term_positions t)\<subseteq>{..<length (fst C)}"
proof -
  have "set (isabelle_term_positions (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ms)) t))\<subseteq>{..<N}"
    if "t\<in>set ts" for t
    by (rule isabelle_shared_term_positions[OF nodes, where M=M])
      (use terms that M in \<open>simp_all add: list_all_iff\<close>)
  then show ?thesis using names by (auto simp: roots presented isabelle_shared_terms_def isabelle_shared_context_fields)
qed

text \<open>
  The roots of a defined state are distinct: each is a constant, and the positions of their constants,
  read from the shared presentation of the roots alone, are distinct.
\<close>

lemma isabelle_shared_heads:
  fixes f :: "nat \<Rightarrow> isabelle_type"
  shows "map (\<lambda>t. hd (isabelle_term_positions (map_isabelle_term_with f t))) []=[]"
    "map (\<lambda>t. hd (isabelle_term_positions (map_isabelle_term_with f t))) (Isabelle_Constant c T#ts)=
      c#map (\<lambda>t. hd (isabelle_term_positions (map_isabelle_term_with f t))) ts"
  by simp_all

lemma isabelle_shared_roots_distinct:
  assumes roots: "R=isabelle_shared_terms ms ts"
    and heads: "map (\<lambda>t. hd (isabelle_term_positions
      (map_isabelle_term_with (isabelle_table_type (isabelle_type_table ms)) t))) ts=cs"
    and distinct: "distinct cs"
  shows "distinct R"
proof -
  have "distinct (map (\<lambda>t. hd (isabelle_term_positions t)) R)"
    using heads distinct by (simp add: roots isabelle_shared_terms_def Let_def comp_def)
  then show ?thesis by (simp add: distinct_map)
qed

lemma isabelle_shared_names_distinct:
  assumes presented: "C=isabelle_shared_context names ns es" and increasing: "sorted_wrt (<) names"
  shows "distinct (fst C)"
  using increasing by (simp add: presented isabelle_shared_context_fields strict_sorted_iff)

lemma isabelle_literal_less_same:
  fixes s t :: String.literal
  assumes less: "s<t"
  shows "String.Literal b0 b1 b2 b3 b4 b5 b6 s<String.Literal b0 b1 b2 b3 b4 b5 b6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons_eq)
    (simp_all only: less_irrefl not_False_eq_True less[unfolded String.less_literal.rep_eq])

lemma isabelle_literal_less_empty: "(0::String.literal)<String.Literal b0 b1 b2 b3 b4 b5 b6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq String.zero_literal.rep_eq
  by (rule ord.lexordp.Nil)

text \<open>
  Two characters that first differ, counting from the highest bit, at a bit the first has unset and the
  second set are in that order, whatever their lower bits: the lower bits of the first stay below the
  bit, and the higher bits are shared. There is one rule for each bit of the seven, so the order of two
  concrete characters is one instantiation, with no arithmetic.
\<close>

lemma isabelle_char_bits_less:
  assumes "length xs=length ys"
  shows "horner_sum of_bool (2::nat) (xs@False#zs)<horner_sum of_bool 2 (ys@True#zs)"
  using horner_sum_of_bool_2_less[of xs, where 'a=nat] assms
  by (simp add: horner_sum_append distrib_left; linarith)

lemma isabelle_literal_less_bit6: "String.Literal b0 b1 b2 b3 b4 b5 False s<String.Literal c0 c1 c2 c3 c4 c5 True t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0,b1,b2,b3,b4,b5]" "[c0,c1,c2,c3,c4,c5]" "[False]"] in simp)

lemma isabelle_literal_less_bit5: "String.Literal b0 b1 b2 b3 b4 False h6 s<String.Literal c0 c1 c2 c3 c4 True h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0,b1,b2,b3,b4]" "[c0,c1,c2,c3,c4]" "[h6,False]"] in simp)

lemma isabelle_literal_less_bit4: "String.Literal b0 b1 b2 b3 False h5 h6 s<String.Literal c0 c1 c2 c3 True h5 h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0,b1,b2,b3]" "[c0,c1,c2,c3]" "[h5,h6,False]"] in simp)

lemma isabelle_literal_less_bit3: "String.Literal b0 b1 b2 False h4 h5 h6 s<String.Literal c0 c1 c2 True h4 h5 h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0,b1,b2]" "[c0,c1,c2]" "[h4,h5,h6,False]"] in simp)

lemma isabelle_literal_less_bit2: "String.Literal b0 b1 False h3 h4 h5 h6 s<String.Literal c0 c1 True h3 h4 h5 h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0,b1]" "[c0,c1]" "[h3,h4,h5,h6,False]"] in simp)

lemma isabelle_literal_less_bit1: "String.Literal b0 False h2 h3 h4 h5 h6 s<String.Literal c0 True h2 h3 h4 h5 h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[b0]" "[c0]" "[h2,h3,h4,h5,h6,False]"] in simp)

lemma isabelle_literal_less_bit0: "String.Literal False h1 h2 h3 h4 h5 h6 s<String.Literal True h1 h2 h3 h4 h5 h6 t"
  unfolding String.less_literal.rep_eq String.Literal.rep_eq
  by (rule ord.lexordp.Cons) (use isabelle_char_bits_less[of "[]" "[]" "[h1,h2,h3,h4,h5,h6,False]"] in simp)

ML \<open>
structure Isabelle_Entity_Export =
struct

val base_sessions = ["Pure", "HOL", "HOL-Library"];

(*The theory long name that declared a constant.*)
fun declaring_theory thy name =
  #theory_long_name (Name_Space.the_entry (Sign.const_space thy) name);

(*The session of the theory that declared a constant. A theory's long name is qualified by its
  session, except the theory Pure, whose long name is the name of its session: read by its
  qualifier alone, every constant of Pure would be a development constant.*)
fun declaring_session thy name =
  let val theory = declaring_theory thy name
  in (case Long_Name.qualifier theory of "" => theory | session => session) end;

fun base_constant thy name = member (op =) base_sessions (declaring_session thy name);

datatype item = Definition | Specification | Code_Equation;

(*Positions and indices are binary numerals, so a long table costs no successor chain.*)
fun number i = HOLogic.mk_number \<^typ>\<open>nat\<close> i;

(*The declarations and items of the constants reached from the roots of a checked context.
  Only an expanded constant contributes items; every other development constant reached is
  on the frontier of the state and is extended when work demands it.*)
fun context_items thy expand roots =
  let
    val kernel = Isabelle_Constant_Closure.kernel_definitions thy;
    val definitional = Symtab.make_set (map #2 (Defs.dest_constdefs [] (Theory.defs_of thy)));
    val specifications =
      fold (fn (name, prop) =>
          if Symtab.defined definitional name then I
          else fold (fn c => Symtab.cons_list (c, (name, prop))) (Term.add_const_names prop []))
        (Theory.all_axioms_of thy) Symtab.empty;
    fun code_equations c = map Thm.prop_of (Isabelle_Constant_Closure.code_equation_theorems thy c);
    fun items c =
      if base_constant thy c orelse not (expand c) then []
      else
        map (fn (name, prop) => ("definition " ^ name, (Definition, prop))) (kernel c) @
        map (fn (name, prop) => ("specification " ^ name, (Specification, prop)))
          (these (Symtab.lookup specifications c)) @
        map_index (fn (i, prop) => ("code " ^ c ^ " " ^ string_of_int i, (Code_Equation, prop)))
          (code_equations c);
    val (seen, selected) =
      Isabelle_Constant_Closure.closure items (fn (_, prop) => Term.add_const_names prop []) roots;
  in (sort string_ord (Symtab.keys seen), map snd (Symtab.dest selected)) end;

(*Every name a type or term uses, in the order of its occurrences.*)
fun type_names (Type (c, Ts)) = c :: maps type_names Ts
  | type_names (TFree (a, S)) = a :: S
  | type_names (TVar ((a, _), S)) = a :: S;

fun term_names (Const (c, T)) = c :: type_names T
  | term_names (Free (x, T)) = x :: type_names T
  | term_names (Var ((x, _), T)) = x :: type_names T
  | term_names (Bound _) = []
  | term_names (Abs (_, T, t)) = type_names T @ term_names t
  | term_names (t $ u) = term_names t @ term_names u;

fun type_term position (Type (c, Ts)) =
      \<^Const>\<open>Isabelle_Type_Application\<close> $ position c $
        HOLogic.mk_list \<^typ>\<open>isabelle_type\<close> (map (type_term position) Ts)
  | type_term position (TFree (a, S)) =
      \<^Const>\<open>Isabelle_Type_Free\<close> $ position a $ HOLogic.mk_list \<^typ>\<open>nat\<close> (map position S)
  | type_term position (TVar ((a, i), S)) =
      \<^Const>\<open>Isabelle_Type_Variable\<close> $ position a $ number i $
        HOLogic.mk_list \<^typ>\<open>nat\<close> (map position S);

(*A term over a presentation of its types: typT is the type presenting a type, typ presents one.*)
fun term_with typT typ position =
  let
    fun term (Const (c, T)) = \<^Const>\<open>Isabelle_Constant typT\<close> $ position c $ typ T
      | term (Free (x, T)) = \<^Const>\<open>Isabelle_Free typT\<close> $ position x $ typ T
      | term (Var ((x, i), T)) = \<^Const>\<open>Isabelle_Variable typT\<close> $ position x $ number i $ typ T
      | term (Bound i) = \<^Const>\<open>Isabelle_Bound typT\<close> $ number i
      | term (Abs (_, T, t)) = \<^Const>\<open>Isabelle_Abstraction typT\<close> $ typ T $ term t
      | term (t $ u) = \<^Const>\<open>Isabelle_Application typT\<close> $ term t $ term u;
  in term end;

(*A term carrying its types, as the kernel's term does.*)
fun term_term position = term_with \<^typ>\<open>isabelle_type\<close> (type_term position) position;

(*Every distinct type of the terms once, each argument before its application: the positions of
  the types and the nodes of the table in order.*)
fun type_table position terms =
  let
    fun collect T (index, nodes, count) =
      if Typtab.defined index T then (index, nodes, count)
      else
        let
          val (index', nodes', count') =
            (case T of Type (_, Ts) => fold collect Ts (index, nodes, count) | _ => (index, nodes, count));
          fun at U = number (the (Typtab.lookup index' U));
          val node =
            (case T of
              Type (c, Ts) => \<^Const>\<open>Isabelle_Node_Application\<close> $ position c $
                HOLogic.mk_list \<^typ>\<open>nat\<close> (map at Ts)
            | TFree (a, S) => \<^Const>\<open>Isabelle_Node_Free\<close> $ position a $
                HOLogic.mk_list \<^typ>\<open>nat\<close> (map position S)
            | TVar ((a, i), S) => \<^Const>\<open>Isabelle_Node_Variable\<close> $ position a $ number i $
                HOLogic.mk_list \<^typ>\<open>nat\<close> (map position S));
        in (Typtab.update (T, count') index', node :: nodes', count' + 1) end;
    val (index, nodes, _) = fold (fn t => Term.fold_types collect t) terms (Typtab.empty, [], 0);
  in
    (term_with \<^typ>\<open>nat\<close> (fn T => number (the (Typtab.lookup index T))) position,
      HOLogic.mk_list \<^typ>\<open>isabelle_type_node\<close> (rev nodes))
  end;

(*Terms read back through their own table of types.*)
fun shared_terms position terms =
  let val (term, nodes) = type_table position terms
  in \<^Const>\<open>isabelle_shared_terms\<close> $ nodes $
    HOLogic.mk_list \<^typ>\<open>isabelle_shared_term\<close> (map term terms)
  end;

(*The defined context: one name table, the declarations of every reached constant and the
  items the expanded constants contribute, every distinct type held once; the roots are defined
  as the constants they name. The name table also holds the names of any further terms the
  caller presents against it.*)
fun context_terms thy expand root_names seeds groups further =
  let
    val (constants, items) = context_items thy expand (root_names @ seeds);
    fun constant c = Const (c, Sign.the_const_type thy c);
    val roots = map constant root_names;
    val declarations = map constant constants;
    val props = map snd items;
    val table = sort_distinct string_ord (maps term_names (roots @ declarations @ props @ further));
    val positions = Symtab.make (map_index (fn (i, name) => (name, i)) table);
    fun position name = number (the (Symtab.lookup positions name));
    val (term, nodes) = type_table position (declarations @ props);
    val entityT = \<^typ>\<open>isabelle_shared_term\<close>;
    fun declaration c =
      (if base_constant thy c then \<^Const>\<open>Isabelle_Base_Constant entityT\<close>
        else if expand c then \<^Const>\<open>Isabelle_Development_Constant entityT\<close>
        else \<^Const>\<open>Isabelle_Frontier_Constant entityT\<close>)
        $ term (constant c);
    fun item (Definition, prop) = \<^Const>\<open>Isabelle_Definition entityT\<close> $ term prop
      | item (Specification, prop) = \<^Const>\<open>Isabelle_Specification entityT\<close> $ term prop
      | item (Code_Equation, prop) = \<^Const>\<open>Isabelle_Code_Equation entityT\<close> $ term prop;
    val names_term = HOLogic.mk_list \<^typ>\<open>String.literal\<close> (map HOLogic.mk_literal table);
    val entities_term =
      HOLogic.mk_list \<^typ>\<open>isabelle_shared_entity\<close> (map declaration constants @ map item items);
    fun root_terms names = shared_terms position (map constant names);
  in
    (\<^Const>\<open>isabelle_shared_context\<close> $ names_term $ nodes $ entities_term, root_terms root_names,
      map (fn (suffix, names) => (suffix, root_terms names)) groups, position)
  end;

(*The declared constants of a defined state, read from the spine of its entity list: a declaration
  contributes the position of its constant, a statement nothing, and no term is read further. Each
  equation of the notion is read once, from its own statement: the constructor of the list element
  its left side takes, and whether its right side keeps a position (a Cons) or drops the entity; the
  equation without an element is the empty list's. At a state the entity at the head of the list
  names its equation, which is instantiated at the parts of the list its left side takes (the
  entity's arguments and the rest of the list): no match, rewrite or beta conversion reads the rest
  of the list, so each entity costs one instantiation. An entity the notion has no equation for is a
  defect of the exporter.*)
val declared_rules = map mk_meta_eq @{thms isabelle_shared_declarations};

fun declared_list rule =
  (case Thm.term_of (Thm.lhs_of rule) of
    _ $ _ $ (_ $ _ $ list) => list
  | _ => raise THM ("declared_rules: not an equation of the declarations", 0, [rule]));

fun declared_cons (Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ _) = true
  | declared_cons _ = false;

val declared_nil =
  the_single (filter (fn rule => not (declared_cons (declared_list rule))) declared_rules);
val declared_entity =
  map_filter (fn rule =>
    (case declared_list rule of
      Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ e $ _ =>
        (case Term.head_of e of
          Const (c, _) => SOME (c, (rule, declared_cons (Thm.term_of (Thm.rhs_of rule))))
        | _ => raise THM ("declared_rules: an element without a constructor", 0, [rule]))
    | _ => NONE)) declared_rules;

(*The instance of a rule at a cterm that a pattern of the rule takes, read by the structure of the
  pattern alone: a variable is bound to the part of the cterm at its place, a constant is compared by
  name. The declarations' conversion takes an equation at its left side, the increasing chain its step
  at the list.*)
fun declared_bind (Var v) ct = [(v, ct)]
  | declared_bind (Const (a, _)) ct =
      (case Thm.term_of ct of
        Const (b, _) =>
          if a = b then [] else raise CTERM ("declared_conv: not an instance of the equation", [ct])
      | _ => raise CTERM ("declared_conv: not an instance of the equation", [ct]))
  | declared_bind (p $ q) ct =
      (case Thm.term_of ct of
        _ $ _ => declared_bind p (Thm.dest_fun ct) @ declared_bind q (Thm.dest_arg ct)
      | _ => raise CTERM ("declared_conv: not an instance of the equation", [ct]))
  | declared_bind _ ct = raise CTERM ("declared_conv: not an instance of the equation", [ct]);

fun instance_at pattern rule ct =
  Thm.instantiate (TVars.empty, Vars.make (declared_bind pattern ct)) rule;

fun declared_instance rule = instance_at (Thm.term_of (Thm.lhs_of rule)) rule;

fun declared_conv ct =
  (case Thm.term_of ct of
    _ $ _ $ (_ $ _ $ (Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ e $ _)) =>
      (case
        (case Term.head_of e of
          Const (c, _) => AList.lookup (op =) declared_entity c
        | _ => NONE) of
        SOME (rule, declares) =>
          let val step = declared_instance rule ct
          in
            Thm.transitive step
              ((if declares then Conv.arg_conv declared_conv else declared_conv) (Thm.rhs_of step))
          end
      | NONE => raise CTERM ("declared_conv: not an entity of the state", [ct]))
  | _ => declared_instance declared_nil ct);

(*A strictly increasing list is distinct, proved by comparing each adjacent pair as numerals, by the
  order of binary numerals alone: HOL's rules of sorted_wrt (<).*)
val increasing_distinct = @{thm strict_sorted_iff[THEN iffD1, THEN conjunct2]};
val increasing_step = @{thm sorted_wrt2[OF transp_on_less, THEN iffD2, OF conjI]};
val increasing_ends = @{thms sorted_wrt.simps(1)[THEN eqTrueE] sorted_wrt1[THEN eqTrueE]};

fun numeral_less_ctxt ctxt = put_simpset HOL_basic_ss ctxt addsimps
  @{thms zero_less_one zero_less_numeral one_less_numeral_iff numeral_less_iff less_num_simps le_num_simps};

(*A strictly increasing list, proved from its last element back to its first: each adjacent pair
  by the supplied comparison of its two elements. The rules are taken once at the element type,
  read from the order's type, and the ends at the order; each step is then instantiated at the list
  it proves by its structure alone, without reading the rest. The declared positions and the names
  of a table are its two uses.*)
fun sorted_list (_ $ (_ $ _ $ list)) = list
  | sorted_list t = raise TERM ("increasing: not a sorted list", [t]);

fun sorted_order (_ $ (_ $ (Var v) $ _)) = v
  | sorted_order t = raise TERM ("increasing: not an end with a variable order", [t]);

fun increasing _ order pair =
  let
    val T = Thm.dest_ctyp0 (Thm.ctyp_of_cterm order);
    fun at_type rule =
      Thm.instantiate (TVars.make (map (fn v => (v, T)) (Term.add_tvars (Thm.prop_of rule) [])), Vars.empty)
        rule;
    fun at_order rule =
      Thm.instantiate (TVars.empty, Vars.make [(sorted_order (Thm.concl_of rule), order)]) rule;
    val step = at_type increasing_step;
    val one = at_order (at_type (nth increasing_ends 1));
    val none = at_order (at_type (nth increasing_ends 0));
    val (step_list, one_list, none_list) =
      (sorted_list (Thm.concl_of step), sorted_list (Thm.concl_of one), sorted_list (Thm.concl_of none));
    fun chain ct =
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ (Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ _) =>
          let val rest = Thm.dest_arg ct
          in
            Thm.implies_elim
              (Thm.implies_elim (instance_at step_list step ct) (pair (Thm.dest_arg1 ct) (Thm.dest_arg1 rest)))
              (chain rest)
          end
      | Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ _ => instance_at one_list one ct
      | _ => instance_at none_list none ct);
  in chain end;

(*Two positions compared as numerals.*)
fun numeral_less ctxt x y =
  Goal.prove_internal ctxt []
    (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.apply (Thm.apply \<^cterm>\<open>(<) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> x) y))
    (fn _ => simp_tac (numeral_less_ctxt ctxt) 1);

(*The obligation that the state a definition presents declares each constant once. It is proved of
  the definition's right-hand side: the reduction is instantiated at its three arguments, the declared
  positions are computed by the conversion from the spine of its entity list, and their strict
  increase is proved by comparing each adjacent pair. The theorem is then transported to the defined
  constant through the definition's equation, by congruence, so no step reads the context term
  beyond the spine. A state whose positions do not increase fails the proof.*)
fun declared_once ctxt def =
  let
    val def' = Local_Defs.meta_rewrite_rule ctxt def;
    val rhs = Thm.rhs_of def';
    val (names_ns, es) = Thm.dest_comb rhs;
    val (names_app, ns) = Thm.dest_comb names_ns;
    val names = Thm.dest_arg names_app;
    val shared = infer_instantiate ctxt [(("names", 0), names), (("ns", 0), ns), (("es", 0), es)]
      @{thm isabelle_shared_declared_once};
    val positions = HOLogic.Trueprop_conv (Conv.arg_conv declared_conv) (Thm.cprem_of shared 1);
    val declared = Thm.dest_arg (Thm.dest_arg (Thm.rhs_of positions));
    val increasing = increasing_distinct OF
      [increasing ctxt \<^cterm>\<open>(<) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> (numeral_less ctxt) declared];
    val once = Thm.implies_elim shared (Thm.equal_elim (Thm.symmetric positions) increasing);
    val transport = Thm.combination (Thm.reflexive \<^cterm>\<open>Trueprop\<close>)
      (Thm.combination (Thm.reflexive \<^cterm>\<open>isabelle_declared_once\<close>) (Thm.symmetric def'));
  in Thm.equal_elim transport once end;

(*A natural successor as a numeral.*)
fun successor_ctxt ctxt = put_simpset HOL_basic_ss ctxt addsimps
  @{thms Suc_numeral Suc_1 add_One inc.simps One_nat_def[symmetric]};

(*The length of a listed table as a numeral: each element costs one instantiation and one successor.*)
val length_rules = map mk_meta_eq
  @{thms list.size(3)[where 'a=String.literal] length_Cons[where 'a=String.literal]
    list.size(3)[where 'a=isabelle_type_node] length_Cons[where 'a=isabelle_type_node]};

fun length_conv ctxt (nil_rule, cons_rule) =
  let
    val successor = Simplifier.rewrite (successor_ctxt ctxt);
    fun conv ct =
      (case Thm.term_of ct of
        _ $ (Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ _) =>
          let
            val step = declared_instance cons_rule ct;
            val counted = Thm.transitive step (Conv.arg_conv conv (Thm.rhs_of step));
          in Thm.transitive counted (successor (Thm.rhs_of counted)) end
      | _ => declared_instance nil_rule ct);
  in conv end;

fun names_length ctxt = length_conv ctxt (nth length_rules 0, nth length_rules 1);
fun nodes_length ctxt = length_conv ctxt (nth length_rules 2, nth length_rules 3);

(*The conditions that the positions of a presentation are below their bounds, read by constructor:
  the equation of a condition is chosen by the constructor of its last argument and instantiated at
  the parts of the term its left side takes, so no step reads the rest of the presentation. A
  comparison of a position with its bound is proved once, and a conjunction of two proved conditions
  is proved by one combination. A position that is not below its bound fails the proof.*)
val below_rules = map mk_meta_eq @{thms isabelle_node_below.simps isabelle_nodes_below.simps
  isabelle_shared_term_below.simps isabelle_shared_entity_below.simps
  list.pred_inject(1)[THEN eqTrueI] list.pred_inject(2)};

fun below_key t =
  (case strip_comb t of
    (Const (p, _), args as _ :: _) =>
      (case Term.head_of (List.last args) of Const (c, _) => SOME (p, c) | _ => NONE)
  | _ => NONE);

val below_table =
  map (fn rule => (the (below_key (Thm.term_of (Thm.lhs_of rule))), rule)) below_rules;

val true_conj = mk_meta_eq @{lemma "(True \<and> True)=True" by simp};

fun below_conv ctxt =
  let
    val less_ctxt = numeral_less_ctxt ctxt;
    val successor = Simplifier.rewrite (successor_ctxt ctxt);
    val proved = Unsynchronized.ref Termtab.empty;
    fun less ct =
      (case Termtab.lookup (! proved) (Thm.term_of ct) of
        SOME th => th
      | NONE =>
          let val th = Simplifier.rewrite less_ctxt ct
          in
            (case Thm.term_of (Thm.rhs_of th) of
              Const (\<^const_name>\<open>True\<close>, _) => (proved := Termtab.update (Thm.term_of ct, th) (! proved); th)
            | _ => raise CTERM ("below_conv: a position is not below its bound", [ct]))
          end);
    fun element_instance rule ct =
      (case Thm.typ_of_cterm (Thm.dest_arg ct) of
        Type (_, [T]) =>
          Thm.instantiate (TVars.make (map (fn v => (v, Thm.ctyp_of ctxt T)) (Term.add_tvars (Thm.prop_of rule) [])),
            Vars.empty) rule
      | T => raise TYPE ("below_conv: not a list", [T], []));
    fun conv ct =
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>True\<close>, _) => Thm.reflexive ct
      | Abs _ $ _ =>
          let val reduced = Thm.beta_conversion false ct
          in Thm.transitive reduced (conv (Thm.rhs_of reduced)) end
      | Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
          Thm.transitive
            (Thm.combination (Thm.combination (Thm.reflexive (Thm.dest_fun2 ct)) (conv (Thm.dest_arg1 ct)))
              (conv (Thm.dest_arg ct)))
            true_conj
      | Const (\<^const_name>\<open>less\<close>, _) $ _ $ _ => less ct
      | t =>
          (case below_key t of
            SOME (key as (p, _)) =>
              (case AList.lookup (op =) below_table key of
                SOME rule0 =>
                  let
                    val rule = if p = \<^const_name>\<open>list_all\<close> then element_instance rule0 ct else rule0;
                    val counted =
                      if p = \<^const_name>\<open>isabelle_nodes_below\<close>
                      then Conv.fun_conv (Conv.arg_conv successor) ct else Thm.reflexive ct;
                    val step = Thm.transitive counted (declared_instance rule (Thm.rhs_of counted));
                  in Thm.transitive step (conv (Thm.rhs_of step)) end
              | NONE => raise CTERM ("below_conv: no equation for the condition", [ct]))
          | NONE => raise CTERM ("below_conv: not a condition", [ct])));
  in conv end;

(*A premise of the form Trueprop P, proved by evaluating P to True.*)
fun below_premise ctxt th =
  let
    val prem = Thm.cprem_of th 1;
    val holds = below_conv ctxt (Thm.dest_arg prem);
    val true_prop = Thm.combination (Thm.reflexive (Thm.dest_fun prem)) holds;
  in Thm.implies_elim th (Thm.equal_elim (Thm.symmetric true_prop) @{thm TrueI}) end;

fun meta_premise th eq = Thm.implies_elim th (@{thm meta_eq_to_obj_eq} OF [eq]);

(*The order of two names, compared from their first differing character: a common character is
  passed by one instantiation, a differing one is compared as a number, and a name is below every
  name it is a proper prefix of.*)
fun literal_parts ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>String.Literal\<close>, _) $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _ => SOME (snd (Drule.strip_comb ct))
  | _ => NONE);

fun literal_bits prefix bits = map_index (fn (i, b) => (prefix ^ string_of_int i, b)) bits;

(*A literal rule instantiated at its variables by name; every variable is bool or a literal, so no
  type is inferred.*)
fun literal_instance rule insts =
  Thm.instantiate (TVars.empty, Vars.make (map (fn v as ((x, _), _) => (v, the (AList.lookup (op =) insts x)))
    (Term.add_vars (Thm.prop_of rule) []))) rule;

val literal_bit_rules = @{thms isabelle_literal_less_bit0 isabelle_literal_less_bit1 isabelle_literal_less_bit2
  isabelle_literal_less_bit3 isabelle_literal_less_bit4 isabelle_literal_less_bit5 isabelle_literal_less_bit6};

fun literal_less ctxt a b =
  (case (literal_parts a, literal_parts b, Thm.term_of a) of
    (SOME xs, SOME ys, _) =>
      let
        val (bs, s) = (take 7 xs, nth xs 7);
        val (cs, t) = (take 7 ys, nth ys 7);
        val ends = [("s", s), ("t", t)];
      in
        (case find_first (fn i => not (aconvc (nth bs i, nth cs i))) [6, 5, 4, 3, 2, 1, 0] of
          NONE =>
            Thm.implies_elim (literal_instance @{thm isabelle_literal_less_same} (literal_bits "b" bs @ ends))
              (literal_less ctxt s t)
        | SOME k =>
            (case (Thm.term_of (nth bs k), Thm.term_of (nth cs k)) of
              (Const (\<^const_name>\<open>False\<close>, _), Const (\<^const_name>\<open>True\<close>, _)) =>
                literal_instance (nth literal_bit_rules k)
                  (literal_bits "b" (take k bs) @ literal_bits "c" (take k cs) @
                    map (fn i => ("h" ^ string_of_int i, nth bs i)) (k + 1 upto 6) @ ends)
            | _ => raise CTERM ("literal_less: the names are not strictly increasing", [a, b])))
      end
  | (NONE, SOME ys, Const (\<^const_name>\<open>Groups.zero\<close>, _)) =>
      literal_instance @{thm isabelle_literal_less_empty} (literal_bits "b" (take 7 ys) @ [("t", nth ys 7)])
  | _ => raise CTERM ("literal_less: the names are not strictly increasing", [a, b]));

(*The distinct names and the closed positions of a defined context, and the length of its table.*)
fun context_closure ctxt def =
  let
    val def' = Local_Defs.meta_rewrite_rule ctxt def;
    val C = Thm.lhs_of def';
    val rhs = Thm.rhs_of def';
    val (names_ns, es) = Thm.dest_comb rhs;
    val (names_app, ns) = Thm.dest_comb names_ns;
    val names = Thm.dest_arg names_app;
    val counted = names_length ctxt (Thm.apply \<^cterm>\<open>length :: String.literal list \<Rightarrow> nat\<close> names);
    val nodes_counted = nodes_length ctxt (Thm.apply \<^cterm>\<open>length :: isabelle_type_node list \<Rightarrow> nat\<close> ns);
    val context_inst = [(("C", 0), C), (("names", 0), names), (("ns", 0), ns), (("es", 0), es)];
    val distinct_names =
      Thm.implies_elim
        (meta_premise (infer_instantiate ctxt context_inst @{thm isabelle_shared_names_distinct}) def')
        (increasing ctxt \<^cterm>\<open>(<) :: String.literal \<Rightarrow> String.literal \<Rightarrow> bool\<close> (literal_less ctxt) names);
    val positions =
      infer_instantiate ctxt
        (context_inst @ [(("N", 0), Thm.rhs_of counted), (("M", 0), Thm.rhs_of nodes_counted)])
        @{thm isabelle_shared_positions_closed}
      |> (fn th => meta_premise th def') |> (fn th => meta_premise th counted)
      |> below_premise ctxt |> (fn th => meta_premise th nodes_counted) |> below_premise ctxt;
  in (def', counted, distinct_names, positions) end;

(*The roots of a defined context use only positions of the context's table.*)
fun roots_closure ctxt (def', counted) roots_def =
  let
    val roots_def' = Local_Defs.meta_rewrite_rule ctxt roots_def;
    val R = Thm.lhs_of roots_def';
    val (ms_app, ts) = Thm.dest_comb (Thm.rhs_of roots_def');
    val ms = Thm.dest_arg ms_app;
    val nodes_counted = nodes_length ctxt (Thm.apply \<^cterm>\<open>length :: isabelle_type_node list \<Rightarrow> nat\<close> ms);
    val rhs = Thm.rhs_of def';
    val (names_ns, es) = Thm.dest_comb rhs;
    val (names_app, ns) = Thm.dest_comb names_ns;
  in
    infer_instantiate ctxt
      [(("R", 0), R), (("ms", 0), ms), (("ts", 0), ts), (("C", 0), Thm.lhs_of def'),
       (("names", 0), Thm.dest_arg names_app), (("ns", 0), ns), (("es", 0), es),
       (("N", 0), Thm.rhs_of counted), (("M", 0), Thm.rhs_of nodes_counted)]
      @{thm isabelle_shared_roots_closed}
    |> (fn th => meta_premise th roots_def') |> (fn th => meta_premise th def')
    |> (fn th => meta_premise th counted) |> below_premise ctxt
    |> (fn th => meta_premise th nodes_counted) |> below_premise ctxt
  end;

(*The roots of a defined context are distinct: the positions of their constants are read from the
  shared presentation of the roots alone, each root by one instantiation that reads neither its type
  nor the table of types, and the positions are compared as numerals.*)
val heads_rules = map mk_meta_eq @{thms isabelle_shared_heads};

fun distinct_numerals_ctxt ctxt = put_simpset HOL_basic_ss ctxt addsimps
  @{thms distinct.simps list.set insert_iff empty_iff simp_thms numeral_eq_iff num.inject num.distinct
    zero_neq_numeral numeral_eq_one_iff one_eq_numeral_iff zero_neq_one};

fun roots_distinct ctxt roots_def =
  let
    val roots_def' = Local_Defs.meta_rewrite_rule ctxt roots_def;
    val (ms_app, ts) = Thm.dest_comb (Thm.rhs_of roots_def');
    val ms = Thm.dest_arg ms_app;
    val f = Thm.apply \<^cterm>\<open>isabelle_table_type\<close> (Thm.apply \<^cterm>\<open>isabelle_type_table\<close> ms);
    fun heads ct =
      (case Thm.term_of (Thm.dest_arg ct) of
        Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ _ $ _ =>
          let
            val xs = Thm.dest_arg ct;
            val x = Thm.dest_arg1 xs;
            val step = literal_instance (nth heads_rules 1)
              [("f", f), ("c", Thm.dest_arg1 x), ("T", Thm.dest_arg x), ("ts", Thm.dest_arg xs)];
          in Thm.transitive step (Conv.arg_conv heads (Thm.rhs_of step)) end
      | _ => literal_instance (nth heads_rules 0) [("f", f)]);
    val rule =
      meta_premise (infer_instantiate ctxt
        [(("R", 0), Thm.lhs_of roots_def'), (("ms", 0), ms), (("ts", 0), ts)]
        @{thm isabelle_shared_roots_distinct}) roots_def';
    val read = heads (Thm.dest_arg1 (Thm.dest_arg (Thm.cprem_of rule 1)));
    val rule' = meta_premise (infer_instantiate ctxt [(("cs", 0), Thm.rhs_of read)] rule) read;
    val distinct = Goal.prove_internal ctxt [] (Thm.cprem_of rule' 1)
      (fn _ => simp_tac (distinct_numerals_ctxt ctxt) 1);
  in Thm.implies_elim rule' distinct end;

(*Define NAME_context and NAME_roots and note the exporter's obligations at the defined state:
  NAME_declared_once, NAME_names_distinct, NAME_positions_closed, NAME_roots_closed and
  NAME_roots_distinct.*)
fun define_state binding context roots lthy =
  let
    val name = Binding.suffix_name "_context" binding;
    val ((_, (_, def)), lthy1) = Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), context)) lthy;
    val once = declared_once lthy1 def;
    val (def', counted, distinct_names, positions) = context_closure lthy1 def;
    val roots_name = Binding.suffix_name "_roots" binding;
    val ((_, (_, roots_def)), lthy2) =
      Local_Theory.define ((roots_name, NoSyn), ((Thm.def_binding roots_name, []), roots)) lthy1;
    val roots_closed = roots_closure lthy2 (def', counted) roots_def;
    val distinct_roots = roots_distinct lthy2 roots_def;
    fun note suffix th = Local_Theory.note ((Binding.suffix_name suffix binding, []), [th]) #> snd;
  in
    lthy2 |> note "_declared_once" once |> note "_names_distinct" distinct_names
      |> note "_positions_closed" positions |> note "_roots_closed" roots_closed
      |> note "_roots_distinct" distinct_roots
  end;

(*Define NAME_context, NAME_roots and the roots of each named group. Every group is read
  against the one name table of the defined context, so the positions of a group's roots are
  positions of that context. Which roots form a group is the caller's choice, not the
  exporter's.*)
fun define binding groups lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    fun names_of terms = distinct (op =) (maps (fn t => rev (Term.add_const_names t [])) terms);
    val group_names = map (apsnd names_of) groups;
    val root_names = distinct (op =) (maps snd group_names);
    val (context, root_list, group_lists, _) =
      context_terms thy (member (op =) root_names) root_names [] group_names [];
    fun define_value suffix value =
      let val name = Binding.suffix_name suffix binding
      in Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), value)) #> snd end;
  in
    lthy |> define_state binding context root_list
      |> fold (fn (suffix, value) => define_value suffix value) group_lists
  end;

(*The root names of a state defined in an ancestor context: the positions of its roots, read
  from the definition of its roots, resolved in the table of the definition of its context.*)
fun defined_root_names roots_def context_def =
  let
    fun arguments def = snd (strip_comb (Thm.term_of (Thm.rhs_of def)));
    val names =
      (case arguments context_def of
        [names, _, _] => map HOLogic.dest_literal (HOLogic.dest_list names)
      | _ => raise THM ("Not a shared context definition", 0, [context_def]));
    val roots =
      (case arguments roots_def of
        [_, roots] => HOLogic.dest_list roots
      | _ => raise THM ("Not a shared roots definition", 0, [roots_def]));
    fun root (\<^Const_>\<open>Isabelle_Constant _ for position _\<close>) = nth names (snd (HOLogic.dest_number position))
      | root t = raise TERM ("Root is not a constant", [t]);
  in distinct (op =) (map root roots) end;

(*Define NAME_context and NAME_roots again in the current context, from the same roots as a
  state defined in an ancestor context, and NAME_introduced as the logical constants a given
  theory declares. Those constants are expanded and seeded besides the roots, so the state holds
  their specifications even when no root reaches them; an introduced constant no root reaches
  is then an unreached entity of the state, not an invisible one. An abbreviation is syntax: it
  declares no logical constant, so it introduces no entity.*)
fun define_again binding (roots_def, context_def) introducing lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val root_names = defined_root_names roots_def context_def;
    val theory_name = Context.theory_long_name introducing;
    val introduced =
      map_filter (fn (c, (_, NONE)) => if declaring_theory thy c = theory_name then SOME c else NONE
                   | _ => NONE)
        (#constants (Consts.dest (Sign.consts_of thy)));
    val expand = member (op =) (root_names @ introduced);
    val (context, root_list, group_lists, _) =
      context_terms thy expand root_names introduced [("_introduced", introduced)] [];
    fun define_value suffix value =
      let val name = Binding.suffix_name suffix binding
      in Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), value)) #> snd end;
  in
    lthy |> define_state binding context root_list
      |> fold (fn (suffix, value) => define_value suffix value) group_lists
  end;

end
\<close>

end
