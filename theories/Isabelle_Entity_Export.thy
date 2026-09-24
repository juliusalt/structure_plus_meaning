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
  equation, so the context term is never rewritten into the goal; of the term itself only the spine
  of the entity list is read, each entity once, by the constructor that names the equation applying
  to it. No name, no type and no statement is evaluated.
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
  contributes the position of its constant, a statement nothing, and no term is read further. The
  entity at the head of the list names the one equation of the notion that applies to it, so each
  entity is rewritten once, by its constructor rather than by trying the equations: a declaration
  keeps its position and the conversion goes on under it, a statement drops out and the conversion
  goes on in its place. An entity the notion has no equation for is a defect of the exporter.*)
val declared_rules = map mk_meta_eq @{thms isabelle_shared_declarations};
val declared_nil = hd declared_rules;
val declared_entity =
  [(\<^const_name>\<open>Isabelle_Base_Constant\<close>, (nth declared_rules 1, true)),
   (\<^const_name>\<open>Isabelle_Development_Constant\<close>, (nth declared_rules 2, true)),
   (\<^const_name>\<open>Isabelle_Frontier_Constant\<close>, (nth declared_rules 3, true)),
   (\<^const_name>\<open>Isabelle_Definition\<close>, (nth declared_rules 4, false)),
   (\<^const_name>\<open>Isabelle_Specification\<close>, (nth declared_rules 5, false)),
   (\<^const_name>\<open>Isabelle_Code_Equation\<close>, (nth declared_rules 6, false))];

fun declared_conv ct =
  (case Thm.term_of ct of
    _ $ _ $ (_ $ _ $ (Const (\<^const_name>\<open>List.list.Cons\<close>, _) $ e $ _)) =>
      (case
        (case Term.head_of e of
          Const (c, _) => AList.lookup (op =) declared_entity c
        | _ => NONE) of
        SOME (rule, declares) =>
          (Conv.rewr_conv rule then_conv
            (if declares then Conv.arg_conv declared_conv else declared_conv)) ct
      | NONE => raise CTERM ("declared_conv: not an entity of the state", [ct]))
  | _ => Conv.rewr_conv declared_nil ct);

(*A strictly increasing list is distinct, proved by comparing each adjacent pair as numerals, by the
  order of binary numerals alone: HOL's rules of sorted_wrt (<).*)
val increasing_distinct = @{thm strict_sorted_iff[THEN iffD1, THEN conjunct2]};
val increasing_step = @{thm sorted_wrt2[OF transp_on_less, THEN iffD2, OF conjI]};
val increasing_ends = @{thms sorted_wrt.simps(1)[THEN eqTrueE] sorted_wrt1[THEN eqTrueE]};

fun numeral_less_ctxt ctxt = put_simpset HOL_basic_ss ctxt addsimps
  @{thms zero_less_one zero_less_numeral one_less_numeral_iff numeral_less_iff less_num_simps le_num_simps};

fun increasing_tac ctxt =
  let val less_ctxt = numeral_less_ctxt ctxt
  in
    resolve_tac ctxt [increasing_distinct] 1
    THEN REPEAT_DETERM (resolve_tac ctxt [increasing_step] 1 THEN SOLVED' (simp_tac less_ctxt) 1)
    THEN resolve_tac ctxt increasing_ends 1
  end;

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
    val increasing = Goal.prove_internal ctxt [] (Thm.rhs_of positions) (fn _ => increasing_tac ctxt);
    val once = Thm.implies_elim shared (Thm.equal_elim (Thm.symmetric positions) increasing);
    val transport = Thm.combination (Thm.reflexive \<^cterm>\<open>Trueprop\<close>)
      (Thm.combination (Thm.reflexive \<^cterm>\<open>isabelle_declared_once\<close>) (Thm.symmetric def'));
  in Thm.equal_elim transport once end;

(*Define NAME_context and note NAME_declared_once, the exporter's obligation at the defined state.*)
fun define_context binding context lthy =
  let
    val name = Binding.suffix_name "_context" binding;
    val (_, (_, def), lthy') =
      (case Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), context)) lthy of
        ((t, (n, th)), lthy') => (t, (n, th), lthy'));
    val once = declared_once lthy' def;
  in
    lthy' |> Local_Theory.note ((Binding.suffix_name "_declared_once" binding, []), [once]) |> snd
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
    lthy |> define_context binding context |> define_value "_roots" root_list
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
    lthy |> define_context binding context |> define_value "_roots" root_list
      |> fold (fn (suffix, value) => define_value suffix value) group_lists
  end;

end
\<close>

end
