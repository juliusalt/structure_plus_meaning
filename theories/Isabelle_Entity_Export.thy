theory Isabelle_Entity_Export
  imports Isabelle_Entities Isabelle_Constant_Closure
begin

section \<open>A checked theory context defines the entities reachable from its roots\<close>

text \<open>
  The exporter runs inside the checked context. It follows the shared constant closure:
  a development constant contributes its kernel definitions, the non-definitional axioms
  that mention it and the code equations in effect; a constant of the fixed Isabelle/HOL
  base contributes nothing. Types and terms are translated constructor by constructor,
  and every name is a position in one table of the defined context. The result is an
  ordinary definition of the checked context, so a failed build defines nothing and every
  later use reads exactly the defined value.
\<close>

ML \<open>
structure Isabelle_Entity_Export =
struct

val base_sessions = ["Pure", "HOL", "HOL-Library"];

fun base_constant thy name =
  member (op =) base_sessions
    (Long_Name.qualifier (#theory_long_name (Name_Space.the_entry (Sign.const_space thy) name)));

datatype item = Definition | Specification | Code_Equation;

(*Positions and indices are binary numerals, so a long table costs no successor chain.*)
fun number i = HOLogic.mk_number \<^typ>\<open>nat\<close> i;

(*The declarations and items of the constants reached from the roots of a checked context.
  Only an expanded constant contributes items; every other development constant reached is
  on the frontier of the state and is extended when work demands it.*)
fun context_items thy expand roots =
  let
    val ctxt = Proof_Context.init_global thy;
    val kernel = Isabelle_Constant_Closure.kernel_definitions thy;
    val definitional = Symtab.make_set (map #2 (Defs.dest_constdefs [] (Theory.defs_of thy)));
    val specifications =
      fold (fn (name, prop) =>
          if Symtab.defined definitional name then I
          else fold (fn c => Symtab.cons_list (c, (name, prop))) (Term.add_const_names prop []))
        (Theory.all_axioms_of thy) Symtab.empty;
    fun code_equations c =
      (case try (Code.get_cert ctxt []) c of
        NONE => []
      | SOME cert =>
          (case try (Code.equations_of_cert thy) cert of
            SOME (_, SOME equations) =>
              map_filter (fn (_, (SOME th, _)) => SOME (Thm.prop_of th) | _ => NONE) equations
          | _ => []));
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
  in (Symtab.keys seen, map snd (Symtab.dest selected)) end;

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

fun term_term position (Const (c, T)) =
      \<^Const>\<open>Isabelle_Constant\<close> $ position c $ type_term position T
  | term_term position (Free (x, T)) = \<^Const>\<open>Isabelle_Free\<close> $ position x $ type_term position T
  | term_term position (Var ((x, i), T)) =
      \<^Const>\<open>Isabelle_Variable\<close> $ position x $ number i $ type_term position T
  | term_term position (Bound i) = \<^Const>\<open>Isabelle_Bound\<close> $ number i
  | term_term position (Abs (_, T, t)) =
      \<^Const>\<open>Isabelle_Abstraction\<close> $ type_term position T $ term_term position t
  | term_term position (t $ u) =
      \<^Const>\<open>Isabelle_Application\<close> $ term_term position t $ term_term position u;

(*The defined context: one name table, the declarations of every reached constant and the
  items the expanded constants contribute; the roots are defined as the constants they name.*)
fun context_terms thy expand root_names groups =
  let
    val (constants, items) = context_items thy expand root_names;
    fun constant c = Const (c, Sign.the_const_type thy c);
    val roots = map constant root_names;
    val declarations = map constant constants;
    val table = sort_distinct string_ord (maps term_names (roots @ declarations @ map snd items));
    val positions = Symtab.make (map_index (fn (i, name) => (name, i)) table);
    fun position name = number (the (Symtab.lookup positions name));
    fun declaration c =
      (if base_constant thy c then \<^Const>\<open>Isabelle_Base_Constant\<close>
        else if expand c then \<^Const>\<open>Isabelle_Development_Constant\<close>
        else \<^Const>\<open>Isabelle_Frontier_Constant\<close>)
        $ term_term position (constant c);
    fun item (Definition, prop) = \<^Const>\<open>Isabelle_Definition\<close> $ term_term position prop
      | item (Specification, prop) = \<^Const>\<open>Isabelle_Specification\<close> $ term_term position prop
      | item (Code_Equation, prop) = \<^Const>\<open>Isabelle_Code_Equation\<close> $ term_term position prop;
    val names_term = HOLogic.mk_list \<^typ>\<open>String.literal\<close> (map HOLogic.mk_literal table);
    val entities_term =
      HOLogic.mk_list \<^typ>\<open>isabelle_entity\<close> (map declaration constants @ map item items);
    fun root_terms names =
      HOLogic.mk_list \<^typ>\<open>isabelle_term\<close> (map (term_term position o constant) names);
  in
    (HOLogic.mk_prod (names_term, entities_term), root_terms root_names,
      map (fn (suffix, names) => (suffix, root_terms names)) groups)
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
    val (context, root_list, group_lists) =
      context_terms thy (member (op =) root_names) root_names group_names;
    fun define_value suffix value =
      let val name = Binding.suffix_name suffix binding
      in Local_Theory.define ((name, NoSyn), ((Thm.def_binding name, []), value)) #> snd end;
  in
    lthy |> define_value "_context" context |> define_value "_roots" root_list
      |> fold (fn (suffix, value) => define_value suffix value) group_lists
  end;

end
\<close>

end
