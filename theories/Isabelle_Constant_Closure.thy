theory Isabelle_Constant_Closure
  imports Main
begin

section \<open>A checked context reaches the specifications of its constants\<close>

ML \<open>
structure Isabelle_Constant_Closure =
struct

(*Every kernel definition of a constant, keyed by the name of its definitional axiom.*)
fun kernel_definitions thy =
  let
    val by_constant = Symtab.make_list (Defs.dest_constdefs [] (Theory.defs_of thy));
    val axioms = Symtab.make (Theory.all_axioms_of thy);
    fun fetch def =
      (case Symtab.lookup axioms def of
        SOME prop => (def, prop)
      | NONE => error ("Missing kernel definition " ^ quote def));
  in fn name => map fetch (these (Symtab.lookup by_constant name)) end;

(*Each reached constant contributes its keyed items; the constants of every selected item
  are reached in turn. The result retains every reached constant and every selected item.*)
fun closure items constants seeds =
  let
    fun expand [] seen selected = (seen, selected)
      | expand (name :: pending) seen selected =
          if Symtab.defined seen name then expand pending seen selected
          else
            let val found = items name
            in
              expand (maps (constants o snd) found @ pending) (Symtab.update (name, ()) seen)
                (fold Symtab.update found selected)
            end;
  in expand seeds Symtab.empty Symtab.empty end;

(*The code equations in effect for a constant of a checked context, exactly as they were declared.
  Certifying them is not reading them: the code generator certifies a declared equation only after
  its function transformers (a Suc pattern under Code_Target_Nat is no constructor until one of them
  rewrites the family), and certifying under the theory's global simpset rewrites every equation by
  all simplification rules, while the code graph's certificate also carries the sorts demanded by
  what the constant calls, so it is not local to the constant. The declared equations are what a
  certificate is built from: every function transformer receives them, and the reading takes them
  from that receipt, transforms nothing and only unoverloads class operations as certification
  does. A constant without declared equations (unimplemented, abstract or a projection) has none.*)
fun code_equation_theorems thy c =
  let
    val ctxt = Simplifier.empty_simpset (Proof_Context.init_global thy);
    val declared = Unsynchronized.ref ([] : thm list);
    fun receive equations = (declared := map fst equations; NONE);
    val _ = try (Code.get_cert ctxt [receive]) c;
  in map (Axclass.unoverload ctxt) (! declared) end;

(*Note the code equations in effect for a constant under a binding of the local theory.*)
fun note_code_equations binding c lthy =
  snd (Local_Theory.note ((binding, []), code_equation_theorems (Proof_Context.theory_of lthy) c) lthy);

end
\<close>

text \<open>
  The traversal is shared by every exporter that presents checked context content: an
  exporter chooses which items a constant contributes and which constants an item mentions.
  It computes a selection inside the checked context; it establishes no semantic claim. The
  code equations in effect for a constant are read here too, so the exporter and every frame
  that offers them as a fact read them in one way.
\<close>

end
