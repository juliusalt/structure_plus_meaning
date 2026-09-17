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

end
\<close>

text \<open>
  The traversal is shared by every exporter that presents checked context content: an
  exporter chooses which items a constant contributes and which constants an item mentions.
  It computes a selection inside the checked context; it establishes no semantic claim.
\<close>

end
