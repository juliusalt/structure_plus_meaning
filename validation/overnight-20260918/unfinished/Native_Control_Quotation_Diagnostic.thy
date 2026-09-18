theory Native_Control_Quotation_Diagnostic
  imports Factor_Request_Quotation_Base Factor_Executable_Systems Finite_Set_Encoding
    Isabelle_Entity_Export
begin

section \<open>Executable constructors are reduced from the complete checked program\<close>

definition finite_request_quotation_program where
  "finite_request_quotation_program=finite_system_of (request_quotation_system {})"

lemma finite_request_quotation_program_exact:
  "decode_finite_system finite_request_quotation_program=request_quotation_system {}"
  unfolding finite_request_quotation_program_def
  by (rule decode_finite_system_of[OF request_quotation_formed])

lemma finite_request_quotation_program_formed:
  "finite_system_formed finite_request_quotation_program"
  by (simp only: finite_system_formed_correct finite_request_quotation_program_exact request_quotation_formed)

ML \<open>
structure Native_Finite_Equations =
struct
(*This only derives an equation by kernel-checked simplification with existing
  definitional theorems. It introduces no axiom, oracle, or semantic verdict.
  The complete RHS determines the reached definitions; no host schema table is
  supplied. A failed reduction remains a failed proof/export obligation.*)
fun note binding definition lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val _ = writeln "FINITE_PROGRAM_CLOSURE_BEGIN";
    val (_, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of definition));
    fun items c =
      if Isabelle_Entity_Export.base_constant thy c then []
      else (case try (Global_Theory.get_thm thy) (c ^ "_def") of
        NONE => [] | SOME th => [(c, th)]);
    val (_, selected) = Isabelle_Constant_Closure.closure items
      (fn th => Term.add_const_names (Thm.prop_of th) []) (Term.add_const_names rhs []);
    val definitions = map snd (Symtab.dest selected);
    val _ = writeln ("FINITE_PROGRAM_CLOSURE_END definitions=" ^ string_of_int (length definitions) ^ "\n" ^ cat_lines (Symtab.keys selected));
    val _ = writeln "FINITE_PROGRAM_SIMPLIFY_BEGIN";
    val equation = definition;
    val _ = writeln ("FINITE_PROGRAM_REDUCTION definitions=" ^ string_of_int (length definitions) ^
      " nodes=" ^ string_of_int (Term.size_of_term (Thm.prop_of equation)));
  in snd (Local_Theory.note ((binding, []), [equation]) lthy) end;
end;
\<close>

local_setup \<open>Native_Finite_Equations.note @{binding finite_request_quotation_program_code}
  @{thm finite_request_quotation_program_def}\<close>


end
