theory Native_Control_Quotation_Code
  imports Native_Control_Quotation_Representation
begin

lemma indexed_interface_enumeration:
  "{(d,p d) |d. d\<in>D}=(\<lambda>d. (d,p d)) ` D"
  by auto

lemma indexed_clause_enumeration:
  "{((d,c),S). d\<in>D \<and> (c,S)\<in>C d}=
    (\<Union>d\<in>D. (\<lambda>(c,S). ((d,c),S)) ` C d)"
  by auto

lemma finite_empty_object_encoding [simp]:
  "finite_object_of empty_artifact=finite_empty_artifact"
  using finite_object_of_decode[of finite_empty_artifact] by simp

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
    fun record_generated c =
      let val qualifier = Long_Name.qualifier c
      in qualifier <> "" andalso
        (is_some (Record.get_info thy qualifier) orelse record_generated qualifier) end;
    fun items c =
      if Isabelle_Entity_Export.base_constant thy c orelse record_generated c
        orelse c = @{const_name empty_artifact} then []
      else (case try (Global_Theory.get_thm thy) (c ^ "_def") of
        NONE => [] | SOME th => [(c, th)]);
    val (_, selected) = Isabelle_Constant_Closure.closure items
      (fn th => Term.add_const_names (Thm.prop_of th) []) (Term.add_const_names rhs []);
    val enumeration = put_simpset HOL_basic_ss lthy addsimps
      @{thms indexed_interface_enumeration indexed_clause_enumeration};
    val definitions = map (Simplifier.full_simplify enumeration o snd) (Symtab.dest selected);
    val _ = writeln ("FINITE_PROGRAM_CLOSURE_END definitions=" ^ string_of_int (length definitions) ^ "\n" ^ cat_lines (Symtab.keys selected));
    val _ = writeln "FINITE_PROGRAM_SIMPLIFY_BEGIN";
    val equation = Simplifier.full_simplify (lthy addsimps definitions) definition;
    val _ = writeln ("FINITE_PROGRAM_REDUCTION definitions=" ^ string_of_int (length definitions) ^
      " nodes=" ^ string_of_int (Term.size_of_term (Thm.prop_of equation)));
  in snd (Local_Theory.note ((binding, @{attributes [code]}), [equation]) lthy) end;
end;
\<close>

local_setup \<open>Native_Finite_Equations.note @{binding finite_request_quotation_program_code}
  @{thm finite_request_quotation_program_def}\<close>

export_code finite_request_quotation_program finite_system_formed fcard finite_system_definitions integer_of_nat
  in Eval module_name Native_Control_Quotation file_prefix "native_control_quotation"

end
