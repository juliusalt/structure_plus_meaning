theory Native_Control_Quotation_Code
  imports Native_Control_Quotation_Representation Factor_Finite_System_Presentations
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

section \<open>The derivation of a presentation's code equation\<close>

text \<open>
  The generic laws the derivation applies stand in @{text Factor_Finite_System_Presentations}.
\<close>

ML \<open>
structure Native_Finite_Equations =
struct
(*This only derives an equation by kernel-checked simplification with existing
  definitional theorems. It introduces no axiom, oracle, or semantic verdict.
  The complete RHS determines the reached definitions; no host schema table is
  supplied. A failed reduction remains a failed proof/export obligation.*)
fun reached_definitions lthy t =
  let
    val thy = Proof_Context.theory_of lthy;
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
      (fn th => Term.add_const_names (Thm.prop_of th) []) (Term.add_const_names t []);
    val enumeration = put_simpset HOL_basic_ss lthy addsimps
      @{thms indexed_interface_enumeration indexed_clause_enumeration};
  in (map (Simplifier.full_simplify enumeration o snd) (Symtab.dest selected), Symtab.keys selected) end;

(*The compositional derivation: a program defined as a union or a view extension, read through its
  definition or a supplied structural equation, is presented by the finite union or view extension of
  its parts' presentations (finite_system_of_union, finite_system_of_view), each part in turn; a part
  whose presentation a supplied piece already defines is that piece, reduced nowhere again; any other
  part, and a view's own interface and clauses, are reduced as a whole program is. Each part reduced
  whole is named, with why (FINITE_PROGRAM_WHOLE): it is neither a union nor a view nor a defined
  constant, it unfolds to neither, or the simpset does not prove its formation; a costly fallback thus
  shows where it happens. A sub-lineage of a presented program is to be supplied as a piece, its code
  equation the restriction of that program's presentation (finite_system_of_whole_agreement).*)
fun reduce lthy ct = Simplifier.rewrite (lthy addsimps fst (reached_definitions lthy (Thm.term_of ct))) ct;

fun composed lthy pieces structures =
  let
    val thy = Proof_Context.theory_of lthy;
    val piece_eqs = map (fn th => mk_meta_eq (th RS @{thm sym})) pieces;
    val structure_eqs = map mk_meta_eq structures;
    val memo = Unsynchronized.ref Termtab.empty;
    val counts = Unsynchronized.ref (0, 0, 0);
    val wholes = Unsynchronized.ref ([] : string list);
    fun part_name S = (case Term.head_of S of
        Const (c, _) => Long_Name.base_name c
      | _ => "a term of size " ^ string_of_int (Term.size_of_term S));
    fun presentation S =
      Thm.cterm_of lthy (Syntax.check_term lthy (Const (@{const_name finite_system_of}, dummyT) $ S));
    fun formed S = try (Goal.prove lthy [] []
        (HOLogic.mk_Trueprop (Const (@{const_name schema_system_formed}, fastype_of S --> HOLogic.boolT) $ S)))
      (fn _ => asm_full_simp_tac lthy 1);
    fun structural S_ct =
      let val S = Thm.term_of S_ct in
        (case find_first (fn eq => Thm.term_of (Thm.lhs_of eq) aconv S) structure_eqs of
          SOME eq => SOME eq
        | NONE => (case Term.head_of S of
            Const (c, _) =>
              if c = @{const_name add_view_definition} orelse c = @{const_name system_union}
              then SOME (Thm.reflexive S_ct)
              else (case try (Global_Theory.get_thm thy) (c ^ "_def") of
                NONE => NONE
              | SOME th => try (Conv.rewr_conv (mk_meta_eq th)) S_ct)
          | _ => NONE))
      end;
    fun compose S_ct =
      let val S = Thm.term_of S_ct in
        (case find_first (fn eq => (case Thm.term_of (Thm.lhs_of eq) of _ $ S' => S' aconv S | _ => false))
            piece_eqs of
          SOME eq => (counts := (fn (a, b, c) => (a, b + 1, c)) (!counts); eq)
        | NONE => (case Termtab.lookup (!memo) S of
            SOME eq => eq
          | NONE => let val eq = decompose S_ct in memo := Termtab.update (S, eq) (!memo); eq end))
      end
    and decompose S_ct =
      let
        val S = Thm.term_of S_ct;
        val fso_ct = presentation S;
        fun base reason =
          let
            val _ = counts := (fn (a, b, c) => (a, b, c + 1)) (!counts);
            val _ = wholes := (part_name S ^ " (" ^ reason ^ ")") :: !wholes;
            val _ = writeln ("FINITE_PROGRAM_WHOLE " ^ part_name S ^ ": " ^ reason);
          in reduce lthy fso_ct end;
        val unformed = "the simpset does not prove its formation";
        val neither = "it unfolds to neither a union nor a view";
        fun sub ct = Conv.rewr_conv (compose (Thm.dest_arg ct)) ct;
        fun step view seq fS =
          let
            val frhs = Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (K seq))) fS;
            val rule = if view then @{thm finite_system_of_view} else @{thm finite_system_of_union};
            val eq1 = Thm.transitive (Thm.combination (Thm.reflexive (Thm.dest_fun fso_ct)) seq)
              (mk_meta_eq (rule OF [frhs]));
            val conv = if view then
                Conv.combination_conv (Conv.combination_conv
                  (Conv.combination_conv (Conv.arg_conv sub) Conv.all_conv) (reduce lthy)) (reduce lthy)
              else Conv.combination_conv (Conv.arg_conv sub) sub;
            val _ = counts := (fn (a, b, c) => (a + 1, b, c)) (!counts);
          in Thm.transitive eq1 (conv (Thm.rhs_of eq1)) end;
      in
        (case structural S_ct of
          NONE => base "neither a union, a view nor a defined constant"
        | SOME seq =>
            (case Term.strip_comb (Thm.term_of (Thm.rhs_of seq)) of
              (Const (c, _), [_, _, _, _]) =>
                if c <> @{const_name add_view_definition} then base neither
                else (case formed S of NONE => base unformed | SOME fS => step true seq fS)
            | (Const (c, _), [_, _]) =>
                if c <> @{const_name system_union} then base neither
                else (case formed S of NONE => base unformed | SOME fS => step false seq fS)
            | _ => base neither))
      end;
  in (compose, fn () => (!counts, rev (!wholes))) end;

fun note_composed binding definition pieces structures lthy =
  let
    val (_, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of definition));
    val S = (case rhs of _ $ S => S | _ => raise TERM ("note_composed", [rhs]));
    val (compose, counts) = composed lthy pieces structures;
    val (time, eq) = Timing.timing compose (Thm.cterm_of lthy S);
    val equation = Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (K eq))) definition;
    val ((steps, reused, bases), wholes) = counts ();
    val _ = writeln ("FINITE_PROGRAM_COMPOSED " ^ Binding.name_of binding ^ " steps=" ^ string_of_int steps ^
      " pieces=" ^ string_of_int reused ^ " bases=" ^ string_of_int bases ^
      " nodes=" ^ string_of_int (Term.size_of_term (Thm.prop_of equation)) ^ " " ^ Timing.message time ^
      " whole=[" ^ commas wholes ^ "]");
  in snd (Local_Theory.note ((binding, @{attributes [code]}), [equation]) lthy) end;
end;
\<close>

section \<open>The pieces of the complete-data lineage and the request quotation program\<close>

text \<open>
  Definition admission and complete data admission are presented once, each derived from what precedes
  it in the lineage; the request quotation program and every later program over this lineage take them
  as parts.
\<close>

definition finite_call_admission_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_call_admission_program=finite_system_of definition_call_admission_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_call_admission_program_code}
  @{thm finite_call_admission_program_def} [] []\<close>

definition finite_complete_data_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_complete_data_program=finite_system_of complete_data_admission_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_complete_data_program_code}
  @{thm finite_complete_data_program_def} [@{thm finite_call_admission_program_def}] []\<close>

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_request_quotation_program_code}
  @{thm finite_request_quotation_program_def}
  [@{thm finite_complete_data_program_def}, @{thm finite_call_admission_program_def}] []\<close>

export_code finite_request_quotation_program finite_system_formed fcard finite_system_definitions integer_of_nat
  in Eval module_name Native_Control_Quotation file_prefix "native_control_quotation"

end
