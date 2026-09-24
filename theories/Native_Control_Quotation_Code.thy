theory Native_Control_Quotation_Code
  imports Native_Control_Quotation_Representation Factor_Finite_System_Unions Factor_Finite_View_Installation
    Factor_System_Restriction Bootstrap_Finite_Closure
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

section \<open>A program's finite presentation is derived from its parts'\<close>

text \<open>
  A system whose interfaces and clauses lie within those of a formed system is presented exactly by its
  finite presentation, formed or not: a union's parts and a view extension's predecessor are such parts.
  So the presentation of a formed union is the finite union of its parts' presentations, that of a formed
  view extension the finite view extension of its predecessor's, and that of a restriction the finite
  restriction of the restricted program's. A rooted program is the restriction to the closure its finite
  presentation computes.
\<close>

lemma decode_finite_system_of_part:
  assumes formed: "schema_system_formed R"
    and interfaces: "system_interfaces P\<subseteq>system_interfaces R" and clauses: "system_clauses P\<subseteq>system_clauses R"
  shows "decode_finite_system (finite_system_of P)=P"
proof -
  have finite: "finite (system_interfaces P)" "finite (system_clauses P)"
    using formed interfaces clauses by (auto simp: schema_system_formed_def intro: finite_subset)
  have interface: "decode_finite_pattern (finite_pattern_of p)=p" if "(d,p)\<in>system_interfaces P" for d p
  proof -
    have "(d,p)\<in>system_interfaces R" using that interfaces by blast
    then show ?thesis using formed by (auto simp: schema_system_formed_def intro: decode_finite_pattern_of)
  qed
  have clause: "decode_finite_schema (finite_schema_of S)=S" if "(k,S)\<in>system_clauses P" for k S
  proof -
    have "(k,S)\<in>system_clauses R" using that clauses by blast
    then show ?thesis using formed by (cases k) (auto simp: schema_system_formed_def intro: decode_finite_schema_of)
  qed
  have i: "map_relation_values decode_finite_pattern
      (map_relation_values finite_pattern_of (system_interfaces P))=system_interfaces P"
    by (rule map_relation_values_inverse) (erule interface)
  have c: "map_relation_values decode_finite_schema
      (map_relation_values finite_schema_of (system_clauses P))=system_clauses P"
    by (rule map_relation_values_inverse) (erule clause)
  have ifs: "fset (Abs_fset (map_relation_values finite_pattern_of (system_interfaces P)))=
      map_relation_values finite_pattern_of (system_interfaces P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  have cfs: "fset (Abs_fset (map_relation_values finite_schema_of (system_clauses P)))=
      map_relation_values finite_schema_of (system_clauses P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  show ?thesis
    by (rule schema_system.equality)
      (simp_all add: decode_finite_system_def finite_system_of_def ifs cfs i c)
qed

theorem finite_system_of_union:
  assumes formed: "schema_system_formed (system_union P Q)"
  shows "finite_system_of (system_union P Q)=finite_system_union (finite_system_of P) (finite_system_of Q)"
proof -
  have left: "decode_finite_system (finite_system_of P)=P"
    by (rule decode_finite_system_of_part[OF formed]) (simp_all add: system_union_def)
  have right: "decode_finite_system (finite_system_of Q)=Q"
    by (rule decode_finite_system_of_part[OF formed]) (simp_all add: system_union_def)
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: finite_system_union_correct decode_finite_system_of[OF formed] left right)
qed

theorem finite_system_of_view:
  assumes formed: "schema_system_formed (add_view_definition P d p C)"
  shows "finite_system_of (add_view_definition P d p C)=finite_add_view_definition (finite_system_of P) d
    (finite_pattern_of p) (Abs_fset (map_relation_values finite_schema_of C))"
proof -
  have base: "decode_finite_system (finite_system_of P)=P"
    by (rule decode_finite_system_of_part[OF formed]) (auto simp: add_view_definition_def)
  have interface: "(d,p)\<in>system_interfaces (add_view_definition P d p C)"
    by (simp add: add_view_definition_def)
  have pattern: "decode_finite_pattern (finite_pattern_of p)=p"
    using formed interface by (auto simp: schema_system_formed_def intro: decode_finite_pattern_of)
  have image: "(\<lambda>(c,S). ((d,c),S)) ` C\<subseteq>system_clauses (add_view_definition P d p C)"
    by (auto simp: add_view_definition_def)
  have finite: "finite C"
  proof -
    have "finite ((\<lambda>(c,S). ((d,c),S)) ` C)"
      using formed image finite_subset by (auto simp: schema_system_formed_def)
    moreover have "inj_on (\<lambda>(c,S). ((d,c),S)) C" by (auto simp: inj_on_def)
    ultimately show ?thesis by (rule finite_imageD)
  qed
  have schemas: "decode_finite_schema (finite_schema_of S)=S" if "(c,S)\<in>C" for c S
  proof -
    have "((d,c),S)\<in>system_clauses (add_view_definition P d p C)" using that image by blast
    then show ?thesis using formed by (auto simp: schema_system_formed_def intro: decode_finite_schema_of)
  qed
  have abs: "fset (Abs_fset (map_relation_values finite_schema_of C))=map_relation_values finite_schema_of C"
    by (rule Abs_fset_inverse) (simp add: finite)
  have clauses: "map_relation_values decode_finite_schema (fset (Abs_fset (map_relation_values finite_schema_of C)))=C"
    unfolding abs by (rule map_relation_values_inverse) (erule schemas)
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: finite_add_view_definition_correct decode_finite_system_of[OF formed] base pattern clauses)
qed

definition finite_system_restriction ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd fset \<Rightarrow> ('a,'s,'d,'c) finite_schema_system" where
  "finite_system_restriction P U=\<lparr>
    finite_system_interfaces=ffilter (\<lambda>(d,p). d|\<in>|U) (finite_system_interfaces P),
    finite_system_clauses=ffilter (\<lambda>((d,c),S). d|\<in>|U) (finite_system_clauses P)\<rparr>"

lemma finite_system_restriction_correct:
  "decode_finite_system (finite_system_restriction P U)=system_restriction (decode_finite_system P) (fset U)"
  by (rule schema_system.equality)
    (auto simp: set_eq_iff finite_system_restriction_def ffilter.rep_eq)

theorem finite_system_of_restriction:
  assumes formed: "schema_system_formed P"
  shows "finite_system_of (system_restriction P (fset U))=finite_system_restriction (finite_system_of P) U"
proof -
  have part: "decode_finite_system (finite_system_of (system_restriction P (fset U)))=system_restriction P (fset U)"
    by (rule decode_finite_system_of_part[OF formed]) auto
  show ?thesis
    by (rule decode_finite_system_injective[THEN iffD1])
      (simp only: part finite_system_restriction_correct decode_finite_system_of[OF formed])
qed

definition finite_dependency_edges :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('d\<times>'d) fset" where
  "finite_dependency_edges P=ffUnion (fimage (\<lambda>z. fimage (Pair (fst (fst z))) (finite_schema_dependencies (snd z)))
    (finite_system_clauses P))"

lemma finite_dependency_edges_correct:
  "fset (finite_dependency_edges P)=system_dependency_edges (decode_finite_system P)"
proof (rule set_eqI)
  fix x :: "'a\<times>'a"
  obtain d e where x: "x=(d,e)" by (cases x)
  have "x\<in>fset (finite_dependency_edges P) \<longleftrightarrow>
      (\<exists>z\<in>fset (finite_system_clauses P). d=fst (fst z) \<and> e\<in>fset (finite_schema_dependencies (snd z)))"
    by (auto simp: x finite_dependency_edges_def ffUnion.rep_eq fimage.rep_eq)
  also have "\<dots> \<longleftrightarrow> x\<in>system_dependency_edges (decode_finite_system P)"
    by (auto simp: x system_dependency_edges_def finite_schema_dependencies_correct; force)
  finally show "x\<in>fset (finite_dependency_edges P) \<longleftrightarrow> x\<in>system_dependency_edges (decode_finite_system P)" .
qed

definition finite_definition_closure :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd fset \<Rightarrow> 'd fset" where
  "finite_definition_closure P R=R|\<union>|fimage snd (ffilter (\<lambda>z. fst z|\<in>|R)
    (finite_edge_closure (finite_dependency_edges P)))"

lemma finite_definition_closure_correct:
  "fset (finite_definition_closure P R)=system_definition_closure (decode_finite_system P) (fset R)"
proof (rule set_eqI)
  fix d
  show "d\<in>fset (finite_definition_closure P R) \<longleftrightarrow> d\<in>system_definition_closure (decode_finite_system P) (fset R)"
    by (auto simp: finite_definition_closure_def system_definition_closure_def finite_edge_closure_correct
      finite_dependency_edges_correct rtrancl_eq_or_trancl ffilter.rep_eq fimage.rep_eq image_iff; force)
qed

theorem finite_system_of_rooted:
  assumes formed: "schema_system_formed P"
  shows "finite_system_of (rooted_system P (fset R))=
    finite_system_restriction (finite_system_of P) (finite_definition_closure (finite_system_of P) R)"
  by (simp only: rooted_system_def finite_system_of_restriction[OF formed, symmetric]
    finite_definition_closure_correct decode_finite_system_of[OF formed])

section \<open>The derivation of a presentation's code equation\<close>

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

fun note binding definition lthy =
  let
    val _ = writeln "FINITE_PROGRAM_CLOSURE_BEGIN";
    val (_, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of definition));
    val (definitions, names) = reached_definitions lthy rhs;
    val _ = writeln ("FINITE_PROGRAM_CLOSURE_END definitions=" ^ string_of_int (length definitions) ^ "\n" ^
      cat_lines names);
    val _ = writeln "FINITE_PROGRAM_SIMPLIFY_BEGIN";
    val equation = Simplifier.full_simplify (lthy addsimps definitions) definition;
    val _ = writeln ("FINITE_PROGRAM_REDUCTION definitions=" ^ string_of_int (length definitions) ^
      " nodes=" ^ string_of_int (Term.size_of_term (Thm.prop_of equation)));
  in snd (Local_Theory.note ((binding, @{attributes [code]}), [equation]) lthy) end;

(*The compositional derivation: a program defined as a union or a view extension, read through its
  definition or a supplied structural equation, is presented by the finite union or view extension of
  its parts' presentations (finite_system_of_union, finite_system_of_view), each part in turn; a part
  whose presentation a supplied piece already defines is that piece, reduced nowhere again; any other
  part, and a view's own interface and clauses, are reduced as a whole program is.*)
fun reduce lthy ct = Simplifier.rewrite (lthy addsimps fst (reached_definitions lthy (Thm.term_of ct))) ct;

fun composed lthy pieces structures =
  let
    val thy = Proof_Context.theory_of lthy;
    val piece_eqs = map (fn th => mk_meta_eq (th RS @{thm sym})) pieces;
    val structure_eqs = map mk_meta_eq structures;
    val memo = Unsynchronized.ref Termtab.empty;
    val counts = Unsynchronized.ref (0, 0, 0);
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
        fun base () = (counts := (fn (a, b, c) => (a, b, c + 1)) (!counts); reduce lthy fso_ct);
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
          NONE => base ()
        | SOME seq =>
            (case Term.strip_comb (Thm.term_of (Thm.rhs_of seq)) of
              (Const (c, _), [_, _, _, _]) =>
                if c <> @{const_name add_view_definition} then base ()
                else (case formed S of NONE => base () | SOME fS => step true seq fS)
            | (Const (c, _), [_, _]) =>
                if c <> @{const_name system_union} then base ()
                else (case formed S of NONE => base () | SOME fS => step false seq fS)
            | _ => base ()))
      end;
  in (compose, fn () => !counts) end;

fun note_composed binding definition pieces structures lthy =
  let
    val (_, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of definition));
    val S = (case rhs of _ $ S => S | _ => raise TERM ("note_composed", [rhs]));
    val (compose, counts) = composed lthy pieces structures;
    val (time, eq) = Timing.timing compose (Thm.cterm_of lthy S);
    val equation = Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (K eq))) definition;
    val (steps, reused, bases) = counts ();
    val _ = writeln ("FINITE_PROGRAM_COMPOSED " ^ Binding.name_of binding ^ " steps=" ^ string_of_int steps ^
      " pieces=" ^ string_of_int reused ^ " bases=" ^ string_of_int bases ^
      " nodes=" ^ string_of_int (Term.size_of_term (Thm.prop_of equation)) ^ " " ^ Timing.message time);
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
