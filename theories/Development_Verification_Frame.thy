theory Development_Verification_Frame
  imports Isabelle_Constant_Closure Carrier_Indexes Factor_Use_Renaming
begin

section \<open>The frame a verification answer's theory is read in\<close>

text \<open>
  The first problem's verification request (DECISIONS.md, "The first problem's requirements use the
  test of a native distinction; the octet audit is one of its parts", and "Non-nominality of uses is
  equivariance under use permutations, a contract the verification request checks") checks on
  Isabelle text the parts of the test no native program checks today. The answer's theory states a
  program and, for each entry the answer adds, its contract and its equivariance clause; the frame's
  check, run after them as the command
  \<open>ML \<open>Development_Verification_Frame.check \<^theory> "P" ["d\<^sub>1", \<dots>, "d\<^sub>n"]\<close>\<close> (the harness
  places it; the repository's theory headers declare no keywords, so the frame adds none), refuses
  the theory, naming the entry, unless for every named entry \<open>d\<close>:

  \<^item> (a), (b) a contract stands in a required form: an interpretation of
    @{text presented_relation_contract} (an interpretation of @{text presented_function_contract}
    registers its graph relation so) whose observation is \<open>\<lambda>p q. (d, Pair_Term p q) \<in> positive_meaning P\<close>;
    its two classes are presentation classes by the locale, so the contract's invariance over every
    presentation is the locale's theorem;
  \<^item> (c) no statement of that contract (its classes, relation and observation) reaches, through the
    shared constant closure (@{text Isabelle_Constant_Closure}: kernel definitions, followed to every
    constant they mention), a constant or a type of the bootstrap loop's presentations as task 381's
    entry lists them, named by the theories that declare them;
  \<^item> (f) where that closure reaches a store (the binary and path stores, the red-black tree), some
    interpretation of @{text native_carrier_index} has an index or search the closure reaches too;
  \<^item> (d) a theorem of this theory states the notion's clause @{text renaming_equivariant} of the
    contract's relation, over the product of its two classes' domains, at the use action those
    classes derive: an action the use instance states as a theorem (the environment, site context,
    program entry, site and use actions of @{text Factor_Use_Renaming}), found by its domain at its
    notion's own type; the product, list, finite-set and library finite-set actions of the classes
    whose domains have the forms those constructions produce; the trivial action on a type built
    only from constructors of exact values (@{text use_free_constructors}). Any other class is
    refused, its domain named.
    The frame states the clause; an action the answer supplies never enters it.

  These are proxies read on Isabelle text, the bootstrap verifier's, until native proof admission;
  they fix the forms a contract takes and the constants it may not reach, nothing of what it states.
  How the clause is proved is the answer's; that it stands is checked.
\<close>

ML \<open>
structure Development_Verification_Frame =
struct

(*The bootstrap loop's presentations (task 381's part (c)): the development_problem datatype, the
  Isabelle state datatypes, task 9's rows, loci, prefixes and keys, readiness_presents,
  state_presents, request_presents and development_rows_present, by the theories declaring them.*)
val bootstrap_theories =
  ["Development_Problems", "Isabelle_Terms", "Isabelle_Entities", "Development_Rows",
   "Development_Row_Data", "Development_State_Rows", "Development_State_Presenter",
   "Development_Loci", "Development_Entity_Keys", "Development_Request_Keys",
   "Development_Native_Selection"];

val store_theories =
  ["Binary_Path_Stores", "Binary_Relation_Stores", "Binary_Nested_Stores", "Native_Path_Stores",
   "RBT", "RBT_Impl"];

fun home name = hd (Long_Name.explode name);

fun add_type_constructors (Type (a, Ts)) = insert (op =) a #> fold add_type_constructors Ts
  | add_type_constructors _ = I;

val use_type = \<^typ>\<open>local_address option\<close>;

(*Each action the use instance states, at the subject type of its notion: a polymorphic theorem is
  never matched at another type, so no component holding uses is left unrenamed.*)
val use_actions =
  [(@{thm Factor_Use_Renaming.environment_renaming_action},
     \<^typ>\<open>local_address option artifact_environment\<close>),
   (@{thm Factor_Use_Renaming.site_context_renaming_action}, \<^typ>\<open>site_context\<close>),
   (@{thm Factor_Use_Renaming.program_entry_renaming_action}, \<^typ>\<open>program_entry_context\<close>),
   (@{thm Factor_Use_Renaming.site_renaming_action}, \<^typ>\<open>local_address option \<times> local_address\<close>),
   (@{thm Factor_Use_Renaming.use_renaming_action}, use_type)];

(*The type constructors of exact values, which hold no use by their definitions: the trivial action
  is derived only over types built from them alone, never over a type variable or another
  constructor, whose definition may hold a use.*)
val use_free_constructors =
  [\<^type_name>\<open>bool\<close>, \<^type_name>\<open>nat\<close>, \<^type_name>\<open>unit\<close>, \<^type_name>\<open>list\<close>,
   \<^type_name>\<open>prod\<close>, \<^type_name>\<open>option\<close>, \<^type_name>\<open>set\<close>, \<^type_name>\<open>fset\<close>,
   \<^type_name>\<open>fun\<close>, \<^type_name>\<open>factor_term\<close>, \<^type_name>\<open>exact_target\<close>,
   "Generation_Structures.generation_structure", fst (dest_Type \<^typ>\<open>exact_artifact\<close>),
   fst (dest_Type \<^typ>\<open>nat rra_structure\<close>), fst (dest_Type \<^typ>\<open>(nat,nat) opaque_basis\<close>)];

fun use_free T =
  not (Term.exists_subtype (fn U => U = use_type) T) andalso
  (case T of
    Type (a, Ts) => member (op =) use_free_constructors a andalso forall use_free Ts
  | _ => false);

fun refuse entry msg =
  error ("The verification frame refuses the theory at the entry " ^ entry ^ ": " ^ msg);

fun instances thy loc morph =
  map (fn ((x, T), _) => (x, Morphism.term morph (Free (x, T)))) (Locale.params_of thy loc);

fun registrations thy name =
  let val loc = Locale.intern thy name
  in map (instances thy loc o snd) (Locale.registrations_of (Context.Theory thy) loc) end;

fun param ps x = the (AList.lookup (op =) ps x);

(*An action the use instance states, if its domain is the class's.*)
fun stated_action thy D (th, subject) =
  let
    val (adm, act, dom) =
      (case HOLogic.dest_Trueprop (Thm.concl_of th) of
        _ $ adm $ act $ dom => (adm, act, dom)
      | t => raise TERM ("stated_action", [t]));
    val tyenv = Sign.typ_match thy (fastype_of dom, fastype_of D) Vartab.empty;
  in
    if domain_type (fastype_of D) = subject andalso
      Envir.subst_type tyenv (fastype_of adm) = (use_type --> use_type) --> HOLogic.boolT andalso
      Envir.beta_eta_contract (Envir.subst_term_types tyenv dom) aconv Envir.beta_eta_contract D
    then SOME (Envir.subst_term_types tyenv act) else NONE
  end handle Type.TYPE_MATCH => NONE;

fun component T (Const (\<^const_name>\<open>True\<close>, _)) _ = SOME (Abs ("x", T, \<^const>\<open>True\<close>))
  | component _ (d $ (Const (s, _) $ Bound 0)) sel =
      if s = sel andalso not (loose_bvar1 (d, 0)) then SOME d else NONE
  | component _ _ _ = NONE;

fun lifted construction act =
  Abs ("h", use_type --> use_type, Const (construction, dummyT) $ (act $ Bound 0));

(*The use action a class's domain derives, or none: an action the use instance states, at its
  notion's type; the constructions of Presentation_Equivariance at the domain forms their classes
  produce — the product (renaming_action_product, also of two unrestricted components), lists
  (renaming_action_lists), finite sets (renaming_action_sets) and finite sets of the library
  (renaming_action_fsets); the trivial action over a use-free type.*)
fun derive thy D =
  (case get_first (stated_action thy D) use_actions of
    SOME act => SOME act
  | NONE =>
      let
        val T = domain_type (fastype_of D);
        fun product d1 d2 =
          (case (derive thy d1, derive thy d2) of
            (SOME a1, SOME a2) => SOME (Const (\<^const_name>\<open>product_action\<close>, dummyT) $ a1 $ a2)
          | _ => NONE);
        fun each d construction =
          if loose_bvar1 (d, 0) then NONE else Option.map (lifted construction) (derive thy d);
      in
        (case Envir.beta_eta_contract D of
          Abs (_, _, Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>set\<close>, _) $ Bound 0) $ d) =>
            each d \<^const_name>\<open>map\<close>
        | Abs (_, _, Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>fset\<close>, _) $ Bound 0) $ d) =>
            each d \<^const_name>\<open>fimage\<close>
        | Abs (_, _, Const (\<^const_name>\<open>conj\<close>, _) $ (Const (\<^const_name>\<open>finite\<close>, _) $ Bound 0) $
            (Const (\<^const_name>\<open>Ball\<close>, _) $ Bound 0 $ d)) => each d \<^const_name>\<open>image\<close>
        | Abs (_, Type (\<^type_name>\<open>prod\<close>, [T1, T2]), Const (\<^const_name>\<open>conj\<close>, _) $ l $ r) =>
            (case (component T1 l \<^const_name>\<open>fst\<close>, component T2 r \<^const_name>\<open>snd\<close>) of
              (SOME d1, SOME d2) => product d1 d2
            | _ => NONE)
        | Abs (_, Type (\<^type_name>\<open>prod\<close>, [T1, T2]), Const (\<^const_name>\<open>True\<close>, _)) =>
            product (Abs ("x", T1, \<^const>\<open>True\<close>)) (Abs ("x", T2, \<^const>\<open>True\<close>))
        | _ => if use_free T then SOME (Abs ("h", use_type --> use_type, Abs ("a", T, Bound 0))) else NONE)
      end);

fun clause_of ctxt (actD, actE) D E rel =
  let
    val fst_z = Const (\<^const_name>\<open>fst\<close>, dummyT) $ Bound 0;
    val snd_z = Const (\<^const_name>\<open>snd\<close>, dummyT) $ Bound 0;
  in
    Syntax.check_term ctxt (HOLogic.mk_Trueprop
      (Const (\<^const_name>\<open>renaming_equivariant\<close>, dummyT) $ Syntax.parse_term ctxt "bij" $
        (Const (\<^const_name>\<open>product_action\<close>, dummyT) $ actD $ actE) $
        Abs ("z", dummyT, Const (\<^const_name>\<open>conj\<close>, dummyT) $ (D $ fst_z) $ (E $ snd_z)) $
        Abs ("z", dummyT, rel $ fst_z $ snd_z)))
    |> Envir.beta_eta_contract
  end;

fun own_facts thy =
  Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy))
    (Global_Theory.facts_of thy)
  |> maps snd;

fun stands thy facts clause =
  exists (fn th => Thm.nprems_of th = 0 andalso
    Pattern.matches thy (Envir.beta_eta_contract (Thm.prop_of th), clause)) facts;

fun check thy program entries =
  let
    val ctxt = Proof_Context.init_global thy;
    val P = Syntax.read_term ctxt program;
    val contracts = registrations thy "presented_relation_contract";
    val stores = registrations thy "native_carrier_index";
    val definitions = Isabelle_Constant_Closure.kernel_definitions thy;
    val facts = own_facts thy;
    fun reached seeds =
      let
        val (seen, selected) =
          Isabelle_Constant_Closure.closure definitions (fn t => Term.add_const_names t [])
            (fold Term.add_const_names seeds []);
      in
        (sort_strings (Symtab.keys seen),
         sort_strings (fold (fold_types add_type_constructors)
           (seeds @ map snd (Symtab.dest selected)) []))
      end;
    fun observation d =
      Syntax.check_term ctxt (Abs ("p", dummyT, Abs ("q", dummyT,
        Const (\<^const_name>\<open>Set.member\<close>, dummyT) $
          (Const (\<^const_name>\<open>Pair\<close>, dummyT) $ d $
            (Const (\<^const_name>\<open>Pair_Term\<close>, dummyT) $ Bound 1 $ Bound 0)) $
          (Const (\<^const_name>\<open>positive_meaning\<close>, dummyT) $ P))))
      |> Envir.beta_eta_contract;
    fun check_entry entry =
      let
        val expected = observation (Syntax.parse_term ctxt entry);
        val found =
          filter (fn ps => Envir.beta_eta_contract (param ps "observe") aconv expected) contracts;
        val _ =
          if null found then
            refuse entry ("no interpretation of presented_relation_contract or " ^
              "presented_function_contract states a contract whose observation is " ^
              Syntax.string_of_term ctxt expected)
          else ();
        fun check_contract ps =
          let
            val (constants, types) = reached (map snd ps);
            val bootstrap_constants = filter (member (op =) bootstrap_theories o home) constants;
            val bootstrap_types = filter (member (op =) bootstrap_theories o home) types;
            val _ =
              if null bootstrap_constants andalso null bootstrap_types then ()
              else refuse entry ("its contract's statement reaches, through the shared constant " ^
                "closure, the bootstrap loop's presentations: the constants " ^
                commas bootstrap_constants ^ "; the types " ^ commas bootstrap_types);
            val store_constants = filter (member (op =) store_theories o home) constants;
            fun indexes ps' =
              fold Term.add_const_names (map (param ps') ["build", "search", "index_term"]) [];
            val _ =
              if null store_constants orelse
                exists (fn ps' => exists (member (op =) store_constants) (indexes ps')) stores
              then ()
              else refuse entry ("its contract relies on the store constant " ^ hd store_constants ^
                ", and no interpretation of native_carrier_index has an index the closure reaches");
            val D = param ps "D";
            val E = param ps "E";
            fun action t =
              (case derive thy t of
                SOME a => a
              | NONE => refuse entry ("no use action derives for the class over the domain " ^
                  Syntax.string_of_term ctxt t));
            val clause = clause_of ctxt (action D, action E) D E (param ps "relation");
          in
            if stands thy facts clause then ()
            else refuse entry ("no theorem of this theory states its use equivariance clause " ^
              Syntax.string_of_term ctxt clause)
          end;
      in List.app check_contract found end;
    val _ = List.app check_entry entries;
  in
    writeln ("The verification frame accepts the entries " ^ commas entries ^ " of " ^
      Syntax.string_of_term ctxt P)
  end;

end
\<close>

end
